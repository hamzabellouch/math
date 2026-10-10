import Mathlib
import OAI.Analysis.Conductivity.Variational.AxialDecayL2

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma finiteDecayLp_real_norm_sq (m R r : ℝ) (a : ℂ) :
    ‖finiteDecayLp m R ((r:ℂ)*a)‖^2=r^2*‖finiteDecayLp m R a‖^2 := by
  rw [finiteDecayLp_smul,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma finiteDecayLp_imag_norm_sq (m R r : ℝ) (a : ℂ) :
    ‖finiteDecayLp m R (Complex.I*(r:ℂ)*a)‖^2=r^2*‖finiteDecayLp m R a‖^2 := by
  rw [finiteDecayLp_smul,norm_smul,norm_mul,Complex.norm_I,one_mul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma torusFrequency_sq_le_rate (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : TorusModes) (j : Fin 2) : (h j:ℝ)^2 ≤ 4*(torusRate s h)^2 := by
  have hh := torusRate_lower hs h
  have hj : |(h j:ℝ)| ≤ torusSize h := by
    fin_cases j <;> simp only [torusSize,Fin.zero_eta,Fin.mk_one]
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · exact le_add_of_nonneg_left (abs_nonneg _)
  have hnon : 0 ≤ torusRate s h := Real.sqrt_nonneg _
  have habs : |(h j:ℝ)| ≤ 2*torusRate s h := by linarith
  have he := pow_le_pow_left₀ (abs_nonneg (h j:ℝ)) habs 2
  simpa only [sq_abs,mul_pow,show (2:ℝ)^2=4 by norm_num] using he

lemma finiteDecayLp_angular_bound (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (h : TorusModes) (j : Fin 2) (a : ℂ) :
    ‖finiteDecayLp (torusRate s h) R (Complex.I*(h j:ℂ)*a)‖^2 ≤
      2*torusRate s h*‖a‖^2 := by
  have hr := finiteDecayLp_rate_norm_sq (torusRate s h) R (Real.sqrt_nonneg _) a
  rw [finiteDecayLp_real_norm_sq] at hr
  have hh := mul_le_mul_of_nonneg_right (torusFrequency_sq_le_rate s hs h j)
    (sq_nonneg ‖finiteDecayLp (torusRate s h) R a‖)
  have he : (h j:ℂ)=((h j:ℝ):ℂ) := by norm_cast
  rw [he,finiteDecayLp_imag_norm_sq]
  nlinarith only [hr,hh]

lemma finiteDecayLp_axial_bound (m R : ℝ) (hm : 0  ≤  m) (a : ℂ) :
    ‖finiteDecayLp m R (-(m:ℂ)*a)‖^2 ≤ m*‖a‖^2/2 := by
  have hh := finiteDecayLp_rate_norm_sq m R hm a
  rw [finiteDecayLp_real_norm_sq] at hh
  rw [show -(m:ℂ)=((-m:ℝ):ℂ) by simp,finiteDecayLp_real_norm_sq,neg_sq]
  exact hh

def endModeCoefficient (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) : Fin 4 → ℂ :=
  ![a,-(torusRate s h:ℂ)*a,Complex.I*(h 0:ℂ)*a,Complex.I*(h 1:ℂ)*a]

abbrev FiniteCylinderJets (R : ℝ) :=
  PiLp 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R))

def endPoissonSequence (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    lp (fun _ : TorusModes => FiniteAxisL2 R) 2 :=
  ⟨fun h => finiteDecayLp (torusRate s h) R (endModeCoefficient s h (f.val 0 h) j),by
    have hu := (lp.memℓp (f.val 0)).summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hu
    have hw : Summable (fun h => torusRate s h*‖f.val 0 h‖^2) :=
      (spectralTraceGraph_exists_iff (fun h => Real.sqrt_nonneg _) (f.val 0)).mp ⟨f,rfl⟩
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    fin_cases j
    · exact (hu.mul_left R).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => finiteDecayLp_norm_sq (Real.sqrt_nonneg _) hR (f.val 0 h))
    · exact (hw.div_const 2).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => finiteDecayLp_axial_bound (torusRate s h) R (Real.sqrt_nonneg _) (f.val 0 h))
    · exact (hw.mul_left 2).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => by simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 0 (f.val 0 h))
    · exact (hw.mul_left 2).of_nonneg_of_le (fun h => sq_nonneg _)
        (fun h => by simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 1 (f.val 0 h))⟩

def endPoissonJet (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) : FiniteCylinderJets R :=
  WithLp.toLp 2 (fun j => cylinderFourier (FiniteAxisMeasure R) (endPoissonSequence s hs R hR f j))

def endPoissonModeJet (s : Fin 3 → ℝ) (R : ℝ) (h : TorusModes) (a : ℂ) : FiniteCylinderJets R :=
  WithLp.toLp 2 (fun j => cylinderMode (FiniteAxisMeasure R) h
    (finiteDecayLp (torusRate s h) R (endModeCoefficient s h a j)))

lemma endPoissonJet_component_hasSum (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    HasSum (fun h => endPoissonModeJet s R h (f.val 0 h) j) (endPoissonJet s hs R hR f j) :=
  cylinderFourier_hasSum (FiniteAxisMeasure R) (endPoissonSequence s hs R hR f j)

lemma endPoissonJet_hasSum (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) :
    HasSum (fun h => endPoissonModeJet s R h (f.val 0 h)) (endPoissonJet s hs R hR f) := by
  have ht : Tendsto (fun F : Finset TorusModes => fun j => ∑ h ∈ F,endPoissonModeJet s R h (f.val 0 h) j)
      atTop (𝓝 (fun j => endPoissonJet s hs R hR f j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact endPoissonJet_component_hasSum s hs R hR f j
  have hmap := (PiLp.continuous_toLp 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R))).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h ∈ F,endPoissonModeJet s R h (f.val 0 h)) atTop _
  convert hmap using 1
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]

theorem endPoissonJet_mem_mode_closure (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (R : ℝ) (hR : 0 ≤ R) (f : spectralTraceGraph (torusRate s)) :
    endPoissonJet s hs R hR f ∈ closure
      {u : FiniteCylinderJets R | ∃ (F : Finset TorusModes) (a : TorusModes → ℂ),
        u=∑ h ∈ F,endPoissonModeJet s R h (a h)} := by
  apply mem_closure_of_tendsto (endPoissonJet_hasSum s hs R hR f)
  exact Filter.Eventually.of_forall (fun F => ⟨F,fun h => f.val 0 h,rfl⟩)

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma spectralGraph_norm_sq {ι : Type*} (w : ι → ℝ) (f : spectralTraceGraph w) :
    ‖f‖^2=‖f.val 0‖^2+‖f.val 1‖^2 := by
  change ‖f.val‖^2=_
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_two]

lemma spectralGraph_weight_norm_sq {ι : Type*} (w : ι → ℝ) (hw : ∀ i,0 ≤ w i)
    (f : spectralTraceGraph w) :
    ‖f.val 1‖^2=∑' i,w i*‖f.val 0 i‖^2 := by
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (f.val 1)
  have he (i : ι) : ‖f.val 1 i‖^2=w i*‖f.val 0 i‖^2 := by
    rw [f.property i]
    exact sqrt_weight_norm_sq hw (f.val 0) i
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,he] using hn

lemma endModeCoefficient_add (s : Fin 3 → ℝ) (h : TorusModes) (a b : ℂ) (j : Fin 4) :
    endModeCoefficient s h (a+b) j=endModeCoefficient s h a j+endModeCoefficient s h b j := by
  fin_cases j <;> simp [endModeCoefficient,mul_add]

lemma endModeCoefficient_smul (s : Fin 3 → ℝ) (h : TorusModes) (c a : ℂ) (j : Fin 4) :
    endModeCoefficient s h (c*a) j=c*endModeCoefficient s h a j := by
  fin_cases j <;> dsimp [endModeCoefficient] <;> ring

variable (s : Fin 3 → ℝ)
  (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
  (R : ℝ) (hR : 0 ≤ R)

lemma endPoissonSequence_add (f g : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    endPoissonSequence s hs R hR (f+g) j=
      endPoissonSequence s hs R hR f j+endPoissonSequence s hs R hR g j := by
  apply lp.ext
  funext h
  change finiteDecayLp _ _ (endModeCoefficient s h (f.val 0 h+g.val 0 h) j)=_
  rw [endModeCoefficient_add,finiteDecayLp_add]
  rfl

lemma endPoissonSequence_smul (c : ℂ) (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    endPoissonSequence s hs R hR (c•f) j=c•endPoissonSequence s hs R hR f j := by
  apply lp.ext
  funext h
  change finiteDecayLp _ _ (endModeCoefficient s h (c*f.val 0 h) j)=_
  rw [endModeCoefficient_smul,finiteDecayLp_smul]
  rfl

lemma endPoissonJet_add (f g : spectralTraceGraph (torusRate s)) :
    endPoissonJet s hs R hR (f+g)=endPoissonJet s hs R hR f+endPoissonJet s hs R hR g := by
  apply PiLp.ext
  intro j
  change cylinderFourier _ (endPoissonSequence _ _ _ _ (f+g) j)=_
  rw [endPoissonSequence_add,map_add]
  rfl

lemma endPoissonJet_smul (c : ℂ) (f : spectralTraceGraph (torusRate s)) :
    endPoissonJet s hs R hR (c•f)=c•endPoissonJet s hs R hR f := by
  apply PiLp.ext
  intro j
  change cylinderFourier _ (endPoissonSequence _ _ _ _ (c•f) j)=_
  rw [endPoissonSequence_smul,map_smul]
  rfl

lemma endPoissonJet_component_norm_sq (f : spectralTraceGraph (torusRate s)) (j : Fin 4) :
    ‖endPoissonJet s hs R hR f j‖^2=
      ∑' h,‖finiteDecayLp (torusRate s h) R (endModeCoefficient s h (f.val 0 h) j)‖^2 :=
  cylinderFourier_norm_sq _ _

lemma endPoissonJet_component_bound (f : spectralTraceGraph (torusRate s)) :
    ‖endPoissonJet s hs R hR f 0‖^2 ≤ R*‖f.val 0‖^2 ∧
    ‖endPoissonJet s hs R hR f 1‖^2 ≤ ‖f.val 1‖^2/2 ∧
    ‖endPoissonJet s hs R hR f 2‖^2 ≤ 2*‖f.val 1‖^2 ∧
    ‖endPoissonJet s hs R hR f 3‖^2 ≤ 2*‖f.val 1‖^2 := by
  have hu := (lp.memℓp (f.val 0)).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hu
  have hw : Summable (fun h => torusRate s h*‖f.val 0 h‖^2) :=
    (spectralTraceGraph_exists_iff (fun h => Real.sqrt_nonneg _) (f.val 0)).mp ⟨f,rfl⟩
  have huEq : ‖f.val 0‖^2=∑' h,‖f.val 0 h‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (f.val 0)
  have hwEq := spectralGraph_weight_norm_sq (torusRate s) (fun h => Real.sqrt_nonneg _) f
  have hj (j : Fin 4) : Summable (fun h =>
      ‖finiteDecayLp (torusRate s h) R (endModeCoefficient s h (f.val 0 h) j)‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,endPoissonSequence] using
      (lp.memℓp (endPoissonSequence s hs R hR f j)).summable
        (by norm_num : 0<(2:ℝ≥0∞).toReal)
  refine ⟨?_,?_,?_,?_⟩
  · rw [endPoissonJet_component_norm_sq,huEq,←tsum_mul_left]
    exact (hj 0).tsum_le_tsum (fun h => finiteDecayLp_norm_sq (Real.sqrt_nonneg _) hR (f.val 0 h))
      (hu.mul_left R)
  · rw [endPoissonJet_component_norm_sq,hwEq,←tsum_div_const]
    exact (hj 1).tsum_le_tsum (fun h => finiteDecayLp_axial_bound _ _ (Real.sqrt_nonneg _) (f.val 0 h))
      (hw.div_const 2)
  · rw [endPoissonJet_component_norm_sq,hwEq,←tsum_mul_left]
    exact (hj 2).tsum_le_tsum (fun h => by
      simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 0 (f.val 0 h))
      (hw.mul_left 2)
  · rw [endPoissonJet_component_norm_sq,hwEq,←tsum_mul_left]
    exact (hj 3).tsum_le_tsum (fun h => by
      simpa [endModeCoefficient,mul_assoc] using finiteDecayLp_angular_bound s hs R h 1 (f.val 0 h))
      (hw.mul_left 2)

lemma endPoissonJet_norm_sq_le (f : spectralTraceGraph (torusRate s)) :
    ‖endPoissonJet s hs R hR f‖^2 ≤ (R+5)*‖f‖^2 := by
  obtain ⟨h0,h1,h2,h3⟩ := endPoissonJet_component_bound s hs R hR f
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_four]
  rw [spectralGraph_norm_sq]
  nlinarith [sq_nonneg ‖f.val 0‖,sq_nonneg ‖f.val 1‖,mul_nonneg hR (sq_nonneg ‖f.val 1‖)]

lemma endPoissonJet_norm_le (f : spectralTraceGraph (torusRate s)) :
    ‖endPoissonJet s hs R hR f‖ ≤ (R+6)*‖f‖ := by
  have hn := endPoissonJet_norm_sq_le s hs R hR f
  have hb : R+5 ≤ (R+6)^2 := by nlinarith [sq_nonneg R]
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f‖)
  nlinarith [norm_nonneg (endPoissonJet s hs R hR f),norm_nonneg f,
    mul_nonneg (show 0 ≤ R+6 by linarith) (norm_nonneg f)]

def endPoissonCLM : spectralTraceGraph (torusRate s) →L[ℂ] FiniteCylinderJets R :=
  ({ toFun := fun f => endPoissonJet s hs R hR f
     map_add' := endPoissonJet_add s hs R hR
     map_smul' := endPoissonJet_smul s hs R hR } :
    spectralTraceGraph (torusRate s) →ₗ[ℂ] FiniteCylinderJets R).mkContinuous (R+6)
    (endPoissonJet_norm_le s hs R hR)

end ScalarConductivity

end

end OAI
