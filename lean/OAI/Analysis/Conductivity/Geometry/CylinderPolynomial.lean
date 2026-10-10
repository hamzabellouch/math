import Mathlib
import OAI.Analysis.Conductivity.Geometry.CylinderJetOrthogonal

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def smoothComplexAxis : Submodule ℂ (ℝ → ℂ) where
  carrier := {q | ContDiff ℝ (↑(⊤ : ℕ∞)) q}
  zero_mem' := by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : ℝ => (0:ℂ))
    exact contDiff_const
  add_mem' := by
    intro q r hq hr
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) q from hq).add
      (show ContDiff ℝ (↑(⊤ : ℕ∞)) r from hr)
  smul_mem' := by
    intro c q hq
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) q from hq).const_smul c

instance : CoeFun smoothComplexAxis (fun _ => ℝ → ℂ) := ⟨fun q => q.val⟩

lemma smoothComplexAxis_smooth (q : smoothComplexAxis) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) q := q.property

lemma smoothFiniteAxisLp_add {q r : ℝ → ℂ} (hq : Continuous q) (hr : Continuous r) (R : ℝ) :
    smoothFiniteAxisLp (hq.add hr) R=smoothFiniteAxisLp hq R+smoothFiniteAxisLp hr R := by
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae (hq.add hr) R,smoothFiniteAxisLp_ae hq R,
    smoothFiniteAxisLp_ae hr R,Lp.coeFn_add (smoothFiniteAxisLp hq R) (smoothFiniteAxisLp hr R)]
    with t h1 h2 h3 h4
  simp only [h1,h4,h2,h3,Pi.add_apply]

lemma smoothFiniteAxisLp_smul {q : ℝ → ℂ} (hq : Continuous q) (c : ℂ) (R : ℝ) :
    smoothFiniteAxisLp (hq.const_smul c) R=c•smoothFiniteAxisLp hq R := by
  apply Lp.ext
  filter_upwards [smoothFiniteAxisLp_ae (hq.const_smul c) R,smoothFiniteAxisLp_ae hq R,
    Lp.coeFn_smul c (smoothFiniteAxisLp hq R)] with t h1 h2 h3
  simp only [h1,h3,h2,Pi.smul_apply]

lemma smoothAxisModeJet_add (q r : smoothComplexAxis) (R : ℝ) (h : TorusModes) :
    smoothAxisModeJet (smoothComplexAxis_smooth (q+r)) R h=
      smoothAxisModeJet (smoothComplexAxis_smooth q) R h+
        smoothAxisModeJet (smoothComplexAxis_smooth r) R h := by
  have hd : deriv (fun t => q t+r t)=deriv q+deriv r := by
    funext t
    exact deriv_add ((smoothComplexAxis_smooth q).differentiable (by simp) t)
      ((smoothComplexAxis_smooth r).differentiable (by simp) t)
  apply PiLp.ext
  intro j
  fin_cases j
  · exact smoothFiniteAxisLp_add (smoothComplexAxis_smooth q).continuous
      (smoothComplexAxis_smooth r).continuous R
  · change smoothFiniteAxisLp ((smoothComplexAxis_smooth (q+r)).continuous_deriv (by simp)) R=
      smoothFiniteAxisLp ((smoothComplexAxis_smooth q).continuous_deriv (by simp)) R+
        smoothFiniteAxisLp ((smoothComplexAxis_smooth r).continuous_deriv (by simp)) R
    simp only [show ((q+r : smoothComplexAxis) : ℝ → ℂ)=(fun t => q t+r t) from rfl,hd]
    exact smoothFiniteAxisLp_add _ _ R
  · change (Complex.I*(h 0:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_add]
    exact smul_add _ _ _
  · change (Complex.I*(h 1:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_add]
    exact smul_add _ _ _

lemma smoothAxisModeJet_smul (c : ℂ) (q : smoothComplexAxis) (R : ℝ) (h : TorusModes) :
    smoothAxisModeJet (smoothComplexAxis_smooth (c•q)) R h=
      c•smoothAxisModeJet (smoothComplexAxis_smooth q) R h := by
  have hd : deriv (fun t => c•q t)=c•deriv q := by
    funext t
    exact deriv_const_smul c ((smoothComplexAxis_smooth q).differentiable (by simp) t)
  apply PiLp.ext
  intro j
  fin_cases j
  · exact smoothFiniteAxisLp_smul (smoothComplexAxis_smooth q).continuous c R
  · change smoothFiniteAxisLp ((smoothComplexAxis_smooth (c•q)).continuous_deriv (by simp)) R=
      c•smoothFiniteAxisLp ((smoothComplexAxis_smooth q).continuous_deriv (by simp)) R
    simp only [show ((c•q : smoothComplexAxis) : ℝ → ℂ)=(fun t => c•q t) from rfl,hd]
    exact smoothFiniteAxisLp_smul _ c R
  · change (Complex.I*(h 0:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_smul]
    exact smul_comm _ _ _
  · change (Complex.I*(h 1:ℂ))•smoothFiniteAxisLp _ R=_
    rw [smoothFiniteAxisLp_smul]
    exact smul_comm _ _ _

def smoothAxisModeJetL (R : ℝ) (h : TorusModes) : smoothComplexAxis →ₗ[ℂ] FiniteAxisJets R where
  toFun q := smoothAxisModeJet (smoothComplexAxis_smooth q) R h
  map_add' q r := smoothAxisModeJet_add q r R h
  map_smul' c q := smoothAxisModeJet_smul c q R h

def cylinderPolynomialJetL (R : ℝ) : (TorusModes →₀ smoothComplexAxis) →ₗ[ℂ] FiniteCylinderJets R :=
  Finsupp.lsum ℂ (fun h => (cylinderJetMode R h).toLinearMap.comp (smoothAxisModeJetL R h))

lemma cylinderPolynomialJetL_apply (R : ℝ) (p : TorusModes →₀ smoothComplexAxis) :
    cylinderPolynomialJetL R p=
      ∑ h∈p.support,smoothCylinderModeJet (smoothComplexAxis_smooth (p h)) R h := by
  rw [cylinderPolynomialJetL,Finsupp.lsum_apply]
  exact Finset.sum_congr rfl (fun h _ => cylinderJetMode_smooth _ R h)

open Set MeasureTheory Filter Topology
open scoped ENNReal

abbrev SpectralModeFiber := PiLp 2 (fun _ : Fin 2 => ℂ)

def spectralJetSingle (h : TorusModes) : SpectralModeFiber →ₗᵢ[ℂ] SpectralJet TorusModes where
  toFun a := WithLp.toLp 2 (fun j => (lp.single 2 h (a j) : SpectralL2 TorusModes))
  map_add' a b := by
    apply PiLp.ext
    intro j
    exact lp.single_add (E := fun _ : TorusModes => ℂ) 2 h (a j) (b j)
  map_smul' c a := by
    apply PiLp.ext
    intro j
    exact lp.single_smul (E := fun _ : TorusModes => ℂ) 2 h c (a j)
  norm_map' a := by
    have he : ‖WithLp.toLp 2 (fun j : Fin 2 => (lp.single 2 h (a j) : SpectralL2 TorusModes))‖^2=‖a‖^2 := by
      simp only [PiLp.norm_sq_eq_of_L2,lp.norm_single (by norm_num : (0:ℝ≥0∞)<2)]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

lemma spectralJetSingle_orthogonal :
    OrthogonalFamily ℂ (fun _ : TorusModes => SpectralModeFiber) spectralJetSingle := by
  intro h k hne a b
  rw [PiLp.inner_apply]
  have hz (j : Fin 2) : inner ℂ (lp.single 2 h (a j) : SpectralL2 TorusModes) (lp.single 2 k (b j))=0 := by
    rw [lp.inner_single_left,lp.single_apply,Pi.single_eq_of_ne hne,inner_zero_right]
  exact (Finset.sum_congr rfl (fun j _ => hz j)).trans (Finset.sum_const_zero)

def weightedModeFiberL (s : Fin 3 → ℝ) (h : TorusModes) : ℂ →ₗ[ℂ] SpectralModeFiber where
  toFun a := WithLp.toLp 2 ![a,(Real.sqrt (torusRate s h):ℂ)*a]
  map_add' a b := by apply PiLp.ext; intro j; fin_cases j <;> simp [mul_add]
  map_smul' c a := by
    apply PiLp.ext
    intro j
    fin_cases j <;> simp [mul_comm,mul_assoc]

lemma weightedModeFiber_norm_sq (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) :
    ‖weightedModeFiberL s h a‖^2=(1+torusRate s h)*‖a‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin 2,‖(![a,(Real.sqrt (torusRate s h):ℂ)*a] j)‖^2)=_
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,
    Matrix.cons_val_one,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (show 0≤torusRate s h from Real.sqrt_nonneg _)]
  ring

def spectralTraceSingleL (s : Fin 3 → ℝ) (h : TorusModes) :
    ℂ →ₗ[ℂ] spectralTraceGraph (torusRate s) :=
  ((spectralJetSingle h).toLinearMap.comp (weightedModeFiberL s h)).codRestrict _ (by
    intro a k
    change (lp.single 2 h ((Real.sqrt (torusRate s h):ℂ)*a) : SpectralL2 TorusModes) k=
      (Real.sqrt (torusRate s k):ℂ)*(lp.single 2 h a : SpectralL2 TorusModes) k
    by_cases hk : k=h
    · subst k; simp
    · simp only [lp.single_apply,Pi.single_eq_of_ne hk,mul_zero])

def cylinderPolynomialTraceL (s : Fin 3 → ℝ) (t : ℝ) :
    (TorusModes →₀ smoothComplexAxis) →ₗ[ℂ] spectralTraceGraph (torusRate s) :=
  Finsupp.lsum ℂ (fun h => (spectralTraceSingleL s h).comp
    ((LinearMap.proj t).comp smoothComplexAxis.subtype))

lemma cylinderPolynomialTraceL_apply (s : Fin 3 → ℝ) (t : ℝ)
    (p : TorusModes →₀ smoothComplexAxis) :
    (cylinderPolynomialTraceL s t p).val=
      ∑ h∈p.support,spectralJetSingle h (weightedModeFiberL s h (p h t)) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_apply]
  change (spectralTraceGraph (torusRate s)).subtype (∑ h∈p.support,_)=_
  rw [map_sum]
  rfl

lemma cylinderPolynomialTraceL_norm_sq (s : Fin 3 → ℝ) (t : ℝ)
    (p : TorusModes →₀ smoothComplexAxis) :
    ‖cylinderPolynomialTraceL s t p‖^2=
      ∑ h∈p.support,(1+torusRate s h)*‖p h t‖^2 := by
  change ‖(cylinderPolynomialTraceL s t p).val‖^2=_
  rw [cylinderPolynomialTraceL_apply,spectralJetSingle_orthogonal.norm_sum]
  exact Finset.sum_congr rfl (fun h _ => weightedModeFiber_norm_sq s h (p h t))

lemma cylinderPolynomial_trace_bound (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R)
    (p : TorusModes →₀ smoothComplexAxis) {t : ℝ} (ht : t=0 ∨ t=R) :
    ‖cylinderPolynomialTraceL s t p‖^2≤cylinderTraceConstant s R*‖cylinderPolynomialJetL R p‖^2 := by
  rw [cylinderPolynomialTraceL_norm_sq,cylinderPolynomialJetL_apply,
    smoothCylinder_polynomial_norm_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [←smoothAxisModeJet_norm_sq]
  rcases ht with rfl | rfl
  · exact smoothAxisMode_trace_left s (smoothComplexAxis_smooth (p h)) hR h
  · exact smoothAxisMode_trace_right s (smoothComplexAxis_smooth (p h)) hR h

end ScalarConductivity

end

end OAI
