import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedSmear

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RetainedMeasurable_scope

open MeasureTheory Set Filter
open scoped BigOperators

open CoulombAtom
variable {N : ℕ} {A : Type*} [MeasurableSpace A]

lemma retainedSmear_measurable_eval (b : ℝ) (S : A → Finset (Fin N))
    (u : A → Configuration N) (v : A → Space)
    (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun a => retainedSmear b (S a) (u a) (v a)) := by
  simp_rw [retainedSmear_ite]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hS i)
    ((varthetaScaled_measurable b).comp (hv.sub ((measurable_pi_apply i).comp hu))) measurable_const

lemma retainedPressure_measurable_param (b : ℝ) (S : A → Finset (Fin N))
    (u : A → Configuration N) (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hu : Measurable u) :
    Measurable (fun a => retainedPressure b (S a) (u a)) := by
  have hh := retainedSmear_measurable_eval b (fun p : A × Space => S p.1)
    (fun p => u p.1) Prod.snd (fun i => measurable_fst (hS i)) (hu.comp measurable_fst) measurable_snd
  exact (hh.pow_const _).stronglyMeasurable.integral_prod_right.measurable

lemma retainedDirect_measurable_param (b : ℝ) (S : A → Finset (Fin N))
    (u : A → Configuration N) (hS : ∀ i, MeasurableSet {a | i ∈ S a}) (hu : Measurable u) :
    Measurable (fun a => retainedDirect b (S a) (u a)) := by
  have h1 := retainedSmear_measurable_eval b (fun p : A × (Space × Space) => S p.1)
    (fun p => u p.1) (fun p => p.2.1) (fun i => measurable_fst (hS i))
    (hu.comp measurable_fst) (measurable_fst.comp measurable_snd)
  have h2 := retainedSmear_measurable_eval b (fun p : A × (Space × Space) => S p.1)
    (fun p => u p.1) (fun p => p.2.2) (fun i => measurable_fst (hS i))
    (hu.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have hk : Measurable (fun p : A × (Space × Space) => ‖p.2.1-p.2.2‖) := by fun_prop
  exact ((h1.mul h2).div hk).stronglyMeasurable.integral_prod_right.measurable.const_mul _

end Work_RetainedMeasurable_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

open CoulombAtom
variable {N : ℕ}

def FlatAntisymmetric (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) : Prop :=
  ∀ i j, i ≠ j → ∀ s x,
    f (s ∘ Equiv.swap i j) (x ∘ particlePermute (Equiv.swap i j)) = -f s x

def shiftedFunction (z : (Fin N × Fin 3) → ℤ)
    (f : ((Fin N × Fin 3) → ℝ) → ℂ) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  f (fun q => (z q:ℝ)+x q)

lemma shiftedFunction_contDiff {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (z : (Fin N × Fin 3) → ℤ) : ContDiff ℝ 1 (shiftedFunction z f) :=
  hf.comp (contDiff_const.add contDiff_id)

lemma shiftedFunction_anti {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (hanti : FlatAntisymmetric f)
    (z : (Fin N × Fin 3) → ℤ) :
    CellAntisymmetric (indexCell z) (fun s => finiteCubeFunction (shiftedFunction_contDiff (hf s) z)) := by
  classical
  intro i j hij hc s x
  change f (s ∘ Equiv.swap i j) (fun q => (z q:ℝ)+(x (particlePermute (Equiv.swap i j) q):ℝ)) =
    -f s (cubeShift z x)
  have hz (q : Fin N × Fin 3) : z (particlePermute (Equiv.swap i j) q) = z q := by
    rcases q with ⟨k,a⟩
    change z (Equiv.swap i j k,a) = z (k,a)
    have he : z (i,a) = z (j,a) := congrFun hc a
    by_cases hi : k=i
    · subst k; simpa using he.symm
    · by_cases hj : k=j
      · subst k; simpa using he
      · rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  convert hanti i j hij s (cubeShift z x) using 1
  congr 1
  funext q
  simp only [Function.comp_apply,cubeShift,hz]

lemma finiteCubeGradient_value {d : Type*} [Fintype d] [DecidableEq d]
    {f : (d → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) (q : d) (x : d → I) :
    finiteCubeGradient hf q x = fderiv ℝ f (fun r => (x r:ℝ)) (Pi.single q 1) := by
  simp only [finiteCubeGradient,ContinuousMap.coe_mk]
  congr 1
  funext r
  by_cases hr : r=q <;> simp [hr]

lemma shiftedFunction_gradient {f : ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (z : (Fin N × Fin 3) → ℤ) (q : Fin N × Fin 3)
    (x : (Fin N × Fin 3) → I) :
    finiteCubeGradient (shiftedFunction_contDiff hf z) q x =
      fderiv ℝ f (cubeShift z x) (Pi.single q 1) := by
  classical
  rw [finiteCubeGradient_value]
  change fderiv ℝ (fun y => f ((fun r => (z r:ℝ))+y)) (fun r => (x r:ℝ)) (Pi.single q 1) = _
  have h := ((hf.differentiable (by simp) (cubeShift z x)).hasFDerivAt).comp
    (fun r => (x r:ℝ)) ((hasFDerivAt_const (fun r => (z r:ℝ)) (fun r => (x r:ℝ))).add (hasFDerivAt_id _))
  simpa [Function.comp_def] using congrArg
    (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv

theorem neumann_global_smooth_component
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (hanti : FlatAntisymmetric f)
    (hm : ∀ s, MemLp (f s) 2)
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    (s : Fin N → Fin 2) :
    tfKinetic*(∫ x, cellPressure (pointCell x)*‖f s x‖^2) ≤
      (1/2:ℝ)*(∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x, ‖f s x‖^2) := by
  classical
  have hc (z : (Fin N × Fin 3) → ℤ) :
      tfKinetic*(∫ x in floorCube z, cellPressure (pointCell x)*‖f s x‖^2) ≤
        (1/2:ℝ)*(∑ q, ∫ x in floorCube z, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2) +
        neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*(∫ x in floorCube z, ‖f s x‖^2) := by
    have hh := neumann_cells_pressure_lower (indexCell z)
      (fun s => shiftedFunction_contDiff (hf s) z) (shiftedFunction_anti hf hanti z) s
    rw [←cellPressure_eq] at hh
    have hegrad (q : Fin N × Fin 3) :
        (∫ x, ‖finiteCubeGradient (shiftedFunction_contDiff (hf s) z) q x‖^2) =
          ∫ x in floorCube z, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2 := by
      calc
        _ = ∫ x : (Fin N × Fin 3) → I, ‖fderiv ℝ (f s) (cubeShift z x) (Pi.single q 1)‖^2 := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact congrArg (fun v : ℂ => ‖v‖^2) (shiftedFunction_gradient (hf s) z q x)
        _ = _ := integral_cubeShift z _ (hg s q).norm.integrable_sq.aestronglyMeasurable.restrict
    simp_rw [hegrad] at hh
    have hv : (∫ x, ‖finiteCubeFunction (shiftedFunction_contDiff (hf s) z) x‖^2) =
        ∫ x in floorCube z, ‖f s x‖^2 :=
      integral_cubeShift z (fun x => ‖f s x‖^2) (hm s).norm.integrable_sq.aestronglyMeasurable.restrict
    rw [hv] at hh
    rw [integral_floorCube_pressure]
    nlinarith
  have hasC {g : ((Fin N × Fin 3) → ℝ) → ℝ} (hi : Integrable g) :
      HasSum (fun z : (Fin N × Fin 3) → ℤ => ∫ x in floorCube z, g x) (∫ x, g x) := by
    have h := hasSum_integral_iUnion floorCube_measurable floorCube_disjoint hi.integrableOn
    simpa only [floorCube_cover,Measure.restrict_univ] using h
  have hl := (hasC (flatPressure_integrable (hm s))).mul_left tfKinetic
  have hr := ((hasSum_sum (s := Finset.univ) (fun q _ => hasC (hg s q).norm.integrable_sq)).mul_left (1/2:ℝ)).add
    ((hasC (hm s).norm.integrable_sq).mul_left (neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))))
  exact hasSum_le hc hl hr

end CoulombNeumann

end

end OAI
