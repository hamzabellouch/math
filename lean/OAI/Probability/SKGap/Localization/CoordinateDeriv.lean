import Mathlib
import OAI.Probability.SKGap.Gaussian.StandardGaussianProduct

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKGap

def coordinateDeriv {n : ℕ} (i : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ)
    (x : Fin (n+1) → ℝ) : ℝ :=
  deriv (fun z => f (i.insertNth z (i.removeNth x))) (x i)

lemma lipschitz_insertNth {n : ℕ} (i : Fin (n+1)) (u : Fin n → ℝ) :
    LipschitzWith 1 (fun z : ℝ => i.insertNth (α := fun _ => ℝ) z u) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).2
  refine i.forall_iff_succAbove.mpr ⟨?_,?_⟩
  · simp only [Fin.insertNth_apply_same,le_refl]
  · intro k
    simp only [Fin.insertNth_apply_succAbove,dist_self]
    exact dist_nonneg

lemma continuous_insertNth_uncurry {n : ℕ} (i : Fin (n+1)) :
    Continuous (fun p : (Fin n → ℝ) × ℝ => i.insertNth (α := fun _ => ℝ) p.2 p.1) := by
  apply continuous_pi
  refine i.forall_iff_succAbove.mpr ⟨?_,?_⟩
  · simpa only [Fin.insertNth_apply_same] using (continuous_snd : Continuous (fun p : (Fin n → ℝ) × ℝ => p.2))
  · intro k
    simpa only [Fin.insertNth_apply_succAbove,Function.comp_def] using (continuous_apply k).comp continuous_fst

lemma measurable_coordinateDeriv {n : ℕ} (i : Fin (n+1)) {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Continuous f) : Measurable (coordinateDeriv i f) := by
  have h := measurable_deriv_with_param (f := fun u z => f (i.insertNth z u))
    (hf.comp (continuous_insertNth_uncurry i))
  have hc : Continuous (fun x : Fin (n+1) → ℝ => (i.removeNth x,x i)) := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro k
      exact continuous_apply (i.succAbove k)
    · exact continuous_apply i
  exact h.comp hc.measurable

lemma norm_coordinateDeriv_le {n : ℕ} (i : Fin (n+1)) {f : (Fin (n+1) → ℝ) → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (x : Fin (n+1) → ℝ) :
    ‖coordinateDeriv i f x‖ ≤ L := by
  have hl := hf.comp (lipschitz_insertNth i (i.removeNth x))
  simpa only [mul_one,coordinateDeriv,Function.comp_def] using norm_deriv_le_of_lipschitz hl (x₀ := x i)

theorem gaussianProduct_lipschitz_IBP {n : ℕ} (i : Fin (n+1))
    {f : (Fin (n+1) → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i * f x ∂standardGaussianProduct (n+1)) =
      ∫ x, coordinateDeriv i f x ∂standardGaussianProduct (n+1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp : MeasurePreserving e.symm
      ((gaussianReal 0 1).prod (standardGaussianProduct n))
      (standardGaussianProduct (n+1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun x : Fin (n+1) → ℝ => x i * f x)
      (standardGaussianProduct (n+1)) := by
    simpa only [mul_comm,standardGaussianProduct] using
      (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
        hf.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have hi' : Integrable (coordinateDeriv i f) (standardGaussianProduct (n+1)) :=
    Integrable.of_bound (measurable_coordinateDeriv i hf.continuous).aestronglyMeasurable (L:ℝ)
      (ae_of_all _ (norm_coordinateDeriv_le i hf))
  have hsplit (g : (Fin (n+1) → ℝ) → ℝ) (hg : Integrable g (standardGaussianProduct (n+1))) :
      (∫ x, g x ∂standardGaussianProduct (n+1)) =
        ∫ u, ∫ z, g (i.insertNth (α := fun _ => ℝ) z u) ∂gaussianReal 0 1 ∂standardGaussianProduct n := by
    have hi2 : Integrable (fun x => g (e.symm x))
        ((gaussianReal 0 1).prod (standardGaussianProduct n)) := hp.integrable_comp_of_integrable hg
    rw [← hp.integral_comp' g,integral_prod _ hi2,integral_integral_swap hi2]
    rfl
  rw [hsplit _ hi,hsplit _ hi']
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [coordinateDeriv,Fin.insertNth_apply_same,Fin.removeNth_insertNth]
  simpa only [sub_zero,NNReal.coe_one,one_mul,Function.comp_def] using
    gaussian_lipschitz_IBP (d := 0) (s := 1) (by norm_num)
      (hf.comp (lipschitz_insertNth i u)) (fun z => hC (i.insertNth (α := fun _ => ℝ) z u))

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def finiteCoordinateDeriv (i : κ) (f : (κ → ℝ) → ℝ) (x : κ → ℝ) : ℝ :=
  deriv (fun z => f (Function.update x i z)) (x i)

lemma lipschitz_coordinate_update (i : κ) (x : κ → ℝ) :
    LipschitzWith 1 (fun z : ℝ => Function.update x i z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).2
  intro k
  by_cases h : k = i
  · subst k; simp
  · simp only [Function.update_of_ne h,dist_self]; exact dist_nonneg

lemma measurable_finiteCoordinateDeriv (i : κ) {f : (κ → ℝ) → ℝ}
    (hf : Continuous f) : Measurable (finiteCoordinateDeriv i f) := by
  have h := measurable_deriv_with_param (f := fun x z => f (Function.update x i z))
    (hf.comp (continuous_update i))
  exact h.comp ((continuous_id.prodMk (continuous_apply i)).measurable)

lemma norm_finiteCoordinateDeriv_le (i : κ) {f : (κ → ℝ) → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (x : κ → ℝ) :
    ‖finiteCoordinateDeriv i f x‖ ≤ L := by
  simpa only [finiteCoordinateDeriv,Function.comp_def,mul_one] using
    norm_deriv_le_of_lipschitz (hf.comp (lipschitz_coordinate_update i x)) (x₀ := x i)

lemma gaussianFinite_lipschitz_IBP_equiv {n : ℕ} (e : Fin (n+1) ≃ κ) (i : κ)
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ x, finiteCoordinateDeriv i f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  have he (x : Fin (n+1) → ℝ) (k : κ) : E x k = x (e.symm k) := by
    simp [E,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have hl : LipschitzWith 1 E := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul]
    apply (dist_pi_le_iff dist_nonneg).2
    intro k
    simpa only [he] using dist_le_pi_dist x y (e.symm k)
  have hp := measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e
  have hh := gaussianProduct_lipschitz_IBP (e.symm i)
    (by simpa only [mul_one,Function.comp_def] using hf.comp hl) (fun x => hC (E x))
  have hu (x : Fin (n+1) → ℝ) (z : ℝ) :
      E ((e.symm i).insertNth z ((e.symm i).removeNth x)) =
        Function.update (E x) i z := by
    rw [Fin.insertNth_removeNth]
    ext k
    simp only [he]
    by_cases h : k = i
    · subst k; simp
    · simp [he,Function.update_of_ne h,show e.symm k ≠ e.symm i from fun h' => h (e.symm.injective h')]
  have hd (x : Fin (n+1) → ℝ) :
      coordinateDeriv (e.symm i) (f ∘ E) x = finiteCoordinateDeriv i f (E x) := by
    simp only [coordinateDeriv,finiteCoordinateDeriv,Function.comp_def,hu,he]
  rw [← hp.integral_comp' (fun x => x i*f x),
    ← hp.integral_comp' (finiteCoordinateDeriv i f)]
  change (∫ x, E x i*f (E x) ∂standardGaussianProduct (n+1)) =
    ∫ x, finiteCoordinateDeriv i f (E x) ∂standardGaussianProduct (n+1)
  simpa only [← hd,he,Function.comp_def] using hh

theorem gaussianFinite_lipschitz_IBP (i : κ)
    {f : (κ → ℝ) → ℝ} {L : ℝ≥0} {C : ℝ}
    (hf : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, x i*f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) =
      ∫ x, finiteCoordinateDeriv i f x ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  have hn : Fintype.card κ ≠ 0 := by
    let : Nonempty κ := ⟨i⟩
    exact Fintype.card_ne_zero
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let e : κ ≃ Fin (n+1) := (Fintype.equivFin κ).trans (Equiv.cast (congrArg Fin hn))
  exact gaussianFinite_lipschitz_IBP_equiv e.symm i hf hC

end SKGap

end

end OAI
