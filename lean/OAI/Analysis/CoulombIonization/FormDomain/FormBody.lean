import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PacketDensity

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators

def formOneBody {N : ℕ} (ψ : FormVector N) (w : Space → ℝ) : ℝ :=
  ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2 * w (x i)

def OneBodyIntegrable {N : ℕ} (ψ : FormVector N) (w : Space → ℝ) : Prop :=
  ∀ s i, Integrable (fun x => ‖ψ.value s x‖^2 * w (x i))

lemma formOneBody_scale {N : ℕ} (ψ : FormVector N) (w : Space → ℝ) (c : ℝ) :
    formOneBody (scaleForm c ψ) w = c^2 * formOneBody ψ w := by
  unfold formOneBody
  simp only [scaleForm,norm_real_mul_sq,mul_assoc,integral_const_mul,Finset.mul_sum]

lemma OneBodyIntegrable.scale {N : ℕ} {ψ : FormVector N} {w : Space → ℝ}
    (h : OneBodyIntegrable ψ w) (c : ℝ) : OneBodyIntegrable (scaleForm c ψ) w := by
  intro s i
  simpa only [scaleForm,norm_real_mul_sq,mul_assoc] using (h s i).const_mul (c^2)

lemma OneBodyIntegrable.reindex {N M : ℕ} {ψ : FormVector N} {w : Space → ℝ}
    (h : OneBodyIntegrable ψ w) (e : Fin M ≃ Fin N) : OneBodyIntegrable (reindexForm e ψ) w := by
  intro s i
  simpa only [Function.comp_def,configurationReindex_apply,reindexForm,Equiv.symm_apply_apply]
    using (configurationReindex_preserving e).integrable_comp_of_integrable (h (s ∘ e.symm) (e i))

lemma formOneBody_reindex {N M : ℕ} (ψ : FormVector N) (w : Space → ℝ) (e : Fin M ≃ Fin N) :
    formOneBody (reindexForm e ψ) w = formOneBody ψ w := by
  have hh (s : Spins M) (i : Fin M) :
      (∫ x, ‖(reindexForm e ψ).value s x‖^2 * w (x i)) =
        ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x (e i)) := by
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,reindexForm] using
      integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖^2 * w (x (e i)))
  have hi (s : Spins M) :
      (∑ i : Fin M, ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x (e i))) =
      ∑ i : Fin N, ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x i) :=
    Equiv.sum_comp e (fun i : Fin N => ∫ x, ‖ψ.value (s ∘ e.symm) x‖^2 * w (x i))
  unfold formOneBody
  simp_rw [hh,hi]
  exact sum_spin_reindex e (fun s => ∑ i, ∫ x, ‖ψ.value s x‖^2 * w (x i))

lemma formOneBody_sum_disjoint {ι : Type*} [Fintype ι] {N : ℕ}
    {ψ : ι → FormVector N} {w : Space → ℝ}
    (h : ∀ k, OneBodyIntegrable (ψ k) w) (hd : FormsDisjoint ψ) :
    formOneBody (sumForm ψ) w = ∑ k, formOneBody (ψ k) w := by
  have hh (s : Spins N) (i : Fin N) :
      (∫ x, ‖(sumForm ψ).value s x‖^2 * w (x i)) =
        ∑ k, ∫ x, ‖(ψ k).value s x‖^2 * w (x i) := by
    simp only [sumForm,norm_sum_sq_disjoint _ (fun k l hkl => hd.1 k l hkl s _),Finset.sum_mul]
    exact integral_finsetSum _ (fun k _ => h k s i)
  unfold formOneBody
  simp_rw [hh]
  calc
    _ = ∑ s, ∑ k, ∑ i, ∫ x, ‖(ψ k).value s x‖^2 * w (x i) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

lemma formOneBody_insertionTerm {N : ℕ} (T : FormVector (N+1)) (w : Space → ℝ) (i : Fin (N+1)) :
    formOneBody (insertionTerm T i) w = formOneBody T w := by
  rw [insertionTerm,formOneBody_scale,formOneBody_reindex,real_sign_sq,one_mul]

lemma formOneBody_wedge {N : ℕ} {T : FormVector (N+1)} {w : Space → ℝ}
    (h : OneBodyIntegrable T w) (hd : FormsDisjoint (insertionTerm T)) :
    formOneBody (wedgeForm T) w = (N+1 : ℝ) * formOneBody T w := by
  have hk (i : Fin (N+1)) : OneBodyIntegrable (insertionTerm T i) w :=
    (h.reindex (insertionSwap i)).scale _
  rw [wedgeForm,formOneBody_sum_disjoint hk hd]
  simp only [formOneBody_insertionTerm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_add,Nat.cast_one]

lemma formOneBody_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) (w : Space → ℝ) :
    formOneBody (tensorForm ψ φ) w = formOneBody ψ w * formMass φ +
      formMass ψ * formOneBody φ w := by
  have hl (s : Spins N) (t : Spins M) (i : Fin N) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 * w (z (finSumFinEquiv (Sum.inl i)))) =
        (∫ x, ‖ψ.value s x‖^2 * w (x i)) * (∫ y, ‖φ.value t y‖^2) := by
    change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
      φ.value (rightList (joinLists s t)) (rightList z)‖^2 * w (leftList z i)) = _
    simp only [leftList_join,rightList_join,norm_mul,mul_pow]
    simp_rw [mul_right_comm _ _ (w _)]
    exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2 * w (x i))
      (fun y => ‖φ.value t y‖^2)
  have hr (s : Spins N) (t : Spins M) (i : Fin M) :
      (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 * w (z (finSumFinEquiv (Sum.inr i)))) =
        (∫ x, ‖ψ.value s x‖^2) * (∫ y, ‖φ.value t y‖^2 * w (y i)) := by
    change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
      φ.value (rightList (joinLists s t)) (rightList z)‖^2 * w (rightList z i)) = _
    simp only [leftList_join,rightList_join,norm_mul,mul_pow,mul_assoc]
    exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2)
      (fun y => ‖φ.value t y‖^2 * w (y i))
  have hk (s : Spins N) (t : Spins M) :
      (∑ i, ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 * w (z i)) =
      (∑ i, ∫ x, ‖ψ.value s x‖^2 * w (x i))*(∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*(∑ i, ∫ y, ‖φ.value t y‖^2 * w (y i)) := by
    rw [← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
    simp only [hl,hr,Finset.sum_mul,Finset.mul_sum]
  unfold formOneBody formMass
  rw [← sum_spin_join]
  simp_rw [hk,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]

def insertOrbital {N : ℕ} (ψ : FormVector N) (φ : FormVector 1) : FormVector (N+1) :=
  scaleForm (Real.sqrt (N+1 : ℝ))⁻¹ (wedgeForm (tensorForm ψ φ))

lemma insertOrbital_sobolev {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevFermion ψ) (hφ : SobolevFermion φ) : SobolevFermion (insertOrbital ψ φ) :=
  (wedgeForm_fermion (hψ.sobolevVector.tensor hφ.sobolevVector)
    (tensor_coreAntisymmetric hψ φ)).scale _

lemma insertion_normalizer (N : ℕ) : (Real.sqrt (N+1 : ℝ))⁻¹^2 * (N+1 : ℝ) = 1 := by
  rw [inv_pow,Real.sq_sqrt (by positivity)]
  exact inv_mul_cancel₀ (by positivity)

lemma formMass_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ))) :
    formMass (insertOrbital ψ φ) = formMass ψ * formMass φ := by
  rw [insertOrbital,formMass_scale,formMass_wedge (hψ.tensor hφ) hd,← mul_assoc,
    insertion_normalizer,one_mul,formMass_tensor]

lemma formEnergy_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ))) (Z : ℝ) :
    formEnergy Z (insertOrbital ψ φ) = formEnergy Z (tensorForm ψ φ) := by
  rw [insertOrbital,formEnergy_scale,formEnergy_wedge (hψ.tensor hφ) hd,← mul_assoc,
    insertion_normalizer,one_mul]

lemma formOneBody_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1} {w : Space → ℝ}
    (h : OneBodyIntegrable (tensorForm ψ φ) w)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ))) :
    formOneBody (insertOrbital ψ φ) w = formOneBody ψ w * formMass φ +
      formMass ψ * formOneBody φ w := by
  rw [insertOrbital,formOneBody_scale,formOneBody_wedge h hd,← mul_assoc,
    insertion_normalizer,one_mul,formOneBody_tensor]


open MeasureTheory Filter
open scoped Topology BigOperators


def FormAvoids {N : ℕ} (ψ : FormVector N) (S : Set Space) : Prop :=
  ∀ x i, x i ∈ S → FormZeroAt ψ x

lemma FormAvoids.scale {N : ℕ} {ψ : FormVector N} {S : Set Space}
    (h : FormAvoids ψ S) (c : ℝ) : FormAvoids (scaleForm c ψ) S := by
  intro x i hx s
  constructor
  · change _ * ψ.value s x = 0
    rw [(h x i hx s).1,mul_zero]
  · intro j a
    change _ * ψ.gradient s j a x = 0
    rw [(h x i hx s).2,mul_zero]

lemma FormAvoids.reindex {N M : ℕ} {ψ : FormVector N} {S : Set Space}
    (h : FormAvoids ψ S) (e : Fin M ≃ Fin N) : FormAvoids (reindexForm e ψ) S := by
  intro x i hx s
  have hz := h (x ∘ e.symm) (e i) (by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hx)
  exact ⟨(hz (s ∘ e.symm)).1, fun j a => (hz (s ∘ e.symm)).2 (e j) a⟩

lemma FormAvoids.sum {ι : Type*} [Fintype ι] {N : ℕ} {ψ : ι → FormVector N} {S : Set Space}
    (h : ∀ k, FormAvoids (ψ k) S) : FormAvoids (sumForm ψ) S := by
  intro x i hx s
  constructor
  · change (∑ k, (ψ k).value s x) = 0
    exact Finset.sum_eq_zero (fun k _ => (h k x i hx s).1)
  · intro j a
    change (∑ k, (ψ k).gradient s j a x) = 0
    exact Finset.sum_eq_zero (fun k _ => (h k x i hx s).2 j a)

lemma FormAvoids.tensor {N M : ℕ} {ψ : FormVector N} {φ : FormVector M} {S : Set Space}
    (hψ : FormAvoids ψ S) (hφ : FormAvoids φ S) : FormAvoids (tensorForm ψ φ) S := by
  intro x i hx
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => exact tensor_zero_left ψ φ (hψ (leftList x) i hx)
  | inr i => exact tensor_zero_right ψ φ (hφ (rightList x) i hx)

lemma FormAvoids.wedge {N : ℕ} {T : FormVector (N+1)} {S : Set Space}
    (h : FormAvoids T S) : FormAvoids (wedgeForm T) S := by
  apply FormAvoids.sum
  intro i
  exact (h.reindex (insertionSwap i)).scale _

lemma FormAvoids.insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1} {S : Set Space}
    (hψ : FormAvoids ψ S) (hφ : FormAvoids φ S) : FormAvoids (insertOrbital ψ φ) S :=
  (hψ.tensor hφ).wedge.scale _

lemma FormAvoids.mono {N : ℕ} {ψ : FormVector N} {S T : Set Space}
    (h : FormAvoids ψ T) (hst : S ⊆ T) : FormAvoids ψ S :=
  fun x i hx => h x i (hst hx)

lemma radialLocalOrbital_avoids (y z : Space) {R B : ℝ} (hR : 0 < R)
    (hsep : R+B ≤ ‖y-z‖) : FormAvoids (radialLocalOrbital y R) (Metric.ball z B) := by
  intro x i hx
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hx' : ‖x 0-z‖ < B := Metric.mem_ball.mp hx
  have ht : ‖y-z‖ ≤ ‖x 0-y‖+‖x 0-z‖ := by
    calc
      _ ≤ ‖y-x 0‖+‖x 0-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev y (x 0)]
  exact radialLocalOrbital_zero y hR (by linarith)

lemma integrable_coreCoulombAt {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {B : ℝ} (hB : 0 < B) (hc : FormAvoids ψ (Metric.ball y B)) (s : Spins N) (i : Fin N) :
    Integrable (fun x => ‖ψ.value s x‖^2/‖x i-y‖) := by
  have hm1 : AEStronglyMeasurable (fun x : Configuration N => ‖ψ.value s x‖^2) volume :=
    (hψ.1 s).aestronglyMeasurable.norm.pow 2
  have hm2 : AEStronglyMeasurable (fun x : Configuration N => ‖x i-y‖⁻¹) volume :=
    (((continuous_apply i).sub continuous_const).norm.measurable.inv).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun x : Configuration N => ‖ψ.value s x‖^2/‖x i-y‖) volume := by
    simpa only [div_eq_mul_inv] using hm1.fun_mul hm2
  apply Integrable.mono' (((hψ.1 s).integrable_norm_pow (by norm_num)).div_const B) hm
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (norm_nonneg _))]
  by_cases hz : ψ.value s x = 0
  · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]
  · have hd : B ≤ ‖x i-y‖ := by
      by_contra hh
      exact hz (hc x i (Metric.mem_ball.mpr (not_le.mp hh)) s).1
    exact div_le_div_of_nonneg_left (sq_nonneg _) hB hd

lemma coreCoulombAt_eq_formOneBody {N : ℕ} (ψ : FormVector N) (y : Space) :
    coreCoulombAt ψ y = formOneBody ψ (fun x => 1/‖x-y‖) := by
  simp only [coreCoulombAt,formOneBody,mul_one_div]

lemma coreCoulombAt_insertOrbital {N : ℕ} {ψ : FormVector N} {φ : FormVector 1}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (hd : FormsDisjoint (insertionTerm (tensorForm ψ φ)))
    (y : Space) {B : ℝ} (hB : 0 < B)
    (hcψ : FormAvoids ψ (Metric.ball y B)) (hcφ : FormAvoids φ (Metric.ball y B)) :
    coreCoulombAt (insertOrbital ψ φ) y = coreCoulombAt ψ y * formMass φ +
      formMass ψ * coreCoulombAt φ y := by
  simp only [coreCoulombAt_eq_formOneBody]
  apply formOneBody_insertOrbital _ hd
  intro s i
  simpa only [mul_one_div] using integrable_coreCoulombAt (hψ.tensor hφ) y hB
    (hcψ.tensor hcφ) s i

lemma coreCoulombAt_packet (y z : Space) {R : ℝ} (hR : 0 < R)
    (hsep : R < ‖y-z‖) : coreCoulombAt (radialLocalOrbital y R) z = 1/‖y-z‖ := by
  have hh (s : Spins 1) := radialLocalOrbital_potential y hR
    (z := z) (by rwa [norm_sub_rev]) s
  simp only [coreCoulombAt,Fin.sum_univ_one]
  have he (s : Spins 1) : (∫ x : Configuration 1,
      ‖(radialLocalOrbital y R).value s x‖^2/‖x 0-z‖) = (1/2:ℝ)/‖y-z‖ := by
    simpa only [norm_sub_rev] using hh s
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num [Spins]
  ring


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
