import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialCountSelection

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

def outProjection {N M : ℕ} (x : Configuration (N+M)) : Configuration M :=
  fun i => x (finSumFinEquiv (Sum.inr i))

lemma outProjection_measurable (N M : ℕ) :
    Measurable (outProjection (N := N) (M := M)) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma outProjection_join {N M : ℕ} (x : Configuration N) (y : Configuration M) :
    outProjection (joinLists x y) = y := by
  funext i; exact joinLists_right x y i

lemma weighted_coreSlice_eq_full {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {g : Configuration M → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    (∑ s : Spins M, ∫ u, g u*formMass (coreSlice ψ s u)) =
      ∑ s : Spins (N+M), ∫ x, g (outProjection x)*‖ψ.value s x‖^2 := by
  have hi (s : Spins (N+M)) : Integrable (fun x => g (outProjection x)*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul
      (hg.comp (outProjection_measurable N M)).aestronglyMeasurable (ae_of_all _ (fun x => hB _))
  have hj (s : Spins N) (t : Spins M) : Integrable (fun p : Configuration N × Configuration M =>
      g p.2*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    simpa only [outProjection_join] using integrable_join (N := N) (M := M) (hi (joinLists s t))
  have hk (s : Spins N) (t : Spins M) : Integrable (fun u : Configuration M =>
      g u*(∫ v : Configuration N, ‖ψ.value (joinLists s t) (joinLists v u)‖^2)) := by
    simpa only [integral_const_mul] using (hj s t).integral_prod_right
  simp only [formMass,Finset.mul_sum,coreSlice]
  simp_rw [integral_finsetSum _ (fun s _ => hk s _),←integral_const_mul]
  have he (s : Spins N) (t : Spins M) :
      (∫ u : Configuration M, ∫ v : Configuration N,
        g u*‖ψ.value (joinLists s t) (joinLists v u)‖^2) =
      ∫ x, g (outProjection x)*‖ψ.value (joinLists s t) x‖^2 := by
    simpa only [outProjection_join] using integral_join (N := N) (M := M) (hi (joinLists s t))
  simp_rw [he]
  exact sum_spin_join (fun s : Spins (N+M) =>
    ∫ x, g (outProjection x)*‖ψ.value s x‖^2)

def cutOutPositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) :
    Configuration (cutOutNumber c) :=
  fun i => x (cutOrder c (finSumFinEquiv (Sum.inr i)))

lemma cutOutPositions_reindex {L : ℕ} (c : Fin L → Fin 2)
    (x : Configuration (cutCoreNumber c+cutOutNumber c)) :
    cutOutPositions c (x ∘ (cutOrder c).symm) = outProjection x := by
  ext i
  simp only [cutOutPositions,Function.comp_apply,Equiv.symm_apply_apply,outProjection]

lemma cutOuter_expectation_eq_full {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevVector ψ)
    (c : Fin L → Fin 2) {g : Configuration (cutOutNumber c) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    (∑ s : Spins (cutOutNumber c), ∫ u,
      g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      ∑ s : Spins L, ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
  rw [weighted_coreSlice_eq_full (orderedCutForm_sobolev p hp hψ c) hg hB]
  have he (s : Spins (cutCoreNumber c+cutOutNumber c)) :
      (∫ x, g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2) =
      ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value
        (s ∘ (cutOrder c).symm) x‖^2 := by
    simpa only [orderedCutForm,reindexForm,cutOutPositions_reindex] using
      integral_reindex (cutOrder c) (fun x => g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value (s ∘ (cutOrder c).symm) x‖^2)
  simp_rw [he]
  exact sum_spin_reindex (cutOrder c) (fun s : Spins L =>
    ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2)

lemma sum_cutOutPositions {L : ℕ} (c : Fin L → Fin 2) (x : Configuration L) (f : Space → ℝ) :
    (∑ i, f (cutOutPositions c x i)) = ∑ i, if c i ≠ 0 then f (x i) else 0 := by
  classical
  have he := Equiv.sum_comp (Fintype.equivFin {i // c i ≠ 0}).symm (fun i => f (x i.val))
  have hs := Finset.sum_subtype (p := fun i => c i ≠ 0) (F := inferInstance) (Finset.univ.filter (fun i => c i ≠ 0))
    (fun _ => by simp) (fun i => f (x i))
  calc
    _ = ∑ i : {i // c i ≠ 0}, f (x i.val) := by
      simpa only [cutOutPositions,cutOrder,Equiv.trans_apply,Equiv.symm_apply_apply,
        Equiv.sumCongr_apply,Sum.map_inr,Equiv.sumCompl_apply_inr] using he
    _ = ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), f (x i) := hs.symm
    _ = _ := Finset.sum_filter _ _

def outerDeletedCount {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) : ℝ :=
  ∑ i, if t-7*b ≤ ‖u i-y‖ then 1 else 0

lemma outerDeletedCount_nonneg {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    0 ≤ outerDeletedCount y t b u := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> norm_num

lemma outerDeletedCount_le {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    outerDeletedCount y t b u ≤ M := by
  calc
    _ ≤ ∑ _ : Fin M, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = M := by simp

lemma outerDeletedCount_measurable {M : ℕ} (y : Space) (t b : ℝ) :
    Measurable (outerDeletedCount (M := M) y t b) := by
  apply Finset.measurable_sum; intro i _
  exact Measurable.ite (measurableSet_le measurable_const (configuration_distance_measurable y i))
    measurable_const measurable_const

lemma outerDeletedCount_cutOutPositions {L : ℕ} (y : Space) (t b : ℝ)
    (c : Fin L → Fin 2) (x : Configuration L) :
    outerDeletedCount y t b (cutOutPositions c x) = cutDeletedCount y t b c x := by
  rw [outerDeletedCount,sum_cutOutPositions c x (fun z => if t-7*b ≤ ‖z-y‖ then 1 else 0)]
  unfold cutDeletedCount
  apply Finset.sum_congr rfl; intro i _
  split_ifs <;> simp_all

lemma outerDeleted_second_moment_eq_cut {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) (t b : ℝ) :
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      spatialCutExpectation p hp ψ (fun c x => cutDeletedCount y t b c x^2) := by
  unfold spatialCutExpectation
  apply Finset.sum_congr rfl; intro c _
  rw [cutOuter_expectation_eq_full p hp hψ c ((outerDeletedCount_measurable y t b).pow_const 2)
    (fun u => norm_sq_le_of_nonneg (outerDeletedCount_nonneg _ _ _ _) (outerDeletedCount_le _ _ _ _))]
  simp only [outerDeletedCount_cutOutPositions]

end CoulombAtom

end

end OAI
