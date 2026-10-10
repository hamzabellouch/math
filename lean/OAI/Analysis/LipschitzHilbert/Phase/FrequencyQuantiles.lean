import OAI.Analysis.LipschitzHilbert.Phase.Quantiles
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort

namespace OAI

/-! Quarter-tail quantiles in a finite ordered frequency list. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

/-- Extend finite weights by zero, only to use natural-number prefix sums. -/
def extendWeights {N : ℕ} (x : Fin N → ℝ) (i : ℕ) : ℝ :=
  if hi : i < N then x ⟨i, hi⟩ else 0

theorem extendWeights_nonneg {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ extendWeights x i := by
  intro i
  unfold extendWeights
  split <;> simp_all

theorem prefixMass_extend {N : ℕ} (x : Fin N → ℝ) {k : ℕ} (hk : k ≤ N) :
    prefixMass (extendWeights x) k = ∑ i : Fin N, if (i : ℕ) < k then x i else 0 := by
  classical
  have he : (Finset.range N).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∑ i ∈ Finset.range N, if i < k then extendWeights x i else 0 := by
      rw [← Finset.sum_filter, he]
      rfl
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp [extendWeights, i.isLt]

/-- Quarter-tail quantiles for strictly ordered frequencies. -/
theorem finite_frequency_quantiles {N : ℕ} (x frequency : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hfrequency : StrictMono frequency) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hatom : ∀ i, x i ≤ 1 - κ) :
    ∃ a b : Fin N, a < b ∧
      κ / 4 ≤ (∑ i, if frequency i ≤ frequency a then x i else 0) ∧
      κ / 4 ≤ (∑ i, if frequency b ≤ frequency i then x i else 0) ∧
      1 - κ / 2 ≤ intervalMass x frequency (frequency a) (frequency b) := by
  classical
  have htotal : prefixMass (extendWeights x) N = 1 := by
    rw [prefixMass_extend x le_rfl]
    simpa only [Fin.isLt, ite_true] using hsum
  obtain ⟨a, b, hab, hbN, ha, ha', hb, hb', hcentral⟩ :=
    exists_distinct_quantiles (extendWeights x) N hκ hκ1
      (extendWeights_nonneg x hx) htotal (fun i hi => by simpa [extendWeights, hi] using hatom ⟨i, hi⟩)
  have haN : a < N := lt_trans hab hbN
  let a' : Fin N := ⟨a, haN⟩
  let b' : Fin N := ⟨b, hbN⟩
  have hleft : prefixMass (extendWeights x) (a + 1) =
      ∑ i, if frequency i ≤ frequency a' then x i else 0 := by
    rw [prefixMass_extend x (by omega)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hfrequency.le_iff_le]
    congr 1
    apply propext
    change ((i : ℕ) < a + 1 ↔ (i : ℕ) ≤ a)
    omega
  have hright : (∑ i, if frequency b' ≤ frequency i then x i else 0) =
      1 - prefixMass (extendWeights x) b := by
    rw [prefixMass_extend x hbN.le, ← hsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hfrequency.le_iff_le]
    by_cases hi : (i : ℕ) < b
    · have hn : ¬ b' ≤ i := by simpa [b', Fin.le_def] using (not_le.mpr hi)
      simp [hi, hn]
    · have hn : b' ≤ i := by simpa [b', Fin.le_def] using (Nat.le_of_not_gt hi)
      simp [hi, hn]
  have hmiddle : intervalMass x frequency (frequency a') (frequency b') =
      prefixMass (extendWeights x) (b + 1) - prefixMass (extendWeights x) a := by
    rw [prefixMass_extend x (by omega), prefixMass_extend x haN.le]
    unfold intervalMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hfrequency.le_iff_le, Fin.le_def, a', b']
    by_cases hi : (i : ℕ) < a
    · have hib : (i : ℕ) < b + 1 := by omega
      have hni : ¬ a ≤ (i : ℕ) := by omega
      simp [hi, hib, hni]
    · have hni : a ≤ (i : ℕ) := by omega
      by_cases hib : (i : ℕ) < b + 1
      · have hle : (i : ℕ) ≤ b := by omega
        simp [hi, hib, hni, hle]
      · have hle : ¬ (i : ℕ) ≤ b := by omega
        simp [hi, hib, hni, hle]
  refine ⟨a', b', hab, ?_, ?_, ?_⟩
  · rwa [← hleft]
  · rw [hright]
    linarith
  · rwa [hmiddle]

/-- Sorting by the injective frequency map removes the ordering hypothesis
from the finite quantile construction. -/
theorem frequency_quantiles {ι : Type*} [Fintype ι] (x frequency : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hinj : Function.Injective frequency) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hatom : ∀ i, x i ≤ 1 - κ) :
    ∃ a b : ι, frequency a < frequency b ∧
      κ / 4 ≤ (∑ i, if frequency i ≤ frequency a then x i else 0) ∧
      κ / 4 ≤ (∑ i, if frequency b ≤ frequency i then x i else 0) ∧
      1 - κ / 2 ≤ intervalMass x frequency (frequency a) (frequency b) := by
  classical
  let : LinearOrder ι := LinearOrder.lift' frequency hinj
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  have he : StrictMono (fun i => frequency (e i)) := fun _ _ hij => e.strictMono hij
  have hs : (∑ i, x (e i)) = 1 := (Equiv.sum_comp e.toEquiv x).trans hsum
  obtain ⟨a, b, hab, ha, hb, hc⟩ := finite_frequency_quantiles
    (fun i => x (e i)) (fun i => frequency (e i)) (fun i => hx (e i)) hs he
      hκ hκ1 (fun i => hatom (e i))
  refine ⟨e a, e b, he hab, ?_, ?_, ?_⟩
  · rw [← Equiv.sum_comp e.toEquiv
      (fun i => if frequency i ≤ frequency (e a) then x i else 0)]
    exact ha
  · rw [← Equiv.sum_comp e.toEquiv
      (fun i => if frequency (e b) ≤ frequency i then x i else 0)]
    exact hb
  · change 1 - κ / 2 ≤ ∑ i, if frequency (e a) ≤ frequency i ∧
        frequency i ≤ frequency (e b) then x i else 0
    rw [← Equiv.sum_comp e.toEquiv
      (fun i => if frequency (e a) ≤ frequency i ∧ frequency i ≤ frequency (e b)
        then x i else 0)]
    exact hc

end LipschitzHilbert

end

end OAI
