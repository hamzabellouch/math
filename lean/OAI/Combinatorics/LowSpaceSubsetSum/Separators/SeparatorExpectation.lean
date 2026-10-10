import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResourceMoments
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorBlocks
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! # Exact separator incidence expectations under independent indexed draws -/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorExpectation

open RepresentationMoments
open scoped BigOperators

variable {Ω K : Type*} [Fintype Ω] [Nonempty Ω] [Fintype K] [DecidableEq K]

theorem mean_coordinate (f : Ω → ℝ) (i : K) :
    mean (fun draws : K → Ω => f (draws i)) = mean f := by
  have he := mean_equiv (Equiv.funSplitAt i Ω)
    (fun p : Ω × ({j : K // j ≠ i} → Ω) => f p.1)
  simpa only [Equiv.funSplitAt_apply, mean_prod, mean_const] using he

theorem mean_pi_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : ι → Type*} [∀ i, Fintype (Ψ i)] [∀ i, Nonempty (Ψ i)]
    (i : ι) (f : Ψ i → ℝ) : mean (fun draws : ∀ i, Ψ i => f (draws i)) = mean f := by
  have he := mean_equiv (Equiv.piSplitAt i Ψ)
    (fun p : Ψ i × (∀ j : {j : ι // j ≠ i}, Ψ j) => f p.1)
  simpa only [Equiv.piSplitAt_apply, mean_prod, mean_const] using he

theorem probability_pi_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : ι → Type*} [∀ i, Fintype (Ψ i)] [∀ i, Nonempty (Ψ i)]
    (i : ι) (P : Ψ i → Prop) :
    finiteUniformProbability (fun draws : ∀ i, Ψ i => P (draws i)) =
      finiteUniformProbability P := by
  classical
  simpa only [mean, ← finiteUniformProbability_eq_indicator_mean] using
    mean_pi_coordinate i (fun x => if P x then (1 : ℝ) else 0)

omit [DecidableEq K] in
theorem mean_sum {Ψ : Type*} [Fintype Ψ] (f : K → Ψ → ℝ) :
    mean (fun x => ∑ i : K, f i x) = ∑ i : K, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

def incidence (P : Ω → Prop) (draws : K → Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => P (draws i))).card

theorem mean_incidence (P : Ω → Prop) :
    mean (fun draws : K → Ω => (incidence P draws : ℝ)) =
      Fintype.card K * finiteUniformProbability P := by
  classical
  have hpoint (draws : K → Ω) : (incidence P draws : ℝ) =
      ∑ i : K, if P (draws i) then (1 : ℝ) else 0 := by
    simp only [incidence, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  simp_rw [hpoint]
  rw [mean_sum]
  have hcoord (i : K) : mean (fun draws : K → Ω => if P (draws i) then 1 else 0) =
      mean (fun x : Ω => if P x then 1 else 0) :=
    mean_coordinate (fun x : Ω => if P x then (1 : ℝ) else 0) i
  simp_rw [hcoord]
  change (∑ _ : K, mean (fun x : Ω => if P x then 1 else 0)) = _
  rw [show mean (fun x : Ω => if P x then 1 else 0) = finiteUniformProbability P from
    (finiteUniformProbability_eq_indicator_mean P).symm]
  simp

/-- The indexed stored incidence array counts the same individual draws. -/
theorem table_size_eq {ν : ℕ} {α β : Type*} (family : Fin ν → β)
    (compatible : α → β → Bool) (x : α) :
    (SeparatorIncidenceTable.table (Array.ofFn family) compatible x).size =
      incidence (fun y => compatible x y = true) family := by
  classical
  have hcard (a : Array β) : (SeparatorIncidenceTable.table a compatible x).size =
      (Finset.univ.filter (fun j : Fin a.size => compatible x a[j.val] = true)).card := by
    simp only [SeparatorIncidenceTable.table, List.size_toArray, List.length_map]
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange a.size).filter _)]
    simp
  rw [hcard]
  unfold incidence
  simp only [← Fintype.card_subtype]
  have hsize : (Array.ofFn family).size = ν := Array.size_ofFn
  let eqv : {j : Fin (Array.ofFn family).size // compatible x (Array.ofFn family)[j.val] = true} ≃
      {j : Fin ν // compatible x (family j) = true} :=
    Equiv.subtypeEquiv (finCongr hsize) (by
      intro j
      simp only [Array.getElem_ofFn]
      rfl)
  exact @Fintype.card_congr _ _ _ _ eqv

/-- Product factorization uses the actual independent uniform family law. -/
theorem mean_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {Ψ : ι → Type*}
    [∀ i, Fintype (Ψ i)] (f : ∀ i, Ψ i → ℝ) :
    mean (fun draws : ∀ i, Ψ i => ∏ i, f i (draws i)) = ∏ i, mean (f i) := by
  simp only [mean, Fintype.card_pi, Nat.cast_prod]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]

variable {ι : Type*} [DecidableEq ι]

/-- Exact probability that one sampled separator contains/avoids fixed masks. -/
theorem sample_probability (U L R : Finset ι) (e : ℕ)
    (hL : L ⊆ U) (hR : R ⊆ U) (hd : Disjoint L R) (he : L.card ≤ e) :
    finiteUniformProbability (fun S : SeparatorSample U e => L ⊆ S.val ∧ Disjoint S.val R) =
      (Nat.choose (U.card - R.card - L.card) (e - L.card) : ℝ) / Nat.choose U.card e := by
  classical
  let : DecidablePred (fun S : SeparatorSample U e => L ⊆ S.val ∧ Disjoint S.val R) :=
    fun _ => Classical.propDecidable _
  let equiv : {S : SeparatorSample U e // L ⊆ S.val ∧ Disjoint S.val R} ≃
      {S : Finset ι // S ∈ separatingSubsets U L R e} :=
    { toFun := fun S => ⟨S.1.1, Finset.mem_filter.mpr ⟨S.1.2, S.2⟩⟩
      invFun := fun S => ⟨⟨S.1, (Finset.mem_filter.mp S.2).1⟩, (Finset.mem_filter.mp S.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold finiteUniformProbability
  calc
    _ = (Fintype.card {S : Finset ι // S ∈ separatingSubsets U L R e} : ℝ) /
        Fintype.card (SeparatorSample U e) := by
      congr 1
      norm_cast
      exact @Fintype.card_congr _ _ _ _ equiv
    _ = _ := by
      simp only [Fintype.card_coe, card_separatingSubsets U L R e hL hR hd he,
        Finset.card_powersetCard]

theorem containment_probability (U L : Finset ι) (e : ℕ) (hL : L ⊆ U) (he : L.card ≤ e) :
    finiteUniformProbability (fun S : SeparatorSample U e => L ⊆ S.val) =
      (Nat.choose (U.card - L.card) (e - L.card) : ℝ) / Nat.choose U.card e := by
  simpa using sample_probability U L ∅ e hL (Finset.empty_subset _) (by simp) he

theorem avoidance_probability (U R : Finset ι) (e : ℕ) (hR : R ⊆ U) :
    finiteUniformProbability (fun S : SeparatorSample U e => Disjoint S.val R) =
      (Nat.choose (U.card - R.card) e : ℝ) / Nat.choose U.card e := by
  simpa using sample_probability U ∅ R e (Finset.empty_subset _) hR (by simp) (by simp)

theorem mean_containment (U L : Finset ι) (e ν : ℕ)
    (hL : L ⊆ U) (he : L.card ≤ e) (heU : e ≤ U.card) :
    mean (fun family : Fin ν → SeparatorSample U e =>
      (incidence (fun S => L ⊆ S.val) family : ℝ)) =
      ν * ((Nat.choose (U.card - L.card) (e - L.card) : ℝ) / Nat.choose U.card e) := by
  let : Nonempty (SeparatorSample U e) :=
    ⟨⟨_, (Finset.powersetCard_nonempty.mpr heU).choose_spec⟩⟩
  rw [mean_incidence, containment_probability U L e hL he, Fintype.card_fin]

theorem mean_avoidance (U R : Finset ι) (e ν : ℕ)
    (hR : R ⊆ U) (heU : e ≤ U.card) :
    mean (fun family : Fin ν → SeparatorSample U e =>
      (incidence (fun S => Disjoint S.val R) family : ℝ)) =
      ν * ((Nat.choose (U.card - R.card) e : ℝ) / Nat.choose U.card e) := by
  let : Nonempty (SeparatorSample U e) :=
    ⟨⟨_, (Finset.powersetCard_nonempty.mpr heU).choose_spec⟩⟩
  rw [mean_incidence, avoidance_probability U R e hR, Fintype.card_fin]

end LowSpaceSubsetSum.SeparatorExpectation

end

end OAI
