import OAI.MathematicalPhysics.Heisenberg.StablePinLaw

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

def subsetLaw (μ : Ω → ℝ) (A : Ω → Finset V) (B : Finset V) : ℝ :=
  ∑ ω, if A ω = B then μ ω else 0

omit [Fintype V] in
lemma subsetLaw_nonneg (μ : Ω → ℝ) (A : Ω → Finset V)
    (hμ : ∀ ω, 0 ≤ μ ω) (B : Finset V) : 0 ≤ subsetLaw μ A B := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> simp [hμ]

lemma presence_subsetLaw (μ : Ω → ℝ) (A : Ω → Finset V) (J : Finset V) :
    presence (subsetLaw μ A) J = ∑ ω, if J ⊆ A ω then μ ω else 0 := by
  have hterm (B : Finset V) : (if J ⊆ B then subsetLaw μ A B else 0) =
      ∑ ω, if A ω = B then (if J ⊆ A ω then μ ω else 0) else 0 := by
    by_cases hJ : J ⊆ B
    · rw [ite_eq_left hJ]
      unfold subsetLaw
      apply Finset.sum_congr rfl
      intro ω _
      by_cases he : A ω = B <;> simp [he, hJ]
    · rw [ite_eq_right hJ]
      symm
      apply Finset.sum_eq_zero
      intro ω _
      by_cases he : A ω = B <;> simp [he, hJ]
  unfold presence
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

lemma presencePolynomial_subsetLaw (μ : Ω → ℝ) (A : Ω → Finset V) :
    presencePolynomial (subsetLaw μ A) ∅ =
      ∑ ω, MvPolynomial.C (μ ω : ℂ) * subsetMonomial (A ω) := by
  simp only [presencePolynomial, Finset.empty_subset, ite_true, Finset.sdiff_empty,
    subsetLaw, Complex.ofReal_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [apply_ite, Complex.ofReal_zero, map_zero, ite_mul, zero_mul]
  simp

omit [Fintype V] in
lemma subsetMonomial_image (π : Equiv.Perm V) (T : Finset V) :
    subsetMonomial (T.image π) = ∏ i ∈ T, MvPolynomial.X (π i) := by
  simp only [subsetMonomial]
  exact Finset.prod_image (fun i _ j _ h => π.injective h)

lemma subsetLaw_output (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (T : Finset V) :
    presencePolynomial (subsetLaw μ (fun ω => T.image (π ω))) ∅ =
      outputSymbol μ (fun ω => π ω) T := by
  rw [presencePolynomial_subsetLaw]
  simp only [subsetMonomial_image, outputSymbol]

theorem finite_output_return_bound (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (h₁ : ∑ ω, μ ω = 1) (hs : Stable (lawSymbol μ π))
    (T : Finset V) (hT : T.Nonempty) :
    (∑ ω, if T ⊆ T.image (π ω) then μ ω else 0) ≤
      ((∑ j ∈ T, ∑ ω, if j ∈ T.image (π ω) then μ ω else 0) / T.card) ^ T.card := by
  let ν := subsetLaw μ (fun ω => T.image (π ω))
  have hν : ∀ B, 0 ≤ ν B := subsetLaw_nonneg μ _ hμ
  have hν₁ : presence ν ∅ = 1 := by
    rw [presence_subsetLaw]
    simpa using h₁
  have hνs : Stable (presencePolynomial ν ∅) := by
    rw [subsetLaw_output]
    exact stable_outputSymbol μ π (by rw [h₁]; norm_num) hs T
  have hb := presence_mean_bound hν hν₁ hνs T hT
  simpa only [ν, presence_subsetLaw, Finset.singleton_subset_iff] using hb

end Heisenberg.Pin

noncomputable section
open scoped Classical
namespace Heisenberg.Cycle
open Equiv
variable {V : Type*} [Fintype V]

lemma missingCount_antitone (π : Perm V) {E P : Set V} (hEP : E ⊆ P) :
    missingCount π P ≤ missingCount π E := by
  apply Nat.card_le_card_of_injective
    (fun c : MissingClasses π P => (⟨c.val, fun i hi => c.property i (hEP hi)⟩ : MissingClasses π E))
  intro a b h
  exact Subtype.ext (congrArg (fun c : MissingClasses π E => c.val) h)

lemma missingCount_union_le (π : Perm V) (E : Set V) (T : Finset V) :
    missingCount π E ≤ missingCount π (E ∪ (T : Set V)) + T.card := by
  let _ : Fintype (Classes π) := Fintype.ofFinite _
  let A : Finset (Classes π) := Finset.univ.filter (fun c => ∀ i ∈ E, c ≠ classOf π i)
  let B : Finset (Classes π) := Finset.univ.filter (fun c => ∀ i ∈ E ∪ (T : Set V), c ≠ classOf π i)
  have hA : missingCount π E = A.card := by
    simp [missingCount, A, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hB : missingCount π (E ∪ (T : Set V)) = B.card := by
    simp [missingCount, B, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : A ⊆ B ∪ T.image (classOf π) := by
    intro c hc
    have hcE : ∀ i ∈ E, c ≠ classOf π i := (Finset.mem_filter.mp hc).2
    by_cases hcB : c ∈ B
    · exact Finset.mem_union_left _ hcB
    · apply Finset.mem_union_right
      have hh : ¬ ∀ i ∈ E ∪ (T : Set V), c ≠ classOf π i := by
        simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and] using hcB
      push Not at hh
      obtain ⟨i, hi, he⟩ := hh
      rcases hi with hi | hi
      · exact False.elim (hcE i hi he)
      · exact Finset.mem_image.mpr ⟨i, hi, he.symm⟩
  rw [hA, hB]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le) _))

theorem pin_weight_comparison (π : Perm V) (E : Set V) (T : Finset V) :
    (2 : ℝ) ^ missingCount π (E ∪ (T : Set V)) ≤ (2 : ℝ) ^ missingCount π E ∧
    (2 : ℝ) ^ missingCount π E ≤
      (2 : ℝ) ^ T.card * (2 : ℝ) ^ missingCount π (E ∪ (T : Set V)) := by
  constructor
  · exact pow_le_pow_right₀ (by norm_num) (missingCount_antitone π Set.subset_union_left)
  · calc
      (2 : ℝ) ^ missingCount π E ≤
          (2 : ℝ) ^ (missingCount π (E ∪ (T : Set V)) + T.card) :=
        pow_le_pow_right₀ (by norm_num) (missingCount_union_le π E T)
      _ = _ := by rw [pow_add, mul_comm]

end Heisenberg.Cycle

noncomputable section
open scoped Classical
namespace Heisenberg.Return
open Equiv
variable {V : Type*} [Fintype V]

theorem nextPoint_preserves_iff (π : Perm V) (E T : Set V)
    (hET : Disjoint E T) :
    (∀ i (hi : i ∈ T), (nextPoint π (E ∪ T) ⟨i, Or.inr hi⟩ : V) ∈ T) ↔
    ∀ i ∈ T, ¬ HasHit π E i := by
  constructor
  · intro hnext
    have hall (n : ℕ) : ∀ i ∈ T, (π ^ n) i ∉ E := by
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro i hi hE
        have hn : 0 < n := by
          by_contra h
          have hz : n = 0 := by omega
          rw [hz, pow_zero, Perm.one_apply] at hE
          exact Set.disjoint_left.mp hET hE hi
        let p : ↥(E ∪ T) := ⟨i, Or.inr hi⟩
        let m := nextTime π (E ∪ T) p
        have hm0 : 0 < m := nextTime_pos π (E ∪ T) p
        have hmn : m ≤ n := nextTime_min π (E ∪ T) p hn (Or.inl hE)
        have hlt : n - m < n := Nat.sub_lt hn hm0
        have hp : (nextPoint π (E ∪ T) p : V) ∈ T := hnext i hi
        have he : (π ^ (n - m)) (nextPoint π (E ∪ T) p : V) = (π ^ n) i := by
          rw [← nextPoint_spec, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hmn]
        exact ih _ hlt _ hp (he ▸ hE)
    intro i hi ⟨n, hn⟩
    exact hall n i hi hn
  · intro havoid i hi
    have hp := (nextPoint π (E ∪ T) ⟨i, Or.inr hi⟩).property
    rcases hp with hE | hT
    · exact False.elim (havoid i hi ⟨nextTime π (E ∪ T) ⟨i, Or.inr hi⟩,
        (nextPoint_spec π (E ∪ T) ⟨i, Or.inr hi⟩).symm ▸ hE⟩)
    · exact hT

omit [Fintype V] in
lemma subset_image_iff_mapsTo (π : Perm V) (T : Finset V) :
    T ⊆ T.image π ↔ ∀ i ∈ T, π i ∈ T := by
  have hc : (T.image π).card = T.card := Finset.card_image_of_injective T π.injective
  constructor
  · intro h i hi
    have he : T.image π = T := (Finset.eq_of_subset_of_card_le h (by omega)).symm
    rw [← he]
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro h
    have hsub : T.image π ⊆ T := by
      rintro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact h i hi
    rw [Finset.eq_of_subset_of_card_le hsub (by omega)]

end Heisenberg.Return

noncomputable section
open scoped Classical
namespace Heisenberg.Pin
attribute [-instance] Subtype.instDecidableEq
open Heisenberg.Cycle Heisenberg.Return
variable {V Ω : Type*} [Fintype V] [Fintype Ω]

omit [Fintype V] in
lemma input_output_card (π : Equiv.Perm V) (T : Finset V) :
    (T.filter (fun j => j ∈ T.image π)).card =
      (T.filter (fun i => π i ∈ T)).card := by
  symm
  apply Finset.card_bij (fun i _ => π i)
  · intro i hi
    obtain ⟨hi, hπ⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hπ, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  · intro i _ j _ hij
    exact π.injective hij
  · intro j hj
    obtain ⟨hj, hmem⟩ := Finset.mem_filter.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hj⟩, rfl⟩

omit [Fintype V] in
lemma input_output_sum (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (T : Finset V) :
    (∑ j ∈ T, ∑ ω, if j ∈ T.image (π ω) then μ ω else 0) =
      ∑ i ∈ T, ∑ ω, if π ω i ∈ T then μ ω else 0 := by
  rw [Finset.sum_comm, Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, input_output_card]

def pinPartition (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (P : Set V) : ℝ :=
  ∑ ω, μ ω * (2 : ℝ) ^ missingCount (π ω) P

omit [Fintype V] in
lemma pinPartition_pos (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (P : Set V) :
    0 < pinPartition μ π P := by
  apply hpos.trans_le
  apply Finset.sum_le_sum
  intro ω _
  exact le_mul_of_one_le_right (hμ ω) (one_le_pow₀ (by norm_num))

def pinDensity (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) (P : Set V) (ω : Ω) : ℝ :=
  (μ ω * (2 : ℝ) ^ missingCount (π ω) P) / pinPartition μ π P

omit [Fintype V] in
lemma pinDensity_nonneg (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (P : Set V) (ω : Ω) :
    0 ≤ pinDensity μ π P ω :=
  div_nonneg (mul_nonneg (hμ ω) (by positivity)) (pinPartition_pos μ π hμ hpos P).le

omit [Fintype V] in
lemma pinDensity_sum (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (P : Set V) :
    ∑ ω, pinDensity μ π P ω = 1 := by
  simp only [pinDensity, ← Finset.sum_div]
  change pinPartition μ π P / pinPartition μ π P = 1
  exact div_self (pinPartition_pos μ π hμ hpos P).ne'

lemma stable_pinDensity (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω)
    (hs : Stable (lawSymbol μ π)) (P : Set V) :
    Stable (lawSymbol (pinDensity μ π P) (fun ω => nextPermutation (π ω) P)) := by
  have he : lawSymbol (pinDensity μ π P) (fun ω => nextPermutation (π ω) P) =
      MvPolynomial.C ((pinPartition μ π P : ℂ)⁻¹) * pinLaw μ π P := by
    simp only [pinLaw, lawSymbol, pinDensity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    push_cast
    simp only [div_eq_mul_inv, map_mul]
    ring
  rw [he]
  intro z hz
  simp only [map_mul, MvPolynomial.eval_C]
  apply mul_ne_zero
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (pinPartition_pos μ π hμ hpos P).ne')
  · exact stable_pinLaw μ π hμ hpos hs P z hz

lemma finite_input_return_bound (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∀ ω, 0 ≤ μ ω) (h₁ : ∑ ω, μ ω = 1) (hs : Stable (lawSymbol μ π))
    (T : Finset V) (hT : T.Nonempty) :
    (∑ ω, if ∀ i ∈ T, π ω i ∈ T then μ ω else 0) ≤
      ((∑ i ∈ T, ∑ ω, if π ω i ∈ T then μ ω else 0) / T.card) ^ T.card := by
  have h := finite_output_return_bound μ π hμ h₁ hs T hT
  rw [input_output_sum] at h
  simpa only [subset_image_iff_mapsTo] using h

end Heisenberg.Pin
end
end
end
end
end
end
end
end
end
end

end OAI
