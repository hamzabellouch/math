import OAI.Combinatorics.BalancedRyser.Local.InjectionExposureLaw
import OAI.Combinatorics.BalancedRyser.Probability.CountingExposureKernel

namespace OAI

open scoped BigOperators

namespace Balanced.CountingExposurePosterior

noncomputable section
attribute [local instance] Classical.propDecidable
open InjectionExposureLaw

theorem expect_subtype {α : Type*} (s : Finset α) (g : α → ℝ) :
    (𝔼 x ∈ s, g x) = 𝔼 x : s, g x := by
  rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, Fintype.card_coe]
  congr 1
  exact Finset.sum_subtype s (fun _ => Iff.rfl) g

theorem expect_pi_apply {G : Type*} [Fintype G] [DecidableEq G]
    (Ω : G → Type*) [∀ d, Fintype (Ω d)] [∀ d, Nonempty (Ω d)]
    (d : G) (g : Ω d → ℝ) :
    (𝔼 f : ∀ d, Ω d, g (f d)) = 𝔼 x : Ω d, g x := by
  calc
    _ = 𝔼 x : Ω d × (∀ j : {j // j ≠ d}, Ω j), g x.1 := by
      apply Fintype.expect_equiv (Equiv.piSplitAt d Ω)
      intro f
      rfl
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      simp only [Fintype.expect_const]

variable {G ι α : Type*} [Fintype G] [Fintype ι] [Fintype α]
  [DecidableEq G] [DecidableEq ι] [DecidableEq α]

def exposedIndices (S : Finset (G × ι)) (d : G) : Finset ι :=
  Finset.univ.filter fun j => (d, j) ∈ S

abbrev OffsetHistory (S : Finset (G × ι)) (h : G → ι ↪ α) :=
  ∀ d, {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)}

omit [Fintype G] in
theorem offsetHistoryCoordinateNonempty (S : Finset (G × ι)) (h : G → ι ↪ α)
    (d : G) : Nonempty {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)} :=
  ⟨⟨h d, self_mem_history _ _⟩⟩

theorem expect_offset_given_history (S : Finset (G × ι)) (h : G → ι ↪ α)
    (t : G × ι) (ht : t ∉ S) (g : α → ℝ) :
    (𝔼 f : OffsetHistory S h, g ((f t.1).val t.2)) =
      𝔼 x ∈ available (exposedIndices S t.1) (h t.1), g x := by
  let (d : G) : Nonempty {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)} :=
    offsetHistoryCoordinateNonempty S h d
  have hi : t.2 ∉ exposedIndices S t.1 := by simpa [exposedIndices] using ht
  calc
    _ = 𝔼 f : {f : ι ↪ α // f ∈ history (exposedIndices S t.1) (h t.1)},
        g (f.val t.2) := expect_pi_apply
          (fun d : G => {f : ι ↪ α // f ∈ history (exposedIndices S d) (h d)})
          t.1 (fun f => g (f.val t.2))
    _ = 𝔼 f ∈ history (exposedIndices S t.1) (h t.1), g (f t.2) :=
      (expect_subtype (history (exposedIndices S t.1) (h t.1))
        (fun f : ι ↪ α => g (f t.2))).symm
    _ = _ := expect_next_given_history (exposedIndices S t.1) (h t.1) t.2 hi g

abbrev Experiment := Equiv.Perm (G × ι) × (G → ι ↪ α)

def countingHistory (P : Finset (G × ι)) (π : Equiv.Perm (G × ι))
    (h : G → ι ↪ α) : Finset (Experiment (G := G) (ι := ι) (α := α)) :=
  Finset.univ.filter fun ω =>
    ω.1 ∈ permutationHistory P π ∧
    ∀ d, ω.2 d ∈ history (exposedIndices (P.map π.toEmbedding) d) (h d)

def historyEquiv (P : Finset (G × ι)) (π : Equiv.Perm (G × ι))
    (h : G → ι ↪ α) :
    ↥(countingHistory P π h) ≃
      ↥(permutationHistory P π) × OffsetHistory (P.map π.toEmbedding) h where
  toFun ω := ⟨⟨ω.val.1, (Finset.mem_filter.mp ω.property).2.1⟩,
    fun d => ⟨ω.val.2 d, (Finset.mem_filter.mp ω.property).2.2 d⟩⟩
  invFun x := ⟨(x.1.val, fun d => (x.2 d).val),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.1.property, fun d => (x.2 d).property⟩⟩
  left_inv ω := by apply Subtype.ext; rfl
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · funext d; apply Subtype.ext; rfl

def nextLine (ω : Experiment (G := G) (ι := ι) (α := α)) (i : G × ι) : G × α :=
  ((ω.1 i).1, ω.2 (ω.1 i).1 (ω.1 i).2)

theorem expect_history_factorization (P : Finset (G × ι))
    (π : Equiv.Perm (G × ι)) (h : G → ι ↪ α)
    (g : Experiment (G := G) (ι := ι) (α := α) → ℝ) :
    (𝔼 ω ∈ countingHistory P π h, g ω) =
      𝔼 σ ∈ permutationHistory P π,
        𝔼 f : OffsetHistory (P.map π.toEmbedding) h,
          g (σ, fun d => (f d).val) := by
  let S := P.map π.toEmbedding
  calc
    _ = 𝔼 ω : ↥(countingHistory P π h), g ω.val :=
      expect_subtype (countingHistory P π h) g
    _ = 𝔼 x : ↥(permutationHistory P π) × OffsetHistory S h,
        g (x.1.val, fun d => (x.2 d).val) := by
      apply Fintype.expect_equiv (historyEquiv P π h)
      intro ω
      rfl
    _ = 𝔼 σ : ↥(permutationHistory P π), 𝔼 f : OffsetHistory S h,
        g (σ.val, fun d => (f d).val) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = _ := (expect_subtype (permutationHistory P π)
      (fun σ => 𝔼 f : OffsetHistory S h, g (σ, fun d => (f d).val))).symm

theorem expect_nextLine_given_history (P : Finset (G × ι))
    (π : Equiv.Perm (G × ι)) (h : G → ι ↪ α) (i : G × ι) (hi : i ∉ P)
    (g : G × α → ℝ) :
    (𝔼 ω ∈ countingHistory P π h, g (nextLine ω i)) =
      𝔼 t ∈ available P π.toEmbedding,
        𝔼 x ∈ available (exposedIndices (P.map π.toEmbedding) t.1) (h t.1),
          g (t.1, x) := by
  rw [expect_history_factorization P π h (fun ω => g (nextLine ω i))]
  let S := P.map π.toEmbedding
  calc
    _ = 𝔼 σ ∈ permutationHistory P π,
        𝔼 x ∈ available (exposedIndices S (σ i).1) (h (σ i).1),
          g ((σ i).1, x) := by
      apply Finset.expect_congr rfl
      intro σ hσ
      have he : σ i ∉ S := by
        apply (mem_available P π.toEmbedding (σ i)).mp
        apply next_mem_available P π.toEmbedding σ.toEmbedding i hi
        simpa [history, permutationHistory] using hσ
      exact expect_offset_given_history S h (σ i) he (fun x => g ((σ i).1, x))
    _ = _ := expect_permutation_next_given_history P π i hi
      (fun t => 𝔼 x ∈ available (exposedIndices S t.1) (h t.1), g (t.1, x))

def remainingTokens (S : Finset (G × ι)) (d : G) : ℕ :=
  (Finset.univ.filter fun j : ι => (d, j) ∉ S).card

theorem sum_remaining_by_direction (S : Finset (G × ι)) (a : G → ℝ) :
    (∑ t ∈ Finset.univ \ S, a t.1) =
      ∑ d, (remainingTokens S d : ℝ) * a d := by
  have heq : Finset.univ \ S = Finset.univ.filter (fun t : G × ι => t ∉ S) := by
    ext t; simp
  rw [heq, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp [remainingTokens]

theorem sum_remainingTokens (S : Finset (G × ι)) :
    (∑ d, (remainingTokens S d : ℝ)) = ((Finset.univ \ S).card : ℝ) := by
  simpa using (sum_remaining_by_direction S (fun _ => (1 : ℝ))).symm

omit [Fintype G] in

theorem remainingTokens_eq (S : Finset (G × ι)) (d : G) :
    remainingTokens S d = Fintype.card ι - (exposedIndices S d).card := by
  have heq : Finset.univ.filter (fun j : ι => (d, j) ∉ S) =
      Finset.univ \ exposedIndices S d := by
    ext j; simp [exposedIndices]
  rw [remainingTokens, heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]

theorem expect_remaining_by_direction (S : Finset (G × ι)) (a : G → ℝ) :
    (𝔼 t ∈ Finset.univ \ S, a t.1) =
      ∑ d, ((remainingTokens S d : ℝ) / ∑ e, (remainingTokens S e : ℝ)) * a d := by
  rw [Finset.expect_eq_sum_div_card, sum_remaining_by_direction, sum_remainingTokens,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem expect_nextLine_direction_mixture (P : Finset (G × ι))
    (π : Equiv.Perm (G × ι)) (h : G → ι ↪ α) (i : G × ι) (hi : i ∉ P)
    (g : G × α → ℝ) :
    (𝔼 ω ∈ countingHistory P π h, g (nextLine ω i)) =
      ∑ d, ((remainingTokens (P.map π.toEmbedding) d : ℝ) /
        ∑ e, (remainingTokens (P.map π.toEmbedding) e : ℝ)) *
        (𝔼 x ∈ available (exposedIndices (P.map π.toEmbedding) d) (h d), g (d, x)) := by
  rw [expect_nextLine_given_history P π h i hi g]
  exact expect_remaining_by_direction (P.map π.toEmbedding)
    (fun d => 𝔼 x ∈ available (exposedIndices (P.map π.toEmbedding) d) (h d), g (d, x))

def usedOffsets (S : Finset (G × ι)) (h : G → ι ↪ α) (d : G) : Finset α :=
  (exposedIndices S d).map (h d)

section AffineTokens
variable {F : Type*} [Fintype F] [DecidableEq F] {k : ℕ}

theorem nextLine_probability_eq_tokenWeight
    (P : Finset (Direction F × Fin k)) (π : Equiv.Perm (Direction F × Fin k))
    (h : Direction F → Fin k ↪ F) (i : Direction F × Fin k) (hi : i ∉ P)
    (l : Line F) :
    (𝔼 ω ∈ countingHistory P π h, if nextLine ω i = l then (1 : ℝ) else 0) =
      CountingExposureKernel.tokenWeight (remainingTokens (P.map π.toEmbedding))
        (usedOffsets (P.map π.toEmbedding) h) l := by
  rw [expect_nextLine_direction_mixture P π h i hi
    (fun y => if y = l then (1 : ℝ) else 0)]
  rw [Finset.sum_eq_single l.1]
  · unfold CountingExposureKernel.tokenWeight
    congr 1
    rw [Finset.expect_eq_sum_div_card]
    have hpair (x : F) : (l.1, x) = l ↔ x = l.2 := by cases l; simp
    simp [hpair, InjectionExposureLaw.available, usedOffsets,
      CountingExposureKernel.uniformSetWeight, CountingExposureKernel.available,
      ite_div, one_div]
  · intro d _ hd
    have he (x : F) : (d, x) ≠ l := by
      intro hx
      exact hd (congrArg Prod.fst hx)
    simp [he, Finset.expect]
  · simp

omit [Fintype F] in

theorem history_counts_le (S : Finset (Direction F × Fin k))
    (h : Direction F → Fin k ↪ F) (d : Direction F) :
    remainingTokens S d ≤ k ∧ (usedOffsets S h d).card ≤ k := by
  constructor
  · simpa [remainingTokens] using
      (Finset.card_filter_le (s := (Finset.univ : Finset (Fin k)))
        (p := fun j => (d, j) ∉ S))
  · simpa [usedOffsets, exposedIndices] using
      (Finset.card_filter_le (s := (Finset.univ : Finset (Fin k)))
        (p := fun j => (d, j) ∈ S))

variable [Field F]

theorem marked_probability_given_history_le
    (P : Finset (Direction F × Fin k)) (π : Equiv.Perm (Direction F × Fin k))
    (h : Direction F → Fin k ↪ F) (i : Direction F × Fin k) (hi : i ∉ P)
    (U : Finset (Point F)) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η)
    (hk : 0 < k) (hqk : 2 * k ≤ Fintype.card F)
    (hremaining : η * (k : ℝ) * ((Fintype.card F : ℝ) + 1) ≤
      ∑ d, (remainingTokens (P.map π.toEmbedding) d : ℝ)) :
    (𝔼 ω ∈ countingHistory P π h,
      if nextLine ω i ∈ CountingExposureKernel.markedLines U ε then (1 : ℝ) else 0) ≤
        (2 / η) / (4 * ε ^ 2 * Fintype.card F) := by
  let A := CountingExposureKernel.markedLines U ε
  calc
    _ = 𝔼 ω ∈ countingHistory P π h,
        ∑ l ∈ A, if nextLine ω i = l then (1 : ℝ) else 0 := by
      apply Finset.expect_congr rfl
      intro ω _
      simp [A]
    _ = ∑ l ∈ A, 𝔼 ω ∈ countingHistory P π h,
        if nextLine ω i = l then (1 : ℝ) else 0 :=
      Finset.expect_sum_comm _ _ _
    _ = ∑ l ∈ A, CountingExposureKernel.tokenWeight
        (remainingTokens (P.map π.toEmbedding)) (usedOffsets (P.map π.toEmbedding) h) l := by
      apply Finset.sum_congr rfl
      intro l _
      exact nextLine_probability_eq_tokenWeight P π h i hi l
    _ ≤ _ := CountingExposureKernel.token_marked_mass_le U ε
      (remainingTokens (P.map π.toEmbedding)) (usedOffsets (P.map π.toEmbedding) h)
      k η hε hk hη hqk
      (fun d => (history_counts_le (P.map π.toEmbedding) h d).1)
      (fun d => (history_counts_le (P.map π.toEmbedding) h d).2) hremaining

end AffineTokens

end
end Balanced.CountingExposurePosterior

end OAI
