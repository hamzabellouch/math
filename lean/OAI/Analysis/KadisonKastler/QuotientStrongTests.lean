import OAI.Analysis.KadisonKastler.QuotientUnitBall
import OAI.Analysis.KadisonKastler.PublishedKaplansky
import OAI.Analysis.KadisonKastler.SequentialConjugacyTests

namespace OAI

/-! # Strong test fields from norm-dense quotient generators

The same fixed sequence in a separable source C-star algebra gives strong
unit-ball tests in each fiber representation. Nonfaithful fiber maps are
handled by the proved exact contraction-lifting theorem.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H]

omit [SeparableSpace H] in
theorem countableStrongTests_of_quotient_dense
    (hK : PublishedKaplanskyDensity.{v}) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (s : ℕ → A)
    (hd : ∀ a : A, ‖a‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ j, ‖a - s j‖ < ε)
    (ξ : ℕ → H) (T : H →L[ℂ] H)
    (hT : T ∈ unitBall (generatedVonNeumannAlgebra φ.range)) :
    CountableStrongTests ξ (Set.range (fun j => φ (s j))) T := by
  classical
  intro m k
  let V : Finset H := (Finset.range (m + 1)).image ξ
  let C : ℝ := 1 + ∑ l ∈ Finset.range (m + 1), ‖ξ l‖
  have hsum : 0 ≤ ∑ l ∈ Finset.range (m + 1), ‖ξ l‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hC : 0 < C := by dsimp [C]; linarith
  let ε : ℝ := 1 / (k + 1 : ℝ) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hTc : T ∈ Set.centralizer (Set.centralizer (φ.range : Set (H →L[ℂ] H))) := by
    have hm : T ∈ (generatedVonNeumannAlgebra φ.range : Set (H →L[ℂ] H)) := hT.1
    rwa [generatedVonNeumannAlgebra_coe] at hm
  obtain ⟨b, hbn, hb⟩ := hK H φ.range T hTc hT.2 V ε hε
  have hbφ : (b : H →L[ℂ] H) ∈ Set.range φ := b.property
  obtain ⟨a, han, hab⟩ := exists_contractive_starAlgHom_preimage φ hbφ hbn
  obtain ⟨j, hj⟩ := hd a han (ε / C) (div_pos hε hC)
  have hdiff : ‖(b : H →L[ℂ] H) - φ (s j)‖ ≤ ‖a - s j‖ := by
    rw [← hab, ← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le φ _
  have hprod : ‖a - s j‖ * C ≤ ε := by
    exact (le_div_iff₀ hC).mp hj.le
  refine ⟨φ (s j), ⟨j, rfl⟩, ?_⟩
  intro l hl
  have hlmem : l ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
  have hlC : ‖ξ l‖ ≤ C := by
    have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (m + 1)) => norm_nonneg (ξ i)) hlmem
    dsimp [C]
    linarith
  have hvec : ‖((b : H →L[ℂ] H) - φ (s j)) (ξ l)‖ ≤ ε :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul hdiff hlC (norm_nonneg _) (norm_nonneg _)).trans hprod)
  have hfirst := hb (ξ l) (Finset.mem_image.mpr ⟨l, hlmem, rfl⟩)
  have ht := norm_add_le (T (ξ l) - (b : H →L[ℂ] H) (ξ l))
    ((b : H →L[ℂ] H) (ξ l) - φ (s j) (ξ l))
  rw [sub_add_sub_cancel] at ht
  simp only [sub_apply] at hvec ⊢
  dsimp [ε] at hfirst hvec
  linarith

def quotientStrongUnitBallTests
    (hK : PublishedKaplanskyDensity.{v}) (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (s : ℕ → A) (hs : ∀ j, ‖s j‖ ≤ 1)
    (hd : ∀ a : A, ‖a‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ j, ‖a - s j‖ < ε) :
    StrongUnitBallTestSequence (generatedVonNeumannAlgebra φ.range) where
  op j := φ (s j)
  mem j := ⟨subset_generatedVonNeumannAlgebra φ.range ⟨s j, rfl⟩,
    (NonUnitalStarAlgHom.norm_apply_le φ _).trans (hs j)⟩
  dense T hT := by
    obtain ⟨ξ, hξ⟩ := exists_dense_seq (α := H)
    exact exists_strong_sequence_of_countable_tests ξ hξ (Set.range (fun j => φ (s j)))
      (by rintro _ ⟨j, rfl⟩; exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans (hs j))
      T hT.2 (countableStrongTests_of_quotient_dense hK φ s hd ξ T hT)

end

end KadisonKastler

end OAI
