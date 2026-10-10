import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.FiniteParameterSelection
import OAI.Combinatorics.IndependentSets.Reduction.DeletedProjection
import OAI.Combinatorics.IndependentSets.Reduction.Law

namespace OAI

namespace LargeIndependentSets
open scoped BigOperators Classical
open BooleanJunta PhaseTest Coefficient

lemma LayerLaw.sum_supported {r s : ℕ} (μ : LayerLaw r s) (f : Finset (Fin r) → ℚ) :
    (∑ B : {B : Finset (Fin r) // B.card = s}, μ.weight B.val * f B.val) =
      ∑ B, μ.weight B * f B := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun B : Finset (Fin r) => B.card = s))
    (by simp) (fun B => μ.weight B * f B)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : B.card = s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, μ.support B h, zero_mul]

noncomputable def LayerLaw.supported {r s : ℕ} (μ : LayerLaw r s) :
    RationalLaw {B : Finset (Fin r) // B.card = s} where
  weight B := μ.weight B.val
  nonneg B := μ.nonneg B.val
  total := by
    simpa using (μ.sum_supported (fun _ => 1)).trans (by simpa using μ.total)

lemma LayerLaw.expect_supported {r s : ℕ} (μ : LayerLaw r s) (f : Finset (Fin r) → ℝ) :
    (∑ B : {B : Finset (Fin r) // B.card = s}, (μ.supported.weight B : ℝ) * f B.val) =
      ∑ B, (μ.weight B : ℝ) * f B := by
  change (∑ B : {B : Finset (Fin r) // B.card = s}, (μ.weight B.val : ℝ) * f B.val) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun B : Finset (Fin r) => B.card = s))
    (by simp) (fun B => (μ.weight B : ℝ) * f B)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : B.card = s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, μ.support B h, Rat.cast_zero, zero_mul]

lemma LayerLaw.bad_supported {r s : ℕ} (μ : LayerLaw r s)
    {M : Type} (A : Finset (Fin r) → Finset M) :
    (∑ B : {B : Finset (Fin r) // B.card = s}, (μ.supported.weight B : ℝ) *
      (if ¬Aligned A B.val then 1 else 0)) = (μ.badMass A : ℝ) := by
  rw [μ.expect_supported (fun B => if ¬Aligned A B then 1 else 0)]
  simp only [LayerLaw.badMass, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : Aligned A B <;> simp [h]

abbrev SamplerOutcome (L R : Type) (n s m k : ℕ) :=
  Σ B : {B : Finset (Fin (n+1)) // B.card = s},
    Σ _t : B.val → Fin (m+1), SubchainCoord L R n B.val → Cube k

noncomputable def samplerLaw {L R : Type} [Fintype L] [Fintype R]
    {n s : ℕ} (μ : LayerLaw (n+1) s) (m k : ℕ) {ρ : ℚ} (hρ : 0 ≤ ρ) :
    RationalLaw (SamplerOutcome L R n s m k) :=
  μ.supported.bind (fun B =>
    (RationalLaw.pi (fun _ : B.val => Coefficient.law m hρ)).bind (fun _ =>
      RationalLaw.uniform (SubchainCoord L R n B.val → Cube k)))

lemma supported_nonempty {n s : ℕ} (hs : 0 < s)
    (B : {B : Finset (Fin (n+1)) // B.card = s}) : B.val.Nonempty :=
  Finset.card_pos.mp (by omega)

noncomputable def sampleLocation {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C) (hs : 0 < s)
    (o : SamplerOutcome L R n s m k) :
    GridLocation (LayerAnswer L R (U:=U) (V:=V) (n:=n)) (m*2^k) :=
  let b := subchainBase o.1.val (supported_nonempty hs o.1)
  ⟨occurrenceQuestion lc chain b.val,
    gridLocation (fun j : o.1.val =>
      chainComposite lc chain b.val.val j.val.val (subchainBase_le _ _ j))
      o.2.1 (fun c => gridEquiv k (o.2.2 c))⟩

lemma sampleLocation_phase {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (hs : 0 < s) (hm : 0 < m)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (o : SamplerOutcome L R n s m k) :
    letI : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
    F (sampleLocation lc chain hs o).1 (torusGrid (sampleLocation lc chain hs o).2) =
      viewFunction F (supported_nonempty hs o.1) (chainView lc chain o.1.val) o.2.1
        (fun c => scalarCell (o.2.2 c) 0) := by
  let : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
  let b := subchainBase o.1.val (supported_nonempty hs o.1)
  exact congrArg (F (occurrenceQuestion lc chain b.val))
    (gridLocation_cube (fun j : o.1.val =>
      chainComposite lc chain b.val.val j.val.val (subchainBase_le _ _ j)) hm k o.2.1 o.2.2)

theorem sampler_expectation {U V L R C : Type} [Fintype L] [Fintype R]
    {n s m k : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (μ : LayerLaw (n+1) s) {ρ : ℚ} (hρ : 0 ≤ ρ) (hs : 0 < s) (hm : 0 < m)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ) :
    letI : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
    (∑ o, ((samplerLaw (L:=L) (R:=R) μ m k hρ).weight o : ℝ) *
      (F (sampleLocation lc chain hs o).1 (torusGrid (sampleLocation lc chain hs o).2))^2) =
    ∑ B, (μ.supported.weight B : ℝ) *
      fiberSquare lc chain F B.val (supported_nonempty hs B) m ρ k := by
  let : NeZero (m*2^k) := ⟨Nat.ne_of_gt (Nat.mul_pos hm (by positivity))⟩
  unfold samplerLaw
  rw [RationalLaw.expect_bind]
  apply Finset.sum_congr rfl
  intro B _
  congr 1
  rw [RationalLaw.expect_bind]
  unfold fiberSquare
  apply Finset.sum_congr rfl
  intro t _
  rw [Coefficient.pi_law_real]
  congr 1
  rw [RationalLaw.expect_uniform]
  apply Finset.expect_congr rfl
  intro v _
  rw [sampleLocation_phase lc chain hs hm F]

lemma fiberSquare_le_one {U V L R C : Type} [Fintype L] [Fintype R]
    {n : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (hb : ∀ q x, |F q x| ≤ 1) (B : Finset (Fin (n+1))) (hB : B.Nonempty)
    (m k : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : fiberSquare lc chain F B hB m ρ k ≤ 1 := by
  unfold fiberSquare
  calc
    _ ≤ ∑ t : B → Fin (m+1), mass m ρ t * 1 := by
      apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (mass_nonneg m hρ t)
      apply Finset.expect_le Finset.univ_nonempty
      intro v _
      change (F _ _)^2 ≤ 1
      exact (sq_le_one_iff_abs_le_one _).mpr (hb _ _)
    _ = 1 := by simpa using (mass_total (ι:=B) m hρ)

end LargeIndependentSets

end OAI
