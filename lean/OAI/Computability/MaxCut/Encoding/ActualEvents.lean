import Mathlib
import OAI.Computability.MaxCut.Encoding.ActualGoodRows
import OAI.Computability.MaxCut.Games.RowErasureSelection

namespace OAI

/-! The two full-table events used in the projected-witness transfer. Their
sample space contains actual occurrence tuples and complete affine tables,
but no projection choice. The selected witness depends on row advice only.
-/

namespace MaxCutGames.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

abbrev Context (S : Source) (k d : ℕ) :=
  ActualGame.Question S k × (ActualHomogeneous.E k →ₗ[F2] Vector d)

abbrev Sample (S : Source) (k s d r : ℕ) :=
  Context S k d × (RowErasureDescriptions.RowMap s r × Mat s (1 + 2 * k))

abbrev FullTableSample (S : Source) (k s d r : ℕ) :=
  (ActualGame.Question S k × (Alphabet s →ₗ[F2] Vector r)) × ActualGame.Map k s d

/-- A bijection merely rearranges the full sampled table and changes its
matrix coordinates. It never appends the hidden projection to this law. -/
def fullTableEquiv (S : Source) (k s d r : ℕ) :
    FullTableSample S k s d r ≃ Sample S k s d r where
  toFun p := ((p.1.1, (LinearMap.snd F2 (Alphabet s) (Vector d)).comp p.2),
    (LinearMap.toMatrix' p.1.2,
      MatrixCoordinates.mapEquiv k s ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp p.2)))
  invFun q := ((q.1.1, Matrix.toLin' q.2.1),
    ((MatrixCoordinates.mapEquiv k s).symm q.2.2).prod q.1.2)
  left_inv p := by
    rcases p with ⟨⟨U, A⟩, P⟩
    apply Prod.ext
    · simp
    · apply LinearMap.ext
      intro x
      simp only [LinearEquiv.symm_apply_apply, LinearMap.prod_apply]
      rfl
  right_inv q := by
    rcases q with ⟨⟨U, T⟩, A, M⟩
    apply Prod.ext
    · apply Prod.ext rfl
      apply LinearMap.ext
      intro x
      rfl
    · apply Prod.ext
      · exact LinearMap.toMatrix'_toLin' A
      · change MatrixCoordinates.mapEquiv k s
          ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T)) = M
        have hf : (LinearMap.fst F2 (Alphabet s) (Vector d)).comp
            (((MatrixCoordinates.mapEquiv k s).symm M).prod T) =
              (MatrixCoordinates.mapEquiv k s).symm M := by
          apply LinearMap.ext
          intro x
          rfl
        rw [hf, LinearEquiv.apply_symm_apply]

def unrestricted (S : Source) (k s d r : ℕ) : FiniteDistribution (Sample S k s d r) :=
  FiniteDistribution.uniform _

def sliceEvent (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedEvent
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

theorem targetHit_implies_slice (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r)
    (h : targetHit S k s d r labeling α p = true) :
    sliceEvent S k s d r labeling α p = true := by
  exact of_decide_eq_true h |> fun hm => decide_eq_true
    ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch_event _ α _ _ hm)

theorem uniform_probability_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Bool) :
    (FiniteDistribution.uniform Ω).probability p =
      𝔼 x : Ω, if p x then (1 : ℝ) else 0 := by
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform,
    Fintype.expect_eq_sum_div_card, Finset.sum_div, ite_div, one_div, zero_div]

theorem unrestricted_slice_mass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) =
      𝔼 q : Context S k d,
        RowErasureMatrix.selectedEventMass r
          (ActualGoodRows.table S k s d labeling q.1 q.2) α := by
  unfold unrestricted
  rw [uniform_probability_expect, ActualSpectral.expect_prod]
  apply Finset.expect_congr rfl
  intro q _
  rw [ActualSpectral.expect_prod]
  simp only [sliceEvent, RowErasureMatrix.selectedEventMass, uniformMass, indicator,
    decide_eq_true_eq]

theorem unrestricted_match_mass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (unrestricted S k s d r).probability
      (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) =
      𝔼 q : Context S k d,
        RowErasureMatrix.selectedMatchMass r
          (ActualGoodRows.table S k s d labeling q.1 q.2) α := by
  have he : (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) =
      targetHit S k s d r labeling α := by
    funext p
    by_cases h : targetHit S k s d r labeling α p = true
    · simp [h, targetHit_implies_slice S k s d r labeling α p h]
    · simp [Bool.eq_false_iff.mpr h]
  rw [he]
  unfold unrestricted
  rw [uniform_probability_expect, ActualSpectral.expect_prod]
  apply Finset.expect_congr rfl
  intro q _
  rw [ActualSpectral.expect_prod]
  simp only [targetHit, RowErasureMatrix.selectedMatchMass, uniformMass, indicator,
    decide_eq_true_eq]

/-- The full-table slice event pays exactly one bounded column-fiber factor. -/
theorem slice_probability_lower (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α g₀ : ℝ)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α) :
    g₀ * (1 / (2 : ℝ) ^ (s * r)) ≤
      (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) := by
  rw [unrestricted_slice_mass]
  have h := RowErasureMatrix.selectedEventMass_contextual_ge (r := r)
    (fun q : Context S k d => ActualGoodRows.table S k s d labeling q.1 q.2) α g₀
    (by simpa only [ActualGoodRows.adviceMass, ActualSpectral.expect_prod] using hgood)
  simpa only [mul_comm] using h

theorem target_probability_lower (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    (α / 2) * (unrestricted S k s d r).probability (sliceEvent S k s d r labeling α) ≤
      (unrestricted S k s d r).probability
        (fun p => sliceEvent S k s d r labeling α p && targetHit S k s d r labeling α p) := by
  rw [unrestricted_slice_mass, unrestricted_match_mass]
  exact RowErasureMatrix.selectedMatchMass_contextual_ge (r := r)
    (fun q : Context S k d => ActualGoodRows.table S k s d labeling q.1 q.2) α

end
end MaxCutGames.Decoder.ActualEvents

end OAI
