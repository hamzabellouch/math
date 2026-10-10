import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.ActualGoodRows

namespace OAI

namespace DFVSGames.Inverse.RowErasureColumnMass

noncomputable section

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Decoder.AdviceFibers
open DFVSGames.Inverse.RowErasureSliceQuotient

variable {E K R : Type*}
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K]
  [AddCommGroup R] [Module F2 R]

theorem card_affineSlice (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (AffineSlice A Q M₀) =
      2 ^ (Module.finrank F2 (E ⧸ Q) * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (equiv A Q M₀).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

theorem card_rowFiber (A : K →ₗ[F2] R) (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) =
      2 ^ (Module.finrank F2 E * Module.finrank F2 A.ker) := by
  rw [Nat.card_congr (rowFiberEquiv A (A.comp M₀) M₀ rfl).symm,
    Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

theorem card_rowFiber_eq_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    Nat.card (RowFiber A (A.comp M₀)) = Nat.card (AffineSlice A Q M₀) *
      2 ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  rw [card_rowFiber, card_affineSlice, ← pow_add, ← Nat.add_mul,
    Q.finrank_quotient_add_finrank]

theorem card_rowFiber_le_mul (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    Nat.card (RowFiber A (A.comp M₀)) ≤
      Nat.card (AffineSlice A Q M₀) * 2 ^ (ell * r) := by
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  rw [card_rowFiber_eq_mul A Q M₀]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexponent)

theorem column_fraction_eq (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) :
    (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) =
      1 / (2 : ℝ) ^ (Module.finrank F2 Q * Module.finrank F2 A.ker) := by
  have hs : (0 : ℝ) < Nat.card (AffineSlice A Q M₀) := by
    rw [card_affineSlice]
    positivity
  rw [card_rowFiber_eq_mul A Q M₀]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_cancel_left₀ hs.ne', one_div]

theorem column_fraction_ge (A : K →ₗ[F2] R) (Q : Submodule F2 E)
    (M₀ : E →ₗ[F2] K) (ell r : ℕ)
    (hQ : Module.finrank F2 Q ≤ r) (hK : Module.finrank F2 K ≤ ell) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (Nat.card (AffineSlice A Q M₀) : ℝ) /
        (Nat.card (RowFiber A (A.comp M₀)) : ℝ) := by
  rw [column_fraction_eq]
  have hker : Module.finrank F2 A.ker ≤ ell := A.ker.finrank_le.trans hK
  have hexponent : Module.finrank F2 Q * Module.finrank F2 A.ker ≤ ell * r := by
    simpa only [Nat.mul_comm r ell] using Nat.mul_le_mul hQ hker
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)

end
end DFVSGames.Inverse.RowErasureColumnMass

namespace DFVSGames.Inverse.Shortcode.Slice

noncomputable section
open scoped BigOperators Matrix

variable {ell m : ℕ}

theorem difference_row_zero (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.rowMap.comp (Matrix.toLin' (M - M₀)) = 0 := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  have hrow : LinearMap.toMatrix' S.rowMap = S.rowCoefficient :=
    LinearMap.toMatrix'_toLin' S.rowCoefficient
  rw [hrow]
  ext i j
  change (∑ a, S.rowCoefficient i a * (M - M₀) a j) = 0
  simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hM.1 i j, h₀.1 i j, sub_self]

theorem difference_range_le (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    LinearMap.range (Matrix.toLin' (M - M₀)) ≤ S.rowMap.ker := by
  rintro _ ⟨v, rfl⟩
  have h := LinearMap.congr_fun (S.difference_row_zero hM h₀) v
  exact h

theorem difference_vanishes_columns (S : Slice ell m) {M M₀ : Mat ell m}
    (hM : S.Contains M) (h₀ : S.Contains M₀) :
    S.columnSpan ≤ LinearMap.ker (Matrix.toLin' (M - M₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change Matrix.toLin' (M - M₀) (S.columnCoefficient i) = 0
  have he : Matrix.toLin' (M - M₀) (S.columnCoefficient i) =
      evaluate M (S.columnCoefficient i) - evaluate M₀ (S.columnCoefficient i) := by
    rw [map_sub, LinearMap.sub_apply]
    rfl
  rw [he, hM.2 i, h₀.2 i, sub_self]

theorem directionEmbedding_surjective (S : Slice ell m)
    (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    Function.Surjective (S.directionEmbedding M₀ h₀) := by
  intro M
  have hM : S.Contains M.val := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property
  obtain ⟨N, hN⟩ :=
    RowErasureSliceQuotient.exists_direction_of_row_and_column
      S.rowMap S.columnSpan (Matrix.toLin' (M.val - M₀))
      (S.difference_vanishes_columns hM h₀) (S.difference_range_le hM h₀)
  have hdir : S.directionMap N = Matrix.toLin' (M.val - M₀) := hN
  have hmat : S.directionMatrix N = M.val - M₀ := by
    unfold directionMatrix
    rw [hdir, LinearMap.toMatrix'_toLin']
  refine ⟨N, ?_⟩
  apply Subtype.ext
  change M₀ + S.directionMatrix N = M.val
  rw [hmat]
  abel

def directionEquiv (S : Slice ell m) (M₀ : Mat ell m) (h₀ : S.Contains M₀) :
    S.Directions ≃ S.points :=
  Equiv.ofBijective (S.directionEmbedding M₀ h₀)
    ⟨(S.directionEmbedding M₀ h₀).injective, S.directionEmbedding_surjective M₀ h₀⟩

@[simp] theorem directionEquiv_val (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (N : S.Directions) :
    (S.directionEquiv M₀ h₀ N).val = M₀ + S.directionMatrix N := rfl

instance directionsFintype (S : Slice ell m) : Fintype S.Directions := by
  classical
  letI : Fintype (Vector m ⧸ S.columnSpan) := Fintype.ofFinite _
  letI : Fintype S.rowMap.ker := Fintype.ofFinite _
  exact Fintype.ofInjective
    (fun N : S.Directions => (N : (Vector m ⧸ S.columnSpan) → S.rowMap.ker))
    DFunLike.coe_injective

theorem card_points_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) : S.points.card = Nat.card S.Directions := by
  rw [← Nat.card_eq_finsetCard, Nat.card_congr (S.directionEquiv M₀ h₀).symm]

theorem points_expect_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (f : Mat ell m → ℝ) :
    S.points.expect f = 𝔼 N : S.Directions, f (M₀ + S.directionMatrix N) := by
  have h := Fintype.expect_equiv (S.directionEquiv M₀ h₀)
    (fun N => f (M₀ + S.directionMatrix N)) (fun M => f M.val) (fun _ => rfl)
  rw [h, Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  simp only [Fintype.card_coe, Finset.sum_coe_sort]

theorem directionMatrix_evaluate (S : Slice ell m) (N : S.Directions) (z : Vector m) :
    evaluate (S.directionMatrix N) z = (N (S.columnSpan.mkQ z) : Vector ell) := by
  change (S.directionMatrix N) *ᵥ z = _
  rw [directionMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem direction_affine_target (S : Slice ell m) (M₀ : Mat ell m)
    (N : S.Directions) (z : Vector m) (u : Vector ell) :
    evaluate (M₀ + S.directionMatrix N) z + u =
      (N (S.columnSpan.mkQ z) : Vector ell) + (evaluate M₀ z + u) := by
  have he : evaluate (M₀ + S.directionMatrix N) z =
      evaluate M₀ z + evaluate (S.directionMatrix N) z := by
    ext i
    simp [evaluate, add_mul, Finset.sum_add_distrib]
  rw [he, S.directionMatrix_evaluate]
  abel

theorem affineAgreement_eq_directions (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) (f : Mat ell m → Vector ell)
    (z : Vector m) (u : Vector ell) :
    S.affineAgreement f z u = 𝔼 N : S.Directions,
      if f (M₀ + S.directionMatrix N) =
        (N (S.columnSpan.mkQ z) : Vector ell) + (evaluate M₀ z + u)
      then (1 : ℝ) else 0 := by
  classical
  rw [affineAgreement, S.points_expect_eq_directions M₀ h₀]
  simp only [S.direction_affine_target]

end
end DFVSGames.Inverse.Shortcode.Slice

namespace DFVSGames.Inverse.RowErasureDescriptionColumnMass

noncomputable section
open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasureDescriptions
open DFVSGames.Inverse.RowErasureMatrix
open scoped BigOperators Classical

def rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m) :
    Finset (Mat ell m) :=
  Finset.univ.filter fun M => rowAdvice A M = s

@[simp] theorem mem_rowFiber {ell m r : ℕ} (A : RowMap ell r) (s : Mat r m)
    (M : Mat ell m) : M ∈ rowFiber A s ↔ rowAdvice A M = s := by
  simp [rowFiber]

def rowOnly {ell m : ℕ} (S : Slice ell m) : Slice ell m where
  rows := S.rows
  columns := 0
  rowCoefficient := S.rowCoefficient
  rowValue := S.rowValue
  columnCoefficient := Fin.elim0
  columnValue := Fin.elim0

theorem rowOnly_contains_iff {ell m : ℕ} (S : Slice ell m) (M : Mat ell m) :
    (rowOnly S).Contains M ↔ rowAdvice S.rowCoefficient M = S.rowValue := by
  constructor
  · intro h
    funext i j
    exact h.1 i j
  · intro h
    constructor
    · intro i j
      exact congrFun (congrFun h i) j
    · intro i
      exact Fin.elim0 i

theorem rowOnly_points {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).points = rowFiber S.rowCoefficient S.rowValue := by
  ext M
  simp only [Slice.points, rowFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rowOnly_contains_iff]

theorem contains_rowOnly {ell m : ℕ} (S : Slice ell m) {M : Mat ell m}
    (hM : S.Contains M) : (rowOnly S).Contains M := by
  exact ⟨hM.1, fun i => Fin.elim0 i⟩

theorem rowOnly_columnSpan {ell m : ℕ} (S : Slice ell m) :
    (rowOnly S).columnSpan = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro _ ⟨i, _⟩
  exact Fin.elim0 i

theorem rowOnly_quotient_finrank {ell m : ℕ} (S : Slice ell m) :
    Module.finrank F2 (Shortcode.Vector m ⧸ (rowOnly S).columnSpan) = m := by
  have h := (rowOnly S).columnSpan.finrank_quotient_add_finrank
  have hz : Module.finrank F2 (rowOnly S).columnSpan = 0 := by
    rw [rowOnly_columnSpan]
    simp
  have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
  rw [hz, add_zero, hm] at h
  exact h

theorem rowFiber_card {ell m : ℕ} (S : Slice ell m) (M₀ : Mat ell m)
    (h₀ : S.Contains M₀) :
    (rowFiber S.rowCoefficient S.rowValue).card =
      2 ^ (m * Module.finrank F2 S.rowMap.ker) := by
  rw [← rowOnly_points S,
    (rowOnly S).card_points_eq_directions M₀ (contains_rowOnly S h₀),
    (rowOnly S).card_directions, rowOnly_quotient_finrank]
  rfl

theorem rowFiber_nonempty {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) : (rowFiber d.1 d.2.1).Nonempty := by
  obtain ⟨M, hM⟩ := hne
  have hc : d.toSlice.Contains M := (Finset.mem_filter.mp hM).2
  refine ⟨M, (mem_rowFiber _ _ _).mpr ?_⟩
  funext i j
  exact hc.1 i j

theorem column_fraction_ge {ell m r : ℕ} (d : Description ell m r)
    (hne : d.toSlice.points.Nonempty) :
    1 / (2 : ℝ) ^ (ell * r) ≤
      (d.toSlice.points.card : ℝ) / ((rowFiber d.1 d.2.1).card : ℝ) := by
  obtain ⟨M₀, hM₀⟩ := hne
  have h₀ : d.toSlice.Contains M₀ := (Finset.mem_filter.mp hM₀).2
  have hs : d.toSlice.points.card = Nat.card
      (RowErasureSliceQuotient.AffineSlice d.toSlice.rowMap d.toSlice.columnSpan
        (Matrix.toLin' M₀)) := by
    rw [d.toSlice.card_points_eq_directions M₀ h₀, d.toSlice.card_directions,
      RowErasureColumnMass.card_affineSlice]
  have hr : (rowFiber d.1 d.2.1).card = Nat.card
      (DFVSGames.Decoder.AdviceFibers.RowFiber d.toSlice.rowMap
        (d.toSlice.rowMap.comp (Matrix.toLin' M₀))) := by
    have hm : Module.finrank F2 (Shortcode.Vector m) = m := by simp [Shortcode.Vector]
    rw [RowErasureColumnMass.card_rowFiber, hm]
    exact rowFiber_card d.toSlice M₀ h₀
  have h := RowErasureColumnMass.column_fraction_ge
    d.toSlice.rowMap d.toSlice.columnSpan (Matrix.toLin' M₀) ell r
    d.toSlice.columnSpan_finrank_le (by simp [Shortcode.Vector])
  rwa [← hs, ← hr] at h

end
end DFVSGames.Inverse.RowErasureDescriptionColumnMass

section

namespace DFVSGames.Inverse.RowErasure

noncomputable section
open scoped BigOperators

variable {X Y A S D : Type*}

def SliceFamily.selectedPoints (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Finset X :=
  match F.selectedDescription f α a s with
  | none => ∅
  | some d => F.points d

def SliceFamily.selectedHit (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X) : Prop :=
  ∃ d, F.selectedDescription f α a s = some d ∧ f x = F.target d x

theorem SliceFamily.selectedPoints_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    F.selectedPoints f α a s = F.points (F.chosenDescription f α a s hgood) := by
  unfold SliceFamily.selectedPoints
  rw [F.selectedDescription_of_good f α a s hgood]

theorem SliceFamily.selectedHit_of_good (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) (x : X) :
    F.selectedHit f α a s x ↔ f x = F.target (F.chosenDescription f α a s hgood) x := by
  unfold SliceFamily.selectedHit
  rw [F.selectedDescription_of_good f α a s hgood]
  constructor
  · rintro ⟨d, hd, hhit⟩
    have he := Option.some.inj hd
    simpa only [he] using hhit
  · intro hhit
    exact ⟨_, rfl, hhit⟩

theorem SliceFamily.selectedPoints_support (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) (x : X)
    (hx : x ∈ F.selectedPoints f α a s) : F.advice a x = s := by
  classical
  cases hd : F.selectedDescription f α a s with
  | none => simp [SliceFamily.selectedPoints, hd] at hx
  | some d =>
    have hspec := F.selectedDescription_spec f α a s hd
    have hmem : x ∈ F.points d := by
      simpa only [SliceFamily.selectedPoints, hd] using hx
    have h := F.points_row d x hmem
    rw [hspec.1, hspec.2.1] at h
    exact h

theorem SliceFamily.selectedEvent_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedEvent f α a x ↔
      F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x) := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedEvent_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x hx)).elim
    · intro hx
      exact (hg hx.1).elim

theorem SliceFamily.selectedMatch_iff_points (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) :
    F.selectedMatch f α a x ↔
      (F.GoodAdvice f α a (F.advice a x) ∧
        x ∈ F.selectedPoints f α a (F.advice a x)) ∧
          F.selectedHit f α a (F.advice a x) x := by
  classical
  by_cases hg : F.GoodAdvice f α a (F.advice a x)
  · rw [F.selectedMatch_iff_of_advice f α a (F.advice a x) hg x rfl,
      F.selectedPoints_of_good f α a (F.advice a x) hg,
      F.selectedHit_of_good f α a (F.advice a x) hg x]
    simp only [hg, true_and]
  · constructor
    · intro hx
      exact (hg (F.selectedEvent_good f α a x (F.selectedMatch_event f α a x hx))).elim
    · intro hx
      exact (hg hx.1.1).elim

theorem SliceFamily.selectedPoints_match_sum (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S)
    (hgood : F.GoodAdvice f α a s) :
    (α / 2) * ((F.selectedPoints f α a s).card : ℝ) ≤
      ∑ x ∈ F.selectedPoints f α a s, indicator (F.selectedHit f α a s x) := by
  classical
  have hspec := F.chosenDescription_spec f α a s hgood
  have hcard : (0 : ℝ) < (F.points (F.chosenDescription f α a s hgood)).card :=
    Nat.cast_pos.mpr hspec.2.2.1.card_pos
  have hagree := hspec.2.2.2
  rw [SliceFamily.agreement, Finset.expect_eq_sum_div_card] at hagree
  rw [F.selectedPoints_of_good f α a s hgood]
  simp_rw [F.selectedHit_of_good f α a s hgood]
  exact (le_div_iff₀ hcard).mp hagree

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasureMatrix

noncomputable section
open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions
open DFVSGames.Inverse.RowErasureDescriptionColumnMass
open scoped BigOperators

variable {ell m r : ℕ}

theorem selectedPoints_column_mass (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) (s : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A s) :
    (1 / (2 : ℝ) ^ (ell * r)) * ((rowFiber A s).card : ℝ) ≤
      (((family ell m r).selectedPoints f α A s).card : ℝ) := by
  let d := (family ell m r).chosenDescription f α A s hgood
  have hspec := (family ell m r).chosenDescription_spec f α A s hgood
  have hne : d.toSlice.points.Nonempty := hspec.2.2.1
  have hcard : (0 : ℝ) < (rowFiber d.1 d.2.1).card :=
    Nat.cast_pos.mpr (rowFiber_nonempty d hne).card_pos
  have h := (le_div_iff₀ hcard).mp (column_fraction_ge d hne)
  have hA : d.1 = A := hspec.1
  have hs : d.2.1 = s := hspec.2.1
  rw [hA, hs] at h
  rw [(family ell m r).selectedPoints_of_good f α A s hgood]
  exact h

theorem selected_event_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (1 / (2 : ℝ) ^ (ell * r)) *
      uniformMass ((family ell m r).goodAt f α A) ≤
        uniformMass ((family ell m r).selectedEvent f α A) := by
  have h := SelectionPartition.mass_event_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    (1 / (2 : ℝ) ^ (ell * r))
    (fun s hg => by
      have hfiber : SelectionPartition.fiber ((family ell m r).advice A) s =
          rowFiber A s := by
        ext M
        simp only [SelectionPartition.fiber, rowFiber, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rfl
      rw [hfiber]
      exact selectedPoints_column_mass f α A s hg)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  rw [he] at h
  exact h

theorem selected_match_mass_ge (f : Mat ell m → Vector ell) (α : ℝ)
    (A : RowMap ell r) :
    (α / 2) * uniformMass ((family ell m r).selectedEvent f α A) ≤
      uniformMass ((family ell m r).selectedMatch f α A) := by
  have h := SelectionPartition.mass_match_ge
    ((family ell m r).advice A) ((family ell m r).GoodAdvice f α A)
    ((family ell m r).selectedPoints f α A)
    ((family ell m r).selectedPoints_support f α A)
    ((family ell m r).selectedHit f α A)
    (α / 2) ((family ell m r).selectedPoints_match_sum f α A)
  have he : SelectionPartition.event ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A) =
      (family ell m r).selectedEvent f α A := by
    funext M
    exact propext ((family ell m r).selectedEvent_iff_points f α A M).symm
  have hm : SelectionPartition.matchEvent ((family ell m r).advice A)
      ((family ell m r).GoodAdvice f α A) ((family ell m r).selectedPoints f α A)
      ((family ell m r).selectedHit f α A) =
      (family ell m r).selectedMatch f α A := by
    funext M
    exact propext ((family ell m r).selectedMatch_iff_points f α A M).symm
  rw [he, hm] at h
  exact h

def selectedEventMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedEvent f α A)

def selectedMatchMass (r : ℕ) (f : Mat ell m → Vector ell) (α : ℝ) : ℝ :=
  𝔼 A : RowMap ell r, uniformMass ((family ell m r).selectedMatch f α A)

theorem selectedEventMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (1 / (2 : ℝ) ^ (ell * r)) * adviceMass ((family ell m r).goodAt f α) ≤
      selectedEventMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_event_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  have hadvice : (𝔼 A : RowMap ell r, uniformMass ((family ell m r).goodAt f α A)) =
      adviceMass ((family ell m r).goodAt f α) := by
    simp only [uniformMass, adviceMass]
    exact Finset.expect_comm _ _ _
  rw [hadvice] at h
  exact h

theorem selectedMatchMass_ge (f : Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * selectedEventMass r f α ≤ selectedMatchMass r f α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun (A : RowMap ell r) _ => selected_match_mass_ge f α A)
  rw [← Finset.mul_expect] at h
  exact h

theorem selectedEventMass_weighted_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell)
    (α g₀ : ℝ)
    (hgood : g₀ ≤ ∑ q, w q * adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ ∑ q, w q * selectedEventMass r (f q) α := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun q _ =>
    mul_le_mul_of_nonneg_left (selectedEventMass_ge (r := r) (f q) α) (hw q))
  have heq : (∑ q, w q * ((1 / (2 : ℝ) ^ (ell * r)) *
      adviceMass ((family ell m r).goodAt (f q) α))) =
      (1 / (2 : ℝ) ^ (ell * r)) *
        ∑ q, w q * adviceMass ((family ell m r).goodAt (f q) α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [heq] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_weighted_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (∑ q, w q * selectedEventMass r (f q) α) ≤
      ∑ q, w q * selectedMatchMass r (f q) α := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun q _ =>
    mul_le_mul_of_nonneg_left (selectedMatchMass_ge (r := r) (f q) α) (hw q))
  have heq : (∑ q, w q * ((α / 2) * selectedEventMass r (f q) α)) =
      (α / 2) * (∑ q, w q * selectedEventMass r (f q) α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rwa [heq] at h

theorem selectedMatchMass_conditional_ge {Q : Type*} [Fintype Q]
    (w : Q → ℝ) (hw : ∀ q, 0 ≤ w q) (f : Q → Mat ell m → Vector ell) (α : ℝ)
    (hpositive : 0 < ∑ q, w q * selectedEventMass r (f q) α) :
    α / 2 ≤ (∑ q, w q * selectedMatchMass r (f q) α) /
      (∑ q, w q * selectedEventMass r (f q) α) :=
  (le_div_iff₀ hpositive).mpr (selectedMatchMass_weighted_ge w hw f α)

theorem selectedEventMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α g₀ : ℝ)
    (hgood : g₀ ≤ 𝔼 q, adviceMass ((family ell m r).goodAt (f q) α)) :
    (1 / (2 : ℝ) ^ (ell * r)) * g₀ ≤ 𝔼 q, selectedEventMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedEventMass_ge (r := r) (f q) α)
  rw [← Finset.mul_expect] at h
  exact (mul_le_mul_of_nonneg_left hgood (by positivity)).trans h

theorem selectedMatchMass_contextual_ge {Q : Type*} [Fintype Q]
    (f : Q → Mat ell m → Vector ell) (α : ℝ) :
    (α / 2) * (𝔼 q, selectedEventMass r (f q) α) ≤
      𝔼 q, selectedMatchMass r (f q) α := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => selectedMatchMass_ge (r := r) (f q) α)
  rwa [← Finset.mul_expect] at h

end
end DFVSGames.Inverse.RowErasureMatrix
end

namespace DFVSGames.Decoder.ActualEvents

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
end DFVSGames.Decoder.ActualEvents

namespace DFVSGames.Inverse.RowErasureDescriptions

open DFVSGames.Inverse.Shortcode

def Description.withTarget {ell m r : ℕ} (d : Description ell m r)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (d.1, d.2.1, d.2.2.1, d.2.2.2.1, z, u)

@[simp] theorem Description.withTarget_toSlice {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).toSlice = d.toSlice := rfl

@[simp] theorem Description.withTarget_coefficient {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).coefficient = z := rfl

@[simp] theorem Description.withTarget_intercept {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).intercept = u := rfl

end DFVSGames.Inverse.RowErasureDescriptions

namespace DFVSGames.Inverse.RowErasureMatrix

open DFVSGames.Inverse.Shortcode
open DFVSGames.Inverse.RowErasure
open DFVSGames.Inverse.RowErasureDescriptions

noncomputable section

variable {ell m r : ℕ}

theorem exists_normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    ∃ d : Description ell m r,
      (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M := by
  classical
  let d₀ := (family ell m r).chosenDescription f α A S hgood
  obtain ⟨hrow, hvalue, hnonempty, hagree⟩ :=
    (family ell m r).chosenDescription_spec f α A S hgood
  obtain ⟨M₀, hM₀⟩ := hnonempty
  have hcontains : d₀.toSlice.Contains M₀ := by
    exact (Finset.mem_filter.mp hM₀).2
  have hagree' : α / 2 ≤ d₀.toSlice.affineAgreement f d₀.coefficient d₀.intercept := by
    exact (family_agreement d₀ f) ▸ hagree
  obtain ⟨z, u, hfirst, heq, htarget⟩ :=
    d₀.toSlice.first_bit_normalization M₀ hcontains e f d₀.coefficient d₀.intercept
      (fun h M => hfold h M) α hα hagree' hsmall
  have heq' : (family ell m r).agreement f (d₀.withTarget z u) =
      (family ell m r).agreement f d₀ := by
    rw [family_agreement, family_agreement]
    exact heq
  refine ⟨d₀.withTarget z u, hrow, hvalue, ⟨M₀, hM₀⟩, ?_, hfirst, rfl, heq', ?_⟩
  · exact heq'.symm ▸ hagree
  · intro M hM
    exact htarget M (Finset.mem_filter.mp hM).2

def normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    Description ell m r :=
  Classical.choose (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

theorem normalizedChosenDescription_spec
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    let d := normalizedChosenDescription f α A S hgood e hfold hα hsmall
    (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M :=
  Classical.choose_spec
    (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

end
end DFVSGames.Inverse.RowErasureMatrix

end OAI
