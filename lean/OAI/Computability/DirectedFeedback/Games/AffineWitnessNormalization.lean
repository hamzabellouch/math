import Mathlib
import OAI.Computability.DirectedFeedback.Games.RowErasureSlices

namespace OAI

namespace DFVSGames.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

abbrev Slice (A : C →ₗ[F2] R) (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) :=
  {M : D →ₗ[F2] C // InSlice A Z M₀ M}

def sliceShift (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (M : Slice A Z M₀) :
    Slice A Z M₀ :=
  ⟨shift e h M, shift_preserves_slice e A Z M₀ M heZ h M.property⟩

theorem sliceShift_zero (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ 0 M = M := by
  apply Subtype.ext
  exact shift_zero e M.val

theorem sliceShift_add (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h k : A.ker) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ (h + k) M =
      sliceShift e A Z M₀ heZ h (sliceShift e A Z M₀ heZ k M) := by
  apply Subtype.ext
  exact shift_add e (h : C) (k : C) M.val

theorem agreement_count_le [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hno : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u} ≤
      Nat.card (Slice A Z M₀) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  obtain ⟨hz, heZ⟩ := no_affine_representative e Z z hno
  have hcount := folded_action_card_mul_agreement_le
    (sliceShift e A Z M₀ heZ)
    (sliceShift_zero e A Z M₀ heZ)
    (sliceShift_add e A Z M₀ heZ)
    (fun h : A.ker => (h : C)) Subtype.val_injective
    (fun M : Slice A Z M₀ => F M)
    (fun M : Slice A Z M₀ => M.val z + u)
    (fun h M => hfold h M)
    (fun h M => shift_preserves_target e z hz u h M)
  simpa only [Nat.card_eq_fintype_card] using hcount

theorem normalize_of_good_count [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hgood : Nat.card (Slice A Z M₀) <
      Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u}) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  apply normalize e A Z M₀ z u
  by_contra hno
  exact (not_lt_of_ge (agreement_count_le e A Z M₀ z u F hfold hno)) hgood

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Matrix

namespace Slice

variable {ell m : ℕ}

def rowMap (S : Slice ell m) : Vector ell →ₗ[F2] Vector S.rows :=
  Matrix.mulVecLin S.rowCoefficient

def columnSpan (S : Slice ell m) : Submodule F2 (Vector m) :=
  Submodule.span F2 (Set.range S.columnCoefficient)

abbrev Directions (S : Slice ell m) :=
  (Vector m ⧸ S.columnSpan) →ₗ[F2] S.rowMap.ker

def directionMap (S : Slice ell m) (N : S.Directions) :
    Vector m →ₗ[F2] Vector ell :=
  S.rowMap.ker.subtype.comp (N.comp S.columnSpan.mkQ)

def directionMatrix (S : Slice ell m) (N : S.Directions) : Mat ell m :=
  LinearMap.toMatrix' (S.directionMap N)

theorem directionMatrix_injective (S : Slice ell m) :
    Function.Injective S.directionMatrix := by
  intro N P h
  have hmap : S.directionMap N = S.directionMap P :=
    LinearMap.toMatrix'.injective h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := S.columnSpan.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : Vector m →ₗ[F2] Vector ell => f v) hmap

theorem directionMatrix_row (S : Slice ell m) (N : S.Directions)
    (i : Fin S.rows) (j : Fin m) :
    (∑ a, S.rowCoefficient i a * S.directionMatrix N a j) = 0 := by
  have h := (N (S.columnSpan.mkQ (Pi.single j 1))).property
  have hi := congrFun h i
  change (∑ a, S.rowCoefficient i a *
    (N (S.columnSpan.mkQ (Pi.single j 1)) : Vector ell) a) = 0 at hi
  exact hi

theorem directionMatrix_column (S : Slice ell m) (N : S.Directions)
    (i : Fin S.columns) :
    evaluate (S.directionMatrix N) (S.columnCoefficient i) = 0 := by
  have hq : S.columnSpan.mkQ (S.columnCoefficient i) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero S.columnSpan).mpr
    exact Submodule.subset_span ⟨i, rfl⟩
  change (S.directionMatrix N) *ᵥ (S.columnCoefficient i) = 0
  rw [directionMatrix, LinearMap.toMatrix'_mulVec]
  simp [directionMap, hq]

theorem contains_add_direction (S : Slice ell m) (M : Mat ell m)
    (hM : S.Contains M) (N : S.Directions) :
    S.Contains (M + S.directionMatrix N) := by
  constructor
  · intro i j
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hM.1 i j, S.directionMatrix_row N i j, add_zero]
  · intro i
    have hd := S.directionMatrix_column N i
    change evaluate (M + S.directionMatrix N) (S.columnCoefficient i) = _
    have he : evaluate (M + S.directionMatrix N) (S.columnCoefficient i) =
        evaluate M (S.columnCoefficient i) +
          evaluate (S.directionMatrix N) (S.columnCoefficient i) := by
      ext a
      simp [evaluate, add_mul, Finset.sum_add_distrib]
    rw [he, hM.2 i, hd, add_zero]

def directionEmbedding (S : Slice ell m) (M : Mat ell m) (hM : S.Contains M) :
    S.Directions ↪ S.points where
  toFun N := ⟨M + S.directionMatrix N, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    exact S.contains_add_direction M hM N⟩
  inj' := by
    intro N P h
    apply S.directionMatrix_injective
    exact add_left_cancel (congrArg Subtype.val h)

theorem columnSpan_finrank_le (S : Slice ell m) :
    Module.finrank F2 S.columnSpan ≤ S.columns := by
  have h := finrank_range_le_card (R := F2) (M := Vector m) S.columnCoefficient
  change Module.finrank F2 (Submodule.span F2 (Set.range S.columnCoefficient)) ≤
    Fintype.card (Fin S.columns) at h
  rw [Fintype.card_fin] at h
  exact h

theorem quotient_finrank_ge (S : Slice ell m) :
    m - S.columns ≤ Module.finrank F2 (Vector m ⧸ S.columnSpan) := by
  have h := S.columnSpan.finrank_quotient_add_finrank
  have hspan := S.columnSpan_finrank_le
  have hm : Module.finrank F2 (Vector m) = m := by simp [Vector]
  rw [hm] at h
  omega

theorem rowKernel_finrank_ge (S : Slice ell m) :
    ell - S.rows ≤ Module.finrank F2 S.rowMap.ker := by
  have h := S.rowMap.finrank_range_add_finrank_ker
  have hrange : Module.finrank F2 S.rowMap.range ≤ S.rows := by
    exact S.rowMap.range.finrank_le.trans_eq (by simp [Vector])
  have hell : Module.finrank F2 (Vector ell) = ell := by simp [Vector]
  rw [hell] at h
  omega

theorem card_directions (S : Slice ell m) :
    Nat.card S.Directions =
      2 ^ (Module.finrank F2 (Vector m ⧸ S.columnSpan) *
        Module.finrank F2 S.rowMap.ker) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), Module.finrank_linearMap]
  simp [F2]

theorem card_directions_le (S : Slice ell m) (hne : S.points.Nonempty) :
    Nat.card S.Directions ≤ S.points.card := by
  obtain ⟨M, hM⟩ := hne
  have hcontains : S.Contains M := by simpa only [points, Finset.mem_filter,
    Finset.mem_univ, true_and] using hM
  simpa only [Nat.card_eq_finsetCard] using
    Nat.card_le_card_of_injective (S.directionEmbedding M hcontains)
      (S.directionEmbedding M hcontains).injective

theorem pow_dimension_le_card (S : Slice ell m) (r : ℕ)
    (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : S.points.Nonempty) :
    2 ^ ((ell - r) * (m - r)) ≤ S.points.card := by
  have hrow : ell - r ≤ Module.finrank F2 S.rowMap.ker :=
    (Nat.sub_le_sub_left hrows ell).trans S.rowKernel_finrank_ge
  have hcol : m - r ≤ Module.finrank F2 (Vector m ⧸ S.columnSpan) :=
    (Nat.sub_le_sub_left hcolumns m).trans S.quotient_finrank_ge
  have hmul := Nat.mul_le_mul hcol hrow
  rw [Nat.mul_comm (m - r) (ell - r)] at hmul
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hmul
  rw [← S.card_directions] at hp
  exact hp.trans (S.card_directions_le hne)

end Slice
end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical Matrix

namespace Slice

variable {ell m : ℕ}

theorem evaluate_eq_toLin (M : Mat ell m) (z : Vector m) :
    evaluate M z = Matrix.toLin' M z := rfl

theorem row_equations_iff (S : Slice ell m) (M : Mat ell m) :
    (∀ i j, (∑ a, S.rowCoefficient i a * M a j) = S.rowValue i j) ↔
      S.rowMap.comp (Matrix.toLin' M) = Matrix.toLin' S.rowValue := by
  let A : Matrix (Fin S.rows) (Fin ell) F2 := S.rowCoefficient
  let B : Matrix (Fin S.rows) (Fin m) F2 := S.rowValue
  change (∀ i j, (∑ a, A i a * M a j) = B i j) ↔
    (Matrix.toLin' A).comp (Matrix.toLin' M) = Matrix.toLin' B
  constructor
  · intro h
    have hm : A * M = B := by
      ext i j
      exact h i j
    rw [← Matrix.toLin'_mul, hm]
  · intro h
    have hm : A * M = B := by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul]
      exact h
    intro i j
    exact congrFun (congrFun hm i) j

theorem contains_iff_inSlice (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) (M : Mat ell m) :
    S.Contains M ↔
      AffineWitness.InSlice S.rowMap S.columnSpan
        (Matrix.toLin' M₀) (Matrix.toLin' M) := by
  have hrow₀ := (S.row_equations_iff M₀).mp hM₀.1
  have hcol₀ : ∀ i, Matrix.toLin' M₀ (S.columnCoefficient i) =
      S.columnValue i := hM₀.2
  have heq := AffineWitness.explicit_slice_iff S.rowMap
    (Matrix.toLin' S.rowValue) S.columnCoefficient S.columnValue
    (Matrix.toLin' M₀) (Matrix.toLin' M) hrow₀ hcol₀
  constructor
  · intro hM
    exact heq.mp ⟨(S.row_equations_iff M).mp hM.1, hM.2⟩
  · intro hM
    have h := heq.mpr hM
    exact ⟨(S.row_equations_iff M).mpr h.1, h.2⟩

def linearSliceEquiv (S : Slice ell m) (M₀ : Mat ell m)
    (hM₀ : S.Contains M₀) :
    S.points ≃ AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) where
  toFun M := ⟨Matrix.toLin' M.val,
    (S.contains_iff_inSlice M₀ hM₀ M.val).mp (by
      simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using M.property)⟩
  invFun N := ⟨LinearMap.toMatrix' N.val, by
    simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (S.contains_iff_inSlice M₀ hM₀ _).mpr
    simpa only [Matrix.toLin'_toMatrix'] using N.property⟩
  left_inv M := by
    apply Subtype.ext
    exact LinearMap.toMatrix'_toLin' M.val
  right_inv N := by
    apply Subtype.ext
    exact Matrix.toLin'_toMatrix' N.val

theorem affineAgreement_eq_of_target_eq (S : Slice ell m)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  unfold affineAgreement
  apply Finset.expect_congr rfl
  intro M hM
  have hcontains : S.Contains M := by
    simpa only [points, Finset.mem_filter, Finset.mem_univ, true_and] using hM
  rw [htarget M hcontains]

theorem affineAgreement_eq_of_linear_target_eq (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z z' : Vector m) (u u' : Vector ell)
    (htarget : ∀ M, AffineWitness.InSlice S.rowMap S.columnSpan
      (Matrix.toLin' M₀) M → M z' + u' = M z + u) :
    S.affineAgreement f z' u' = S.affineAgreement f z u := by
  apply S.affineAgreement_eq_of_target_eq f z z' u u'
  intro M hM
  exact htarget (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

theorem affineAgreement_translate (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z w : Vector m) (hw : w ∈ S.columnSpan)
    (u : Vector ell) :
    S.affineAgreement f (z + w) (u + evaluate M₀ w) =
      S.affineAgreement f z u := by
  apply S.affineAgreement_eq_of_linear_target_eq M₀ hM₀ f z (z + w) u _
  intro M hM
  exact AffineWitness.translate_target S.rowMap S.columnSpan (Matrix.toLin' M₀)
    M hM z w hw u

end Slice
end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem normalize_of_density [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (η : ℝ)
    (hgood : η ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsize : 1 < η * (Nat.card A.ker : ℝ)) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  let : Nonempty (Slice A Z M₀) := ⟨⟨M₀, rfl, fun _ _ => rfl⟩⟩
  have hpos : (0 : ℝ) < (Nat.card (Slice A Z M₀) : ℝ) := by
    exact_mod_cast Nat.card_pos (α := Slice A Z M₀)
  have hmass := (le_div_iff₀ hpos).mp hgood
  have hmul := mul_le_mul_of_nonneg_right hmass
    (Nat.cast_nonneg (α := ℝ) (Nat.card A.ker))
  have hstrict := mul_lt_mul_of_pos_right hsize hpos
  apply normalize_of_good_count e A Z M₀ z u F hfold
  have hreal : (Nat.card (Slice A Z M₀) : ℝ) <
      (Nat.card A.ker : ℝ) *
        (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) := by
    nlinarith only [hmul, hstrict]
  exact_mod_cast hreal

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse.AffineWitness

theorem first_bit_witness {m ℓ r : ℕ}
    (e : (Fin m → F2) →ₗ[F2] F2)
    (A : (Fin ℓ → F2) →ₗ[F2] (Fin r → F2))
    (Z : Submodule F2 (Fin m → F2))
    (M₀ : (Fin m → F2) →ₗ[F2] (Fin ℓ → F2))
    (z : Fin m → F2) (u : Fin ℓ → F2)
    (F : ((Fin m → F2) →ₗ[F2] (Fin ℓ → F2)) → (Fin ℓ → F2))
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (α : ℝ) (hα : 0 < α)
    (hgood : α / 2 ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsmall : 1 / (2 : ℝ) ^ (ℓ - r) < α / 8) :
    ∃ z' : Fin m → F2, ∃ u' : Fin ℓ → F2, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  have hpow : (0 : ℝ) < 2 ^ (ℓ - r) := pow_pos (by norm_num) _
  have hsep := (div_lt_iff₀ hpow).mp hsmall
  have hk : (2 : ℝ) ^ (ℓ - r) ≤ (Nat.card A.ker : ℝ) := by
    exact_mod_cast binary_kernel_card_lower A
  have hscale := mul_le_mul_of_nonneg_left hk hα.le
  have hsize : 1 < (α / 2) * (Nat.card A.ker : ℝ) := by
    nlinarith only [hsep, hscale]
  exact normalize_of_density e A Z M₀ z u F hfold (α / 2) hgood hsize

end DFVSGames.Inverse.AffineWitness

namespace DFVSGames.Inverse

open scoped BigOperators

variable {X Y : Type*}

theorem card_finset_subtype_eq_filter_card (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    Nat.card {x : s // p x.val} = (s.filter p).card := by
  classical
  let e : {x : s // p x.val} ≃ ↥(s.filter p) :=
    { toFun := fun x =>
        ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x =>
        ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
          (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

theorem finset_expect_indicator_eq_card_ratio (s : Finset X)
    (p : X → Prop) [DecidablePred p] :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {x : s // p x.val} : ℝ) / (Nat.card s : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole,
    card_finset_subtype_eq_filter_card, Nat.card_eq_finsetCard]

theorem nat_card_subtype_equiv (e : X ≃ Y) (p : X → Prop) (q : Y → Prop)
    (h : ∀ x, p x ↔ q (e x)) :
    Nat.card {x : X // p x} = Nat.card {y : Y // q y} :=
  Nat.card_congr (e.subtypeEquiv h)

theorem finset_expect_indicator_eq_card_ratio_of_equiv (s : Finset X)
    (p : X → Prop) [DecidablePred p] (e : ↥s ≃ Y) (q : Y → Prop)
    (h : ∀ x : s, p x.val ↔ q (e x)) :
    s.expect (fun x => if p x then (1 : ℝ) else 0) =
      (Nat.card {y : Y // q y} : ℝ) / (Nat.card Y : ℝ) := by
  rw [finset_expect_indicator_eq_card_ratio,
    nat_card_subtype_equiv e (fun x => p x.val) q h, Nat.card_congr e]

end DFVSGames.Inverse

namespace DFVSGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical

variable {ell m : ℕ}

def functionalRow (e : Vector m →ₗ[F2] F2) : Vector m :=
  fun j => e (Pi.single j 1)

theorem toMatrix_shift (e : Vector m →ₗ[F2] F2) (h : Vector ell)
    (M : Mat ell m) :
    LinearMap.toMatrix' (AffineWitness.shift e h (Matrix.toLin' M)) =
      M + rankOne h (functionalRow e) := by
  rw [AffineWitness.shift, map_add, LinearMap.toMatrix'_toLin']
  congr 1
  ext i j
  simp only [LinearMap.toMatrix'_apply, LinearMap.smulRight_apply,
    Pi.smul_apply, smul_eq_mul, rankOne, functionalRow, mul_comm]

namespace Slice

theorem affineAgreement_eq_linear_ratio (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell) :
    S.affineAgreement f z u =
      (Nat.card {N : AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀) //
        f (LinearMap.toMatrix' N.val) = N.val z + u} : ℝ) /
      (Nat.card (AffineWitness.Slice S.rowMap S.columnSpan (Matrix.toLin' M₀)) : ℝ) := by
  unfold affineAgreement
  apply finset_expect_indicator_eq_card_ratio_of_equiv S.points
    (fun M => f M = evaluate M z + u) (S.linearSliceEquiv M₀ hM₀)
    (fun N => f (LinearMap.toMatrix' N.val) = N.val z + u)
  intro M
  change (f M.val = evaluate M.val z + u) ↔
    (f (LinearMap.toMatrix' (Matrix.toLin' M.val)) = Matrix.toLin' M.val z + u)
  rw [LinearMap.toMatrix'_toLin']
  rfl

theorem first_bit_normalization (S : Slice ell m)
    (M₀ : Mat ell m) (hM₀ : S.Contains M₀)
    (e : Vector m →ₗ[F2] F2)
    (f : Mat ell m → Vector ell) (z : Vector m) (u : Vector ell)
    (hfold : ∀ (h : S.rowMap.ker) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (α : ℝ) (hα : 0 < α) (hgood : α / 2 ≤ S.affineAgreement f z u)
    (hsmall : 1 / (2 : ℝ) ^ (ell - S.rows) < α / 8) :
    ∃ z' : Vector m, ∃ u' : Vector ell, e z' = 1 ∧
      S.affineAgreement f z' u' = S.affineAgreement f z u ∧
      ∀ M, S.Contains M → evaluate M z' + u' = evaluate M z + u := by
  let F : (Vector m →ₗ[F2] Vector ell) → Vector ell :=
    fun N => f (LinearMap.toMatrix' N)
  have hfold' : ∀ (h : S.rowMap.ker) N,
      F (AffineWitness.shift e h N) = F N + h := by
    intro h N
    have hs : LinearMap.toMatrix' (AffineWitness.shift e h N) =
        LinearMap.toMatrix' N + rankOne h (functionalRow e) := by
      simpa only [Matrix.toLin'_toMatrix'] using toMatrix_shift e h (LinearMap.toMatrix' N)
    exact (congrArg f hs).trans (hfold h (LinearMap.toMatrix' N))
  have hgood' := hgood
  rw [S.affineAgreement_eq_linear_ratio M₀ hM₀ f z u] at hgood'
  obtain ⟨z', u', he, ht⟩ := AffineWitness.first_bit_witness e S.rowMap S.columnSpan
    (Matrix.toLin' M₀) z u F hfold' α hα hgood' hsmall
  refine ⟨z', u', he, S.affineAgreement_eq_of_linear_target_eq M₀ hM₀ f z z' u u' ht, ?_⟩
  intro M hM
  exact ht (Matrix.toLin' M) ((S.contains_iff_inSlice M₀ hM₀ M).mp hM)

end Slice
end
end DFVSGames.Inverse.Shortcode

namespace DFVSGames.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

def domainCoordinates (k : ℕ) :
    ActualHomogeneous.E k ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [ActualHomogeneous.finrank_E, Module.finrank_fin_fun])

def changeDomain {D E K : Type*} [AddCommGroup D] [Module F2 D]
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    (e : D ≃ₗ[F2] E) : (D →ₗ[F2] K) ≃ₗ[F2] (E →ₗ[F2] K) where
  toFun M := M.comp e.symm.toLinearMap
  invFun M := M.comp e.toLinearMap
  left_inv M := by ext x; simp
  right_inv M := by ext x; simp
  map_add' M N := by ext x; rfl
  map_smul' c M := by ext x; rfl

def mapEquiv (k ell : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) ≃ₗ[F2]
      Inverse.Shortcode.Mat ell (1 + 2 * k) :=
  (changeDomain (domainCoordinates k)).trans LinearMap.toMatrix'

@[simp] theorem mapEquiv_apply (k ell : ℕ)
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k ell M = LinearMap.toMatrix' (M.comp (domainCoordinates k).symm.toLinearMap) :=
  rfl

@[simp] theorem mapEquiv_symm_apply (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) :
    (mapEquiv k ell).symm M = (Matrix.toLin' M).comp (domainCoordinates k).toLinearMap :=
  rfl

def functionalEquiv (k : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] F2) ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  (changeDomain (domainCoordinates k)).trans ((Pi.basisFun F2 (Fin (1 + 2 * k))).constr F2).symm

@[simp] theorem functionalEquiv_apply (k : ℕ)
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (j : Fin (1 + 2 * k)) :
    functionalEquiv k l j = l ((domainCoordinates k).symm (Pi.single j 1)) := by
  simp [functionalEquiv, changeDomain, Module.Basis.constr_symm_apply, Pi.basisFun_apply]

theorem mapEquiv_rankOne (k ell : ℕ) (l : ActualHomogeneous.E k →ₗ[F2] F2)
    (a : Fin ell → F2) :
    mapEquiv k ell (l.smulRight a) = Inverse.Shortcode.rankOne a (functionalEquiv k l) := by
  ext i j
  simp [Inverse.Shortcode.rankOne, mul_comm]

theorem mapEquiv_symm_add_rankOne (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k))
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (a : Fin ell → F2) :
    (mapEquiv k ell).symm (M + Inverse.Shortcode.rankOne a (functionalEquiv k l)) =
      (mapEquiv k ell).symm M + l.smulRight a := by
  apply (mapEquiv k ell).injective
  rw [LinearEquiv.apply_symm_apply, map_add, LinearEquiv.apply_symm_apply, mapEquiv_rankOne]

def coordinateTau (k : ℕ) : (Fin (1 + 2 * k) → F2) →ₗ[F2] F2 :=
  ActualHomogeneous.tau.comp (domainCoordinates k).symm.toLinearMap

theorem functionalEquiv_tau (k : ℕ) :
    functionalEquiv k ActualHomogeneous.tau =
      Inverse.Shortcode.functionalRow (coordinateTau k) := by
  ext j
  rw [functionalEquiv_apply]
  rfl

theorem mapEquiv_symm_firstBit_shift (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (a : Fin ell → F2) :
    (mapEquiv k ell).symm
        (M + Inverse.Shortcode.rankOne a (Inverse.Shortcode.functionalRow (coordinateTau k))) =
      (mapEquiv k ell).symm M + ActualHomogeneous.tau.smulRight a := by
  rw [← functionalEquiv_tau]
  exact mapEquiv_symm_add_rankOne k ell M ActualHomogeneous.tau a

theorem affine_evaluation (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) (z : Fin (1 + 2 * k) → F2)
    (u : Fin ell → F2) :
    Inverse.Shortcode.evaluate M z + u =
      (mapEquiv k ell).symm M ((domainCoordinates k).symm z) + u := by
  change Inverse.Shortcode.evaluate M z + u =
    Matrix.toLin' M ((domainCoordinates k) ((domainCoordinates k).symm z)) + u
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem mapEquiv_rowAdvice (k ell r : ℕ)
    (A : (Fin ell → F2) →ₗ[F2] (Fin r → F2))
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k r (A.comp M) =
      Inverse.RowErasureMatrix.rowAdvice (LinearMap.toMatrix' A) (mapEquiv k ell M) := by
  change LinearMap.toMatrix' (A.comp (M.comp (domainCoordinates k).symm.toLinearMap)) = _
  rw [LinearMap.toMatrix'_comp]
  rfl

private theorem indicator_congr_inline_MatrixCoordinates (P Q : Prop) (dP : Decidable P) (dQ : Decidable Q)
    (h : P ↔ Q) : @ite ℝ P dP 1 0 = @ite ℝ Q dQ 1 0 := by
  cases propext h
  cases Subsingleton.elim dP dQ
  rfl

theorem shortcodeAcceptance_eq (k ell : ℕ)
    (f : (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) → (Fin ell → F2)) :
    SurrogateFibers.shortcodeAcceptance f =
      Inverse.Shortcode.equalityAcceptance (fun M => f ((mapEquiv k ell).symm M)) := by
  unfold SurrogateFibers.shortcodeAcceptance Inverse.Shortcode.equalityAcceptance
  apply Fintype.expect_equiv (mapEquiv k ell).toEquiv
  intro M
  apply Finset.expect_congr rfl
  intro a _
  apply Fintype.expect_equiv (functionalEquiv k).toEquiv
  intro l
  simp only [LinearEquiv.coe_toEquiv, mapEquiv_symm_add_rankOne,
    LinearEquiv.symm_apply_apply]
  exact indicator_congr_inline_MatrixCoordinates _ _ _ _ Iff.rfl

end
end DFVSGames.Decoder.MatrixCoordinates

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

theorem table_expect_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → ℝ) :
    Finset.univ.expect (fun r : X → Y => ∏ x, f x (r x)) =
      ∏ x, Finset.univ.expect (f x) := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.prod_sum,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow]

private theorem exp_half_le_seven_quarters_inline_RowErasureConcentration : Real.exp (1 / 2 : ℝ) ≤ 7 / 4 := by
  have h := Real.exp_bound' (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

private theorem exp_half_indicator_inline_RowErasureConcentration (P : Prop) :
    Real.exp (indicator P / 2) = 1 + (Real.exp (1 / 2 : ℝ) - 1) * indicator P := by
  classical
  by_cases h : P <;> simp [indicator, h]

theorem table_coordinate_exp_le {Y : Type*} [Fintype Y] [Nonempty Y]
    (P : Prop) (target : Y) :
    Finset.univ.expect (fun y => Real.exp (indicator (P ∧ y = target) / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hP : P
  · have hsingle : Finset.univ.expect (fun y : Y => indicator (y = target)) =
        1 / (Fintype.card Y : ℝ) := by
      simp [indicator]
    have heq : Finset.univ.expect
        (fun y => Real.exp (indicator (P ∧ y = target) / 2)) =
        1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) := by
      simp_rw [hP, true_and, exp_half_indicator_inline_RowErasureConcentration]
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, hsingle]
      simp [div_eq_mul_inv]
    rw [heq]
    calc
      1 + (Real.exp (1 / 2 : ℝ) - 1) / (Fintype.card Y : ℝ) ≤
          1 + 3 / (4 * (Fintype.card Y : ℝ)) := by
        have h := div_le_div_of_nonneg_right
          (show Real.exp (1 / 2 : ℝ) - 1 ≤ 3 / 4 by
            linarith [exp_half_le_seven_quarters_inline_RowErasureConcentration]) hcard.le
        simpa only [div_div, add_comm] using add_le_add_left h 1
      _ ≤ Real.exp (3 / (4 * (Fintype.card Y : ℝ))) := by
        simpa only [add_comm] using Real.add_one_le_exp (3 / (4 * (Fintype.card Y : ℝ)))
  · simp only [hP, false_and, indicator_false, zero_div, Real.exp_zero,
      Fintype.expect_const]
    exact Real.one_le_exp (by positivity)

end
end DFVSGames.Inverse.RowErasure

namespace DFVSGames.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

def randomizedMatches {X Y : Type*} (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) : ℝ :=
  ∑ x ∈ s, indicator (B x ∧ replacement x = target x)

private theorem randomizedMatches_eq_masked_sum_inline_RowErasureTail
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    randomizedMatches s B target replacement =
      ∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
  classical
  symm
  calc
    (∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x)) =
        ∑ x ∈ s, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro x _ hx
      simp [indicator, hx]
    _ = randomizedMatches s B target replacement := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [indicator, hx]

private theorem randomizedMatches_exp_product_inline_RowErasureTail
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    Real.exp (randomizedMatches s B target replacement / 2) =
      ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2) := by
  rw [randomizedMatches_eq_masked_sum_inline_RowErasureTail]
  simp only [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]

private theorem table_randomizedMatches_mgf_eq_inline_RowErasureTail
    {X Y : Type*} [Fintype X] [Fintype Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) =
      ∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) := by
  classical
  calc
    _ = Finset.univ.expect (fun replacement : X → Y =>
        ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2)) := by
      apply Finset.expect_congr rfl
      intro replacement _
      exact randomizedMatches_exp_product_inline_RowErasureTail s B target replacement
    _ = _ := table_expect_prod (X := X) (Y := Y)
      (fun x y => Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))

private theorem table_randomizedMatches_product_le_inline_RowErasureTail
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    (∏ x, Finset.univ.expect (fun y : Y =>
      Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  classical
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hpoint : ∀ x : X,
      Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) ≤
      Real.exp (if x ∈ s then c else 0) := by
    intro x
    by_cases hx : x ∈ s
    · simpa only [hx, true_and, ite_true] using table_coordinate_exp_le (B x) (target x)
    · simp [hx, indicator]
  calc
    (∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
        ∏ x, Real.exp (if x ∈ s then c else 0) := by
      apply Finset.prod_le_prod₀
      · intro x _
        exact Finset.expect_nonneg fun _ _ => (Real.exp_pos _).le
      · intro x _
        exact hpoint x
    _ = Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
      rw [← Real.exp_sum]
      congr 1
      simp [c, mul_comm]

theorem table_randomizedMatches_mgf_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  rw [table_randomizedMatches_mgf_eq_inline_RowErasureTail]
  exact table_randomizedMatches_product_le_inline_RowErasureTail s B target

theorem uniformMass_mono {R : Type*} [Fintype R]
    {p q : R → Prop} (h : ∀ r, p r → q r) : uniformMass p ≤ uniformMass q := by
  classical
  apply Finset.expect_le_expect
  intro r _
  by_cases hp : p r
  · simp [indicator, hp, h r hp]
  · simpa [indicator, hp] using indicator_nonneg (q r)

theorem table_randomizedMatches_tail_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) :
    uniformMass (fun replacement : X → Y =>
      α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
      Real.exp (-(α ^ 2 * s.card) / 32) := by
  classical
  let N : ℝ := s.card
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp : ∀ replacement : X → Y,
      indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Real.exp (randomizedMatches s B target replacement / 2) := by
    intro replacement
    by_cases h : α * s.card / 4 ≤ randomizedMatches s B target replacement
    · rw [show indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) = 1
          from by simp [indicator, h], ← Real.exp_add]
      apply Real.one_le_exp
      dsimp [N]
      linarith
    · simp only [indicator, ite_eq_right h]
      positivity
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun replacement _ => hp replacement)
  change uniformMass _ ≤ _ at hm
  rw [← Finset.mul_expect] at hm
  have hmgf := table_randomizedMatches_mgf_le s B target
  have hc : c ≤ 3 * α / 32 := by
    dsimp [c]
    calc
      3 / (4 * (Fintype.card Y : ℝ)) = (3 / 4) * (1 / (Fintype.card Y : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ 3 * α / 32 := by nlinarith [hsmall]
  have hexponent : -(α * N) / 8 + c * N ≤ -(α ^ 2 * N) / 32 := by
    have hcN := mul_le_mul_of_nonneg_right hc hN
    have hsq : α ^ 2 ≤ α := by
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hαone)]
    have hsqN := mul_le_mul_of_nonneg_right hsq hN
    nlinarith
  calc
    uniformMass (fun replacement : X → Y =>
        α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Finset.univ.expect (fun replacement : X → Y =>
            Real.exp (randomizedMatches s B target replacement / 2)) := hm
    _ ≤ Real.exp (-(α * N) / 8) * Real.exp (c * N) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-(α * N) / 8 + c * N) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(α ^ 2 * s.card) / 32) := Real.exp_le_exp.mpr hexponent

theorem SliceFamily.randomizedAgreement_probability_le
    {X Y A S D : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (F : SliceFamily X Y A S D) (B : X → Prop) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) (d : D) :
    uniformMass (fun replacement : X → Y =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d) ≤
      Real.exp (-(α ^ 2 * (F.points d).card) / 32) := by
  apply le_trans (uniformMass_mono ?_) (table_randomizedMatches_tail_le
    (F.points d) B (F.target d) α hα hαone hsmall)
  intro replacement h
  have hcard : (0 : ℝ) < (F.points d).card := Nat.cast_pos.mpr h.1.card_pos
  have hmass := h.2
  rw [SliceFamily.randomizedAgreement, Finset.expect_eq_sum_div_card] at hmass
  have hm := (le_div_iff₀ hcard).mp hmass
  dsimp [randomizedMatches]
  nlinarith

end
end DFVSGames.Inverse.RowErasure

end OAI
