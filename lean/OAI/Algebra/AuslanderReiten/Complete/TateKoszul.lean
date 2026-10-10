import OAI.Algebra.AuslanderReiten.Resolutions.BinaryKoszulDual

namespace OAI

noncomputable section

namespace ArExplicit.TateKoszul

universe u
variable {k : Type u} [Field k]
variable (H : ℤ → Type u) [∀ a, AddCommGroup (H a)] [∀ a, Module k (H a)]

def degreeEquiv {a b : ℤ} (h : a = b) : H a ≃ₗ[k] H b := by
  subst b
  exact LinearEquiv.refl k (H a)

variable {H}

structure Model (x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)) where
  positive : ∀ n : ℕ, H (3 * (n : ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n
  negative : ∀ n : ℕ, H (-1 - 3 * (n : ℤ)) ≃ₗ[k] BinaryKoszul.DualPiece k n
  outside : ∀ a : ℤ, (∀ n : ℕ, a ≠ 3 * (n : ℤ)) →
    (∀ n : ℕ, a ≠ -1 - 3 * (n : ℤ)) → Subsingleton (H a)
  positive_x : ∀ (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = 3 * ((n + 1 : ℕ) : ℤ) by omega)).trans
      (positive (n + 1))) (x a v) =
    BinaryKoszul.mulX k n (((degreeEquiv H ha).trans (positive n)) v)
  positive_y : ∀ (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = 3 * ((n + 1 : ℕ) : ℤ) by omega)).trans
      (positive (n + 1))) (y a v) =
    BinaryKoszul.mulY k n (((degreeEquiv H ha).trans (positive n)) v)
  negative_x : ∀ (a : ℤ) (n : ℕ) (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = -1 - 3 * (n : ℤ) by omega)).trans
      (negative n)) (x a v) =
    (BinaryKoszul.mulX k n).dualMap
      (((degreeEquiv H ha).trans (negative (n + 1))) v)
  negative_y : ∀ (a : ℤ) (n : ℕ) (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a),
    ((degreeEquiv H (show a + 3 = -1 - 3 * (n : ℤ) by omega)).trans
      (negative n)) (y a v) =
    (BinaryKoszul.mulY k n).dualMap
      (((degreeEquiv H ha).trans (negative (n + 1))) v)

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)} (M : Model x y)

def positiveAt (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ)) :
    H a ≃ₗ[k] BinaryKoszul.Piece k n :=
  (degreeEquiv H ha).trans (M.positive n)

def negativeAt (a : ℤ) (n : ℕ) (ha : a = -1 - 3 * (n : ℤ)) :
    H a ≃ₗ[k] BinaryKoszul.DualPiece k n :=
  (degreeEquiv H ha).trans (M.negative n)

def row (a : ℤ) : (H a × H a) →ₗ[k] H (a + 3) := (x a).coprod (y a)

def column (a : ℤ) : H a →ₗ[k] (H (a + 3) × H (a + 3)) :=
  (y a).prod (-(x a))

@[simp] theorem row_apply (a : ℤ) (v w : H a) : row (x := x) (y := y) a (v, w) =
    x a v + y a w := rfl

@[simp] theorem column_apply (a : ℤ) (v : H a) : column (x := x) (y := y) a v =
    (y a v, -(x a v)) := rfl

private theorem positive_row (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ))
    (v : H a × H a) :
    positiveAt M (a + 3) (n + 1) (by omega) (row (x := x) (y := y) a v) =
    BinaryKoszul.row k n
      ((positiveAt M a n ha).prodCongr (positiveAt M a n ha) v) := by
  rcases v with ⟨v, w⟩
  change positiveAt M (a + 3) (n + 1) _ (x a v + y a w) = _
  rw [map_add]
  exact congrArg₂ (· + ·) (M.positive_x a n ha v) (M.positive_y a n ha w)

private theorem positive_column (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ))
    (v : H a) :
    ((positiveAt M (a + 3) (n + 1) (by omega)).prodCongr
      (positiveAt M (a + 3) (n + 1) (by omega))) (column (x := x) (y := y) a v) =
    BinaryKoszul.column k n (positiveAt M a n ha v) := by
  apply Prod.ext
  · exact M.positive_y a n ha v
  · change positiveAt M (a + 3) (n + 1) _ (-(x a v)) = _
    rw [map_neg]
    exact congrArg Neg.neg (M.positive_x a n ha v)

private theorem negative_row (a : ℤ) (n : ℕ)
    (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a × H a) :
    negativeAt M (a + 3) n (by omega) (row (x := x) (y := y) a v) =
    BinaryKoszul.dualRow k n
      ((negativeAt M a (n + 1) ha).prodCongr (negativeAt M a (n + 1) ha) v) := by
  rcases v with ⟨v, w⟩
  change negativeAt M (a + 3) n _ (x a v + y a w) = _
  rw [map_add]
  exact congrArg₂ (· + ·) (M.negative_x a n ha v) (M.negative_y a n ha w)

private theorem negative_column (a : ℤ) (n : ℕ)
    (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a) :
    ((negativeAt M (a + 3) n (by omega)).prodCongr
      (negativeAt M (a + 3) n (by omega))) (column (x := x) (y := y) a v) =
    BinaryKoszul.dualColumn k n (negativeAt M a (n + 1) ha v) := by
  apply Prod.ext
  · exact M.negative_y a n ha v
  · change negativeAt M (a + 3) n _ (-(x a v)) = _
    rw [map_neg]
    exact congrArg Neg.neg (M.negative_x a n ha v)

section Transport

variable {U V W U' V' W' : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W] [AddCommGroup U'] [Module k U']
variable [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

private theorem surjective_of_chart (f : U →ₗ[k] V) (f' : U' →ₗ[k] V')
    (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V')
    (h : ∀ u, b (f u) = f' (a u)) (hf : Function.Surjective f') :
    Function.Surjective f := by
  intro v
  obtain ⟨u, hu⟩ := hf (b v)
  refine ⟨a.symm u, b.injective ?_⟩
  rw [h, a.apply_symm_apply, hu]

private theorem injective_of_chart (f : U →ₗ[k] V) (f' : U' →ₗ[k] V')
    (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V')
    (h : ∀ u, b (f u) = f' (a u)) (hf : Function.Injective f') :
    Function.Injective f := by
  intro u v huv
  apply a.injective
  apply hf
  rw [← h, ← h, huv]

private theorem exact_of_charts (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (f' : U' →ₗ[k] V') (g' : V' →ₗ[k] W')
    (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V') (c : W ≃ₗ[k] W')
    (hf : ∀ u, b (f u) = f' (a u)) (hg : ∀ v, c (g v) = g' (b v))
    (he : LinearMap.range f' = LinearMap.ker g') :
    LinearMap.range f = LinearMap.ker g := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    change g (f u) = 0
    apply c.injective
    rw [hg, hf, map_zero]
    have hu : f' (a u) ∈ LinearMap.range f' := ⟨a u, rfl⟩
    rw [he] at hu
    exact hu
  · intro hv
    have hv' : b v ∈ LinearMap.ker g' := by
      change g' (b v) = 0
      rw [← hg, show g v = 0 from hv, map_zero]
    rw [← he] at hv'
    obtain ⟨u, hu⟩ := hv'
    refine ⟨a.symm u, b.injective ?_⟩
    rw [hf, a.apply_symm_apply, hu]

end Transport

include M

theorem row_surjective (a : ℤ) (ha : a ≠ -3) :
    Function.Surjective (row (x := x) (y := y) a) := by
  by_cases hp : ∃ n : ℕ, a + 3 = 3 * (n : ℤ)
  · obtain ⟨n, hn⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      exact surjective_of_chart _ (BinaryKoszul.row k n)
        ((positiveAt M a n (by omega)).prodCongr (positiveAt M a n (by omega)))
        (positiveAt M (a + 3) (n + 1) (by omega))
        (positive_row M a n (by omega)) (BinaryKoszul.row_surjective k n)
  · by_cases hn : ∃ n : ℕ, a + 3 = -1 - 3 * (n : ℤ)
    · obtain ⟨n, hn⟩ := hn
      exact surjective_of_chart _ (BinaryKoszul.dualRow k n)
        ((negativeAt M a (n + 1) (by omega)).prodCongr
          (negativeAt M a (n + 1) (by omega)))
        (negativeAt M (a + 3) n hn) (negative_row M a n (by omega))
        (BinaryKoszul.dualRow_surjective k n)
    · let : Subsingleton (H (a + 3)) := M.outside _
        (fun n h => hp ⟨n, h⟩) (fun n h => hn ⟨n, h⟩)
      intro v
      exact ⟨0, Subsingleton.elim _ _⟩

theorem column_injective (a : ℤ) (ha : a ≠ -1) :
    Function.Injective (column (x := x) (y := y) a) := by
  by_cases hp : ∃ n : ℕ, a = 3 * (n : ℤ)
  · obtain ⟨n, hn⟩ := hp
    exact injective_of_chart _ (BinaryKoszul.column k n)
      (positiveAt M a n hn)
      ((positiveAt M (a + 3) (n + 1) (by omega)).prodCongr
        (positiveAt M (a + 3) (n + 1) (by omega)))
      (positive_column M a n hn) (BinaryKoszul.column_injective k n)
  · by_cases hn : ∃ n : ℕ, a = -1 - 3 * (n : ℤ)
    · obtain ⟨n, hn⟩ := hn
      cases n with
      | zero => omega
      | succ n =>
        exact injective_of_chart _ (BinaryKoszul.dualColumn k n)
          (negativeAt M a (n + 1) (by omega))
          ((negativeAt M (a + 3) n (by omega)).prodCongr
            (negativeAt M (a + 3) n (by omega)))
          (negative_column M a n (by omega)) (BinaryKoszul.dualColumn_injective k n)
    · let : Subsingleton (H a) := M.outside _
        (fun n h => hp ⟨n, h⟩) (fun n h => hn ⟨n, h⟩)
      exact fun _ _ _ => Subsingleton.elim _ _

theorem range_column_eq_ker_row (a : ℤ) :
    LinearMap.range (column (x := x) (y := y) a) =
      LinearMap.ker (row (x := x) (y := y) (a + 3)) := by
  by_cases hp : ∃ n : ℕ, a + 3 = 3 * (n : ℤ)
  · obtain ⟨n, hn⟩ := hp
    cases n with
    | zero =>
      have hs : a = -3 := by omega
      let : Subsingleton (H a) := M.outside _
        (fun n h => by omega) (fun n h => by omega)
      have hi : Function.Injective (row (x := x) (y := y) (a + 3)) :=
        injective_of_chart _ (BinaryKoszul.row k 0)
          ((positiveAt M (a + 3) 0 hn).prodCongr (positiveAt M (a + 3) 0 hn))
          (positiveAt M (a + 3 + 3) 1 (by omega))
          (positive_row M (a + 3) 0 hn) (BinaryKoszul.row_zero_injective k)
      ext v
      constructor
      · rintro ⟨u, rfl⟩
        rw [Subsingleton.elim u 0, map_zero]
        exact Submodule.zero_mem _
      · intro hv
        have hv0 : v = 0 := hi (by simpa using hv)
        exact ⟨0, (map_zero _).trans hv0.symm⟩
    | succ n =>
      exact exact_of_charts _ _ (BinaryKoszul.column k n) (BinaryKoszul.row k (n + 1))
        (positiveAt M a n (by omega))
        ((positiveAt M (a + 3) (n + 1) (by omega)).prodCongr
          (positiveAt M (a + 3) (n + 1) (by omega)))
        (positiveAt M (a + 3 + 3) (n + 2) (by omega))
        (positive_column M a n (by omega)) (positive_row M (a + 3) (n + 1) (by omega))
        (BinaryKoszul.range_column_eq_ker_row k n)
  · by_cases hn : ∃ n : ℕ, a + 3 = -1 - 3 * (n : ℤ)
    · obtain ⟨n, hn⟩ := hn
      cases n with
      | zero =>
        have hs : a = -4 := by omega
        let : Subsingleton (H (a + 3 + 3)) := M.outside _
          (fun n h => by omega) (fun n h => by omega)
        have hu : Function.Surjective (column (x := x) (y := y) a) :=
          surjective_of_chart _ (BinaryKoszul.dualColumn k 0)
            (negativeAt M a 1 (by omega))
            ((negativeAt M (a + 3) 0 hn).prodCongr (negativeAt M (a + 3) 0 hn))
            (negative_column M a 0 (by omega)) (BinaryKoszul.dualColumn_zero_surjective k)
        ext v
        constructor
        · intro _
          exact Subsingleton.elim _ _
        · intro _
          exact hu v
      | succ n =>
        exact exact_of_charts _ _ (BinaryKoszul.dualColumn k (n + 1))
          (BinaryKoszul.dualRow k n)
          (negativeAt M a (n + 2) (by omega))
          ((negativeAt M (a + 3) (n + 1) (by omega)).prodCongr
            (negativeAt M (a + 3) (n + 1) (by omega)))
          (negativeAt M (a + 3 + 3) n (by omega))
          (negative_column M a (n + 1) (by omega)) (negative_row M (a + 3) n (by omega))
          (BinaryKoszul.range_dualColumn_eq_ker_dualRow k n)
    · let : Subsingleton (H (a + 3)) := M.outside _
        (fun n h => hp ⟨n, h⟩) (fun n h => hn ⟨n, h⟩)
      ext v
      rw [Subsingleton.elim v 0]
      simp

end ArExplicit.TateKoszul

end

end OAI
