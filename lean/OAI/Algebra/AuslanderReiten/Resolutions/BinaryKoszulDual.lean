import OAI.Algebra.AuslanderReiten.Resolutions.BinaryKoszul

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [Field k]

abbrev DualPiece (n : ℕ) := Module.Dual k (Piece k n)

def dualRow (n : ℕ) : (DualPiece k (n + 1) × DualPiece k (n + 1)) →ₗ[k] DualPiece k n :=
  (mulX k n).dualMap.coprod (mulY k n).dualMap

def dualColumn (n : ℕ) : DualPiece k (n + 1) →ₗ[k]
    (DualPiece k n × DualPiece k n) :=
  (mulY k n).dualMap.prod (-(mulX k n).dualMap)

@[simp]
theorem dualRow_apply (n : ℕ) (f g : DualPiece k (n + 1)) (x : Piece k n) :
    dualRow k n (f, g) x = f (mulX k n x) + g (mulY k n x) := rfl

@[simp]
theorem dualColumn_apply (n : ℕ) (f : DualPiece k (n + 1)) :
    dualColumn k n f = (f.comp (mulY k n), -(f.comp (mulX k n))) := rfl

theorem exact_dual {U V W : Type u}
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range g.dualMap = LinearMap.ker f.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, h]

theorem dualRow_dualColumn (n : ℕ) : (dualRow k n).comp (dualColumn k (n + 1)) = 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  change f (mulY k (n + 1) (mulX k n x)) + -f (mulX k (n + 1) (mulY k n x)) = 0
  have h := DFunLike.congr_fun (mul_commute k n) x
  change mulX k (n + 1) (mulY k n x) = mulY k (n + 1) (mulX k n x) at h
  rw [h, add_neg_cancel]

theorem dualRow_surjective (n : ℕ) : Function.Surjective (dualRow k n) := by
  intro f
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective (mulX_injective k n) f
  refine ⟨(g, 0), ?_⟩
  change (mulX k n).dualMap g + (mulY k n).dualMap 0 = f
  simpa using hg

theorem dualColumn_injective (n : ℕ) : Function.Injective (dualColumn k n) := by
  intro f g h
  apply LinearMap.ext
  intro x
  obtain ⟨⟨a, b⟩, rfl⟩ := row_surjective k n x
  have hy := congrArg Prod.fst h
  have hx := congrArg Prod.snd h
  have hya := DFunLike.congr_fun hy b
  have hxa := neg_injective (DFunLike.congr_fun hx a)
  change f (mulY k n b) = g (mulY k n b) at hya
  change f (mulX k n a) = g (mulX k n a) at hxa
  simp only [row_apply, map_add, hxa, hya]

theorem range_dualColumn_eq_ker_dualRow (n : ℕ) :
    LinearMap.range (dualColumn k (n + 1)) = LinearMap.ker (dualRow k n) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (dualRow_dualColumn k n)
  · rintro ⟨f, g⟩ h
    let l : Module.Dual k (Piece k (n + 1) × Piece k (n + 1)) := (-g).coprod f
    have hl : l ∈ LinearMap.ker (column k n).dualMap := by
      apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun h x
      change f (mulX k n x) + g (mulY k n x) = 0 at hx
      change -g (mulY k n x) + f (-(mulX k n x)) = 0
      rw [map_neg, ← neg_add, add_comm]
      exact neg_eq_zero.mpr hx
    rw [← exact_dual k (column k n) (row k (n + 1))
      (range_column_eq_ker_row k n)] at hl
    obtain ⟨t, ht⟩ := hl
    refine ⟨t, Prod.ext ?_ ?_⟩
    · apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun ht (0, x)
      simpa [l, row] using hx
    · apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun ht (x, 0)
      have hx' := congrArg Neg.neg hx
      simpa [l, row] using hx'

theorem dualColumn_zero_surjective : Function.Surjective (dualColumn k 0) := by
  rintro ⟨f, g⟩
  let l : Module.Dual k (Piece k 0 × Piece k 0) := (-g).coprod f
  obtain ⟨t, ht⟩ := LinearMap.dualMap_surjective_of_injective (row_zero_injective k) l
  refine ⟨t, Prod.ext ?_ ?_⟩
  · apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun ht (0, x)
    simpa [l, row] using hx
  · apply LinearMap.ext
    intro x
    have hx := congrArg Neg.neg (DFunLike.congr_fun ht (x, 0))
    simpa [l, row] using hx

noncomputable def dualColumnZeroEquiv : DualPiece k 1 ≃ₗ[k]
    (DualPiece k 0 × DualPiece k 0) :=
  LinearEquiv.ofBijective (dualColumn k 0)
    ⟨dualColumn_injective k 0, dualColumn_zero_surjective k⟩

end ArExplicit.BinaryKoszul

end OAI
