import Mathlib.FieldTheory.Differential.Basic

namespace OAI

namespace GrahamSpherical.AlgebraicExtension

open IntermediateField
open scoped Differential

variable {F K : Type*} [Field F] [Field K] [CharZero F]
  [Algebra F K] [Algebra.IsAlgebraic F K] [Differential F]

local instance finiteSimple (x : K) : FiniteDimensional F F⟮x⟯ :=
  IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := F) x)

/-- The value forced by the native derivation on a finite simple subextension. -/
noncomputable def value (x : K) : K :=
  ((Differential.deriv (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯) : F⟮x⟯) : K)

/-- All finite subextensions compute the same derivative of a given element. -/
theorem value_eq (L : IntermediateField F K) [FiniteDimensional F L]
    (x : K) (hx : x ∈ L) :
    value (F := F) x = ((Differential.deriv (⟨x, hx⟩ : L) : L) : K) := by
  have hle : F⟮x⟯ ≤ L := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have h := Differential.algHom_deriv' (inclusion hle) (inclusion_injective hle)
    (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯)
  exact congrArg (fun z : L => (z : K)) h

theorem value_zero : value (F := F) (0 : K) = 0 := by
  rw [value_eq (F⟮(0 : K)⟯) 0 (zero_mem _)]
  change ((Differential.deriv (0 : F⟮(0 : K)⟯) : F⟮(0 : K)⟯) : K) = 0
  simp

theorem value_add (x y : K) :
    value (F := F) (x + y) = value (F := F) x + value (F := F) y := by
  let L : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  have hx : x ∈ L := (show F⟮x⟯ ≤ L from le_sup_left) (mem_adjoin_simple_self F x)
  have hy : y ∈ L := (show F⟮y⟯ ≤ L from le_sup_right) (mem_adjoin_simple_self F y)
  rw [value_eq L (x + y) (L.add_mem hx hy), value_eq L x hx, value_eq L y hy]
  exact congrArg (fun z : L => (z : K))
    (map_add Differential.deriv (⟨x, hx⟩ : L) (⟨y, hy⟩ : L))

theorem value_mul (x y : K) :
    value (F := F) (x * y) = x * value (F := F) y + y * value (F := F) x := by
  let L : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  have hx : x ∈ L := (show F⟮x⟯ ≤ L from le_sup_left) (mem_adjoin_simple_self F x)
  have hy : y ∈ L := (show F⟮y⟯ ≤ L from le_sup_right) (mem_adjoin_simple_self F y)
  rw [value_eq L (x * y) (L.mul_mem hx hy), value_eq L x hx, value_eq L y hy]
  have hm : (⟨x, hx⟩ : L) * (⟨y, hy⟩ : L) = ⟨x * y, L.mul_mem hx hy⟩ := by
    apply Subtype.ext
    exact L.coe_mul _ _
  have hd := Derivation.leibniz Differential.deriv (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)
  rw [hm] at hd
  simpa only [smul_eq_mul, IntermediateField.coe_add, IntermediateField.coe_mul,
    Subtype.coe_mk] using congrArg (fun z : L => (z : K)) hd

/-- Extension to an arbitrary algebraic field extension in characteristic zero. -/
@[instance_reducible]
noncomputable def differentialAlgebraic : Differential K where
  deriv := Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      { toFun := value (F := F), map_zero' := value_zero, map_add' := value_add })
    (by intro x y; exact value_mul x y)

theorem value_algebraMap (x : F) :
    value (F := F) (algebraMap F K x) = algebraMap F K (Differential.deriv x) := by
  let L : IntermediateField F K := F⟮algebraMap F K x⟯
  rw [value_eq L _ (L.algebraMap_mem x)]
  change ((Differential.deriv (algebraMap F L x) : L) : K) = _
  rw [deriv_algebraMap]
  rfl

theorem differentialAlgebraAlgebraic :
    let := differentialAlgebraic (F := F) (K := K)
    DifferentialAlgebra F K := by
  let := differentialAlgebraic (F := F) (K := K)
  exact ⟨value_algebraMap⟩

omit [Differential F] in
/-- Explicit derivation interface, avoiding any preexisting derivative on the target. -/
theorem exists_extension (D : Derivation ℤ F F) :
    ∃ E : Derivation ℤ K K,
      ∀ x : F, E (algebraMap F K x) = algebraMap F K (D x) := by
  let : Differential F := ⟨D⟩
  exact ⟨(differentialAlgebraic (F := F) (K := K)).deriv, value_algebraMap⟩

end GrahamSpherical.AlgebraicExtension

end OAI
