import OAI.Algebra.Finitistic.Bar.ExplicitSignedDifferential
import OAI.Algebra.Finitistic.Bar.SignedBlockModel

namespace OAI
open CategoryTheory TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
local notation "A" => TrivSqZeroExt D X
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))

include hN in
/-- The explicit faces equal the conjugated ordinary faces; this is a theorem,
not the definition of the independent differential. -/
theorem multibarTwoSided_eq_conjugate (n r : ℕ)
    {z : D ⊗[k] term k A N (n+1)} (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    multibarTwoSidedDifferential k D X N n z =
      (-1 : k)^r • twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n
          (twoSidedSignedProjection k D X N (n+1) r z)) := by
  have h := multibarTwoSided_sign k D X N hN n r (twoSidedSignedProjection_mem hz)
  rw [twoSidedSignedProjection_sq hz] at h
  exact h

include hN in
theorem multibarTwoSided_mem (n r : ℕ)
    {z : D ⊗[k] term k A N (n+1)} (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    multibarTwoSidedDifferential k D X N n z ∈ twoSidedWeight k D X N n r := by
  rw [multibarTwoSided_eq_conjugate k D X N hN n r hz]
  exact (twoSidedWeight k D X N n r).restrictScalars k |>.smul_mem _
    (twoSidedSignedProjection_mem (twoSidedDifferential_mem hN n r
      (twoSidedSignedProjection_mem hz)))

include hN in
theorem multibarTwoSided_shifted (n r : ℕ)
    {z : D ⊗[k] term k A N (n+1)} (hz : z ∈ twoSidedWeight k D X N (n+1) r) :
    (-1 : k)^r • multibarTwoSidedDifferential k D X N n z =
      twoSidedSignedProjection k D X N n r
        (twoSidedDifferential k A D N (fstHom k D X) n
          (twoSidedSignedProjection k D X N (n+1) r z)) := by
  rw [multibarTwoSided_eq_conjugate k D X N hN n r hz, smul_smul, ← mul_pow]
  simp

/-- Restriction of the independently defined literal faces to count r. -/
def multibarCountDifferential (n r : ℕ) :
    twoSidedWeight k D X N (n+1) r →ₗ[D] twoSidedWeight k D X N n r :=
  (multibarTwoSidedDifferential k D X N n).restrict
    (fun _ hz => multibarTwoSided_mem k D X N hN n r hz)

/-- There is no outgoing differential from an all-X word, or below its count.
The ordinary r=0 degree-zero boundary is supplied by the chain shape. -/
theorem multibarCountDifferential_zero_of_lt (n r : ℕ) (hn : n < r) :
    multibarCountDifferential k D X N hN n r = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  have hz := (multibarCountDifferential k D X N hN n r z).property
  exact (show twoSidedWeight k D X N n r ≤ ⊥ from
    le_of_eq (twoSidedWeight_eq_bot_of_lt hn)) hz

end DerivedBar.SquareZero
namespace DerivedBar.Multibar.Indexed
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]
  [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]
variable (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = (0 : N))

/-- Literal multibar faces on the direct sum of actual tensor blocks, with the
[r] sign. Only the degreewise tensor decomposition is used for coordinates. -/
def explicitBlockDifferential (n r : ℕ) :
    (⨁ p : Shape (n+1) r, outerTensor k D X N p) →ₗ[D]
      (⨁ p : Shape n r, outerTensor k D X N p) :=
  (decomposition k D X N n r).symm.toLinearMap.comp
    (((-1 : k)^r • SquareZero.multibarCountDifferential k D X N hN n r).comp
      (decomposition k D X N (n+1) r).toLinearMap)

/-- The previously transported signed differential is identified with independent
literal faces, including the endpoint and square-zero empty-block cases. -/
theorem blockDifferential_eq_explicit (n r : ℕ) :
    blockDifferential k D X N hN n r = explicitBlockDifferential k D X N hN n r := by
  apply LinearMap.ext
  intro z
  apply (decomposition k D X N n r).injective
  apply Subtype.ext
  change ((decomposition k D X N n r)
    ((decomposition k D X N n r).symm
      ((SquareZero.signEquiv k D X N n r).symm
        (((SquareZero.twoSidedWeightComplex k D X N hN r).d (n+1) n).hom
          (SquareZero.signEquiv k D X N (n+1) r (decomposition k D X N (n+1) r z)))))).val =
    ((decomposition k D X N n r) ((decomposition k D X N n r).symm
      (((-1 : k)^r • SquareZero.multibarCountDifferential k D X N hN n r)
        (decomposition k D X N (n+1) r z)))).val
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  simp only [SquareZero.twoSidedWeightComplex, ChainComplex.of_d, ModuleCat.hom_ofHom]
  exact (SquareZero.multibarTwoSided_shifted k D X N hN n r
    (decomposition k D X N (n+1) r z).property).symm

/-- Square-zero follows after identifying the independent differential with the
verified chain differential; no transported differential was used to define it. -/
theorem explicitBlockDifferential_sq (n r : ℕ) :
    (explicitBlockDifferential k D X N hN n r).comp
      (explicitBlockDifferential k D X N hN (n+1) r) = 0 := by
  rw [← blockDifferential_eq_explicit, ← blockDifferential_eq_explicit]
  exact blockDifferential_sq k D X N hN n r

theorem explicitBlockDifferential_zero_of_lt (n r : ℕ) (hn : n < r) :
    explicitBlockDifferential k D X N hN n r = 0 := by
  unfold explicitBlockDifferential
  rw [SquareZero.multibarCountDifferential_zero_of_lt k D X N hN n r hn]
  simp
end DerivedBar.Multibar.Indexed

end

end OAI
