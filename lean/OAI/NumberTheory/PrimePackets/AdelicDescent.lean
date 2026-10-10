import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicPacketEquality

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set MeasureTheory
namespace PrimeDegreePackets.Adelic

lemma adelicRegular_principal {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (a : Kˣ) :
    adelicRegular b (tensorPrincipal K a) =
      rationalProjectiveEmbedding n (ProjGenLinGroup.mk (rowRegularUnits b a)) := by
  have h : rowRegularUnits (b.baseChange RationalAdeles) (tensorPrincipal K a) =
      GeneralLinearGroup.map (algebraMap ℚ RationalAdeles) (rowRegularUnits b a) := by
    apply Units.ext
    exact rowRegular_baseChange b a.val
  apply Prod.ext
  · change ProjGenLinGroup.mk (GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) (tensorPrincipal K a))) = _
    rw [h]
    rfl
  · change ProjGenLinGroup.mk (GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) (tensorPrincipal K a))) = _
    rw [h]
    rfl

lemma adelicRegular_scalar {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (a : RationalAdelesˣ) :
    adelicRegular b (tensorScalar K a) = 1 := by
  have h : rowRegularUnits (b.baseChange RationalAdeles) (tensorScalar K a) =
      GeneralLinearGroup.scalar (Fin n) a := by
    apply Units.ext
    exact (rowRegular (b.baseChange RationalAdeles)).commutes a.val
  apply Prod.ext
  · change ProjGenLinGroup.mk (GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) (tensorScalar K a))) = 1
    rw [h,GeneralLinearGroup.map_scalar,ProjGenLinGroup.mk_scalar]
  · change ProjGenLinGroup.mk (GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) (tensorScalar K a))) = 1
    rw [h,GeneralLinearGroup.map_scalar,ProjGenLinGroup.mk_scalar]

lemma adelicRegular_mem_rational_of_principalScalar {n : ℕ} {K : Type*}
    [Field K] [NumberField K] (b : Basis (Fin n) ℚ K)
    {t : (TensorAdeles K)ˣ} (ht : t ∈ torusPrincipalScalarSubgroup K) :
    adelicRegular b t ∈ rationalProjectiveGroup n := by
  have hle : torusPrincipalScalarSubgroup K ≤ (rationalProjectiveGroup n).comap (adelicRegular b) := by
    apply sup_le
    · rintro _ ⟨a,rfl⟩
      exact ⟨ProjGenLinGroup.mk (rowRegularUnits b a),adelicRegular_principal b a |>.symm⟩
    · rintro _ ⟨a,rfl⟩
      change adelicRegular b (tensorScalar K a) ∈ rationalProjectiveGroup n
      rw [adelicRegular_scalar]
      exact Subgroup.one_mem _
  exact hle ht

 
def adelicIdelePoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (σ : OrderedEmbeddings n K) (g : GL (Fin n) RationalFiniteAdeles)
    (t : (TensorAdeles K)ˣ) : X n :=
  (ambientEquiv hodd hn b).symm (DoubleCoset.mk (rationalProjectiveGroup n)
    (finiteProjectiveIntegral n)
    (adelicRegular b t * (ProjGenLinGroup.mk (realBasisGL hn b σ),ProjGenLinGroup.mk g)))

lemma adelicIdelePoint_mul_principalScalar {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (σ : OrderedEmbeddings n K) (g : GL (Fin n) RationalFiniteAdeles)
    {t : (TensorAdeles K)ˣ} (ht : t ∈ torusPrincipalScalarSubgroup K) (s : (TensorAdeles K)ˣ) :
    adelicIdelePoint hodd hn b σ g (t*s) = adelicIdelePoint hodd hn b σ g s := by
  unfold adelicIdelePoint
  congr 1
  apply DoubleCoset.eq.mpr
  refine ⟨adelicRegular b t⁻¹,adelicRegular_mem_rational_of_principalScalar b
    (Subgroup.inv_mem _ ht),1,Subgroup.one_mem _,?_⟩
  rw [map_mul,mul_one]
  simp only [map_inv,← mul_assoc,inv_mul_cancel,one_mul]

 

def adelicTorusPoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (σ : OrderedEmbeddings n K) (g : GL (Fin n) RationalFiniteAdeles) : TorusQuotient K → X n :=
  Quotient.lift (adelicIdelePoint hodd hn b σ g) (by
    intro t s hts
    have hmem : t⁻¹*s ∈ torusPrincipalScalarSubgroup K := QuotientGroup.leftRel_apply.mp hts
    have he := adelicIdelePoint_mul_principalScalar hodd hn b σ g hmem t
    have hc : (t⁻¹*s)*t = s := by rw [mul_comm t⁻¹ s,mul_assoc,inv_mul_cancel,mul_one]
    rw [hc] at he
    exact he.symm)

instance torusQuotientMeasurable (K : Type*) [Field K] [NumberField K] :
    MeasurableSpace (TorusQuotient K) := borel (TorusQuotient K)
instance torusQuotientBorel (K : Type*) [Field K] [NumberField K] :
    BorelSpace (TorusQuotient K) := ⟨rfl⟩

end PrimeDegreePackets.Adelic

end

end OAI
