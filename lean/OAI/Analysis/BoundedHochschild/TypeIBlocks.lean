import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.FactorPrimitive
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers
import OAI.Analysis.BoundedHochschild.CommutativePrimitives
import OAI.Analysis.BoundedHochschild.AtomicPrimitives
import OAI.Analysis.BoundedHochschild.TypeILocalMatrices

namespace OAI

/-!
# Homogeneous central blocks in finite type-I algebras

Cutting a full packing by a central projection gives matrix units with an abelian diagonal.
Every nonzero central cut containing an abelian projection therefore contains such a block.
-/

noncomputable section

open scoped ComplexOrder
namespace HochschildTypeILocal
open BoundedHochschild HochschildComparison HochschildMinimalFactor FinitePathMain
  HochschildTypeII HochschildCorners HochschildAtomic HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma centralCornerMap_star (z : M) (hz : CentralProjection z) (a : M) :
    centralCornerMap z hz.1 hz.2 (star a)=star (centralCornerMap z hz.1 hz.2 a) := by
  apply Subtype.ext
  change z*star a=star (z*a)
  rw [star_mul,hz.1.isSelfAdjoint.star_eq]
  exact (hz.2 (star a)).eq

lemma abelian_centralCorner (z : M) (hz : CentralProjection z) {a : M} (ha : AbelianProjection a) :
    AbelianProjection (centralCornerMap z hz.1 hz.2 a) := by
  have hza := hz.1.mul ha.1 (hz.2 a)
  have hle : z*a≤a := (hza.le_iff_mul_eq_left ha.1).mpr (by rw [mul_assoc,ha.1.isIdempotentElem.eq])
  have hab := abelian_of_le ha hza hle
  refine ⟨⟨Subtype.ext hza.isIdempotentElem.eq,Subtype.ext hza.isSelfAdjoint.star_eq⟩,fun b c => ?_⟩
  exact Subtype.ext ((hab.2 (b:M) (c:M)).eq)

namespace Packing
variable {p : M} {n : ℕ} (P : HochschildMinimalFactor.Packing p n)

def cutMatrixSystem (z : M) (hz : CentralProjection z) (hfull : z*P.total=z) :
    MatrixSystem (Corner z hz.1) n where
  entry i j := centralCornerMap z hz.1 hz.2 ((P.v i:M)*star (P.v j:M))
  star_entry i j := by rw [← centralCornerMap_star z hz]; simp only [star_mul,star_star]
  entry_mul i j k l := by
    rw [← centralCornerMap_mul]
    by_cases h : j=k
    · subst k
      rw [ite_eq_left rfl]
      have he : (P.v i:M)*(P.v j).initial=(P.v i:M) := by
        rw [(P.initial j).trans (P.initial i).symm,(P.v i).mul_initial]
      apply congrArg
      calc
        ((P.v i:M)*star (P.v j:M))*((P.v j:M)*star (P.v l:M)) =
            ((P.v i:M)*(P.v j).initial)*star (P.v l:M) := by simp only [PartialIso.initial,mul_assoc]
        _ = _ := by rw [he]
    · rw [ite_eq_right h]
      have hcross := PartialIso.star_mul_eq_zero_of_final_orthogonal (P.orthogonal j k h)
      have hh : ((P.v i:M)*star (P.v j:M))*((P.v k:M)*star (P.v l:M))=0 := by
        calc
          _ = (P.v i:M)*(star (P.v j:M)*(P.v k:M))*star (P.v l:M) := by simp only [mul_assoc]
          _ = 0 := by rw [hcross,mul_zero,zero_mul]
      rw [hh,map_zero]
  sum_diagonal := by
    rw [← map_sum]
    apply Subtype.ext
    exact hfull

lemma cutMatrix_diagonal_abelian (z : M) (hz : CentralProjection z) (hfull : z*P.total=z)
    (hp : AbelianProjection p) (i : Fin n) :
    AbelianProjection ((HochschildTypeILocal.Packing.cutMatrixSystem P z hz hfull).entry i i) := by
  apply abelian_centralCorner z hz
  apply abelian_final (P.v i)
  simpa only [P.initial i] using hp

lemma total_le_central {c : M} (hc : CentralProjection c) (hpc : p≤c) : P.total≤c := by
  by_cases hn : n=0
  · subst n; simpa [HochschildMinimalFactor.Packing.total] using hc.1.nonneg
  have hp : IsStarProjection p := (P.initial ⟨0,Nat.pos_of_ne_zero hn⟩) ▸ (P.v ⟨0,Nat.pos_of_ne_zero hn⟩).initial_proj
  have hz : (1-c)*p=0 := by rw [sub_mul,one_mul,(hp.le_iff_mul_eq_right hc.1).mp hpc,sub_self]
  have hi (i : Fin n) : (1-c)*(P.v i).initial=0 := by rw [P.initial,hz]
  have hf (i : Fin n) : (1-c)*(P.v i).final=0 :=
    central_initial_zero_final (1-c) (fun a => (Commute.one_left a).sub_left (hc.2 a)) (P.v i) (hi i)
  have hs : (1-c)*P.total=0 := by
    simp only [HochschildMinimalFactor.Packing.total,Finset.mul_sum,hf,Finset.sum_const_zero]
  rw [sub_mul,one_mul,sub_eq_zero] at hs
  exact (P.total_proj.le_iff_mul_eq_right hc.1).mpr hs.symm
end Packing

structure HomogeneousBlock (z : M) : Prop where
  central : CentralProjection z
  nonzero : z≠0
  matrix : ∃ (n : ℕ) (E : MatrixSystem (Corner z central.1) n) (i : Fin n),
    AbelianProjection (E.entry i i)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
include e in

theorem exists_homogeneous_block_below
    (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {c p : M} (hc : CentralProjection c) (hp : AbelianProjection p) (hpc : p≤c) (hp0 : p≠0) :
    ∃ z : M, HomogeneousBlock z ∧ z≤c := by
  obtain ⟨n,P,z,hn,hz,hzp,hfull⟩ := exists_local_full_packing e τ hτ htr hfaith hp hp0
  refine ⟨z,⟨hz,?_,n,HochschildTypeILocal.Packing.cutMatrixSystem P z hz hfull,⟨0,hn⟩,
    HochschildTypeILocal.Packing.cutMatrix_diagonal_abelian P z hz hfull hp _⟩,?_⟩
  · intro hz0; exact hzp (by rw [hz0,zero_mul])
  · have hzt : z≤P.total := (hz.1.le_iff_mul_eq_left P.total_proj).mpr hfull
    exact hzt.trans (HochschildTypeILocal.Packing.total_le_central P hc hpc)

end HochschildTypeILocal

end

end OAI
