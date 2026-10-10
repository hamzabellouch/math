import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.Trace
import OAI.Analysis.FactorGeneration.MatrixUnits
import OAI.Analysis.FactorGeneration.ProjectionComparison
import OAI.Analysis.FactorGeneration.SpectralApproximation

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfactor in
theorem exists_matrixUnits_for_partition {p : AlgebraProjection M}
    (Q : CornerPartition p) (hn : 0 < Q.size)
    (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
    ∃ E : Fin Q.size → Fin Q.size → M.toStarSubalgebra,
      (∀ i, E i i=(Q.piece i).val) ∧
      (∀ i j, star (E i j)=E j i) ∧
      (∀ i j k l, E i j*E k l=if j=k then E i l else 0) ∧
      (∑ i, E i i)=p.val := by
  classical
  let o : Fin Q.size := ⟨0,hn⟩
  have hv : ∀ i, ∃ v : M.toStarSubalgebra,
      star v*v=(Q.piece o).val ∧ v*star v=(Q.piece i).val := fun i =>
    exists_partialIsometry_of_trace_eq τ hfactor (Q.piece o) (Q.piece i) (ht o i)
  choose v hvi hvf using hv
  let V (i : Fin Q.size) : PartialIsometry M := ⟨Q.piece o,v i,hvi i⟩
  have htarget (i : Fin Q.size) : (V i).target=Q.piece i := Subtype.ext (hvf i)
  have hcross (i j : Fin Q.size) (hij : i≠j) : star (v i)*v j=0 := by
    exact (V i).adjoint.mul_eq_zero (V j) (by
      change (V i).target.val*(V j).target.val=0
      rw [htarget,htarget]
      exact Q.orthogonal i j hij)
  let E (i j : Fin Q.size) := v i*star (v j)
  refine ⟨E,hvf,?_,?_,?_⟩
  · intro i j
    simp only [E,star_mul,star_star]
  · intro i j k l
    by_cases hjk : j=k
    · subst k
      rw [ite_eq_left rfl]
      change (v i*star (v j))*(v j*star (v l))=v i*star (v l)
      calc _ = (v i*(star (v j)*v j))*star (v l) := by simp only [mul_assoc]
           _ = v i*star (v l) := by
             rw [hvi,show v i*(Q.piece o).val=v i from (V i).mul_support]
    · rw [ite_eq_right hjk]
      change (v i*star (v j))*(v k*star (v l))=0
      calc _ = (v i*(star (v j)*v k))*star (v l) := by simp only [mul_assoc]
           _ = 0 := by rw [hcross j k hjk,mul_zero,zero_mul]
  · simpa only [E,hvf] using Q.total

end Tracial

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace MatrixUnitSystem
variable (E : Generator.MatrixUnitSystem ι M.toStarSubalgebra)

def concreteHom : Matrix ι ι ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp E.hom

def concreteAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) := E.concreteHom.range

theorem concreteAlgebra_le : E.concreteAlgebra ≤ M.toStarSubalgebra := by
  rintro x ⟨a,rfl⟩
  exact (E.hom a).property

theorem mem_concreteAlgebra (x : M.toStarSubalgebra) :
    x.val ∈ E.concreteAlgebra ↔ x ∈ E.algebra := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,congrArg Subtype.val ha⟩

instance concrete_finiteDimensional : FiniteDimensional ℂ E.concreteAlgebra := by
  change FiniteDimensional ℂ E.concreteHom.toAlgHom.range
  exact FiniteDimensional.of_surjective E.concreteHom.toAlgHom.rangeRestrict.toLinearMap
    E.concreteHom.toAlgHom.rangeRestrict_surjective

def wotLinearMap : Matrix ι ι ℂ →ₗ[ℂ] (H →WOT[ℂ] H) :=
  (ContinuousLinearMap.WOTofCLM.toLinearMap).comp E.concreteHom.toAlgHom.toLinearMap

theorem concreteAlgebra_wotClosed : WOTClosed E.concreteAlgebra := by
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ E.concreteAlgebra} =
      (E.wotLinearMap.range : Set (H →WOT[ℂ] H)) := by
    ext T
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a, congrArg ContinuousLinearMapWOT.ofCLM ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,congrArg ContinuousLinearMapWOT.toCLM ha⟩
  unfold WOTClosed
  rw [heq]
  exact E.wotLinearMap.range.closed_of_finiteDimensional

theorem concreteHom_injective (o : ι) (ho : E.entry o o ≠ 0) :
    Function.Injective E.concreteHom :=
  Subtype.val_injective.comp (E.hom_injective o ho)

end MatrixUnitSystem

namespace Tracial
theorem exists_matrixAlgebra_for_unit_partition (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (Q : CornerPartition (identityProjection M)) (hn : 0 < Q.size)
    (ht : ∀ i j, τ.trace (Q.piece i).val=τ.trace (Q.piece j).val) :
    ∃ E : Generator.MatrixUnitSystem (Fin Q.size) M.toStarSubalgebra,
      (∀ i, E.entry i i=(Q.piece i).val) ∧
      Function.Injective E.hom ∧
      E.concreteAlgebra ≤ M.toStarSubalgebra ∧ WOTClosed E.concreteAlgebra := by
  obtain ⟨e,hd,hs,hm,hu⟩ := exists_matrixUnits_for_partition τ hfactor Q hn ht
  let E : Generator.MatrixUnitSystem (Fin Q.size) M.toStarSubalgebra := ⟨e,hs,hm,hu⟩
  have : Nontrivial M.toStarSubalgebra := by
    apply nontrivial_of_ne (0 : M.toStarSubalgebra) 1
    intro h
    have ht := congrArg τ.trace h
    have hz : τ.trace 0=0 := by simp [TracialRepresentation.trace]
    rw [hz,τ.trace_one] at ht
    exact zero_ne_one ht
  have : Nonempty (Fin Q.size) := ⟨⟨0,hn⟩⟩
  exact ⟨E,hd,E.injective,E.concreteAlgebra_le,E.concreteAlgebra_wotClosed⟩

end Tracial
end

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

def relativeStar : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {x | ∃ a : E.commutant, a.val.val=x}
  zero_mem' := ⟨0,rfl⟩
  one_mem' := ⟨1,rfl⟩
  add_mem' := by rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,rfl⟩
  mul_mem' := by rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a*b,rfl⟩
  algebraMap_mem' z := ⟨algebraMap ℂ E.commutant z,rfl⟩
  star_mem' := by rintro x ⟨a,rfl⟩; exact ⟨star a,rfl⟩

theorem relativeStar_mem (x : H →L[ℂ] H) :
    x ∈ E.relativeStar ↔ x ∈ M ∧ ∀ i j, (E.entry i j).val*x=x*(E.entry i j).val := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨a.val.property,fun i j => congrArg Subtype.val (a.property i j).eq⟩
  · rintro ⟨hx,hc⟩
    exact ⟨⟨⟨x,hx⟩,fun i j => Subtype.ext (hc i j)⟩,rfl⟩

theorem relativeStar_bicommutant :
    Set.centralizer (Set.centralizer (E.relativeStar : Set (H →L[ℂ] H))) =
      (E.relativeStar : Set (H →L[ℂ] H)) := by
  apply Set.Subset.antisymm
  · intro a ha
    apply (E.relativeStar_mem a).mpr
    constructor
    · rw [← SetLike.mem_coe,← M.centralizer_centralizer]
      exact fun b hb => ha b (fun c hc => hb c ((E.relativeStar_mem c).mp hc).1)
    · intro i j
      exact ha (E.entry i j).val
        (fun b hb => (((E.relativeStar_mem b).mp hb).2 i j).symm)
  · intro a ha b hb
    exact (hb a ha).symm

def relativeVonNeumann : VonNeumannAlgebra H where
  toStarSubalgebra := E.relativeStar
  centralizer_centralizer' := E.relativeStar_bicommutant

theorem relativeVonNeumann_le : E.relativeVonNeumann ≤ M := by
  intro x hx
  exact ((E.relativeStar_mem x).mp hx).1

def relativeEquiv : E.commutant ≃⋆ₐ[ℂ] E.relativeVonNeumann.toStarSubalgebra where
  toFun a := ⟨a.val.val,⟨a,rfl⟩⟩
  invFun a := ⟨⟨a.val,((E.relativeStar_mem a.val).mp a.property).1⟩,
    fun i j => Subtype.ext (((E.relativeStar_mem a.val).mp a.property).2 i j)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem relative_scalar_center (o : ι)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : E.relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,a*c=c*a) :
    ∃ z : ℂ,c=z • (1 : E.relativeVonNeumann.toStarSubalgebra) := by
  obtain ⟨z,hz⟩ := E.commutant_scalar_center o hfactor (E.relativeEquiv.symm c) (by
    intro a
    apply E.relativeEquiv.injective
    change E.relativeEquiv (a*E.relativeEquiv.symm c)=
      E.relativeEquiv (E.relativeEquiv.symm c*a)
    rw [map_mul,map_mul,E.relativeEquiv.apply_symm_apply]
    exact hc (E.relativeEquiv a))
  refine ⟨z,?_⟩
  have h := congrArg E.relativeEquiv hz
  simpa only [StarAlgEquiv.apply_symm_apply,map_smul,map_one] using h

theorem relative_diffuse (o : ι)
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : E.relativeVonNeumann.toStarSubalgebra) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : E.relativeVonNeumann.toStarSubalgebra,
      IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := E.commutant_diffuse o hdiff
    (E.relativeEquiv.symm p) (hp.map E.relativeEquiv.symm) (by
      intro h
      apply hp0
      simpa using congrArg E.relativeEquiv h)
  refine ⟨E.relativeEquiv q,?_,?_,?_,?_,?_⟩
  · exact hq.map E.relativeEquiv.toStarAlgHom
  · intro h
    apply hq0
    exact E.relativeEquiv.injective (h.trans (map_zero E.relativeEquiv).symm)
  · intro h
    apply hqp
    exact E.relativeEquiv.injective (h.trans (E.relativeEquiv.apply_symm_apply p).symm)
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hpq
  · simpa only [map_mul,StarAlgEquiv.apply_symm_apply] using congrArg E.relativeEquiv hqp'

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/
variable {ι A B : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

omit [StarModule ℂ A] [StarModule ℂ B] in
theorem commute_mapped_of_amplify (E : MatrixUnitSystem ι A) (o : ι)
    (f : A →⋆ₐ[ℂ] B) (y : B)
    (hE : ∀ i j,Commute (f (E.entry i j)) y)
    (hamp : ∀ a : A,Commute (f (E.amplify o a)) y) (x : A) : Commute (f x) y := by
  rw [← E.reconstruct o x,map_sum]
  apply Commute.sum_left
  intro i hi
  rw [map_sum]
  apply Commute.sum_left
  intro j hj
  rw [map_mul,map_mul]
  exact ((hE i o).mul_left (hamp _)).mul_left (hE o j)

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
variable (E : MatrixUnitSystem ι N.toStarSubalgebra) (hNM : N ≤ M)

theorem relative_inclusion :
    E.relativeVonNeumann ≤ (E.map (coordinateInclusion hNM)).relativeVonNeumann := by
  intro x hx
  have h := (E.relativeStar_mem x).mp hx
  apply ((E.map (coordinateInclusion hNM)).relativeStar_mem x).mpr
  exact ⟨hNM h.1,h.2⟩

theorem relative_irreducible (o : ι)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
        ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (c : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra)
    (hc : ∀ a : E.relativeVonNeumann.toStarSubalgebra,
      coordinateInclusion (E.relative_inclusion hNM) a*c=
        c*coordinateInclusion (E.relative_inclusion hNM) a) :
    ∃ z : ℂ,c=z • (1 : (E.map (coordinateInclusion hNM)).relativeVonNeumann.toStarSubalgebra) := by
  let F := E.map (coordinateInclusion hNM)
  let cM := coordinateInclusion F.relativeVonNeumann_le c
  have hentries : ∀ i j,Commute (coordinateInclusion hNM (E.entry i j)) cM := by
    intro i j
    apply Subtype.ext
    exact ((F.relativeStar_mem c.val).mp c.property).2 i j
  have hamp (a : N.toStarSubalgebra) : Commute
      (coordinateInclusion hNM (E.amplify o a)) cM := by
    let b : E.relativeVonNeumann.toStarSubalgebra :=
      E.relativeEquiv ⟨E.amplify o a,E.amplify_mem o a⟩
    apply Subtype.ext
    exact congrArg (fun t : F.relativeVonNeumann.toStarSubalgebra => t.val) (hc b)
  obtain ⟨z,hz⟩ := hirr cM (fun x =>
    E.commute_mapped_of_amplify o (coordinateInclusion hNM) cM hentries hamp x)
  exact ⟨z,Subtype.ext (congrArg (fun t : M.toStarSubalgebra => t.val) hz)⟩

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators
namespace Bell
variable {n : ℕ} [NeZero n]

theorem char_sum (t : ZMod n) :
    (∑ i : ZMod n, ZMod.stdAddChar (t*i)) = if t=0 then (n : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n h)

theorem char_star (t : ZMod n) : star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  simp only [ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle t)).symm

def projection (s f : ZMod n) : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ :=
  fun a b => if a.2=a.1+s ∧ b.2=b.1+s then
    (n : ℂ)⁻¹ * ZMod.stdAddChar (f*(a.1-b.1)) else 0

theorem projection_star (s f : ZMod n) : star (projection s f) = projection s f := by
  ext a b
  change star (projection s f b a)=projection s f a b
  simp only [projection, apply_ite star, star_mul, char_star, star_zero]
  rw [show -(f*(b.1-a.1))=f*(a.1-b.1) by ring]
  simp [and_comm, mul_comm]

theorem projection_mul (s f t g : ZMod n) :
    projection s f * projection t g = if s=t ∧ f=g then projection s f else 0 := by
  ext a b
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, projection]
  have hterm (i j : ZMod n) :
      (if a.2=a.1+s ∧ j=i+s then (n : ℂ)⁻¹*ZMod.stdAddChar (f*(a.1-i)) else 0) *
      (if j=i+t ∧ b.2=b.1+t then (n : ℂ)⁻¹*ZMod.stdAddChar (g*(i-b.1)) else 0) =
      if a.2=a.1+s ∧ b.2=b.1+t ∧ s=t then
        if j=i+s then (n : ℂ)⁻¹^2 *
          ZMod.stdAddChar (f*a.1-g*b.1) * ZMod.stdAddChar ((g-f)*i) else 0
      else 0 := by
    by_cases ha : a.2=a.1+s
    · by_cases hb : b.2=b.1+t
      · by_cases hs : s=t
        · subst t
          by_cases hj : j=i+s
          · simp only [ha,hb,hj,and_self,ite_true]
            calc
              _ = (n : ℂ)⁻¹^2 * (ZMod.stdAddChar (f*(a.1-i)) *
                    ZMod.stdAddChar (g*(i-b.1))) := by ring
              _ = _ := by
                rw [← AddChar.map_add_eq_mul,
                  show f*(a.1-i)+g*(i-b.1)=(f*a.1-g*b.1)+(g-f)*i by ring,
                  AddChar.map_add_eq_mul]
                ring
          · simp [ha,hb,hj]
        · by_cases hj : j=i+s
          · simp [ha,hb,hs,hj]
          · simp [ha,hb,hs,hj]
      · simp [hb]
    · simp [ha]
  simp_rw [hterm]
  by_cases hs : s=t
  · subst t
    by_cases ha : a.2=a.1+s ∧ b.2=b.1+s
    · simp only [ha.1,ha.2,and_self,ite_true,Finset.sum_ite_eq',Finset.mem_univ]
      rw [← Finset.mul_sum, char_sum]
      by_cases hf : f=g
      · subst g
        simp only [sub_self,ite_true,Matrix.ite_apply,Matrix.zero_apply, and_self, projection, ha, ite_true]
        rw [show f*a.1-f*b.1=f*(a.1-b.1) by ring]
        field_simp
      · simp [sub_eq_zero,Ne.symm hf,hf]
    · simp [ha,Matrix.ite_apply,projection]
  · simp [hs]

theorem projection_total : (∑ s : ZMod n, ∑ f : ZMod n, projection s f) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.one_apply]
  have hf (s : ZMod n) : (∑ f : ZMod n, projection s f a b) =
      if a.2=a.1+s ∧ b.2=b.1+s ∧ a.1=b.1 then 1 else 0 := by
    simp only [projection]
    by_cases h : a.2=a.1+s ∧ b.2=b.1+s
    · simp only [h.1,h.2,and_self,true_and,ite_true]
      rw [← Finset.mul_sum]
      simp_rw [mul_comm _ (a.1-b.1)]
      rw [char_sum]
      by_cases hab : a.1=b.1
      · simp [hab]
      · simp [hab,sub_eq_zero]
    · simp [h,show ¬(a.2=a.1+s ∧ b.2=b.1+s ∧ a.1=b.1) by tauto]
  simp_rw [hf]
  by_cases hab : a.1=b.1
  · have hs (s : ZMod n) : a.2=a.1+s ↔ s=a.2-a.1 := by
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [h]; abel
    simp_rw [hs]
    simp only [hab, and_true]
    simp_rw [ite_and]
    simp [Prod.ext_iff,hab,eq_comm]
  · simp [hab,show a≠b by exact fun h => hab (congrArg Prod.fst h)]

/-- The matrix unit in the first tensor factor, with identity on the second. -/
def leftEntry (i j : ZMod n) : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ :=
  fun a b => if a.1=i ∧ b.1=j ∧ a.2=b.2 then 1 else 0

theorem mul_leftEntry (X : Matrix (ZMod n × ZMod n) (ZMod n × ZMod n) ℂ)
    (i j : ZMod n) (a b : ZMod n × ZMod n) :
    (X * leftEntry i j) a b = if b.1=j then X a (i,b.2) else 0 := by
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,leftEntry,mul_ite,mul_one,mul_zero]
  by_cases h : b.1=j
  · simp [h,ite_and]
  · simp [h]

theorem projection_sandwich (s f i j : ZMod n) :
    projection s f * leftEntry i j * projection s f =
      if i=j then (n : ℂ)⁻¹ • projection s f else 0 := by
  apply Matrix.ext
  intro a b
  have hr : (if i=j then (n : ℂ)⁻¹ • projection s f else 0) a b =
      if i=j then (n : ℂ)⁻¹ * projection s f a b else 0 := by
    split_ifs <;> rfl
  rw [hr]
  rw [Matrix.mul_apply]
  simp only [mul_leftEntry,Fintype.sum_prod_type,ite_mul,zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hterm (k : ZMod n) : projection s f a (i,k)*projection s f (j,k) b =
      if a.2=a.1+s ∧ b.2=b.1+s ∧ i=j then
        if k=i+s then (n : ℂ)⁻¹^2 * ZMod.stdAddChar (f*(a.1-b.1)) else 0
      else 0 := by
    by_cases ha : a.2=a.1+s
    · by_cases hb : b.2=b.1+s
      · by_cases hij : i=j
        · subst j
          by_cases hk : k=i+s
          · simp only [projection,ha,hb,hk,and_self,ite_true]
            calc
              _ = (n : ℂ)⁻¹^2 * (ZMod.stdAddChar (f*(a.1-i)) *
                    ZMod.stdAddChar (f*(i-b.1))) := by ring
              _ = _ := by rw [← AddChar.map_add_eq_mul,
                show f*(a.1-i)+f*(i-b.1)=f*(a.1-b.1) by ring]
          · simp [projection,ha,hb,hk]
        · by_cases hk : k=i+s
          · simp [projection,ha,hb,hij,hk]
          · simp [projection,ha,hb,hij,hk]
      · simp [projection,hb]
    · simp [projection,ha]
  simp_rw [hterm]
  by_cases hij : i=j <;> by_cases h : a.2=a.1+s ∧ b.2=b.1+s <;>
    simp [hij,h,projection,pow_two,mul_assoc]

end Bell

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators
namespace MatrixUnitSystem

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra) (τ : TracialRepresentation M)

theorem trace_diagonal_eq (i j : ι) : τ.trace (E.entry i i)=τ.trace (E.entry j j) := by
  have h := τ.trace_mul_comm (E.entry i j) (E.entry j i)
  simpa only [E.mul_entry,ite_true] using h

theorem trace_off_diagonal (i j : ι) (hij : i ≠ j) : τ.trace (E.entry i j)=0 := by
  have h := τ.trace_mul_comm (E.entry i i) (E.entry i j)
  simpa [E.mul_entry,hij,Ne.symm hij,TracialRepresentation.trace] using h

theorem trace_diagonal (o : ι) :
    τ.trace (E.entry o o)=(Fintype.card ι : ℂ)⁻¹ := by
  have h : (Fintype.card ι : ℂ)*τ.trace (E.entry o o)=1 := by
    calc _ = ∑ i, τ.trace (E.entry i i) := by
               simp only [E.trace_diagonal_eq τ _ o,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
         _ = τ.trace (∑ i,E.entry i i) := by
               let t : M.toStarSubalgebra →+ ℂ :=
                 { toFun := τ.trace, map_zero' := by simp [TracialRepresentation.trace],
                   map_add' := τ.trace_add }
               exact (map_sum t _ _).symm
         _ = 1 := by rw [E.total,τ.trace_one]
  exact eq_inv_of_mul_eq_one_right h

theorem trace_hom (_ : ι) (a : Matrix ι ι ℂ) :
    τ.trace (E.hom a)=(Fintype.card ι : ℂ)⁻¹*Matrix.trace a := by
  have hsum (b : ι → M.toStarSubalgebra) : τ.trace (∑ i,b i)=∑ i,τ.trace (b i) := by
    let t : M.toStarSubalgebra →+ ℂ :=
      { toFun := τ.trace, map_zero' := by simp [TracialRepresentation.trace],
                   map_add' := τ.trace_add }
    exact map_sum t _ _
  rw [E.hom_apply,hsum]
  simp only [hsum,τ.trace_smul]
  have hentry (i j : ι) : τ.trace (E.entry i j)=
      if i=j then (Fintype.card ι : ℂ)⁻¹ else 0 := by
    split
    · next h => subst j; exact E.trace_diagonal τ i
    · next h => exact E.trace_off_diagonal τ i j h
  simp only [hentry,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Matrix.trace,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end

open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n : ℕ} [NeZero n]
variable (E F : MatrixUnitSystem (ZMod n) M.toStarSubalgebra)
variable (hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l))

theorem product_hom_leftEntry (i j : ZMod n) :
    (E.product F hc).hom (Bell.leftEntry i j) = E.entry i j := by
  simp only [hom_apply,Fintype.sum_prod_type,Bell.leftEntry,ite_smul,one_smul,zero_smul]
  simp only [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← E.product_sum_left F hc i j]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_eq_single j]
  · simp
  · intro l hl hlj
    simp [hlj]
  · simp

def bellPiece (s f : ZMod n) : AlgebraProjection M :=
  ⟨(E.product F hc).hom (Bell.projection s f),by
    constructor
    · show (E.product F hc).hom (Bell.projection s f) *
        (E.product F hc).hom (Bell.projection s f) = _
      rw [← map_mul,Bell.projection_mul,ite_eq_left ⟨rfl,rfl⟩]
    · show star ((E.product F hc).hom (Bell.projection s f)) = _
      rw [← map_star,Bell.projection_star]⟩

theorem bellPiece_orthogonal (a b : ZMod n × ZMod n) (h : a≠b) :
    (E.bellPiece F hc a.1 a.2).val * (E.bellPiece F hc b.1 b.2).val = 0 := by
  change (E.product F hc).hom _ * (E.product F hc).hom _ = 0
  rw [← map_mul,Bell.projection_mul,ite_eq_right (fun he => h (Prod.ext he.1 he.2)),map_zero]

theorem bellPiece_total :
    (∑ a : ZMod n × ZMod n,(E.bellPiece F hc a.1 a.2).val) = 1 := by
  change (∑ a : ZMod n × ZMod n,(E.product F hc).hom (Bell.projection a.1 a.2))=1
  rw [← map_sum,Fintype.sum_prod_type,Bell.projection_total,map_one]

def bellPartition : CornerPartition (identityProjection M) where
  size := Fintype.card (ZMod n × ZMod n)
  piece i := let a := (Fintype.equivFin (ZMod n × ZMod n)).symm i
    E.bellPiece F hc a.1 a.2
  orthogonal _ _ h := E.bellPiece_orthogonal F hc _ _
    (fun he => h ((Fintype.equivFin (ZMod n × ZMod n)).symm.injective he))
  total := ((Fintype.equivFin (ZMod n × ZMod n)).symm.sum_comp
    (fun a => (E.bellPiece F hc a.1 a.2).val)).trans (E.bellPiece_total F hc)

theorem bellPiece_sandwich_entry (s f i j : ZMod n) :
    (E.bellPiece F hc s f).val * E.entry i j * (E.bellPiece F hc s f).val =
      if i=j then (n : ℂ)⁻¹ • (E.bellPiece F hc s f).val else 0 := by
  rw [← E.product_hom_leftEntry F hc i j]
  change ((E.product F hc).hom _ * (E.product F hc).hom _) * (E.product F hc).hom _ = _
  rw [← map_mul,← map_mul,Bell.projection_sandwich]
  split <;> simp [bellPiece,map_smul]

theorem bellPartition_pinch_entry (i j : ZMod n) :
    (E.bellPartition F hc).pinch (E.entry i j) =
      if i=j then (n : ℂ)⁻¹ • (1 : M.toStarSubalgebra) else 0 := by
  have hpiece (a : Fin (E.bellPartition F hc).size) :
      ((E.bellPartition F hc).piece a).val * E.entry i j *
        ((E.bellPartition F hc).piece a).val =
      if i=j then (n : ℂ)⁻¹ • ((E.bellPartition F hc).piece a).val else 0 :=
    E.bellPiece_sandwich_entry F hc _ _ i j
  unfold CornerPartition.pinch
  simp_rw [hpiece]
  split
  · simp only [← Finset.smul_sum,(E.bellPartition F hc).total]
    rfl
  · simp

theorem bellPartition_pinch_algebra (τ : TracialRepresentation M)
    (x : M.toStarSubalgebra) (hx : x ∈ E.algebra) :
    (E.bellPartition F hc).pinch x = τ.trace x • (1 : M.toStarSubalgebra) := by
  obtain ⟨a,rfl⟩ := hx
  change (E.bellPartition F hc).pinch (E.hom a)=τ.trace (E.hom a) • 1
  rw [E.trace_hom τ 0]
  have hsum (y : ZMod n → M.toStarSubalgebra) :
      (E.bellPartition F hc).pinch (∑ i,y i) =
        ∑ i,(E.bellPartition F hc).pinch (y i) := by
    simp only [CornerPartition.pinch,Finset.mul_sum,Finset.sum_mul]
    exact Finset.sum_comm
  simp only [hom_apply,hsum,CornerPartition.pinch_smul,E.bellPartition_pinch_entry F hc,
    smul_ite,smul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,smul_smul]
  rw [← Finset.sum_smul,Matrix.trace,Finset.mul_sum]
  congr 1
  simp [ZMod.card,mul_comm]

end MatrixUnitSystem

end Generator

end

end OAI
