import OAI.Combinatorics.EuclideanRamsey.PathSynchronization

namespace OAI

universe uSemigroup

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter

open Set
namespace EuclideanRamsey

theorem exists_group_corner {S : Type uSemigroup} [Nonempty S] [Semigroup S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (hc : ∀ y : S, Continuous (· * y)) :
    ∃ p : S, p*p=p ∧ ∀ y : S, p*y=y → y*p=y →
      ∃ v : S, p*v=v ∧ v*p=v ∧ v*y=p := by
  let ideals : Set (Set S) := {N | IsClosed N ∧ N.Nonempty ∧ ∀ x y, y∈N → x*y∈N}
  have hmin : ∃ N, Minimal (· ∈ ideals) N := by
    refine zorn_superset _ fun c hcs hchain => ?_
    refine ⟨⋂₀ c, ⟨isClosed_sInter (fun N hN => (hcs hN).1), ?_, ?_⟩,
      fun N hN => Set.sInter_subset_of_mem hN⟩
    · obtain rfl | hcn := c.eq_empty_or_nonempty
      · simp
      convert! @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        _ _ _ hcn.coe_sort ((↑) : c → Set S) ?_ ?_ ?_ ?_
      · exact Set.sInter_eq_iInter
      · exact DirectedOn.directed_val (IsChain.directedOn hchain.symm)
      · exact fun N => (hcs N.prop).2.1
      · exact fun N => (hcs N.prop).1.isCompact
      · exact fun N => (hcs N.prop).1
    · intro x y hy
      exact Set.mem_sInter.mpr fun N hN => (hcs hN).2.2 x y (Set.mem_sInter.mp hy N hN)
  obtain ⟨N,hN⟩ := hmin
  have hprincipal (y : S) (hy : y∈N) : Set.range (·*y) = N := by
    apply hN.eq_of_subset
    · refine ⟨isCompact_range (hc y) |>.isClosed, ⟨y*y,y,rfl⟩, ?_⟩
      rintro a _ ⟨b,rfl⟩
      exact ⟨a*b,mul_assoc a b y⟩
    · rintro _ ⟨a,rfl⟩
      exact hN.prop.2.2 a y hy
  obtain ⟨p,hpN,hp⟩ := exists_idempotent_in_compact_subsemigroup hc N
    hN.prop.2.1 hN.prop.1.isCompact (fun x _ y hy => hN.prop.2.2 x y hy)
  refine ⟨p,hp,?_⟩
  intro y hpy hyp
  have hyN : y∈N := hyp ▸ hN.prop.2.2 y p hpN
  have hpr : p ∈ Set.range (·*y) := hprincipal y hyN ▸ hpN
  obtain ⟨v,hv⟩ := hpr
  change v*y=p at hv
  refine ⟨p*v*p,?_,?_,?_⟩
  · simp only [← mul_assoc,hp]
  · simp only [mul_assoc,hp]
  · calc
      (p*v*p)*y = p*v*(p*y) := mul_assoc _ _ _
      _ = p*(v*y) := by rw [hpy,mul_assoc]
      _ = p := by rw [hv,hp]

def Corner {S : Type uSemigroup} [Semigroup S] (p : S) := {x : S // p*x=x ∧ x*p=x}
namespace Corner
variable {S : Type uSemigroup} [Semigroup S] {p : S}
instance : Mul (Corner p) := ⟨fun x y => ⟨x.val*y.val, by
  constructor
  · rw [← mul_assoc,x.property.1]
  · rw [mul_assoc,y.property.2]⟩⟩
@[simp] lemma val_mul (x y : Corner p) : (x*y).val=x.val*y.val := rfl
instance : Semigroup (Corner p) where
  mul_assoc _x _y _z := Subtype.ext (mul_assoc _ _ _)

@[instance_reducible] def group (hp : p*p=p)
    (hi : ∀ y : S, p*y=y → y*p=y → ∃ v : S,p*v=v ∧ v*p=v ∧ v*y=p) : Group (Corner p) := by
  letI : One (Corner p) := ⟨⟨p,hp,hp⟩⟩
  letI : Inv (Corner p) := ⟨fun y =>
    ⟨(hi y.val y.property.1 y.property.2).choose,
      (hi y.val y.property.1 y.property.2).choose_spec.1,
      (hi y.val y.property.1 y.property.2).choose_spec.2.1⟩⟩
  exact Group.ofLeftAxioms (fun x y z => mul_assoc x y z)
    (fun x => Subtype.ext x.property.1)
    (fun x => Subtype.ext (hi x.val x.property.1 x.property.2).choose_spec.2.2)

end Corner
end EuclideanRamsey

end

end OAI
