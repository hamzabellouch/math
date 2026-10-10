import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.FactorComparison
import OAI.Analysis.Commutator.SquareZeroMaximal

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem diffuse_halving (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (hd : DiffuseProjection.HasNoMinimalProjections M)
    {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) :
    ∃ v : Link M e e, v.val*v.val=0 ∧ v.initial+v.final=e := by
  classical
  obtain ⟨v,hmax⟩ := exists_maximal_squareZero M he
  refine ⟨v.val,v.property,?_⟩
  have hpq := v.val.initial_mul_final_eq_zero v.property
  have hsum : IsStarProjection (v.val.initial+v.val.final) :=
    v.val.initial_projection.add v.val.final_projection hpq
  have hsume : v.val.initial+v.val.final≤e := by
    apply (hsum.le_iff_mul_eq_right he).mpr
    rw [mul_add,(v.val.initial_projection.le_iff_mul_eq_right he).mp v.val.source_le,
      (v.val.final_projection.le_iff_mul_eq_right he).mp v.val.target_le]
  let r := e-(v.val.initial+v.val.final)
  have hr : IsStarProjection r := hsum.sub_of_mul_eq_left he
    ((hsum.le_iff_mul_eq_left he).mp hsume)
  have hrM : r∈M := M.sub_mem heM (M.add_mem
    (M.mul_mem (M.star_mem' v.val.mem) v.val.mem)
    (M.mul_mem v.val.mem (M.star_mem' v.val.mem)))
  by_contra hn
  have hrn : r≠0 := fun hz => hn (sub_eq_zero.mp hz).symm
  obtain ⟨a,haM,ha,han,har,hle⟩ := hd r hrM hr hrn
  have hrr : IsStarProjection (r-a) := ha.sub_of_mul_eq_left hr
    ((ha.le_iff_mul_eq_left hr).mp hle)
  have hrrn : r-a≠0 := fun hz => har (sub_eq_zero.mp hz).symm
  obtain ⟨w,hwM,hwn,hwt,hwi,hwf⟩ := FactorCorner.exists_linking_partialIsometry M hM
    haM (M.sub_mem hrM haM) ha hrr han hrrn
  let w₀ : Link M a (r-a) := ⟨w,hwM,hwt,hwi,hwf⟩
  have hww : w*w=0 := by
    have har0 : a*(r-a)=0 := by
      rw [mul_sub,(ha.le_iff_mul_eq_left hr).mp hle,ha.isIdempotentElem.eq,sub_self]
    calc
      _=(w*a)*((r-a)*w) := by rw [w₀.mul_source ha,w₀.target_mul hrr]
      _=0 := by rw [mul_assoc,←mul_assoc a,har0,zero_mul,mul_zero]
  have hir : star w*w≤r := hwi.trans hle
  have hfr : w*star w≤r := hwf.trans (sub_le_self r ha.nonneg)
  let wr : Link M r r := ⟨w,hwM,hwt,hir,hfr⟩
  have hie : r≤e-v.val.initial := sub_le_sub_left
    (le_add_of_nonneg_right v.val.final_projection.nonneg) e
  have hfe : r≤e-v.val.final := sub_le_sub_left
    (le_add_of_nonneg_left v.val.initial_projection.nonneg) e
  let w' : Link M (e-v.val.initial) (e-v.val.final) :=
    ⟨w,hwM,hwt,hir.trans hie,hfr.trans hfe⟩
  have hvr : v.val.val*r=0 := by
    change v.val.val*(e-(v.val.initial+v.val.final))=0
    rw [mul_sub,mul_add,v.val.mul_source he,v.val.mul_initial,
      v.val.self_mul_final_eq_zero v.property,add_zero,sub_self]
  have hrv : r*v.val.val=0 := by
    change (e-(v.val.initial+v.val.final))*v.val.val=0
    rw [sub_mul,add_mul,v.val.target_mul he,v.val.initial_mul_self_eq_zero v.property,
      v.val.final_mul,zero_add,sub_self]
  have hvw : v.val.val*w=0 := by
    calc
      _=v.val.val*(r*w) := by rw [wr.target_mul hr]
      _=0 := by rw [←mul_assoc,hvr,zero_mul]
  have hwv : w*v.val.val=0 := by
    calc
      _=(w*r)*v.val.val := by rw [wr.mul_source hr]
      _=0 := by rw [mul_assoc,hrv,mul_zero]
  let u : SquareZeroLink M e := ⟨v.val.extend he he w',by
    change (v.val.val+w)*(v.val.val+w)=0
    rw [add_mul,mul_add,mul_add,v.property,hvw,hwv,hww,zero_add,zero_add]⟩
  have hvu : v≤u := v.val.le_extend he he w'
  have heq : u=v := le_antisymm (hmax hvu) hvu
  have hval := congrArg (fun z : SquareZeroLink M e => z.val.val) heq
  change v.val.val+w=v.val.val at hval
  exact hwn (add_left_cancel (hval.trans (add_zero v.val.val).symm))

end Kadison.PartialIsometryOrder

end

end
end

end OAI
