import Mathlib

namespace OAI

/-! The actual fundamental group of an H-space is abelian. The proof uses the
relative unit homotopies, not an assumed pi-2 comparison theorem. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.HSpaceFundamental
open Path.Homotopic
variable {X : Type*} [TopologicalSpace X] [HSpace X]
local notation "e" => (HSpace.e : X)
local notation "m" => (HSpace.hmul : C(X × X,X))

def combine (p q : FundamentalGroup X e) : FundamentalGroup X e :=
  ((Path.Homotopic.prod p q).map m).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm

def combinePath (p q : Path e e) : Path e e :=
  ((p.prod q).map (HSpace.hmul : C(X × X,X)).continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm
lemma combine_mk (p q : Path e e) :
    combine (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q) = Path.Homotopic.Quotient.mk (combinePath p q) := rfl

lemma combine_refl_right (p : Path e e) :
    (combinePath p (Path.refl e)).Homotopic p := by
  refine ⟨{ toFun := fun tx => HSpace.hmulE (tx.1,p tx.2)
            continuous_toFun := by fun_prop
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact HSpace.hmulE.map_zero_left (p t)
  · intro t
    exact HSpace.hmulE.map_one_left (p t)
  · intro t s hs
    rcases hs with hs|hs
    · subst s
      exact ((congrArg (fun x => HSpace.hmulE (t, x)) p.source).trans
        ((HSpace.hmulE.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath p (Path.refl e)).source.symm
    · simp only [Set.mem_singleton_iff] at hs
      subst s
      exact ((congrArg (fun x => HSpace.hmulE (t, x)) p.target).trans
        ((HSpace.hmulE.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath p (Path.refl e)).target.symm

lemma combine_refl_left (p : Path e e) :
    (combinePath (Path.refl e) p).Homotopic p := by
  refine ⟨{ toFun := fun tx => HSpace.eHmul (tx.1,p tx.2)
            continuous_toFun := by fun_prop
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact HSpace.eHmul.map_zero_left (p t)
  · intro t
    exact HSpace.eHmul.map_one_left (p t)
  · intro t s hs
    rcases hs with hs|hs
    · subst s
      exact ((congrArg (fun x => HSpace.eHmul (t, x)) p.source).trans
        ((HSpace.eHmul.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath (Path.refl e) p).source.symm
    · simp only [Set.mem_singleton_iff] at hs
      subst s
      exact ((congrArg (fun x => HSpace.eHmul (t, x)) p.target).trans
        ((HSpace.eHmul.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath (Path.refl e) p).target.symm

lemma combine_one_right (p : FundamentalGroup X e) : combine p 1 = p := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.Quotient.eq.mpr (combine_refl_right p)
lemma combine_one_left (p : FundamentalGroup X e) : combine 1 p = p := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.Quotient.eq.mpr (combine_refl_left p)

lemma combine_interchange (a b c d : FundamentalGroup X e) :
    combine (a * b) (c * d) = combine a c * combine b d := by
  induction a using Path.Homotopic.Quotient.ind with | mk a =>
  induction b using Path.Homotopic.Quotient.ind with | mk b =>
  induction c using Path.Homotopic.Quotient.ind with | mk c =>
  induction d using Path.Homotopic.Quotient.ind with | mk d =>
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simp only [Path.cast_coe,Path.map_coe,Function.comp_apply,
    Path.prod_coe,Path.trans_apply]
  split_ifs <;> rfl

/-- The group multiplication is the original fundamental-group multiplication. -/
@[instance_reducible] def commGroup : CommGroup (FundamentalGroup X e) :=
  EckmannHilton.commGroup
    (show EckmannHilton.IsUnital (@combine X _ _) 1 from
      { left_id := combine_one_left, right_id := combine_one_right }) combine_interchange

lemma combine_eq_mul (p q : FundamentalGroup X e) : combine p q = p * q := by
  have hh := combine_interchange p 1 1 q
  simpa only [mul_one,one_mul,combine_one_left,combine_one_right] using hh

end HyperbolicObstruction.HSpaceFundamental
end

end OAI
