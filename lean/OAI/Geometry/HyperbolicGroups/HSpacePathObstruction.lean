import Mathlib
import OAI.Geometry.HyperbolicGroups.HSpaceFundamental

namespace OAI

/-! The cellular obstruction and its exact change under edge corrections. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.HSpacePathObstruction
open Path.Homotopic
variable {Y : Type*} [TopologicalSpace Y] [HSpace Y]
local notation "e" => (HSpace.e : Y)
local notation "Q" => Path.Homotopic.Quotient.mk
local notation "m" => (HSpace.hmul : C(Y × Y,Y))

def pairToUnit {a b : Y} (p : Path a e) (q : Path b e) : Path (m (a,b)) e :=
  ((p.prod q).map (HSpace.hmul : C(Y × Y,Y)).continuous).cast rfl HSpace.hmul_e_e.symm

lemma pairToUnit_trans {a b : Y} (p : Path a e) (q : Path b e)
    (u v : Path e e) :
    pairToUnit (p.trans u) (q.trans v) =
      (pairToUnit p q).trans (HSpaceFundamental.combinePath u v) := by
  ext t
  simp only [pairToUnit,HSpaceFundamental.combinePath,Path.cast_coe,Path.map_coe,
    Function.comp_apply,Path.prod_coe,Path.trans_apply]
  split_ifs <;> rfl

def loopClass (p : Path e e) : FundamentalGroup Y e := Q p

lemma loopClass_combine (u v : Path e e) :
    loopClass (HSpaceFundamental.combinePath u v) = loopClass u * loopClass v :=
  (HSpaceFundamental.combine_mk u v).symm.trans
    (HSpaceFundamental.combine_eq_mul (loopClass u) (loopClass v))

/-- Difference of two paths ending at the same basepoint. -/
def difference {a : Y} (p q : Path a e) : FundamentalGroup Y e := Q (p.symm.trans q)

lemma difference_eq_one_iff {a : Y} (p q : Path a e) :
    difference p q = 1 ↔ p.Homotopic q := by
  constructor
  · intro h
    have hh := congrArg (fun z => (Q p).trans z) h
    change (Q p).trans ((Q p).symm.trans (Q q)) = (Q p).trans (.refl e) at hh
    rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_refl] at hh
    exact Path.Homotopic.symm (Path.Homotopic.Quotient.eq.mp hh)
  · intro h
    change (Q p).symm.trans (Q q) = _
    rw [←Path.Homotopic.Quotient.eq.mpr h,Path.Homotopic.Quotient.symm_trans]
    rfl

lemma difference_trans {a : Y} (p q : Path a e) (u v : Path e e) :
    difference (p.trans u) (q.trans v) =
      loopClass v * difference p q * (loopClass u)⁻¹ := by
  change Q ((p.trans u).symm.trans (q.trans v)) =
    (Q u).symm.trans ((Q (p.symm.trans q)).trans (Q v))
  rw [Path.trans_symm]
  simp only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

variable {a b c d : Y}
/-- Obstruction for a face joining the products of its opposite pairs. -/
def obstruction (F : Path (m (a,b)) (m (c,d)))
    (pa : Path a e) (pb : Path b e) (pc : Path c e) (pd : Path d e) :
    FundamentalGroup Y e := difference (pairToUnit pa pb) (F.trans (pairToUnit pc pd))

lemma correction (F : Path (m (a,b)) (m (c,d)))
    (pa : Path a e) (pb : Path b e) (pc : Path c e) (pd : Path d e)
    (ua ub uc ud : Path e e) :
    obstruction F (pa.trans ua) (pb.trans ub) (pc.trans uc) (pd.trans ud) =
      (loopClass uc * loopClass ud) * obstruction F pa pb pc pd *
        (loopClass ua * loopClass ub)⁻¹ := by
  unfold obstruction
  rw [pairToUnit_trans,pairToUnit_trans]
  have ha : Q (F.trans ((pairToUnit pc pd).trans (HSpaceFundamental.combinePath uc ud))) =
      Q ((F.trans (pairToUnit pc pd)).trans (HSpaceFundamental.combinePath uc ud)) := by
    simp only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.trans_assoc]
  change (Q _).symm.trans (Q _) = _
  rw [ha]
  change difference ((pairToUnit pa pb).trans (HSpaceFundamental.combinePath ua ub))
      ((F.trans (pairToUnit pc pd)).trans (HSpaceFundamental.combinePath uc ud)) = _
  rw [difference_trans,loopClass_combine,loopClass_combine]

/-- The face extends once the corrected obstruction is killed, with the actual
prescribed boundary paths retained. -/
lemma obstruction_vanishes_iff (F : Path (m (a,b)) (m (c,d)))
    (pa : Path a e) (pb : Path b e) (pc : Path c e) (pd : Path d e) :
    obstruction F pa pb pc pd = 1 ↔
      ((pairToUnit pa pb).trans (Path.refl e)).Homotopic (F.trans (pairToUnit pc pd)) := by
  rw [obstruction,difference_eq_one_iff]
  constructor
  · intro h
    exact (Path.Homotopic.trans_refl _).trans h
  · intro h
    exact (Path.Homotopic.trans_refl _).symm.trans h

end HyperbolicObstruction.HSpacePathObstruction
end

end OAI
