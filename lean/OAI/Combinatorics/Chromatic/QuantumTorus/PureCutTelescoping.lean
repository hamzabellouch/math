import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteRefinementImportAll
import OAI.Combinatorics.Chromatic.Walls.AffineCutTelescoping

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {A J:Type*} [Ring A]
def pureCutGauge (f:PowerSeries A) (side:Bool) : PowerSeries A := if side then f else 1
lemma foldr_left_mul (l:List J) (f:J → A) (z:A) :
    l.foldr (fun a x=>f a*x) z=(l.map f).prod*z := by
  induction l with
  | nil=>simp
  | cons a l ih=>simp only [List.foldr_cons,List.map_cons,List.prod_cons,ih,mul_assoc]
omit [Ring A] in
lemma foldr_identity (l:List J) (x:A) : l.foldr (fun _ y=>y) x=x := by
  induction l <;> simp_all

lemma pureCut_local (f:PowerSeries A) (hf:constantCoeff f=1) (u v t:ℝ)
    (hne:u≠0 ∨ v≠0) (x:PowerSeries A) :
    (if u+t*v=0 then orientPowerSeries (!(decide (v<0))) f else 1)*
      (pureCutGauge f (AffineCut.beforeSide u v t)*x)=
      pureCutGauge f (AffineCut.afterSide u v t)*x := by
  by_cases hz:u+t*v=0
  · have hv:v≠0:=by rintro rfl; simp_all
    rw [ite_eq_left hz,(AffineCut.sides_at_zero u v t hz).1,(AffineCut.sides_at_zero u v t hz).2]
    rcases lt_or_gt_of_ne hv with hn|hp
    · simp only [hn,decide_true,Bool.not_true,pureCutGauge,ite_true,
        show ¬0<v by linarith,decide_false,Bool.false_eq_true,ite_false,orientPowerSeries]
      rw [←mul_assoc,PowerSeries.invOfUnit_mul f 1 hf,one_mul]
    · simp [pureCutGauge,orientPowerSeries,hp,show ¬v<0 by linarith]
  · rw [ite_eq_right hz,(AffineCut.sides_eq_of_ne u v t hz).1,
      (AffineCut.sides_eq_of_ne u v t hz).2,one_mul]

lemma pureCut_telescope (f:PowerSeries A) (hf:constantCoeff f=1)
    (u v lo hi:ℝ) (hlohi:lo<hi) (hne:u≠0 ∨ v≠0)
    (hlo:u+lo*v≠0) (hhi:u+hi*v≠0) (T:Finset ℝ)
    (hmem:∀t∈T,lo<t ∧ t<hi)
    (hcut:∀t,lo<t → t<hi → u+t*v=0 → t∈T) :
    ((T.sort (· ≥ ·)).map (fun t=>if u+t*v=0 then
      orientPowerSeries (!(decide (v<0))) f else 1)).prod *
      pureCutGauge f (decide (0<u+lo*v))=pureCutGauge f (decide (0<u+hi*v)) := by
  classical
  have HH:=AffineCut.telescope_sort u v hne (fun _ (x:PowerSeries A)=>x)
    (fun t x=>(if u+t*v=0 then orientPowerSeries (!(decide (v<0))) f else 1)*x)
    (fun side x=>pureCutGauge f side*x) T lo hi hlohi hmem hcut
    (fun t _ x=>pureCut_local f hf u v t hne x) 1
  rw [(AffineCut.sides_eq_of_ne u v lo hlo).2,(AffineCut.sides_eq_of_ne u v hi hhi).1,
    foldr_identity,mul_one,mul_one,foldr_left_mul] at HH
  exact HH
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α β : M →+ ℤ) (hβ : ∀m,β m= -α m)

def fiberReciprocalTerm (m : M) : RatFunc K →+ FiberTorus v Ω β where
  toFun a:=FiberTorus.monomial v Ω β m (reciprocal a)
  map_zero':=by simp
  map_add' a b:=by simp only [map_add,FiberTorus.monomial_add]
def fiberReciprocalAdd : FiberTorus v Ω α →+ FiberTorus v Ω β :=
  Finsupp.liftAddHom (fiberReciprocalTerm v Ω β)
lemma fiberReciprocalAdd_monomial (m : M) (a : RatFunc K) :
    fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α m a)=
      FiberTorus.monomial v Ω β m (reciprocal a) := Finsupp.liftAddHom_apply_single _ _ _
include hβ in
lemma reciprocal_twist (m : M) (a : RatFunc K) :
    reciprocal (FiberTorus.twist v α m a)=FiberTorus.twist v β m (reciprocal a) := by
  have H:=congrArg (fun F : RatFunc K →+* RatFunc K=>F a) (reciprocal_scale (v^(-2*α m)))
  change reciprocal (scale (v^(-2*α m)) a)=scale (v^(-2*β m)) (reciprocal a)
  rw [hβ]
  have he : (v^(-2*α m))⁻¹=v^(-2*(-α m)):=by
    rw [←zpow_neg]
    congr 1
    ring
  simpa only [RingHom.coe_comp,Function.comp_apply,he] using H
include hβ in
lemma fiberReciprocalAdd_mul (f g : FiberTorus v Ω α) :
    fiberReciprocalAdd v Ω α β (f*g)=fiberReciprocalAdd v Ω α β f*fiberReciprocalAdd v Ω α β g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [_root_.add_mul,map_add,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [_root_.mul_add,map_add,hg,hg']
    | single n b=>
      change fiberReciprocalAdd v Ω α β
        (FiberTorus.monomial v Ω α m a*FiberTorus.monomial v Ω α n b)=
        fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α m a)*
          fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α n b)
      rw [FiberTorus.monomial_mul,fiberReciprocalAdd_monomial,
        fiberReciprocalAdd_monomial,fiberReciprocalAdd_monomial,FiberTorus.monomial_mul]
      simp only [map_mul,reciprocal_constant,reciprocal_twist v α β hβ]
def fiberReciprocal : FiberTorus v Ω α →+* FiberTorus v Ω β where
  __:=fiberReciprocalAdd v Ω α β
  map_one':=by
    change fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α 0 1)=_
    rw [fiberReciprocalAdd_monomial,map_one]
    rfl
  map_mul':=fiberReciprocalAdd_mul v Ω α β hβ

lemma fiberReciprocal_oppositeInverse (f : FiberTorus v Ω α) :
    fiberReciprocal v Ω α β hβ (oppositeInverseActionHom v Ω α f)=
      pureActionInvHom v Ω β (fiberReciprocal v Ω α β hβ f) := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change fiberReciprocalAdd v Ω α β (FiberTorus.gaugeAdd v Ω α _
      (FiberTorus.monomial v Ω α m a))=
      FiberTorus.gaugeAdd v Ω β _ (fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α m a))
    rw [FiberTorus.gaugeAdd_monomial,fiberReciprocalAdd_monomial,
      fiberReciprocalAdd_monomial,FiberTorus.gaugeAdd_monomial]
    congr 1
    rw [map_mul,hβ]
    congr 1
    simp only [oppositeInverseRatio,Units.val_inv_eq_inv_val,reciprocalUnit_val,map_inv₀]
    have H:=congrArg (fun F : RatFunc K →+* RatFunc K=>F (↑(pureRatio v (-α m)):RatFunc K))
      reciprocal_involutive
    change reciprocal (reciprocal (↑(pureRatio v (-α m)):RatFunc K))=_ at H
    rw [H]
    rfl

end
end ElementaryPositivity.RationalFiber

end

end OAI
