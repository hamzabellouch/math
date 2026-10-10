import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalFiberTorus
import OAI.Combinatorics.Chromatic.Walls.RationalPureCocycle

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
namespace FiberTorus

def gaugeMonomial (c : ℤ → RatFunc K) (m : M) : RatFunc K →+ FiberTorus v Ω α where
  toFun a:=monomial v Ω α m (a*c (α m))
  map_zero':=by simp
  map_add' a b:=by simp only [_root_.add_mul,monomial_add]
def gaugeAdd (c : ℤ → RatFunc K) : FiberTorus v Ω α →+ FiberTorus v Ω α :=
  Finsupp.liftAddHom (gaugeMonomial v Ω α c)
@[simp] lemma gaugeAdd_monomial (c : ℤ → RatFunc K) (m : M) (a : RatFunc K) :
    gaugeAdd v Ω α c (monomial v Ω α m a)=monomial v Ω α m (a*c (α m)) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma gaugeAdd_mul (c : ℤ → RatFunc K) (hc : ∀t u,c (t+u)=c t*scale (v^(-2*t)) (c u))
    (f g : FiberTorus v Ω α) :
    gaugeAdd v Ω α c (f*g)=gaugeAdd v Ω α c f*gaugeAdd v Ω α c g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [add_mul,map_add,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [mul_add,map_add,hg,hg']
    | single n b=>
      change gaugeAdd v Ω α c (monomial v Ω α m a*monomial v Ω α n b)=
        gaugeAdd v Ω α c (monomial v Ω α m a)*gaugeAdd v Ω α c (monomial v Ω α n b)
      rw [monomial_mul,gaugeAdd_monomial,gaugeAdd_monomial,gaugeAdd_monomial,monomial_mul]
      simp only [map_add,hc,map_mul]
      congr 1
      change a*twist v α m b*RatFunc.C (↑(v^(Ω m n)):K)*
        (c (α m)*twist v α m (c (α n)))=
        (a*c (α m))*(twist v α m b*twist v α m (c (α n)))*RatFunc.C (↑(v^(Ω m n)):K)
      ring
lemma gaugeAdd_one (c : ℤ → RatFunc K) (hc : c 0=1) : gaugeAdd v Ω α c 1=1 := by
  change gaugeAdd v Ω α c (monomial v Ω α 0 1)=monomial v Ω α 0 1
  rw [gaugeAdd_monomial,map_zero,hc,_root_.mul_one]
def gauge (c : ℤ → RatFunc K) (hc0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scale (v^(-2*t)) (c u)) : FiberTorus v Ω α →+* FiberTorus v Ω α where
  __:=gaugeAdd v Ω α c
  map_one':=gaugeAdd_one v Ω α c hc0
  map_mul':=gaugeAdd_mul v Ω α c hc
@[simp] lemma gauge_monomial (c : ℤ → RatFunc K) (hc0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scale (v^(-2*t)) (c u)) (m : M) (a : RatFunc K) :
    gauge v Ω α c hc0 hc (monomial v Ω α m a)=monomial v Ω α m (a*c (α m)) :=
  gaugeAdd_monomial v Ω α c m a
lemma gauge_comp (c d : ℤ → RatFunc K) (f : FiberTorus v Ω α) :
    gaugeAdd v Ω α c (gaugeAdd v Ω α d f)=gaugeAdd v Ω α (fun t=>d t*c t) f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change gaugeAdd v Ω α c (gaugeAdd v Ω α d (monomial v Ω α m a))=
      gaugeAdd v Ω α (fun t=>d t*c t) (monomial v Ω α m a)
    simp only [gaugeAdd_monomial,_root_.mul_assoc]
lemma gaugeAdd_trivial (f : FiberTorus v Ω α) : gaugeAdd v Ω α (fun _=>1) f=f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change gaugeAdd v Ω α (fun _=>1) (monomial v Ω α m a)=monomial v Ω α m a
    rw [gaugeAdd_monomial,_root_.mul_one]
end FiberTorus

lemma pureRatio_val_add (t u : ℤ) : (pureRatio v (t+u):RatFunc K)=
    (pureRatio v t:RatFunc K)*scale (v^(-2*t)) (pureRatio v u:RatFunc K) := by
  rw [pureRatio_add,Units.val_mul,scaleAction_val]
  rfl
lemma pureRatio_inv_val_add (t u : ℤ) : (↑((pureRatio v (t+u))⁻¹):RatFunc K)=
    (↑((pureRatio v t)⁻¹):RatFunc K)*scale (v^(-2*t)) (↑((pureRatio v u)⁻¹):RatFunc K) := by
  simp only [Units.val_inv_eq_inv_val,pureRatio_val_add,map_inv₀,mul_inv_rev]
  exact mul_comm _ _
def pureActionHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(pureRatio v t:RatFunc K)) (by simp) (pureRatio_val_add v)
def pureActionInvHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(↑((pureRatio v t)⁻¹):RatFunc K)) (by simp) (pureRatio_inv_val_add v)
lemma pureAction_cancel (f : FiberTorus v Ω α) :
    pureActionHom v Ω α (pureActionInvHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa using FiberTorus.gaugeAdd_trivial v Ω α f
lemma pureActionInv_cancel (f : FiberTorus v Ω α) :
    pureActionInvHom v Ω α (pureActionHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa using FiberTorus.gaugeAdd_trivial v Ω α f
def pureAction : FiberTorus v Ω α ≃+* FiberTorus v Ω α :=
  RingEquiv.ofRingHom (pureActionHom v Ω α) (pureActionInvHom v Ω α)
    (RingHom.ext (pureAction_cancel v Ω α)) (RingHom.ext (pureActionInv_cancel v Ω α))
@[simp] lemma pureAction_monomial (m : M) (a : RatFunc K) :
    pureAction v Ω α (FiberTorus.monomial v Ω α m a)=
      FiberTorus.monomial v Ω α m (a*(pureRatio v (α m):RatFunc K)) :=
  FiberTorus.gaugeAdd_monomial v Ω α (fun t=>(pureRatio v t:RatFunc K)) m a
@[simp] lemma pureAction_coefficient (a : RatFunc K) :
    pureAction v Ω α (FiberTorus.coefficient v Ω α a)=FiberTorus.coefficient v Ω α a := by
  simp [FiberTorus.coefficient]

def completedPureAction : PowerSeries (FiberTorus v Ω α) ≃+* PowerSeries (FiberTorus v Ω α) :=
  RingEquiv.ofRingHom (PowerSeries.map (pureAction v Ω α).toRingHom)
    (PowerSeries.map (pureAction v Ω α).symm.toRingHom)
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])
end
end ElementaryPositivity.RationalFiber

end

end OAI
