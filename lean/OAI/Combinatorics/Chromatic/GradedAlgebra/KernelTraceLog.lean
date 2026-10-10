import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.QuantumTorusSignFactors
import OAI.Combinatorics.Chromatic.GradedAlgebra.QuantumTorusAlgebra
import OAI.Combinatorics.Chromatic.Shuffle.QuantumTorusTrace
import OAI.Combinatorics.Chromatic.GradedAlgebra.TraceLogDerivative

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
lemma log_map (φ : A→ₐ[ℚ] B) (F : PowerSeries A) :
    FormalLog.log (PowerSeries.map φ.toRingHom F)=PowerSeries.map φ.toRingHom (FormalLog.log F) := by
  ext n
  simp only [FormalLog.log,coeff_mk,coeff_map,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [←map_one (PowerSeries.map φ.toRingHom),←map_sub,←map_pow,coeff_map]
  exact (map_smul φ _ _).symm
end
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FormalLog
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)

def supportedSubalgebra (V : AddSubmonoid M) : Subalgebra ℚ (Torus v Ω) where
  toSubsemiring:=(supportedSubring v Ω V).toSubsemiring
  algebraMap_mem' a:=by
    intro m hm
    rw [Algebra.algebraMap_eq_smul_one,Torus.scalar_one]
    change (Finsupp.single 0 (a • (1:R))) m=0
    exact Finsupp.single_eq_of_ne (fun he=>hm (he ▸ V.zero_mem))

local instance (support : AddSubmonoid M) : AddCommMonoid (supportedSubalgebra v Ω support) :=
  (inferInstance : Ring (supportedSubalgebra v Ω support)).toAddCommMonoid
local instance (support : AddSubmonoid M) : Module ℚ (supportedSubalgebra v Ω support) :=
  Algebra.toModule (R:=ℚ) (A:=supportedSubalgebra v Ω support)

def kernelSupport (r : M) : AddSubmonoid M := (Ω.flip r).ker.toAddSubmonoid

def rootTrace (r : M) : supportedSubalgebra v Ω (kernelSupport Ω r)→ₗ[ℚ] R where
  toFun f:=(f:Torus v Ω) r
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

lemma rootTrace_cyclic (hΩ : ∀m,Ω m m=0) (r : M)
    (f g : supportedSubalgebra v Ω (kernelSupport Ω r)) :
    rootTrace v Ω r (f*g)=rootTrace v Ω r (g*f) := by
  apply coefficient_trace v Ω hΩ r f.val g.val
  intro m hm
  exact f.property m (by simpa [kernelSupport] using hm)

variable (V : AddSubmonoid M)
def supportLift (F : PowerSeries (Torus v Ω))
    (hF : ∀n,coeff n F∈supportedSubalgebra v Ω V) :
    PowerSeries (supportedSubalgebra v Ω V) :=
  PowerSeries.mk (fun n=>⟨coeff n F,hF n⟩)

lemma supportLift_map (F : PowerSeries (Torus v Ω))
    (hF : ∀n,coeff n F∈supportedSubalgebra v Ω V) :
    PowerSeries.map (supportedSubalgebra v Ω V).val.toRingHom (supportLift v Ω V F hF)=F := by
  ext n
  simp only [coeff_map,supportLift,coeff_mk]
  rfl

lemma supportLift_constant (F : PowerSeries (Torus v Ω))
    (hF : ∀n,coeff n F∈supportedSubalgebra v Ω V) (hf : constantCoeff F=1) :
    constantCoeff (supportLift v Ω V F hF)=1 := by
  apply Subtype.ext
  change coeff 0 F=1
  rw [coeff_zero_eq_constantCoeff,hf]

lemma kernel_trace_log_product (hΩ : ∀m,Ω m m=0) (r : M)
    (F G : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1) (hG : constantCoeff G=1)
    (hsF : ∀n,coeff n F∈supportedSubalgebra v Ω (kernelSupport Ω r))
    (hsG : ∀n,coeff n G∈supportedSubalgebra v Ω (kernelSupport Ω r)) (n : ℕ) :
    coeff n (FormalLog.log (F*G)) r=
      coeff n (FormalLog.log F) r+coeff n (FormalLog.log G) r := by
  let V:=kernelSupport Ω r
  let A:=supportLift v Ω V F hsF
  let B:=supportLift v Ω V G hsG
  let φ:=(supportedSubalgebra v Ω V).val
  have hA : PowerSeries.map φ.toRingHom A=F:=supportLift_map v Ω V F hsF
  have hB : PowerSeries.map φ.toRingHom B=G:=supportLift_map v Ω V G hsG
  have H:=congrArg (coeff n) (trace_log_product
    (R:=supportedSubalgebra v Ω (kernelSupport Ω r)) (K:=R) (rootTrace v Ω r)
    (rootTrace_cyclic v Ω hΩ r) A B (supportLift_constant v Ω V F hsF hF)
    (supportLift_constant v Ω V G hsG hG))
  simp only [map_add,coeff_traceSeries] at H
  have Hmap (D : PowerSeries (supportedSubalgebra v Ω V)) :
      rootTrace v Ω r (coeff n (FormalLog.log D))=
      coeff n (FormalLog.log (PowerSeries.map φ.toRingHom D)) r := by
    rw [log_map,coeff_map]
    rfl
  rw [Hmap,Hmap,Hmap,map_mul,hA,hB] at H
  exact H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.FormalLog
lemma coeff_sub_one_succ {A : Type*} [Ring A] (F : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff (n+1) (F-1)=PowerSeries.coeff (n+1) F := by
  simp only [map_sub,PowerSeries.coeff_one,Nat.succ_ne_zero,ite_false,sub_zero]
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)
local instance kernelTraceLogAddCommGroup : AddCommGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommGroup
local instance kernelTraceLogAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
local instance kernelTraceLogSub : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub

def SupportedOn (V : M→Prop) (f : Torus v Ω) : Prop := ∀m,¬V m→f m=0

omit [Algebra ℚ R] in
lemma SupportedOn.zero (V : M→Prop) : SupportedOn v Ω V 0 := fun _ _=>rfl
omit [Algebra ℚ R] in
lemma SupportedOn.add {V : M→Prop} {f g : Torus v Ω}
    (hf : SupportedOn v Ω V f) (hg : SupportedOn v Ω V g) :
    SupportedOn v Ω V (f+g) := by
  intro m hm
  change f m+g m=0
  rw [hf m hm,hg m hm,add_zero]
lemma SupportedOn.smul {V : M→Prop} {f : Torus v Ω} (hf : SupportedOn v Ω V f) (a : ℚ) :
    SupportedOn v Ω V (a • f) := by
  intro m hm
  change a • f m=0
  rw [hf m hm,smul_zero]
omit [Algebra ℚ R] in
lemma SupportedOn.sum {ι : Type*} (s : Finset ι) (f : ι→Torus v Ω) (V : M→Prop)
    (hf : ∀i∈s,SupportedOn v Ω V (f i)) : SupportedOn v Ω V (∑i∈s,f i) := by
  intro m hm
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun i hi=>hf i hi m hm)
omit [Algebra ℚ R] in
lemma SupportedOn.mul {V : M→Prop} (hV : ∀a b,V a→V b→V (a+b))
    {f g : Torus v Ω} (hf : SupportedOn v Ω V f) (hg : SupportedOn v Ω V g) :
    SupportedOn v Ω V (f*g) := by
  classical
  intro m hm
  change (Torus.multiply v Ω f g) m=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  have hfa : V a := by by_contra hn; exact (Finsupp.mem_support_iff.mp ha) (hf a hn)
  have hgb : V b := by by_contra hn; exact (Finsupp.mem_support_iff.mp hb) (hg b hn)
  apply Finsupp.single_eq_of_ne
  intro he
  exact hm (he ▸ hV a b hfa hgb)

omit [Algebra ℚ R] in
lemma series_supported_mul {V : M→Prop} (hV : ∀a b,V a→V b→V (a+b))
    {F G : PowerSeries (Torus v Ω)}
    (hF : ∀n,SupportedOn v Ω V (coeff n F)) (hG : ∀n,SupportedOn v Ω V (coeff n G)) :
    ∀n,SupportedOn v Ω V (coeff n (F*G)) := by
  intro n
  rw [coeff_mul]
  exact SupportedOn.sum v Ω _ _ V (fun p hp=>(hF p.1).mul v Ω hV (hG p.2))

lemma strict_log_support {V : M→Prop} (hV : ∀a b,V a→V b→V (a+b))
    (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1)
    (hf : ∀n,SupportedOn v Ω V (coeff (n+1) F)) :
    ∀n,SupportedOn v Ω V (coeff n (FormalLog.log F)) := by
  have hu : ∀n,SupportedOn v Ω V (coeff n (F-1)) := by
    intro n
    cases n with
    | zero=>simp only [coeff_zero_eq_constantCoeff,map_sub,hF,constantCoeff_one,sub_self]
            exact SupportedOn.zero v Ω V
    | succ n=>rw [FormalLog.coeff_sub_one_succ]; exact hf n
  have hp : ∀k n,SupportedOn v Ω V (coeff n ((F-1)^(k+1))) := by
    intro k
    induction k with
    | zero=>simpa only [zero_add,pow_one] using hu
    | succ k ih=>simpa only [pow_succ] using series_supported_mul v Ω hV ih hu
  intro n
  simp only [FormalLog.log,coeff_mk]
  exact SupportedOn.sum v Ω _ _ V (fun k hk=>(hp k n).smul v Ω _)

lemma log_positive_zero (h : M→+ℝ) (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1)
    (hf : ∀n m,coeff (n+1) F m≠0→0<h m) (r : M) (hr : h r=0) (n : ℕ) :
    coeff n (FormalLog.log F) r=0 := by
  apply strict_log_support v Ω (V:=fun m=>0<h m) (fun a b ha hb=>by rw [map_add]; linarith)
    F hF (fun n m hm=>not_not.mp (fun hn=>hm (hf n m hn))) n r
  simpa only [hr] using (lt_irrefl (0:ℝ))

lemma log_negative_zero (h : M→+ℝ) (F : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1)
    (hf : ∀n m,coeff (n+1) F m≠0→h m<0) (r : M) (hr : h r=0) (n : ℕ) :
    coeff n (FormalLog.log F) r=0 := by
  apply strict_log_support v Ω (V:=fun m=>h m<0) (fun a b ha hb=>by rw [map_add]; linarith)
    F hF (fun n m hm=>not_not.mp (fun hn=>hm (hf n m hn))) n r
  simpa only [hr] using (lt_irrefl (0:ℝ))
end
end ElementaryPositivity.QuantumTorus

end

end OAI
