import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationIncomingProbes

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd : ∀r≠0,∃m,Ω r m≠0)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedIncoming_nonpure (r:M) (hr:e r≠0)
    (hp:e (simpleRoot C pc)∉Submodule.span ℝ {e r})
    (ho:¬OnPositiveRay r (simpleRoot C pc))
    (hn:¬OnPositiveRay (mutationIncomingLabel Ω (simpleRoot C pc) r)
      (simpleRoot (mutatedRoots Ω C pc) pc))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (hA:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      0<realMutationCovector e S (simpleRoot C pc) a (e m))
    (hB:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)<0) (d:ℕ) :
    coeff d (FormalLog.log (chartZero LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (incomingCovector Ω (mutationIncomingLabel Ω (simpleRoot C pc) r))
      (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).val)
      (mutationIncomingLabel Ω (simpleRoot C pc) r)=
    coeff d (FormalLog.log (literalIncomingRay Ω (simpleIncomingList (mutatedRoots Ω C pc))
      (mutationIncomingLabel Ω (simpleRoot C pc) r)))
      (mutationIncomingLabel Ω (simpleRoot C pc) r) := by
  obtain ⟨pos,x,y,HX,HY,sx,sy,hs,hlabel,hxr,hyr,Ho,Hn,Hreg⟩:=
    mutation_incoming_probes Ω C coord hcoord pc e he S hS hcomp
      ((mutationSize Ω C pc+1)*d) d r hr hp
  have H:=mutatedIncoming_probe Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg hnd
    pos d d le_rfl r HA HB HX HY
    (fun n _ m hm=>hA _ (Nat.succ_pos n) m hm)
    (fun n _ m hm=>hB _ (Nat.succ_pos n) m hm)
    (fun n nh m hm=>(Hreg n nh m hm).1)
    (fun n nh m hm=>(Hreg n nh m hm).2) sx sy
    (fun n nh m hm=>⟨fun h=>((Ho n nh m hm).1 h).1,fun h=>((Ho n nh m hm).2 h).1⟩)
    (fun n nh m hm=>⟨fun h=>((Ho n nh m hm).1 h).2,fun h=>((Ho n nh m hm).2 h).2⟩)
    (fun n nh m hm=>⟨fun h=>((Hn n nh m hm).1 h).1,fun h=>((Hn n nh m hm).2 h).1⟩)
    (fun n nh m hm=>⟨fun h=>((Hn n nh m hm).1 h).2,fun h=>((Hn n nh m hm).2 h).2⟩)
    hxr.le hyr
  have HH:=mutation_incoming_log_read Ω hΩ C coord hcoord pc pos r d hs ho hn
  rw [hlabel] at H HH
  exact H.trans HH.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
