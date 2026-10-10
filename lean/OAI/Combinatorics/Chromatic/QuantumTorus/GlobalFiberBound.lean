import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.UpstreamSimpleFiber

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀d m,HasRootDegree C d m → L (e m)=(d:ℝ))
include hcoord he hB hcomp hdeg in
theorem simple_fiber_bound_through (N : ℕ) (hN : 0<N)
    (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  have H : ∀n : ℕ,∀q d,0<d → HasRootDegree C d q → ∀b : Module.Dual ℝ E,
      RayGeneric C N q (b.toAddMonoidHom.comp e) → ∀s : Bool,
      cutSide s (b.toAddMonoidHom.comp e) (simpleRoot C pc) →
      ∀j≤N,∀m,coeff j (chartZero LaurentRay.vUnit Ω C (b.toAddMonoidHom.comp e)
        (simpleTotalTransport Ω C)).val m≠0 → nonpDegree coord pc m=(n:ℤ) →
        m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q d hd hdq b hb s hs
      apply global_simple_fiber_step Ω C coord hcoord pc e he B hB hcomp L hdeg N hN (n:ℤ) ?_
        q d hd hdq b hb s hs
      intro q' d' hd' hdq' b' hb' s' hs' j hj m hm hn
      have hw : 0≤nonpDegree coord pc m:=nonpDegree_root_nonneg C coord hcoord pc
        (chart_root_of_ne LaurentRay.vUnit Ω C _ j m hm)
      exact ih (nonpDegree coord pc m).toNat (by omega) q' d' hd' hdq' b' hb' s' hs'
        j hj m hm (by omega)
  intro j hj m hm
  have hw : 0≤nonpDegree coord pc m:=nonpDegree_root_nonneg C coord hcoord pc
    (chart_root_of_ne LaurentRay.vUnit Ω C _ j m hm)
  exact H (nonpDegree coord pc m).toNat r dr hdr hrd h hg pos hside j hj m hm (by omega)

include hcoord he hB hcomp hdeg in
theorem simple_fiber_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀j m,coeff j (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  intro j m hm
  exact simple_fiber_bound_through Ω C coord hcoord pc e he B hB hcomp L hdeg (max 1 j)
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) r dr hdr hrd h (hg _) pos hside
    j (le_max_right _ _) m hm

include hcoord he hB hcomp hdeg in
theorem simple_fiber_log_bound (r : M) (dr : ℕ) (hdr : 0<dr) (hrd : HasRootDegree C dr r)
    (h : Module.Dual ℝ E) (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e))
    (pos : Bool) (hside : cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc)) :
    ∀j m,coeff j (FormalLog.log (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e)
      (simpleTotalTransport Ω C)).val) m≠0 →
      m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos) := by
  let P:=fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)
  have HH:=simple_fiber_bound Ω C coord hcoord pc e he B hB hcomp L hdeg r dr hdr hrd h hg pos hside
  intro j m hm
  by_contra hn
  exact hm (strict_log_support LaurentRay.vUnit Ω (V:=fun m=>m∈P)
    (fun a b ha hb=>P.add_mem ha hb) _ (chartZero _ _ _ _ _).property.1
    (fun j m hh=>by by_contra hm; exact hh (HH (j+1) m hm)) j m hn)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
