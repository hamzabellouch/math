import Mathlib
import OAI.Geometry.PrescribedPotential.DerivativeEllipticGain
import OAI.Geometry.PrescribedPotential.NonlinearScale
import OAI.Geometry.PrescribedPotential.NonlinearSobolevGain
import OAI.Geometry.PrescribedPotential.WeakNonlinearCommutator
import OAI.Geometry.PrescribedRicci.FiniteCofactorPatch
import OAI.Geometry.PrescribedRicci.TameCofactorGain

namespace OAI

/-! Fixed Cofactor Step. -/

section

 
noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance fixedCofactorStepNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance fixedCofactorStepNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance fixedCofactorStepTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance fixedCofactorStepCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

omit [ConnectedSpace X] in
lemma realLift_transport (s t r : ℝ) (hs : r ≤ s) (ht : r ≤ t) (hst : s = t)
    (u : D.localizers.RealSobolev r)
    (h : ∃ z : D.localizers.RealSobolev s, D.localizers.realLower s r hs z = u) :
    ∃ z : D.localizers.RealSobolev t, D.localizers.realLower t r ht z = u := by
  subst t
  exact h

omit [ConnectedSpace X] in
theorem cofactor_nonlinear_step (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ))
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (hu : D.CofactorSmall (k+1) (by omega) hs u.val)
    (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1:ℕ):ℝ) F) :
    ∃ z : D.localizers.RealSobolev (((k+2:ℕ):ℝ)+2),
      D.localizers.realLower (((k+2:ℕ):ℝ)+2) (((k+1:ℕ):ℝ)+2) (by push_cast; linarith) z = u := by
  have hD (p : ι) (v : EC d) := D.cofactor_global_gain k hk hs u hu
    (D.potentialDerivative k p v u)
    (D.localizers.realEmbed ((k+1:ℕ):ℝ) (D.realLocalizedDerivative p v F) +
      D.realNonlinearRemainder (k+1) (by omega) p v u)
    (D.nonlinear_commutator_solution k hk p v u F hF)
  have hh := D.derivative_lifts_gain k u hD
  have he : ((k+4:ℕ):ℝ) = ((k+2:ℕ):ℝ)+2 := by push_cast; ring
  exact D.realLift_transport _ _ _ _ _ he u hh

 
omit [ConnectedSpace X] in
lemma cofactor_lift_equation (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hkl : k ≤ l)
    (u : D.localizers.RealSobolev ((k:ℝ)+2))
    (v : D.localizers.RealSobolev ((l:ℝ)+2))
    (hv : D.localizers.realLower ((l:ℝ)+2) ((k:ℝ)+2) (by exact_mod_cast Nat.add_le_add_right hkl 2) v = u)
    (F : RealSmooth A) (hF : D.realVolume k hk u = D.localizers.realEmbed (k:ℝ) F) :
    D.realVolume l hl v = D.localizers.realEmbed (l:ℝ) F := by
  apply D.localizers.realLower_injective (by exact_mod_cast hkl : (k:ℝ) ≤ (l:ℝ))
  rw [← D.realVolume_lower l k hl hk hkl, hv, hF,Localizers.realLower_embed]

end GluingData
end GlobalElliptic

end
end

end OAI
