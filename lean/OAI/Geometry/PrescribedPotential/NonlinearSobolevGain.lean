import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.CompletedRealification
import OAI.Geometry.PrescribedPotential.DerivativeEllipticGain
import OAI.Geometry.PrescribedPotential.SobolevFirstGain
import OAI.Geometry.PrescribedPotential.WeakNonlinearCommutator

namespace OAI

/-! Nonlinear Sobolev Gain. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (L : Localizers A ι)
lemma realLower_lower {s t r : ℝ} (hst : t ≤ s) (htr : r ≤ t) (u : L.RealSobolev s) :
    L.realLower t r htr (L.realLower s t hst u) =
      L.realLower s r (htr.trans hst) u := by
  apply Subtype.ext
  exact L.lower_lower hst htr u.val
end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance nonlinearSobGainNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance nonlinearSobGainNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance nonlinearSobGainTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance nonlinearSobGainCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma real_sobolev_first_gain (k : ℕ) (u : D.localizers.RealSobolev ((k : ℝ)+1))
    (hD : ∀ (p : ι) (v : EC d), ∃ w : D.localizers.RealSobolev ((k : ℝ)+1),
      D.localizers.realLower ((k : ℝ)+1) (k : ℝ) (by linarith) w =
        D.realCompletedDerivative k p v u) :
    ∃ w : D.localizers.RealSobolev ((k+2 : ℕ) : ℝ),
      D.localizers.realLower ((k+2 : ℕ) : ℝ) ((k : ℝ)+1) (by push_cast; linarith) w = u := by
  have hc (p : ι) (v : EC d) : ∃ w : D.localizers.Sobolev ((k : ℝ)+1),
      D.localizers.lower ((k : ℝ)+1) (k : ℝ) w = D.completedDerivative k p v u.val := by
    obtain ⟨w,hw⟩ := hD p v
    exact ⟨w.val,congrArg Subtype.val hw⟩
  obtain ⟨w,hw⟩ := D.sobolev_first_gain k u.val hc
  have hm : w ∈ D.localizers.realCompletion ((k+2 : ℕ) : ℝ) := by
    apply D.mem_real_of_lower_eq (k+2) (k+1) ((k : ℝ)+1) (by push_cast; rfl) (by omega)
    have hh : D.localizers.lower ((k+2 : ℕ) : ℝ) ((k : ℝ)+1) w ∈
        D.localizers.realCompletion ((k : ℝ)+1) := hw.symm ▸ u.property
    exact hh
  exact ⟨⟨w,hm⟩,Subtype.ext hw⟩

lemma derivative_lifts_reindex (k : ℕ)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (hD : ∀ (p : ι) (v : EC d), ∃ w : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2),
      D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) w =
        D.potentialDerivative k p v u) :
    ∀ (p : ι) (v : EC d), ∃ w : D.localizers.RealSobolev (((k+2 : ℕ) : ℝ)+1),
      D.localizers.realLower (((k+2 : ℕ) : ℝ)+1) ((k+2 : ℕ) : ℝ) (by linarith) w =
        D.realCompletedDerivative (k+2) p v
          (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) (((k+2 : ℕ) : ℝ)+1)
            (by push_cast; linarith) u) := by
  intro p v
  obtain ⟨w,hw⟩ := hD p v
  refine ⟨D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) (((k+2 : ℕ) : ℝ)+1)
    (by push_cast; linarith) w,?_⟩
  apply D.localizers.realLower_injective (by norm_num : (k : ℝ)+2 ≤ ((k+2 : ℕ) : ℝ))
  rw [Localizers.realLower_lower,Localizers.realLower_lower]
  exact hw

lemma derivative_lifts_gain (k : ℕ)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (hD : ∀ (p : ι) (v : EC d), ∃ w : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2),
      D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) w =
        D.potentialDerivative k p v u) :
    ∃ w : D.localizers.RealSobolev ((k+4 : ℕ) : ℝ),
      D.localizers.realLower ((k+4 : ℕ) : ℝ) (((k+1 : ℕ) : ℝ)+2) (by push_cast; linarith) w = u := by
  let u' := D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) (((k+2 : ℕ) : ℝ)+1)
    (by push_cast; linarith) u
  obtain ⟨w,hw⟩ := D.real_sobolev_first_gain (k+2) u'
    (D.derivative_lifts_reindex k u hD)
  refine ⟨D.localizers.realLower ((k+2+2 : ℕ) : ℝ) ((k+4 : ℕ) : ℝ) (by push_cast; linarith) w,?_⟩
  apply D.localizers.realLower_injective
    (by push_cast; linarith : ((k+2 : ℕ) : ℝ)+1 ≤ ((k+1 : ℕ) : ℝ)+2)
  rw [Localizers.realLower_lower,Localizers.realLower_lower]
  exact hw

variable [ConnectedSpace X]
 

theorem nonlinear_sobolev_gain (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    ∀ᶠ u in 𝓝 (0 : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)),
      ∀ (F : RealSmooth A),
        D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1 : ℕ) : ℝ) F →
      ∃ w : D.localizers.RealSobolev ((k+4 : ℕ) : ℝ),
        D.localizers.realLower ((k+4 : ℕ) : ℝ) (((k+1 : ℕ) : ℝ)+2)
          (by push_cast; linarith) w = u := by
  filter_upwards [D.nonlinear_first_derivative_gain k hk x₀] with u hu
  intro F hF
  exact D.derivative_lifts_gain k u (hu F hF)

end GluingData
end GlobalElliptic

end
end

end OAI
