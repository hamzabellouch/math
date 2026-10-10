import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearScale
import OAI.Geometry.PrescribedPotential.WeakNonlinearCommutator
import OAI.Geometry.PrescribedPotential.TwoScaleRegularity

namespace OAI

/-! Derivative Elliptic Gain. -/

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
local instance (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

omit [ConnectedSpace X] in
lemma nonlinear_commutator_solution (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2))
    (F : RealSmooth A)
    (hF : D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1 : ℕ) : ℝ) F) :
    D.realVolumeDerivative k hk
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u)
      (D.potentialDerivative k p v u) =
      D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
        (D.localizers.realEmbed ((k+1 : ℕ) : ℝ) (D.realLocalizedDerivative p v F) +
          D.realNonlinearRemainder (k+1) (by omega) p v u) := by
  have hh := D.nonlinear_commutator_weak k hk p v u
  rw [hF,D.densityDerivative_embed] at hh
  rw [hh]
  rw [map_add,Localizers.realLower_embed]

omit [ConnectedSpace X] in
lemma linearizedVolume_apply_zero_scalar (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (x₀ : X) (u w : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.linearizedVolume k hk x₀ u (w,0) =
      (D.realVolumeDerivative k hk u w, D.realEvaluation ((k : ℝ)+2) x₀ w) := by
  rw [D.linearizedVolume_apply]
  simp only [map_zero,sub_zero]

 

theorem nonlinear_first_derivative_gain (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (x₀ : X) :
    ∀ᶠ u in 𝓝 (0 : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)),
      ∀ (F : RealSmooth A),
        D.realVolume (k+1) (by omega) u = D.localizers.realEmbed ((k+1 : ℕ) : ℝ) F →
      ∀ (p : ι) (v : EC d),
        ∃ w : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2),
          D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2)
            (by push_cast; linarith) w = D.potentialDerivative k p v u := by
  let : NormedAddCommGroup (D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  filter_upwards [D.linearizedVolume_local_gain (k+1) k (by omega) hk (by omega) x₀]
    with u hu
  intro F hF p v
  let w : D.localizers.RealSobolev ((k : ℝ)+2) × ℝ := (D.potentialDerivative k p v u,0)
  let f : D.localizers.RealSobolev ((k+1 : ℕ) : ℝ) × ℝ :=
    (D.localizers.realEmbed ((k+1 : ℕ) : ℝ) (D.realLocalizedDerivative p v F) +
      D.realNonlinearRemainder (k+1) (by omega) p v u,
      D.realEvaluation ((k : ℝ)+2) x₀ (D.potentialDerivative k p v u))
  have he : D.linearizedVolume k hk x₀
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u) w =
      D.pairLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith) f := by
    change D.linearizedVolume k hk x₀ _ (D.potentialDerivative k p v u,0) = _
    rw [D.linearizedVolume_apply_zero_scalar,D.pairLower_apply]
    apply Prod.ext
    · exact D.nonlinear_commutator_solution k hk p v u F hF
    · rfl
  obtain ⟨z,hz,_⟩ := hu w f he
  refine ⟨z.1,?_⟩
  exact congrArg Prod.fst hz

end GluingData
end GlobalElliptic

end
end

end OAI
