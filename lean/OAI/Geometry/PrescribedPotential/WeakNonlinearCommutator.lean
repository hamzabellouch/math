import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearScale
import OAI.Geometry.PrescribedPotential.RealNonlinearCommutator

namespace OAI

/-! Weak Nonlinear Commutator. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance weakNonlinearCommutatorNormedAddCommGroup (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance weakNonlinearCommutatorNormedSpace (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance weakNonlinearCommutatorIsTopologicalAddGroup (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance weakNonlinearCommutatorContinuousSMul (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma realNonlinearRemainder_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k) (p : ι) (v : EC d)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk)
      (D.realNonlinearRemainder k hk p v u) =
    D.realNonlinearRemainder l hl p v
      (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
        (by exact_mod_cast Nat.add_le_add_right hlk 2) u) := by
  have hst : (l : ℝ)+2 ≤ (k : ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hlk 2
  have hkl : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  let L := D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2) hst
  let M := D.localizers.realLower (k : ℝ) (l : ℝ) hkl
  have he : M ∘ D.realNonlinearRemainder k hk p v =
      D.realNonlinearRemainder l hl p v ∘ L := by
    apply (D.localizers.realEmbed_dense ((k : ℝ)+2)).equalizer
      (M.continuous.comp (D.realNonlinearRemainder_continuous k hk p v))
      ((D.realNonlinearRemainder_continuous l hl p v).comp L.continuous)
    funext f
    dsimp only [Function.comp_apply]
    have hh := congrArg M (D.real_commutator_core k hk p v f)
    have hd := congrArg (fun T : D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ]
        D.localizers.RealSobolev (l : ℝ) => T
          (D.localizers.realEmbed ((k : ℝ)+2) (D.realLocalizedDerivative p v f)))
      (D.realVolumeDerivative_lower k l hk hl hlk (D.localizers.realEmbed ((k : ℝ)+2) f))
    simp only [ContinuousLinearMap.comp_apply,Localizers.realLower_embed] at hd
    change M (D.realVolumeDerivative k hk (D.localizers.realEmbed ((k : ℝ)+2) f)
      (D.localizers.realEmbed ((k : ℝ)+2) (D.realLocalizedDerivative p v f))) = _ at hh
    rw [← hd,D.real_commutator_core l hl p v f,map_add] at hh
    dsimp only [M] at hh
    rw [Localizers.realLower_embed] at hh
    change _ = D.localizers.realEmbed (l : ℝ)
      (D.realLocalizedDerivative p v (RealSmooth.ofReal (g.potentialDensity f.source))) +
      M (D.realNonlinearRemainder k hk p v (D.localizers.realEmbed ((k : ℝ)+2) f)) at hh
    have hh' := add_left_cancel hh
    change M (D.realNonlinearRemainder k hk p v (D.localizers.realEmbed ((k : ℝ)+2) f)) = _
    rw [show L (D.localizers.realEmbed ((k : ℝ)+2) f) = D.localizers.realEmbed ((l : ℝ)+2) f
      from D.localizers.realLower_embed hst f]
    exact hh'.symm
  exact congr_fun he u

def potentialDerivative (k : ℕ) (p : ι) (v : EC d) :
    D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2) →L[ℝ]
      D.localizers.RealSobolev ((k : ℝ)+2) :=
  D.localizers.realLower ((k+2 : ℕ) : ℝ) ((k : ℝ)+2) (by norm_num) ∘L
    D.realCompletedDerivative (k+2) p v ∘L
    D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) (((k+2 : ℕ) : ℝ)+1) (by push_cast; linarith)

lemma potentialDerivative_embed (k : ℕ) (p : ι) (v : EC d) (f : RealSmooth A) :
    D.potentialDerivative k p v (D.localizers.realEmbed (((k+1 : ℕ) : ℝ)+2) f) =
      D.localizers.realEmbed ((k : ℝ)+2) (D.realLocalizedDerivative p v f) := by
  simp only [potentialDerivative,ContinuousLinearMap.comp_apply,
    Localizers.realLower_embed,realCompletedDerivative_embed]

def densityDerivative (k : ℕ) (p : ι) (v : EC d) :
    D.localizers.RealSobolev ((k+1 : ℕ) : ℝ) →L[ℝ] D.localizers.RealSobolev (k : ℝ) :=
  D.realCompletedDerivative k p v ∘L
    D.localizers.realLower ((k+1 : ℕ) : ℝ) ((k : ℝ)+1) (by norm_num)

lemma densityDerivative_embed (k : ℕ) (p : ι) (v : EC d) (f : RealSmooth A) :
    D.densityDerivative k p v (D.localizers.realEmbed ((k+1 : ℕ) : ℝ) f) =
      D.localizers.realEmbed (k : ℝ) (D.realLocalizedDerivative p v f) := by
  simp only [densityDerivative,ContinuousLinearMap.comp_apply,
    Localizers.realLower_embed,realCompletedDerivative_embed]

 

theorem nonlinear_commutator_weak (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) :
    D.realVolumeDerivative k hk
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u)
      (D.potentialDerivative k p v u) =
    D.densityDerivative k p v (D.realVolume (k+1) (by omega) u) +
    D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
      (D.realNonlinearRemainder (k+1) (by omega) p v u) := by
  let L := D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith)
  let M := D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
  have he : (fun u => D.realVolumeDerivative k hk (L u) (D.potentialDerivative k p v u)) =
      (fun u => D.densityDerivative k p v (D.realVolume (k+1) (by omega) u) +
        M (D.realNonlinearRemainder (k+1) (by omega) p v u)) := by
    apply (D.localizers.realEmbed_dense (((k+1 : ℕ) : ℝ)+2)).equalizer
      (((D.realVolumeDerivative_continuous k hk).comp L.continuous).clm_apply
        (D.potentialDerivative k p v).continuous)
      (((D.densityDerivative k p v).continuous.comp (D.realVolume_continuous (k+1) (by omega))).add
        (M.continuous.comp (D.realNonlinearRemainder_continuous (k+1) (by omega) p v)))
    funext f
    dsimp only [L,M,Function.comp_apply,Pi.add_apply]
    rw [Localizers.realLower_embed,D.potentialDerivative_embed,D.realVolume_embed,
      D.densityDerivative_embed,D.realNonlinearRemainder_lower (k+1) k (by omega) hk (by omega),
      Localizers.realLower_embed]
    exact D.real_commutator_core k hk p v f
  exact congr_fun he u

end GluingData
end GlobalElliptic

end
end

end OAI
