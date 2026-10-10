import Mathlib
import OAI.Geometry.PrescribedPotential.BootstrapCalculus
import OAI.Geometry.PrescribedPotential.ClosedRangeSmooth
import OAI.Geometry.PrescribedPotential.RealMapSmooth
import OAI.Geometry.PrescribedPotential.WeakNonlinearCommutator

namespace OAI

/-! Linearized Commutator. -/

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
local instance linComNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance linComNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance linComTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance linComCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma realVolumeDerivative_eq_fderiv (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    D.realVolumeDerivative k hk = fderiv ℝ (D.realVolume k hk) := by
  funext u
  exact (D.realVolume_hasStrictFDerivAt k hk u).hasFDerivAt.fderiv.symm

lemma realVolumeDerivative_contDiff (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ContDiff ℝ ∞ (D.realVolumeDerivative k hk) := by
  rw [D.realVolumeDerivative_eq_fderiv k hk]
  exact (D.realVolume_contDiff k hk).fderiv_right (m := ∞) (by simp)

def realVolumeSecond (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u w v : D.localizers.RealSobolev ((k : ℝ)+2)) : D.localizers.RealSobolev (k : ℝ) := by
  letI : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  letI : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  letI : NormedAddCommGroup (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  letI : NormedSpace ℝ (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  exact fderiv ℝ (D.realVolumeDerivative k hk) u w v

def realRemainderDerivative (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ] D.localizers.RealSobolev (k : ℝ) :=
  fderiv ℝ (D.realNonlinearRemainder k hk p v) u

lemma realVolumeSecond_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k)
    (u w v : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.realVolumeSecond l hl
        (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
          (by exact_mod_cast Nat.add_le_add_right hlk 2) u)
        (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
          (by exact_mod_cast Nat.add_le_add_right hlk 2) w)
        (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
          (by exact_mod_cast Nat.add_le_add_right hlk 2) v) =
      D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk)
        (D.realVolumeSecond k hk u w v) := by
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((l : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((l : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (l : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (l : ℝ)) := inferInstance
  let L := D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
    (by exact_mod_cast Nat.add_le_add_right hlk 2)
  let M := D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk)
  have he : ∀ y z, D.realVolumeDerivative l hl (L y) (L z) =
      M (D.realVolumeDerivative k hk y z) := by
    intro y z
    exact DFunLike.congr_fun (D.realVolumeDerivative_lower k l hk hl hlk y) z
  have hB := (D.realVolumeDerivative_contDiff k hk).differentiable (by simp)
  have hC := (D.realVolumeDerivative_contDiff l hl).differentiable (by simp)
  exact FixedBootstrapCalculus.derivative_compatibility
    (D.realVolumeDerivative k hk) (D.realVolumeDerivative l hl) L M hB hC he u w v

lemma potentialDerivative_lower (k l : ℕ) (hlk : l ≤ k) (p : ι) (v : EC d)
    (u : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) :
    D.potentialDerivative l p v
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) (((l+1 : ℕ) : ℝ)+2)
        (by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hlk 1) 2) u) =
    D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
      (by exact_mod_cast Nat.add_le_add_right hlk 2) (D.potentialDerivative k p v u) := by
  have he : (fun u => D.potentialDerivative l p v
      (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) (((l+1 : ℕ) : ℝ)+2)
        (by exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right hlk 1) 2) u)) =
      (fun u => D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
        (by exact_mod_cast Nat.add_le_add_right hlk 2) (D.potentialDerivative k p v u)) := by
    apply (D.localizers.realEmbed_dense (((k+1 : ℕ) : ℝ)+2)).equalizer
      (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, Localizers.realLower_embed, potentialDerivative_embed]
  exact congr_fun he u

lemma densityDerivative_lower (k l : ℕ) (hlk : l ≤ k) (p : ι) (v : EC d)
    (u : D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)) :
    D.densityDerivative l p v
      (D.localizers.realLower ((k+1 : ℕ) : ℝ) ((l+1 : ℕ) : ℝ)
        (by exact_mod_cast Nat.add_le_add_right hlk 1) u) =
    D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk)
      (D.densityDerivative k p v u) := by
  have he : (fun u => D.densityDerivative l p v
      (D.localizers.realLower ((k+1 : ℕ) : ℝ) ((l+1 : ℕ) : ℝ)
        (by exact_mod_cast Nat.add_le_add_right hlk 1) u)) =
      (fun u => D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk)
        (D.densityDerivative k p v u)) := by
    apply (D.localizers.realEmbed_dense ((k+1 : ℕ) : ℝ)).equalizer
      (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, Localizers.realLower_embed, densityDerivative_embed]
  exact congr_fun he u

 
lemma nonlinear_commutator_linearization (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u w : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) :
    D.realVolumeDerivative k hk
        (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u)
        (D.potentialDerivative k p v w) +
      D.realVolumeSecond k hk
        (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u)
        (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) w)
        (D.potentialDerivative k p v u) =
    D.densityDerivative k p v (D.realVolumeDerivative (k+1) (by omega) u w) +
      D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
        (D.realRemainderDerivative (k+1) (by omega) p v u w) := by
  let : NormedAddCommGroup (D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k+1 : ℕ) : ℝ)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ]
    D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ]
    D.localizers.RealSobolev (k : ℝ)) := inferInstance
  have hF : fderiv ℝ (D.realVolume (k+1) (by omega)) u =
      D.realVolumeDerivative (k+1) (by omega) u :=
    (D.realVolume_hasStrictFDerivAt (k+1) (by omega) u).hasFDerivAt.fderiv
  have hh := FixedBootstrapCalculus.differentiated_commutator
    (D.realVolumeDerivative k hk)
    (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith))
    (D.potentialDerivative k p v) (D.densityDerivative k p v)
    (D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith))
    (D.realVolume (k+1) (by omega)) (D.realNonlinearRemainder (k+1) (by omega) p v)
    ((D.realVolumeDerivative_contDiff k hk).differentiable (by simp))
    ((D.realVolume_contDiff (k+1) (by omega)).differentiable (by simp))
    ((D.realNonlinearRemainder_contDiff (k+1) (by omega) p v).differentiable (by simp))
    (D.nonlinear_commutator_weak k hk p v) u w
  rw [hF] at hh
  exact hh

lemma secondPotential_lower (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev (((k+2 : ℕ) : ℝ)+2))
    (w : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) :
    let u₁ := D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2) (by push_cast; linarith) u
    let L := D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith)
    D.realVolumeSecond k hk (L u₁) (L w) (D.potentialDerivative k p v u₁) =
      D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
        (D.realVolumeSecond (k+1) (by omega) u₁ w (D.potentialDerivative (k+1) p v u)) := by
  dsimp only
  let u₁ := D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2) (by push_cast; linarith) u
  let L := D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith)
  have hd := D.potentialDerivative_lower (k+1) k (by omega) p v u
  have ht := congrArg (D.realVolumeSecond k hk (L u₁) (L w)) hd
  exact ht.trans (D.realVolumeSecond_lower (k+1) k (by omega) hk (by omega)
    u₁ w (D.potentialDerivative (k+1) p v u))

 

lemma linearized_commutator_weak (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (p : ι) (v : EC d) (u : D.localizers.RealSobolev (((k+2 : ℕ) : ℝ)+2))
    (w : D.localizers.RealSobolev (((k+1 : ℕ) : ℝ)+2)) :
    let u₁ := D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2) (by push_cast; linarith) u
    D.realVolumeDerivative k hk
        (D.localizers.realLower (((k+1 : ℕ) : ℝ)+2) ((k : ℝ)+2) (by push_cast; linarith) u₁)
        (D.potentialDerivative k p v w) =
    D.densityDerivative k p v (D.realVolumeDerivative (k+1) (by omega) u₁ w) +
      D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)
        (D.realRemainderDerivative (k+1) (by omega) p v u₁ w -
          D.realVolumeSecond (k+1) (by omega) u₁ w
            (D.potentialDerivative (k+1) p v u)) := by
  dsimp only
  let u₁ := D.localizers.realLower (((k+2 : ℕ) : ℝ)+2) (((k+1 : ℕ) : ℝ)+2) (by push_cast; linarith) u
  exact FixedBootstrapCalculus.lowered_remainder
    (D.localizers.realLower ((k+1 : ℕ) : ℝ) (k : ℝ) (by push_cast; linarith)) _ _ _ _ _
    (D.nonlinear_commutator_linearization k hk p v u₁ w)
    (D.secondPotential_lower k hk p v u w)

end GluingData
end GlobalElliptic

end
end

end OAI
