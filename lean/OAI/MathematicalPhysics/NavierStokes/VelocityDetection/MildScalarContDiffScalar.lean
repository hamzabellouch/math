import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailEvaluation
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ClmDerivWithin

namespace OAI

noncomputable section
namespace VelocityDetection.MildScalar
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open TailSpace.Jets WeakVolterra SpatialCalculus
variable {ν : ℝ} (hν : 0 < ν) (W : Fin 2 → SupportedData) (g : SupportedData)

theorem contDiff_scalar (hg : ∀ t : ℝ, t ≤ 0 → ∀ X, g.scalar t X = 0) :
    ContDiff ℝ ∞ (uncurry (scalar hν W g)) := by
  apply contDiff_infty.mpr
  intro a
  have hh := contDiff_uncurry_value a (contDiff_globalJets_nat hν W g hg a a)
  simp only [value_globalJets] at hh
  convert hh using 1
  rfl

theorem value_timeGenerator (a : ℕ) (t : ℝ) (X : Coord 2) :
    value (timeGenerator hν W g a t) X =
      ν * laplacian (scalar hν W g) t X + g.scalar t X -
        ∑ i : Fin 2, partialD i (fun Y => (W i).scalar t Y * scalar hν W g t Y) X := by
  change evaluate X (ν • laplaceJet (globalJets hν W g (a+2) t) +
    (g.jets a t - ∑ i : Fin 2, differentiate i
      (product ((W i).jets (a+1) t) (globalJets hν W g (a+1) t)))) = _
  rw [map_add, map_smul, map_sub, map_sum]
  simp only [evaluate_apply, value_laplaceJet, value_globalJets,
    SupportedData.jets_value, value_differentiate, value_product]
  change ν * (∑ i : Fin 2, partialD i (partialD i (scalar hν W g t)) X) +
    (g.scalar t X - ∑ i : Fin 2, partialD i
      (fun Y => (W i).scalar t Y * scalar hν W g t Y) X) = _
  change ν * laplacian (scalar hν W g) t X + (g.scalar t X - _) = _
  ring

theorem timeD_scalar {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    timeD (scalar hν W g) t X = value (timeGenerator hν W g 0 t) X := by
  have hh : HasFDerivAt (evaluate X : E 0 →L[ℝ] ℝ) (evaluate X)
      (globalJets hν W g 0 t) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E 0) (F := ℝ) (evaluate X)
  have hd := HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ) (F := E 0) (E := ℝ)
    (l := evaluate X) (l' := evaluate X) t hh
    (hasDerivWithinAt_globalJets hν W g 0 ht)
  exact hd.derivWithin (uniqueDiffOn_Ici (0:ℝ) t ht)

theorem scalar_conservation {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    timeD (scalar hν W g) t X +
      ∑ i : Fin 2, partialD i (fun Y => (W i).scalar t Y * scalar hν W g t Y) X =
        ν * laplacian (scalar hν W g) t X + g.scalar t X := by
  rw [timeD_scalar hν W g ht, value_timeGenerator]
  ring

theorem scalar_equation
    (hdiv : ∀ t : ℝ, 0 ≤ t → ∀ X, divergence (fun t X i => (W i).scalar t X) t X = 0)
    {t : ℝ} (ht : 0 ≤ t) (X : Coord 2) :
    timeD (scalar hν W g) t X +
      advection (fun t X i => (W i).scalar t X) (scalar hν W g) t X =
        ν * laplacian (scalar hν W g) t X + g.scalar t X := by
  have hw (i : Fin 2) : ContDiff ℝ ∞ ((W i).scalar t) :=
    (W i).smooth.comp (contDiff_const.prodMk contDiff_id)
  have hp (i : Fin 2) := partialD_mul i (f := (W i).scalar t) (g := scalar hν W g t)
    ((hw i).differentiable (by simp))
    ((contDiff_scalar_space hν W g t).differentiable (by simp)) X
  have he : (∑ i : Fin 2, partialD i
      (fun Y => (W i).scalar t Y * scalar hν W g t Y) X) =
      advection (fun t X i => (W i).scalar t X) (scalar hν W g) t X := by
    simp only [hp, Finset.sum_add_distrib, ← Finset.sum_mul]
    change divergence (fun t X i => (W i).scalar t X) t X * scalar hν W g t X +
      advection (fun t X i => (W i).scalar t X) (scalar hν W g) t X = _
    rw [hdiv t ht X, zero_mul, zero_add]
  exact he ▸ scalar_conservation hν W g ht X

@[simp] theorem scalar_zero (X : Coord 2) : scalar hν W g 0 X = 0 := by
  simp only [scalar, globalJets_zero]
  rfl

def entryTailL {a : ℕ} (k : ℕ) (hk : k ≤ a) (w : Fin k → Fin 2) :
    E a →L[ℝ] TailSpace.compatible 2 :=
  LinearMap.mkContinuous
    { toFun := fun J : E a => entry J k hk w
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    1 (fun J : E a => by
      change ‖entry J k hk w‖ ≤ 1 * ‖J‖
      rw [one_mul]
      exact norm_entry_le J k hk w)

private theorem entryTail_hasDerivWithinAt (k : ℕ) (w : Fin k → Fin 2)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => entryTailL k (le_refl k) w (globalJets hν W g k r))
      (entryTailL k (le_refl k) w (timeGenerator hν W g k t)) (Ici 0) t := by
  exact clm_derivWithin (A := E k) (B := TailSpace.compatible 2) (entryTailL k (le_refl k) w)
    (hasDerivWithinAt_globalJets hν W g k ht)

theorem wordPartial_C1Tails (k : ℕ) (w : Fin k → Fin 2) :
    TailSpace.C1Tails (fun t => wordPartial w (scalar hν W g t)) := by
  let F : ℝ → TailSpace.compatible 2 := fun t => entryTailL k (le_refl k) w (globalJets hν W g k t)
  let G : ℝ → TailSpace.compatible 2 := fun t => entryTailL k (le_refl k) w (timeGenerator hν W g k t)
  have hF : Continuous F := (entryTailL k (le_refl k) w).continuous.comp (continuous_globalJets hν W g k)
  have hG : Continuous G := (entryTailL k (le_refl k) w).continuous.comp (continuous_timeGenerator hν W g k)
  refine ⟨F, G, hF.continuousOn, hG.continuousOn, ?_, ?_⟩
  · intro t X
    change (entry (globalJets hν W g k t) k (le_refl k) w).val.1 X = _
    rw [congrFun (entry_eq_wordPartial _ k (le_refl k) w) X, value_globalJets]
  · intro t ht
    exact entryTail_hasDerivWithinAt hν W g k w ht

theorem scalar_D_Tails (i : Fin 2) :
    TailSpace.ContinuousTails (spatialD i (scalar hν W g)) := by
  have hh := (wordPartial_C1Tails hν W g 1 (fun _ => i)).continuous
  simp only [wordPartial] at hh
  convert hh using 1
  rfl

theorem scalar_DD_Tails (i j : Fin 2) :
    TailSpace.ContinuousTails (spatialD j (spatialD i (scalar hν W g))) := by
  have hh := (wordPartial_C1Tails hν W g 2 ![j,i]).continuous
  simp only [wordPartial, Matrix.cons_val_zero, Fin.tail_def, Matrix.cons_val_succ] at hh
  convert hh using 1
  rfl

end VelocityDetection.MildScalar
end

end OAI
