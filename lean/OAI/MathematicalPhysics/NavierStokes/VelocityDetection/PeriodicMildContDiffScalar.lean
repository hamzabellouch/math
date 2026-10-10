import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicMildGlobalJetsClamp
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicEvaluation

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicMild
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ZeroAtInfty BigOperators
open PeriodicSpace.Jets WeakVolterra SpatialCalculus
variable {ν : ℝ} (hν : 0 < ν) (W : Fin 2 → PeriodicData) (g : PeriodicData)

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
    PeriodicData.jets_value, value_differentiate, value_product]
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

theorem periodic_scalar (t : ℝ) : FactorsThrough (scalar hν W g t) PeriodicSpace.cover := by
  intro X Y hXY
  exact congrArg (fun Z => (entry (globalJets hν W g 0 t) 0 (le_refl 0) Fin.elim0) Z) hXY

end VelocityDetection.PeriodicMild
end

end OAI
