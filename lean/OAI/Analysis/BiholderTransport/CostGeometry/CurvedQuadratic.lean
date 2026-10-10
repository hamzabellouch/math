import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ContDiffQuadraticUpper

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_curved_quadratic_upper {Q : E → ℝ} {p e : E}
    (hQ : ContDiffAt ℝ 2 Q p) (hQ0 : Q p=0)
    (hmin : ∀ᶠ s : ℝ in 𝓝 0, 0≤Q (p+s • e)) :
    ∃ eps C : ℝ, 0<eps ∧ 0<C ∧ ∀ s ∈ Ioo 0 eps,
      Q ((1-s^2) • (p+s • e))≤C*s^2 := by
  have hl : HasDerivAt (fun s : ℝ => p+s • e) e 0 := by
    convert! (hasDerivAt_const (0:ℝ) p).add ((hasDerivAt_id (0:ℝ)).smul_const e) using 1
    simp
  have hQ' : HasFDerivAt Q (fderiv ℝ Q p) (p+(0:ℝ) • e) := by
    simpa only [zero_smul,add_zero] using (hQ.differentiableAt (by norm_num)).hasFDerivAt
  have hlocal : IsLocalMin (fun s : ℝ => Q (p+s • e)) 0 := by
    change ∀ᶠ s : ℝ in 𝓝 0, Q (p+(0:ℝ) • e) ≤ Q (p+s • e)
    simpa only [zero_smul,add_zero,hQ0] using hmin
  have hderivzero : fderiv ℝ Q p e=0 :=
    hlocal.hasDerivAt_eq_zero (hQ'.comp_hasDerivAt (f := fun s : ℝ => p+s • e) 0 hl)
  let L : ℝ → E := fun s => (1-s^2) • (p+s • e)
  have hL0 : L 0=p := by simp [L]
  have hL : HasDerivAt L e 0 := by
    convert! ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub ((hasDerivAt_id (0:ℝ)).pow 2)).smul hl using 1
    simp
  have hLc : ContDiffAt ℝ 2 L 0 := by dsimp [L]; fun_prop
  have hQc : ContDiffAt ℝ 2 (Q ∘ L) 0 := by
    have hQ' : ContDiffAt ℝ 2 Q (L 0) := by rwa [hL0]
    exact hQ'.comp 0 hLc
  have hqd : HasDerivAt (Q ∘ L) 0 0 := by
    have hd : HasFDerivAt Q (fderiv ℝ Q p) (L 0) := by
      simpa only [hL0] using (hQ.differentiableAt (by norm_num)).hasFDerivAt
    simpa only [hderivzero,Function.comp_def] using hd.comp_hasDerivAt (f := L) 0 hL
  exact contDiffAt_quadratic_upper (f := Q ∘ L) hQc (by change Q (L 0)=0; rw [hL0,hQ0]) hqd.deriv
end WeakMTWTransport

end

end OAI
