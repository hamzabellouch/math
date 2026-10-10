import Mathlib
import OAI.Geometry.WeakMTW.Potentials.SmoothEnvelope
import OAI.Geometry.WeakMTW.Potentials.DiagonalEnvelope

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace QuadraticEnvelope
variable {A E F : Type*} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
 theorem family_local_bounds {k : A → E → ℝ} {P : A → F} {g : E×F → ℝ} {a : A} {Z : E}
     (hP : ContinuousAt P a) (hg : ContDiffAt ℝ ∞ g (Z,P a))
     (heq : ∀ᶠ a' in 𝓝 a, ∀ X, k a' X = g (X,P a')) :
     ∃ U : Set A, IsOpen U ∧ a ∈ U ∧ ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
       ∀ a' ∈ U, ∀ X ∈ Metric.ball Z r, DiagonalBound (k a') X C := by
   obtain ⟨r,C,hr,hC,hb⟩ := smooth_local_bounds hg
   have hp : ∀ᶠ a' in 𝓝 a, dist (P a') (P a) < r := hP.tendsto (Metric.ball_mem_nhds _ hr)
   obtain ⟨U,hUh,hU,haU⟩ := mem_nhds_iff.mp (hp.and heq)
   refine ⟨U,hU,haU,r,C,hr,hC,?_⟩
   intro a' ha' X hX
   have hXp : (X,P a') ∈ Metric.ball (Z,P a) r := by
     rw [← ball_prod_same]
     exact ⟨hX, (hUh ha').1⟩
   have hk : k a' = fun Y => g (Y,P a') := funext (hUh ha').2
   rw [hk]
   exact slice_diagonal_bound (hb _ hXp).1 (hb _ hXp).2
end QuadraticEnvelope
end

end WeakMTWGlobalSupport

end OAI
