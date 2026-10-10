import OAI.Geometry.RCD.Metric.RescaledFiniteNets
import Mathlib.Topology.MetricSpace.Completion

namespace OAI

/-! # Subsequence limits of the sampled rescaling metrics

Uniformly bounded countable samples have a convergent distance matrix.
Its triangle inequalities give an actual pseudometric, whose completion
will supply the pointed limit after the finite-net estimates are applied.
-/

open Set Metric Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] {ι : Type*} [Countable ι]

/-- A countable family of rescaled sample distances has an actual
pseudometric subsequential limit. Only upper bounds on the samples are
required at this stage. -/
theorem exists_rescaling_sample_limit (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (points : ℕ → ι → X) (B : ι → ℝ)
    (hbound : ∀ k a b, dist (points k a) (points k b) / r k ≤ B a + B b) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ d : PseudoMetricSpace ι,
      ∀ a b, Tendsto (fun k => dist (points (phi k) a) (points (phi k) b) / r (phi k))
        atTop (𝓝 (@dist ι d.toDist a b)) := by
  let matrix (k : ℕ) (ab : ι × ι) := dist (points k ab.1) (points k ab.2) / r k
  let S : Set (ι × ι → ℝ) := pi univ (fun ab => Icc 0 (B ab.1 + B ab.2))
  have hS : IsCompact S := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hmatrix (k : ℕ) : matrix k ∈ S := by
    intro ab _
    exact ⟨div_nonneg dist_nonneg (hr k).le, hbound k ab.1 ab.2⟩
  obtain ⟨limit, _, phi, hphi, hlimit⟩ := hS.tendsto_subseq hmatrix
  have hconv (a b : ι) : Tendsto (fun k => matrix (phi k) (a,b)) atTop (𝓝 (limit (a,b))) :=
    (tendsto_pi_nhds.mp hlimit) (a,b)
  have hself (a : ι) : limit (a,a) = 0 := by
    have hh := hconv a a
    simp only [matrix, dist_self, zero_div] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hcomm (a b : ι) : limit (a,b) = limit (b,a) := by
    apply tendsto_nhds_unique (hconv a b)
    simpa only [matrix, dist_comm] using hconv b a
  have htriangle (a b c : ι) : limit (a,c) ≤ limit (a,b) + limit (b,c) := by
    apply le_of_tendsto_of_tendsto (hconv a c) ((hconv a b).add (hconv b c))
    exact Eventually.of_forall fun k => by
      dsimp only [matrix]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (dist_triangle _ _ _) (hr (phi k)).le
  let d : PseudoMetricSpace ι := {
    dist := fun a b => limit (a,b)
    dist_self := hself
    dist_comm := hcomm
    dist_triangle := htriangle }
  exact ⟨phi, hphi, d, hconv⟩

end RegularPointCoordinates

end

end OAI
