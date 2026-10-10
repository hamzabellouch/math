import OAI.Analysis.CoulombTransport.CertificateNeighborhoods

namespace OAI

universe uIndex uX

noncomputable section
open Set Filter Metric
open scoped BigOperators
namespace Problem356

/-- Continuity of finitely many potentials at their centers gives one
positive radius and one positive absolute bound on every component ball. -/
theorem exists_uniform_local_potential_bound {ι : Type uIndex} {X : Type uX} [Fintype ι]
    [PseudoMetricSpace X] (p : ι → X) (v : ι → X → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) :
    ∃ M : ℝ, 0 < M ∧ ∃ r : ℝ, 0 < r ∧
      ∀ i x, x ∈ ball (p i) r → |v i x| ≤ M := by
  classical
  let M : ℝ := (∑ i, |v i (p i)|) + 1
  have hsum : 0 ≤ ∑ i, |v i (p i)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hM : 0 < M := by dsimp [M]; linarith
  have hgap : ∀ i ∈ (Finset.univ : Finset ι), |v i (p i)| < M := by
    intro i _
    have hi : |v i (p i)| ≤ ∑ j, |v j (p j)| :=
      Finset.single_le_sum (f := fun j => |v j (p j)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [M]
    linarith
  obtain ⟨r, hr, h⟩ := finite_strict_neighborhoods Finset.univ p
    (fun i x => |v i x|) (fun _ _ => M)
    (fun i _ => (hv i).abs) (fun _ _ => continuousAt_const) hgap
  refine ⟨M, hM, r, hr, ?_⟩
  intro i x hx
  exact (h i (Finset.mem_univ i) x hx).le

end Problem356

end

end OAI
