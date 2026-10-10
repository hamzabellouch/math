import OAI.Analysis.CircleDomains.Sobolev.StrongWeakPartialLimit
import OAI.Analysis.CircleDomains.Sobolev.MollificationEnergy

namespace OAI

/-! Strong Cauchy control retains the full Dirichlet energy when taking
bounded pointwise limits, rather than only a lower semicontinuity bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem energy_limit_of_strong_cauchy_partials
    {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : ℕ → EuclideanPlane → ℝ} {v : EuclideanPlane → ℝ}
    (hv : MemLp v 2 (volume.restrict U))
    (hu : ∀ n, ContinuousOn (u n) U)
    {C : ℝ} (hb : ∀ n x, x ∈ U → ‖u n x‖ ≤ C)
    (hp : ∀ x ∈ U, Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (g : Fin 2 → ℕ → EuclideanPlane → ℝ)
    (hg : ∀ i n, MemLp (g i n) 2 (volume.restrict U))
    (hw : ∀ i n, DeGiorgi.HasWeakPartialDeriv i (g i n) (u n) U)
    (hc : ∀ i, CauchySeq (fun n => (hg i n).toLp (g i n)))
    {B : ℝ} (he : Tendsto (fun n => ∫ x in U, g 0 n x^2+g 1 n x^2) atTop (𝓝 B)) :
    ∃ W : DeGiorgi.MemW1pWitness 2 v U,
      (∫ x in U, W.weakGrad x 0^2+W.weakGrad x 1^2) = B := by
  choose G hG using fun i => cauchySeq_tendsto_of_complete (hc i)
  let W : DeGiorgi.MemW1pWitness 2 v U := {
    memLp := hv
    weakGrad := fun x => WithLp.toLp 2 (fun i => G i x)
    weakGrad_component_memLp := fun i => Lp.memLp (G i)
    isWeakGrad := fun i => weakPartial_of_bounded_pointwise_strong_limit hU hu hb hp
      (hg i) (hw i) (G i) (hG i) }
  have ht (i : Fin 2) : Tendsto (fun n => ∫ x in U, g i n x^2) atTop
      (𝓝 (∫ x in U, G i x^2)) := by
    apply integral_sq_tendsto_of_L2 (hg i) (Lp.memLp (G i))
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (g i) (hg i) (G i) (Lp.memLp (G i))).mp
    simpa only [Lp.toLp_coeFn] using hG i
  have ht' := (ht 0).add (ht 1)
  simp only [← integral_add (hg 0 _).integrable_sq (hg 1 _).integrable_sq,
    ← integral_add (Lp.memLp (G 0)).integrable_sq (Lp.memLp (G 1)).integrable_sq] at ht'
  exact ⟨W, tendsto_nhds_unique ht' he⟩

end CircleDomainRigidity

end

end OAI
