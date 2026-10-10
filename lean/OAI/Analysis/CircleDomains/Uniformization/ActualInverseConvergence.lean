import OAI.Analysis.CircleDomains.Uniformization.LocalInverseConvergence
import OAI.Analysis.CircleDomains.Selection.RealAnchorRetention

namespace OAI

/-! Inverse convergence for the actual normalized finite transfer stages. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit
variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem inverse_tendsto (hsch : PlanarSchoenflies) (hG : IsOpen G)
    {x : ℂ} (hx : (x : Sphere) ∈ G) :
    Tendsto (fun n => finiteCoord ((M.stages (A.subsequence n)).inverse (A.function x)))
      atTop (𝓝 x) := by
  let _ : ∀ n, Fintype (M.stages (A.subsequence n)).indices :=
    fun n => (M.stages (A.subsequence n)).finite_indices.fintype
  have hf := A.plane_open_embedding hG
  let Gn (n : ℕ) : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹'
    openCompletedRegion (M.stages (A.subsequence n)).terminals.H
  have hd (n : ℕ) := (M.stages (A.subsequence n)).equivalence.finite_open_embedding
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1
    (M.stages (A.subsequence n)).circle_domain.1
  apply inverse_tendsto_of_locally_uniform_open_embeddings hsch
    (hG.preimage OnePoint.continuous_coe) hf.1 hf.2.1 hf.2.2 Gn
    (fun n => (isOpen_openCompletedRegion (M.stages (A.subsequence n)).terminals.H).preimage
      OnePoint.continuous_coe)
    (fun n z => finiteCoord ((M.stages (A.subsequence n)).forward z))
    (fun n z => finiteCoord ((M.stages (A.subsequence n)).inverse z))
    (fun n => (hd n).1) (fun n => (hd n).2.1) (fun n => (hd n).2.2)
    ?_ A.converges ?_ hx
  · intro n z hz
    rw [coe_finiteCoord ((M.stages (A.subsequence n)).equivalence.finite_forward
      (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1 hz),
      (M.stages (A.subsequence n)).equivalence.left_inv _ hz, finiteCoord_coe]
  · intro K hK hKG
    have hsub : ((↑) : ℂ → Sphere) '' K ⊆ G := by
      rintro _ ⟨z, hz, rfl⟩
      exact hKG hz
    filter_upwards [A.strict.tendsto_atTop (M.eventually_model_contains
      (hK.image OnePoint.continuous_coe) hsub)] with n hn
    exact fun z hz => hn (mem_image_of_mem _ hz)

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
