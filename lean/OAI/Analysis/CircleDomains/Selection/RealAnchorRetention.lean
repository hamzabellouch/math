import OAI.Analysis.CircleDomains.Topology.CompactImageRetention
import OAI.Analysis.CircleDomains.Topology.FinitePlaneEmbedding
import OAI.Analysis.CircleDomains.Selection.RealSequenceRetention
import OAI.Analysis.CircleDomains.Transfer.RealMarkedModels

namespace OAI

/-! The source anchor's fixed zero plateau is retained on a compact target anchor in the actual
finite models. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem plane_open_embedding (hG : IsOpen G) :
    ContinuousOn A.function (((↑) : ℂ → Sphere) ⁻¹' G) ∧
      (∀ S : Set ℂ, IsOpen S → S ⊆ ((↑) : ℂ → Sphere) ⁻¹' G →
        IsOpen (A.function '' S)) ∧
      InjOn A.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
  have hinf : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  have hV : IsOpen (extendAtInfinity A.function '' G) :=
    A.conformal.1.isOpen_image hG hG (Subset.refl G)
  obtain ⟨fi, heq⟩ := A.conformal.exists_smooth_inverse hG hV
  simpa only [extendAtInfinity_coe, finiteCoord_coe] using
    heq.finite_open_embedding hinf (by simp) hV

theorem eventually_compact_subset_anchor_image
    (hsch : PlanarSchoenflies) (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    {K : Set ℂ} (hK : IsCompact K) (hKA : K ⊆ A.function '' jordanInterior H) :
    ∀ᶠ n in atTop, K ⊆
      (fun z : ℂ => finiteCoord ((M.stages (A.subsequence n)).forward z)) '' jordanInterior H := by
  let _ : ∀ n, Fintype (M.stages (A.subsequence n)).indices :=
    fun n => (M.stages (A.subsequence n)).finite_indices.fintype
  have hF := A.plane_open_embedding hG
  let Gn (n : ℕ) : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹'
    openCompletedRegion (M.stages (A.subsequence n)).terminals.H
  have hdata (n : ℕ) := (M.stages (A.subsequence n)).equivalence.finite_open_embedding
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1
    (M.stages (A.subsequence n)).circle_domain.1
  apply eventually_compact_subset_image_jordan_disk hsch (hG.preimage OnePoint.continuous_coe)
    hF.1 hF.2.1 hF.2.2 Gn
    (fun n => (isOpen_openCompletedRegion (M.stages (A.subsequence n)).terminals.H).preimage
      OnePoint.continuous_coe)
    (fun n z => finiteCoord ((M.stages (A.subsequence n)).forward z))
    (fun n => (hdata n).1) (fun n => (hdata n).2.1) (fun n => (hdata n).2.2)
    A.converges H hHG ?_ hK hKA
  have hsourceG : ((↑) : ℂ → Sphere) '' closure (jordanInterior H) ⊆ G := by
    rintro _ ⟨z, hz, rfl⟩
    exact hHG hz
  filter_upwards [A.strict.tendsto_atTop (M.eventually_model_contains
    ((isCompact_closure_jordanInterior H).image OnePoint.continuous_coe) hsourceG)] with n hn
  exact fun z hz => hn (mem_image_of_mem _ hz)

/-- A compact portion of the limiting anchor image has the original test value zero in all
sufficiently late finite models, and lies in their actual target domains. -/
theorem eventually_zero_on_anchor_image
    (hsch : PlanarSchoenflies) (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (l : ℕ) (hzero : ∀ z ∈ closure (jordanInterior H), d.physical l (Complex.equivRealProdCLM z) = 0)
    {K : Set ℂ} (hK : IsCompact K) (hKA : K ⊆ A.function '' jordanInterior H) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      (z : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse z) = 0 := by
  have hsourceK := (isCompact_closure_jordanInterior H).image OnePoint.continuous_coe
  have hsourceG : ((↑) : ℂ → Sphere) '' closure (jordanInterior H) ⊆ G := by
    rintro _ ⟨z, hz, rfl⟩
    exact hHG hz
  filter_upwards [A.eventually_compact_subset_anchor_image hsch hG H hHG hK hKA,
    A.strict.tendsto_atTop (M.eventually_model_contains hsourceK hsourceG),
    A.strict.tendsto_atTop (M.eventually_test_eq hsourceK hsourceG l)] with n hn hM htest
  intro z hz
  obtain ⟨x, hx, he⟩ := hn hz
  have hxsource := hM (mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hx))
  have hxfinite := (M.stages (A.subsequence n)).equivalence.finite_forward
    (M.stages (A.subsequence n)).source_infty (M.stages (A.subsequence n)).principal.1 hxsource
  change finiteCoord ((M.stages (A.subsequence n)).forward x) = z at he
  have he' : (M.stages (A.subsequence n)).forward x = (z : Sphere) := by
    rw [← coe_finiteCoord hxfinite, he]
  refine ⟨he' ▸ (M.stages (A.subsequence n)).equivalence.mapsTo hxsource, ?_⟩
  rw [← he', (M.stages (A.subsequence n)).equivalence.left_inv x hxsource]
  change (M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n))
    (Complex.equivRealProdCLM x) = 0
  exact (htest x (mem_image_of_mem ((↑) : ℂ → Sphere) (subset_closure hx))).trans
    (hzero x (subset_closure hx))

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
