import OAI.Analysis.CircleDomains.Transfer.ModelFlattenedSelection

namespace OAI

/-! The simultaneous selection may keep every changed support in a
prescribed source disk containing the dust. This leaves the outer
working collar unchanged. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_flattened_source_selection_in_ball (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
    (hne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    {C : ℝ} (hC : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 C)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (A L : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ S : FlattenedSourceSelection M H W A L δ ε,
      ∀ n, support (S.cutoff n) ⊆ ball 0 C := by
  classical
  obtain ⟨b,z,K,_,hb,hz,hK,hcover⟩ := M.exists_priority_source_data hsard hsch hG hconn hinf hTD hB hne
  have hex (i : Fin m) := exists_compact_value_flattening hcoarea
    (isOpen_physicalPlaneDomain hG) (hu i) (hs i) (W i)
    (C := range (fun n => sphereFromPlaneFunction (u i) (b n : Sphere))) (countable_range _) hδ hε
  choose O WO hO hCO hOc hOs hOclose hOerror hOzero using hex
  obtain ⟨V,WV,hV,hCV,_,hVclose,hVerror,_,_⟩ := H.exists_local_value_flattening hcoarea A
    (C := range (fun n => M.heightSection H (b n : Sphere))) (countable_range _) hδ hε
  obtain ⟨N,hN,hOld,hHeight⟩ := M.exists_common_flattened_neighborhoods hsard hsch
    hG hconn hinf hTD hu H hHz b O hO V hV
    (fun n i => hCO i (mem_range_self n)) (fun n => hCV (mem_range_self n))
  obtain ⟨r,χ,hr,hrt,hrN,hχ,hPc,hPe,hPerror,hSerror⟩ :=
    M.exists_horizontal_priority_with_support hsard hsch hG hconn hinf hTD
      b hb z hz hcover hK (fun n => N n ∩ ball 0 C)
      (fun n => ((hN n).1.inter isOpen_ball).mem_nhds ⟨(hN n).2, hC (hb n)⟩) L hε
  refine ⟨{
    oldValues := O, old_open := hO, oldWitness := WO, old_close := hOclose, old_error := hOerror
    heightValues := V, height_open := hV, heightWitness := WV, height_close := hVclose
    height_error := hVerror
    center := b, center_outside := hb, target := z, target_projection := hz, radius := r, radius_pos := hr, radius_tendsto := hrt
    cutoff := χ, cutoff_smooth := fun n => (hχ n).1
    cutoff_support := fun n => (subset_tsupport _).trans (hχ n).2.2.1
    cutoff_unit := fun n => (hχ n).2.2.2.1
    value := fun n => (finiteCoord (z n)).re, value_eq := fun _ => rfl
    priority_continuous := hPc, priority_error_memLp := hPe
    priority_error := hPerror, support_error := hSerror
    old_constant := ?_, height_constant := ?_ }, ?_⟩
  · intro i n
    refine ⟨flattenValues (O i) (sphereFromPlaneFunction (u i) (b n : Sphere)), ?_⟩
    intro x hx
    exact hOld n i (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx.2))).1
  · intro n
    refine ⟨flattenValues V (M.heightSection H (b n : Sphere)), ?_⟩
    intro x hx
    exact hHeight n (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx.2))).1

  · intro n x hx
    exact (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx))).2

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
