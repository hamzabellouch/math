import OAI.Analysis.CircleDomains.Transfer.ModelPrioritySupport
import OAI.Analysis.CircleDomains.Transfer.ModelPriorityData
import OAI.Analysis.CircleDomains.Topology.ModelFlattenedNeighborhoods
import OAI.Analysis.CircleDomains.Topology.CompactValueFlattening
import OAI.Analysis.CircleDomains.Selection.LocalHeightFlattening

namespace OAI

/-! Simultaneous selection of the actual old-test flattenings, height
flattening, and small-support horizontal priority coordinate. All fields
are constructed from the existing model and the stated energy budgets. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 structure FlattenedSourceSelection (M : CompactScalarModel G u) {R d : ℝ}
    (H : ControlledHeight R d)
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (A L δ ε : ℝ) where
  oldValues : Fin m → Set ℝ
  old_open : ∀ i, IsOpen (oldValues i)
  oldWitness : ∀ i, DeGiorgi.MemW1pWitness 2 (flattenValues (oldValues i) ∘ u i) (physicalPlaneDomain G)
  old_close : ∀ i t, |flattenValues (oldValues i) t-t| < δ
  old_error : ∀ i, (∫⁻ x in physicalPlaneDomain G,
    ENNReal.ofReal (‖(oldWitness i).weakGrad x-(W i).weakGrad x‖^2)) < ENNReal.ofReal ε
  heightValues : Set ℝ
  height_open : IsOpen heightValues
  heightWitness : DeGiorgi.MemW1pWitness 2
    (flattenValues heightValues ∘ H.height ∘ complexPlaneCoordinates) (ball 0 A)
  height_close : ∀ t, |flattenValues heightValues t-t| < δ
  height_error : (∫⁻ x in ball 0 A,
    ENNReal.ofReal (‖heightWitness.weakGrad x-heightLimitGradient H.error₀ H.error₁ x‖^2)) < ENNReal.ofReal ε
  center : ℕ → ℂ
  center_outside : ∀ n, (center n : Sphere) ∉ G
  target : ℕ → Sphere
  target_projection : ∀ n, M.projection (target n) = (center n : Sphere)
  radius : ℕ → ℝ
  radius_pos : ∀ n, 0 < radius n
  radius_tendsto : Tendsto radius atTop (𝓝 0)
  cutoff : ℕ → ℂ → ℝ
  cutoff_smooth : ∀ n, ContDiff ℝ ∞ (cutoff n)
  cutoff_support : ∀ n, support (cutoff n) ⊆ ball (center n) (radius n)
  cutoff_unit : ∀ n z, cutoff n z ∈ Icc (0 : ℝ) 1
  value : ℕ → ℝ
  value_eq : ∀ n, value n = (finiteCoord (target n)).re
  priority_continuous : Continuous (fun z : ℂ => priorityInfiniteValue
    (fun n => cutoff n z) value (M.horizontalSection (z : Sphere)))
  priority_error_memLp : MemLp (fun z : ℂ => fderiv ℝ
    (fun w : ℂ => priorityInfiniteValue (fun n => cutoff n w) value (M.horizontalSection (w : Sphere))) z-
    fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z)
    2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L))
  priority_error : (eLpNorm (fun z : ℂ => fderiv ℝ
    (fun w : ℂ => priorityInfiniteValue (fun n => cutoff n w) value (M.horizontalSection (w : Sphere))) z-
    fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z)
    2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L))).toReal < ε
  support_error : (eLpNorm ((⋃ n, support (cutoff n)).indicator
    (fun z => ‖fderiv ℝ (fun w : ℂ => M.horizontalSection (w : Sphere)) z‖))
    2 (volume.restrict ({z : ℂ | (z : Sphere) ∈ G} ∩ ball 0 L))).toReal < ε
  old_constant : ∀ i n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (cutoff n),
    flattenValues (oldValues i) (sphereFromPlaneFunction (u i) (z : Sphere)) = a
  height_constant : ∀ n, ∃ a : ℝ, ∀ z ∈ {z : ℂ | (z : Sphere) ∉ G} ∩ support (cutoff n),
    flattenValues heightValues (M.heightSection H (z : Sphere)) = a

 theorem exists_flattened_source_selection (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hcoarea : PlanarSobolevCoarea)
    (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {z : ℂ | (z : Sphere) ∉ G})
    (hne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (A L : ℝ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    Nonempty (FlattenedSourceSelection M H W A L δ ε) := by
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
      b hb z hz hcover hK N (fun n => (hN n).1.mem_nhds (hN n).2) L hε
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
    old_constant := ?_, height_constant := ?_ }⟩
  · intro i n
    refine ⟨flattenValues (O i) (sphereFromPlaneFunction (u i) (b n : Sphere)), ?_⟩
    intro x hx
    exact hOld n i (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx.2)))
  · intro n
    refine ⟨flattenValues V (M.heightSection H (b n : Sphere)), ?_⟩
    intro x hx
    exact hHeight n (hrN n ((hχ n).2.2.1 (subset_tsupport _ hx.2)))

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
