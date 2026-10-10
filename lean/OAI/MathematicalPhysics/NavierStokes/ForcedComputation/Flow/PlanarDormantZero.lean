import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDormantAnchors

namespace OAI

/-! Every pulse that does not belong to the tracked branch vanishes at its
current sparse anchor. The proof uses the actual order of the compiled list. -/

noncomputable section
namespace ForcedComputation.PlanarRouting

open ShearFlows Set PlanarHamiltonian

theorem notMem_collar_of_gap {R S : RationalBox 2} {gap δ : ℚ}
    (hg : EndpointGap gap R S) (hδ : 2 * δ < gap) {x : Plane} (hx : x ∈ S.carrier) :
    x ∉ (rectangleCollar R δ).carrier :=
  fun h => Set.disjoint_left.mp (collar_disjoint_of_gap hg hδ) h hx

theorem extract_before_arithmetic {c b e i : ℕ} (hc : c < b) (he : e ≤ 1)
    (hi : 2 * c + e = i) : i ≤ 2 * b := by omega

theorem extract_after_arithmetic {n c b d e i : ℕ} (hb : b < c) (hc : c < n)
    (he : e ≤ 1) (hi : 2 * c + e = i) :
    2 * b + 1 + 1 ≤ i ∧ i ≤ 2 * n + 4 * d := by omega

theorem scale_before_arithmetic {n s c b e i : ℕ} (hs : s < n) (hc : c < b)
    (he : e < 4) (hi : 2 * n + 4 * c + e = i) :
    2 * s + 1 + 1 ≤ i ∧ i ≤ 2 * n + 4 * b := by omega

theorem scale_after_arithmetic {n c b t e i : ℕ} (hb : b < c) (hc : c < n)
    (he : e < 4) (hi : 2 * n + 4 * c + e = i) :
    2 * n + 4 * b + 3 + 1 ≤ i ∧ i ≤ 6 * n + 2 * t := by omega

theorem insert_before_arithmetic {n d c b e i : ℕ} (hd : d < n) (hc : c < b)
    (he : e ≤ 1) (hi : 6 * n + 2 * c + e = i) :
    2 * n + 4 * d + 3 + 1 ≤ i ∧ i ≤ 6 * n + 2 * b := by omega

theorem insert_after_arithmetic {n c b e i : ℕ} (hb : b < c)
    (hi : 6 * n + 2 * c + e = i) : 6 * n + 2 * b + 1 + 1 ≤ i := by omega

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian Set

theorem sourceRank_injective (M : Alternating.Machine) (hM : M.WellFormed) :
    Function.Injective (sourceRank M hM) := by
  intro b c h
  have he := congrArg (fun i => (sourceOrder M hM).get i) h
  simpa only [sourceRank_get] using he

theorem targetRank_injective (M : Alternating.Machine) (hM : M.WellFormed) :
    Function.Injective (targetRank M hM) := by
  intro b c h
  have he := congrArg (fun i => (targetOrder M hM).get i) h
  simpa only [targetRank_get] using he

theorem centers_before_parking (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    centerQ (instruction M hM b).source 0 ≤ parkingFor M hM b 0 ∧
      centerQ (instruction M hM b).target 0 ≤ parkingFor M hM b 0 := by
  have hp := (parkingCenter_bounds (geometricBranches M hM).length (branchIndex M hM b)).1
  have hs := centerQ_between (instruction_source_positive M hM b)
    (instruction_endpoint_bounds M hM b).1 0
  have ht := centerQ_between (instruction_target_positive M hM b)
    (instruction_endpoint_bounds M hM b).2 0
  change (1 / 2 : ℚ) < parkingFor M hM b 0 at hp
  constructor <;> linarith

theorem ordered_source_collar_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM))
    (horder : sourceRank M hM c < sourceRank M hM b) :
    ∃ g : ℚ, 2 * routingCollar M hM < g ∧
      EndpointGap g (⟨c, .extractHorizontal⟩ : Action M hM).rectangle
        (instruction M hM b).source := by
  have h := source_extraction_clearance M hM horder (parkingFor M hM c 0)
    (by simpa only [sourceRank_get] using (centers_before_parking M hM c).1)
  refine ⟨boxGap (instruction M hM c).source (instruction M hM b).source, ?_, ?_⟩
  · simpa only [sourceRank_get] using h.2
  · change EndpointGap _ (translationTube (instruction M hM c).source
      (horizontalCenter (instruction M hM c).source (parkingFor M hM c 0))) _
    simpa only [sourceRank_get] using h.1

theorem ordered_target_collar_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM))
    (horder : targetRank M hM b < targetRank M hM c) :
    ∃ g : ℚ, 2 * routingCollar M hM < g ∧
      EndpointGap g (⟨c, .insertHorizontal⟩ : Action M hM).rectangle
        (instruction M hM b).target := by
  have h := target_insertion_clearance M hM horder (parkingFor M hM c 0)
    (by simpa only [targetRank_get] using (centers_before_parking M hM c).2)
  refine ⟨boxGap (instruction M hM c).target (instruction M hM b).target, ?_, ?_⟩
  · simpa only [targetRank_get] using h.2
  · change EndpointGap _
      (translationTube (recenter (instruction M hM c).target
        (horizontalCenter (instruction M hM c).target (parkingFor M hM c 0)))
        (centerQ (instruction M hM c).target)) _
    rw [translationTube_reverse]
    simpa only [targetRank_get] using h.1

theorem extractHorizontal_sparse_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 2 * (sourceRank M hM c).val = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .extractHorizontal⟩ : Action M hM).rectangle (routingCollar M hM)).carrier := by
  have h0 : (branchIndices M hM b 0).val = 2 * (sourceRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (0 : Fin 8)
  have h1 : (branchIndices M hM b 1).val = 2 * (sourceRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (1 : Fin 8)
  have h2 : (branchIndices M hM b 2).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (2 : Fin 8)
  have h5 : (branchIndices M hM b 5).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 3 := by
    exact congrFun (branchIndices_values M hM b) (5 : Fin 8)
  have h6 : (branchIndices M hM b 6).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (6 : Fin 8)
  have h7 : (branchIndices M hM b 7).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (7 : Fin 8)
  have hsb := (sourceRank M hM b).isLt
  have hsc := (sourceRank M hM c).isLt
  have htb := (targetRank M hM b).isLt
  have htc := (targetRank M hM c).isLt
  have hbb := (branchIndex M hM b).isLt
  have hbc := (branchIndex M hM c).isLt
  have hsl := (sourceOrder_perm M hM).length_eq
  have htl := (targetOrder_perm M hM).length_eq
  have hs := routingCollar_small M hM
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hps := parkedSource_mem M hM b hx
  have hpt := parkedTarget_mem M hM b hx
  have hn : sourceRank M hM c ≠ sourceRank M hM b := fun h => hne (sourceRank_injective M hM h)
  rcases lt_or_gt_of_ne hn with ho | ho
  · have hv := extract_before_arithmetic (e := 0) ho (by decide) (by simpa only [Nat.add_zero] using hidx)
    have hw : i ≤ (branchIndices M hM b 0).val := by rw [h0]; exact hv
    obtain ⟨g, hg, hgap⟩ := ordered_source_collar_gap M hM b c ho
    apply notMem_collar_of_gap hgap hg
    rw [sparseAnchor_source M hM b x hw]
    exact hx
  · have hc : (sourceRank M hM c).val < (geometricBranches M hM).length := by simpa only [hsl] using hsc
    have hv := extract_after_arithmetic (d := (branchIndex M hM b).val) (e := 0) ho hc (by decide)
      (by simpa only [Nat.add_zero] using hidx)
    have hlo : (branchIndices M hM b 1).val + 1 ≤ i := by rw [h1]; exact hv.1
    have hhi : i ≤ (branchIndices M hM b 2).val := by rw [h2]; exact hv.2
    apply notMem_collar_of_gap (extractHorizontal_parking_gap M hM c b) hs.1
    rw [sparseAnchor_parkedSource M hM b x hlo hhi]
    exact hps

theorem extractVertical_sparse_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 2 * (sourceRank M hM c).val + 1 = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .extractVertical⟩ : Action M hM).rectangle (routingCollar M hM)).carrier := by
  have h0 : (branchIndices M hM b 0).val = 2 * (sourceRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (0 : Fin 8)
  have h1 : (branchIndices M hM b 1).val = 2 * (sourceRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (1 : Fin 8)
  have h2 : (branchIndices M hM b 2).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (2 : Fin 8)
  have h5 : (branchIndices M hM b 5).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 3 := by
    exact congrFun (branchIndices_values M hM b) (5 : Fin 8)
  have h6 : (branchIndices M hM b 6).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (6 : Fin 8)
  have h7 : (branchIndices M hM b 7).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (7 : Fin 8)
  have hsb := (sourceRank M hM b).isLt
  have hsc := (sourceRank M hM c).isLt
  have htb := (targetRank M hM b).isLt
  have htc := (targetRank M hM c).isLt
  have hbb := (branchIndex M hM b).isLt
  have hbc := (branchIndex M hM c).isLt
  have hsl := (sourceOrder_perm M hM).length_eq
  have htl := (targetOrder_perm M hM).length_eq
  have hs := routingCollar_small M hM
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hps := parkedSource_mem M hM b hx
  have hpt := parkedTarget_mem M hM b hx
  have hn : sourceRank M hM c ≠ sourceRank M hM b := fun h => hne (sourceRank_injective M hM h)
  rcases lt_or_gt_of_ne hn with ho | ho
  · have hv := extract_before_arithmetic ho (by decide : (1 : ℕ) ≤ 1) hidx
    have hw : i ≤ (branchIndices M hM b 0).val := by rw [h0]; exact hv
    apply notMem_collar_of_gap (extractVertical_source_gap M hM c b) hs.2.1
    rw [sparseAnchor_source M hM b x hw]
    exact hx
  · have hc : (sourceRank M hM c).val < (geometricBranches M hM).length := by simpa only [hsl] using hsc
    have hv := extract_after_arithmetic (d := (branchIndex M hM b).val) ho hc (by decide : (1 : ℕ) ≤ 1) hidx
    have hlo : (branchIndices M hM b 1).val + 1 ≤ i := by rw [h1]; exact hv.1
    have hhi : i ≤ (branchIndices M hM b 2).val := by rw [h2]; exact hv.2
    apply notMem_collar_of_gap (extractVertical_parking_gap M hM hne) hs.2.2
    rw [sparseAnchor_parkedSource M hM b x hlo hhi]
    exact hps

theorem scale_sparse_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (k : Fin 4) (i : ℕ)
    (hidx : 2 * (geometricBranches M hM).length + 4 * (branchIndex M hM c).val + k.val = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .scale k⟩ : Action M hM).rectangle (routingCollar M hM)).carrier := by
  have h0 : (branchIndices M hM b 0).val = 2 * (sourceRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (0 : Fin 8)
  have h1 : (branchIndices M hM b 1).val = 2 * (sourceRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (1 : Fin 8)
  have h2 : (branchIndices M hM b 2).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (2 : Fin 8)
  have h5 : (branchIndices M hM b 5).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 3 := by
    exact congrFun (branchIndices_values M hM b) (5 : Fin 8)
  have h6 : (branchIndices M hM b 6).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (6 : Fin 8)
  have h7 : (branchIndices M hM b 7).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (7 : Fin 8)
  have hsb := (sourceRank M hM b).isLt
  have hsc := (sourceRank M hM c).isLt
  have htb := (targetRank M hM b).isLt
  have htc := (targetRank M hM c).isLt
  have hbb := (branchIndex M hM b).isLt
  have hbc := (branchIndex M hM c).isLt
  have hsl := (sourceOrder_perm M hM).length_eq
  have htl := (targetOrder_perm M hM).length_eq
  have hs := routingCollar_small M hM
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hps := parkedSource_mem M hM b hx
  have hpt := parkedTarget_mem M hM b hx
  have hn : branchIndex M hM c ≠ branchIndex M hM b := fun h => hne (branchIndex_injective M hM h)
  rcases lt_or_gt_of_ne hn with ho | ho
  · have hb : (sourceRank M hM b).val < (geometricBranches M hM).length := by simpa only [hsl] using hsb
    have hv := scale_before_arithmetic hb ho k.isLt hidx
    have hlo : (branchIndices M hM b 1).val + 1 ≤ i := by rw [h1]; exact hv.1
    have hhi : i ≤ (branchIndices M hM b 2).val := by rw [h2]; exact hv.2
    apply notMem_collar_of_gap (scaling_parking_gap M hM hne k) hs.2.2
    rw [sparseAnchor_parkedSource M hM b x hlo hhi]
    exact hps
  · have hv := scale_after_arithmetic (t := (targetRank M hM b).val) ho hbc k.isLt hidx
    have hlo : (branchIndices M hM b 5).val + 1 ≤ i := by rw [h5]; exact hv.1
    have hhi : i ≤ (branchIndices M hM b 6).val := by rw [h6]; exact hv.2
    apply notMem_collar_of_gap (scaling_parking_gap M hM hne k) hs.2.2
    rw [sparseAnchor_parkedTarget M hM b x hlo hhi]
    exact hpt

theorem insertVertical_sparse_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 6 * (geometricBranches M hM).length + 2 * (targetRank M hM c).val = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .insertVertical⟩ : Action M hM).rectangle (routingCollar M hM)).carrier := by
  have h0 : (branchIndices M hM b 0).val = 2 * (sourceRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (0 : Fin 8)
  have h1 : (branchIndices M hM b 1).val = 2 * (sourceRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (1 : Fin 8)
  have h2 : (branchIndices M hM b 2).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (2 : Fin 8)
  have h5 : (branchIndices M hM b 5).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 3 := by
    exact congrFun (branchIndices_values M hM b) (5 : Fin 8)
  have h6 : (branchIndices M hM b 6).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (6 : Fin 8)
  have h7 : (branchIndices M hM b 7).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (7 : Fin 8)
  have hsb := (sourceRank M hM b).isLt
  have hsc := (sourceRank M hM c).isLt
  have htb := (targetRank M hM b).isLt
  have htc := (targetRank M hM c).isLt
  have hbb := (branchIndex M hM b).isLt
  have hbc := (branchIndex M hM c).isLt
  have hsl := (sourceOrder_perm M hM).length_eq
  have htl := (targetOrder_perm M hM).length_eq
  have hs := routingCollar_small M hM
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hps := parkedSource_mem M hM b hx
  have hpt := parkedTarget_mem M hM b hx
  have hn : targetRank M hM c ≠ targetRank M hM b := fun h => hne (targetRank_injective M hM h)
  rcases lt_or_gt_of_ne hn with ho | ho
  · have hv := insert_before_arithmetic (e := 0) hbb ho (by decide) (by simpa only [Nat.add_zero] using hidx)
    have hlo : (branchIndices M hM b 5).val + 1 ≤ i := by rw [h5]; exact hv.1
    have hhi : i ≤ (branchIndices M hM b 6).val := by rw [h6]; exact hv.2
    apply notMem_collar_of_gap (insertVertical_parking_gap M hM hne) hs.2.2
    rw [sparseAnchor_parkedTarget M hM b x hlo hhi]
    exact hpt
  · have hv := insert_after_arithmetic (e := 0) ho (by simpa only [Nat.add_zero] using hidx)
    have hw : (branchIndices M hM b 7).val + 1 ≤ i := by rw [h7]; exact hv
    apply notMem_collar_of_gap (insertVertical_target_gap M hM c b) hs.2.1
    rw [sparseAnchor_target M hM b x hw]
    exact ht

theorem insertHorizontal_sparse_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 6 * (geometricBranches M hM).length + 2 * (targetRank M hM c).val + 1 = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .insertHorizontal⟩ : Action M hM).rectangle (routingCollar M hM)).carrier := by
  have h0 : (branchIndices M hM b 0).val = 2 * (sourceRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (0 : Fin 8)
  have h1 : (branchIndices M hM b 1).val = 2 * (sourceRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (1 : Fin 8)
  have h2 : (branchIndices M hM b 2).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (2 : Fin 8)
  have h5 : (branchIndices M hM b 5).val =
      2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 3 := by
    exact congrFun (branchIndices_values M hM b) (5 : Fin 8)
  have h6 : (branchIndices M hM b 6).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val := by
    exact congrFun (branchIndices_values M hM b) (6 : Fin 8)
  have h7 : (branchIndices M hM b 7).val =
      6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val + 1 := by
    exact congrFun (branchIndices_values M hM b) (7 : Fin 8)
  have hsb := (sourceRank M hM b).isLt
  have hsc := (sourceRank M hM c).isLt
  have htb := (targetRank M hM b).isLt
  have htc := (targetRank M hM c).isLt
  have hbb := (branchIndex M hM b).isLt
  have hbc := (branchIndex M hM c).isLt
  have hsl := (sourceOrder_perm M hM).length_eq
  have htl := (targetOrder_perm M hM).length_eq
  have hs := routingCollar_small M hM
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hps := parkedSource_mem M hM b hx
  have hpt := parkedTarget_mem M hM b hx
  have hn : targetRank M hM c ≠ targetRank M hM b := fun h => hne (targetRank_injective M hM h)
  rcases lt_or_gt_of_ne hn with ho | ho
  · have hv := insert_before_arithmetic hbb ho (by decide : (1 : ℕ) ≤ 1) hidx
    have hlo : (branchIndices M hM b 5).val + 1 ≤ i := by rw [h5]; exact hv.1
    have hhi : i ≤ (branchIndices M hM b 6).val := by rw [h6]; exact hv.2
    apply notMem_collar_of_gap (insertHorizontal_parking_gap M hM c b) hs.1
    rw [sparseAnchor_parkedTarget M hM b x hlo hhi]
    exact hpt
  · have hv := insert_after_arithmetic ho hidx
    have hw : (branchIndices M hM b 7).val + 1 ≤ i := by rw [h7]; exact hv
    obtain ⟨g, hg, hgap⟩ := ordered_target_collar_gap M hM b c ho
    apply notMem_collar_of_gap hgap hg
    rw [sparseAnchor_target M hM b x hw]
    exact ht

theorem action_sparseAnchor_notMem_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (phase : Phase) (i : ℕ)
    (hidx : (⟨c, phase⟩ : Action M hM).index = i) (hne : c ≠ b)
    (hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, phase⟩ : Action M hM).rectangle (routingCollar M hM)).carrier := by
  cases phase with
  | extractHorizontal => exact extractHorizontal_sparse_zero M hM b c hx i hidx hne hi
  | extractVertical => exact extractVertical_sparse_zero M hM b c hx i hidx hne hi
  | scale k => exact scale_sparse_zero M hM b c hx k i hidx hne hi
  | insertVertical => exact insertVertical_sparse_zero M hM b c hx i hidx hne hi
  | insertHorizontal => exact insertHorizontal_sparse_zero M hM b c hx i hidx hne hi

theorem sparseAnchor_notMem_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier)
    (i : Fin (actions M hM).length)
    (hi : ∀ k, (branchIndices M hM b k).val ≠ i.val) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i.val ∉
      (rectangleCollar (compiledPulse M hM i).rectangle (compiledPulse M hM i).collar).carrier := by
  exact action_sparseAnchor_notMem_collar M hM b ((actions M hM).get i).owner hx
    ((actions M hM).get i).phase i.val (Action.index_get M hM i) (unused_owner_ne M hM b i hi) hi

end ForcedComputation.Recorder.Planar

end

end OAI
