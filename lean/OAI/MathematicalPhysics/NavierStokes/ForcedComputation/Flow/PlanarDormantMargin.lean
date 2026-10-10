import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDormantZero
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PulsePlateau

namespace OAI

/-! Quantitative clearance for unused pulses. The enlarged rational collar
leaves room for perturbing an entire source rectangle by a positive radius. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian Set

theorem routingCollar_four_small (M : Alternating.Machine) (hM : M.WellFormed) :
    2 * (4 * routingCollar M hM) < 1 / 4 ∧
      2 * (4 * routingCollar M hM) < 1 / 24 ∧
      2 * (4 * routingCollar M hM) < parkingScale (geometricBranches M hM).length := by
  have h := routingCollar_parking_bound M hM
  have hp := parkingScale_pos (geometricBranches M hM).length
  have hu := parkingScale_le (geometricBranches M hM).length
  constructor
  · linarith
  constructor <;> linarith

theorem ordered_source_four_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM))
    (horder : sourceRank M hM c < sourceRank M hM b) :
    ∃ g : ℚ, 2 * (4 * routingCollar M hM) < g ∧
      EndpointGap g (⟨c, .extractHorizontal⟩ : Action M hM).rectangle
        (instruction M hM b).source := by
  have h := source_extraction_clearance M hM horder (parkingFor M hM c 0)
    (by simpa only [sourceRank_get] using (centers_before_parking M hM c).1)
  have hne : c ≠ b := fun he => (ne_of_lt horder) (congrArg (sourceRank M hM) he)
  have hg := source_branch_gap M hM hne
  have hδ := routingCollar_pos M hM
  refine ⟨boxGap (instruction M hM c).source (instruction M hM b).source, ?_, ?_⟩
  · linarith
  · change EndpointGap _ (translationTube (instruction M hM c).source
      (horizontalCenter (instruction M hM c).source (parkingFor M hM c 0))) _
    simpa only [sourceRank_get] using h.1

theorem ordered_target_four_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM))
    (horder : targetRank M hM b < targetRank M hM c) :
    ∃ g : ℚ, 2 * (4 * routingCollar M hM) < g ∧
      EndpointGap g (⟨c, .insertHorizontal⟩ : Action M hM).rectangle
        (instruction M hM b).target := by
  have h := target_insertion_clearance M hM horder (parkingFor M hM c 0)
    (by simpa only [targetRank_get] using (centers_before_parking M hM c).2)
  have hne : c ≠ b := fun he => (ne_of_gt horder) (congrArg (targetRank M hM) he)
  have hg := target_branch_gap M hM hne
  have hδ := routingCollar_pos M hM
  refine ⟨boxGap (instruction M hM c).target (instruction M hM b).target, ?_, ?_⟩
  · linarith
  · change EndpointGap _
      (translationTube (recenter (instruction M hM c).target
        (horizontalCenter (instruction M hM c).target (parkingFor M hM c 0)))
        (centerQ (instruction M hM c).target)) _
    rw [translationTube_reverse]
    simpa only [targetRank_get] using h.1

theorem extractHorizontal_sparse_four_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 2 * (sourceRank M hM c).val = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .extractHorizontal⟩ : Action M hM).rectangle (4 * routingCollar M hM)).carrier := by
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
  have hs := routingCollar_four_small M hM
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hps := parkedSource_mem M hM b hx
  have hpt := parkedTarget_mem M hM b hx
  have hn : sourceRank M hM c ≠ sourceRank M hM b := fun h => hne (sourceRank_injective M hM h)
  rcases lt_or_gt_of_ne hn with ho | ho
  · have hv := extract_before_arithmetic (e := 0) ho (by decide) (by simpa only [Nat.add_zero] using hidx)
    have hw : i ≤ (branchIndices M hM b 0).val := by rw [h0]; exact hv
    obtain ⟨g, hg, hgap⟩ := ordered_source_four_gap M hM b c ho
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

theorem extractVertical_sparse_four_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 2 * (sourceRank M hM c).val + 1 = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .extractVertical⟩ : Action M hM).rectangle (4 * routingCollar M hM)).carrier := by
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
  have hs := routingCollar_four_small M hM
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

theorem scale_sparse_four_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (k : Fin 4) (i : ℕ)
    (hidx : 2 * (geometricBranches M hM).length + 4 * (branchIndex M hM c).val + k.val = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .scale k⟩ : Action M hM).rectangle (4 * routingCollar M hM)).carrier := by
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
  have hs := routingCollar_four_small M hM
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

theorem insertVertical_sparse_four_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 6 * (geometricBranches M hM).length + 2 * (targetRank M hM c).val = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .insertVertical⟩ : Action M hM).rectangle (4 * routingCollar M hM)).carrier := by
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
  have hs := routingCollar_four_small M hM
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

theorem insertHorizontal_sparse_four_zero (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (i : ℕ)
    (hidx : 6 * (geometricBranches M hM).length + 2 * (targetRank M hM c).val + 1 = i) (hne : c ≠ b)
    (_hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, .insertHorizontal⟩ : Action M hM).rectangle (4 * routingCollar M hM)).carrier := by
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
  have hs := routingCollar_four_small M hM
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
    obtain ⟨g, hg, hgap⟩ := ordered_target_four_gap M hM b c ho
    apply notMem_collar_of_gap hgap hg
    rw [sparseAnchor_target M hM b x hw]
    exact ht

theorem action_sparseAnchor_notMem_four_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (phase : Phase) (i : ℕ)
    (hidx : (⟨c, phase⟩ : Action M hM).index = i) (hne : c ≠ b)
    (hi : ∀ k, (branchIndices M hM b k).val ≠ i) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i ∉
      (rectangleCollar (⟨c, phase⟩ : Action M hM).rectangle (4 * routingCollar M hM)).carrier := by
  cases phase with
  | extractHorizontal => exact extractHorizontal_sparse_four_zero M hM b c hx i hidx hne hi
  | extractVertical => exact extractVertical_sparse_four_zero M hM b c hx i hidx hne hi
  | scale k => exact scale_sparse_four_zero M hM b c hx k i hidx hne hi
  | insertVertical => exact insertVertical_sparse_four_zero M hM b c hx i hidx hne hi
  | insertHorizontal => exact insertHorizontal_sparse_four_zero M hM b c hx i hidx hne hi

theorem sparseAnchor_notMem_four_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier)
    (i : Fin (actions M hM).length)
    (hi : ∀ k, (branchIndices M hM b k).val ≠ i.val) :
    sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i.val ∉
      (rectangleCollar (compiledPulse M hM i).rectangle (4 * (compiledPulse M hM i).collar)).carrier := by
  exact action_sparseAnchor_notMem_four_collar M hM b ((actions M hM).get i).owner hx
    ((actions M hM).get i).phase i.val (Action.index_get M hM i) (unused_owner_ne M hM b i hi) hi

end ForcedComputation.Recorder.Planar

namespace ForcedComputation.PlanarHamiltonian

open ShearFlows Set

/-- Exclusion from the enlarged closed collar persists under a small displacement. -/
theorem notMem_collar_of_notMem_four {R : RationalBox 2} {δ : ℚ}
    (hδ : 0 < δ) {x y : Plane}
    (hx : x ∉ (rectangleCollar R (4 * δ)).carrier)
    (hxy : dist y x < (δ : ℝ)) : y ∉ (rectangleCollar R δ).carrier := by
  intro hy
  apply hx
  intro j
  have hj : |y j - x j| < (δ : ℝ) :=
    (norm_le_pi_norm (y - x) j).trans_lt (by simpa only [dist_eq_norm] using hxy)
  obtain ⟨hj₀, hj₁⟩ := abs_lt.mp hj
  have hp : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hyj := hy j
  dsimp [rectangleCollar] at hyj ⊢
  push_cast at hyj ⊢
  constructor <;> linarith [hyj.1, hyj.2]

end ForcedComputation.PlanarHamiltonian

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian Set

/-- An unused pulse remains zero on a full neighborhood of the current anchor. -/
theorem sparseAnchor_near_notMem_collar (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x y : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier)
    (i : Fin (actions M hM).length)
    (hi : ∀ k, (branchIndices M hM b k).val ≠ i.val)
    (hxy : dist y (sparseAnchor (branchIndices M hM b) (branchAnchors M hM b x) i.val) <
      (routingCollar M hM : ℝ)) :
    y ∉ (rectangleCollar (compiledPulse M hM i).rectangle (compiledPulse M hM i).collar).carrier := by
  exact notMem_collar_of_notMem_four (compiledPulse_valid M hM i).1
    (sparseAnchor_notMem_four_collar M hM b hx i hi) hxy

end ForcedComputation.Recorder.Planar

end

end OAI
