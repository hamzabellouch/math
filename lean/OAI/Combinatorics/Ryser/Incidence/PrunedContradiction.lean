import OAI.Combinatorics.Ryser.Incidence.FourAnchors
import OAI.Combinatorics.Ryser.Incidence.CoordinateTransfer
import OAI.Combinatorics.Ryser.Geometry.Normalization
import OAI.Combinatorics.Ryser.Incidence.WalkQuotients
import OAI.Combinatorics.Ryser.Incidence.GraphParameters
import OAI.Combinatorics.Ryser.Incidence.ExtractedContradiction

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open scoped Pointwise
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pruned_incidence_impossible
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (r U : ℝ) (hr : 0 < r) (hrq : r ^ 2 = (Fintype.card F : ℝ))
    (hU : 2 ≤ U) (hlarge : 4096 * U ^ 7 ≤ r)
    (hremove : (96 / witnessConstant) * U ^ 42 ≤ r)
    (hfirst : 32 * (graphScale U) ^ 2 * (expansionScale (graphScale U)) ^ 127942 < 3 * r)
    (hsecond : 4096 * (graphScale U) ^ 6 * (expansionScale (graphScale U)) ^ 3 < 27 * r)
    (hthird : 2 * (expansionScale (graphScale U)) ^ 527 * graphScale U ≤ r)
    (hproper : ∀ M : Subfield F, M ≠ ⊤ →
      (Nat.card M : ℝ) ^ 3 ≤ (Fintype.card F : ℝ))
    (hPlo : r ^ 2 / (32 * U ^ 4) ≤ (P.card : ℝ))
    (hPup : (P.card : ℝ) ≤ U * r ^ 2)
    (hLup : (L.card : ℝ) ≤ U * r ^ 2)
    (hpoints : ∀ p ∈ P, r / (8 * U ^ 2) ≤
      ((L.filter fun l => ProjectiveIncidence p l).card : ℝ))
    (hlines : ∀ l ∈ L, r / (8 * U ^ 2) ≤
      ((P.filter fun p => ProjectiveIncidence p l).card : ℝ))
    (hmax : ∀ p ∈ P, ((L.filter fun l => ProjectiveIncidence p l).card : ℝ) ≤
      16 * U ^ 3 * r)
    (hcap : ∀ l, ((P.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤
      16 * U ^ 3 * r) : False := by
  classical
  obtain ⟨c, hc, hwitnesses⟩ := fourAnchors_of_pruned_r P L hr hU hlarge
    hPlo hPup hLup hpoints hlines (fun l _ => hcap l)
  rcases c with ⟨ell, triple, p4⟩
  rcases triple with ⟨p1, p2, p3⟩
  obtain ⟨hell, hp1, hp2, hp3, hp4, hi1, hi2, hi3, hnot4, h21, h31, h32⟩ :=
    (mem_anchorConfigurations ProjectiveIncidence P L
      ⟨ell, (⟨p1, p2, p3⟩, p4)⟩).mp hc
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ :=
    exists_projectiveTransform_normalization h21.symm h31.symm h32.symm hi1 hi2 hi3 hnot4
  let W := anchorWitnesses ProjectiveIncidence P L ⟨ell, (⟨p1, p2, p3⟩, p4)⟩
  have hWP : W ⊆ P := by
    intro w hw
    exact (Finset.mem_filter.mp hw).1
  have hj {w p : ProjectivePoint F}
      (h : p ∈ joinedNeighbors ProjectiveIncidence P L w) :
      ∃ l ∈ L, ProjectiveIncidence p l ∧ ProjectiveIncidence w l := by
    simp only [joinedNeighbors, Finset.mem_filter] at h
    obtain ⟨_, _, l, hl, hwl, hpl⟩ := h
    exact ⟨l, hl, hpl, hwl⟩
  have hjoins (w : ProjectivePoint F) (hw : w ∈ W) :
      (∃ l ∈ L, ProjectiveIncidence p1 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p2 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p3 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p4 l ∧ ProjectiveIncidence w l) := by
    have hh := (Finset.mem_filter.mp hw).2
    exact ⟨hj hh.1, hj hh.2.1, hj hh.2.2.1, hj hh.2.2.2⟩
  obtain ⟨hretained, hnonzero, hleft, hright, hdiff, hquot⟩ :=
    coordinate_transfer P W L T p1 p2 p3 p4 (16 * U ^ 3 * r) hWP hcap
      (fun p hp => hmax p hp) hp1 hp2 hp3 hp4 hT1 hT2 hT3 hT4 hjoins
  let G := coordinateGraph T W
  let A := G.image Prod.fst
  let B := G.image Prod.snd
  let V := graphScale U
  let K := expansionScale V
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hVpos : 0 < V := graphScale_pos hUpos
  have hV : 2 ≤ V := (graphScale_bounds hU).1
  have hK : 2 ≤ K := two_le_expansionScale hV
  have hdegree : 16 * U ^ 3 * r ≤ V * r :=
    mul_le_mul_of_nonneg_right (graphScale_bounds hU).2 hr.le
  have hGcard : r ^ 2 / V ≤ (G.card : ℝ) :=
    retained_witness_lower r U W.card G.card hr hU hwitnesses hretained hremove
  have hG : G ⊆ A ×ˢ B := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hz, Finset.mem_image_of_mem Prod.snd hz⟩
  have hA0 (a : F) (ha : a ∈ A) : a ≠ 0 := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact (hnonzero z hz).1
  have hB0 (b : F) (hb : b ∈ B) : b ≠ 0 := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    exact (hnonzero z hz).2
  obtain ⟨S, hSA, hSlo, hShi, hSdiff, hSquot⟩ :=
    exists_simultaneous_small_difference_quotient A B G hG hA0 hB0 hr hV
      (hleft.trans hdegree) (hright.trans hdegree) hGcard
      (hdiff.trans hdegree) (hquot.trans hdegree)
  have hS0 : (0 : F) ∉ S := by
    intro h
    exact hA0 0 (hSA h) rfl
  have hexpand : 2 ^ 20 * V ^ 22 * r ≤ K * (S.card : ℝ) :=
    extraction_expansion_le r V S.card hr.le hVpos hSlo
  exact extracted_set_contradiction S r V K hS0 hK hVpos hr hrq
    (hSdiff.trans hexpand) (hSquot.trans hexpand) hproper hSlo hShi
    hfirst hsecond hthird

end
end RyserCoveringCounterexample.Incidence

end OAI
