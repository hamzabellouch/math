import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedModelInterval
import OAI.Analysis.LipschitzHilbert.Packets.SourceBoundaryPacketRegroup

namespace OAI

/-! The concentration of a recentered assigned family controls the
original masked packet intervals and stopping prefixes. Empty length
fibers contribute zero; no longest-scale restriction is added. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L A : ℝ) (z : ℝ×ℝ) (top : τ)

local notation "Q" => P.assignedReferenceFamily packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency top
local notation "orig" => P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency top
local notation "alts" => P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt top
local notation "halt" => P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
  hw hcone hF hwide hfrequency alt hAlt top
local notation "original" => P.physicalMaskedValue alt hAlt oldSlope b v f
  (fun j l u => T (assigned (Sigma.mk j (Sigma.mk l u)))) L A z

/-- Regrouping the original packets by length preserves the exact
assigned top subset. -/
theorem assignedPhysicalBands_interval_sum (lower upper : ℕ) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
      P.assignedPhysicalBands alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j)) =
      ∑ q ∈ packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper),
        original q := by
  let chosen := packets.filter (fun q => assigned q = top)
  let levels := Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper)
  calc
    _ = ∑ j ∈ levels, ∑ q ∈ chosen.filter (fun q => q.1 = j), original q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [P.assignedPhysicalBands_eq alt hAlt oldSlope b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j)]
      apply Finset.sum_congr
      · ext q
        simp only [chosen,Finset.mem_filter,Prod.mk.injEq,and_assoc]
      · intro q _
        rfl
    _ = ∑ q ∈ chosen.filter (fun q => q.1 ∈ levels), original q :=
      Finset.sum_fiberwise_eq_sum_filter chosen levels (fun q => q.1) original
    _ = _ := by
      apply Finset.sum_congr
      · ext q
        simp only [chosen,levels,Finset.mem_filter,Finset.mem_univ,true_and,and_assoc]
      · intro q _
        rfl

/-- Exact original masked interval, expressed by the raw assigned
reference interval whose norm is bounded on the concentration good set. -/
theorem assignedPhysicalInterval_eq_maskedRawInterval
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (lower upper : ℕ) (hlu : lower ≤ upper) :
    (∑ q ∈ packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper),
      original q) =
      (T top).mask L A z • ((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1) := by
  have hcoeff : (Q).physicalMultiplierCoefficient (T top).slope
      (fun j l => b j (orig j l)) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned top oldSlope
      (T top).slope (R top) cone w F hw hcone hF hwide hfrequency b v f j l u
  have hraw := congrArg
    (fun co => ((Q).withProfile alts halt).rawInterval co 0 lower upper
      z.1 (z.2-(T top).slope*z.1)) hcoeff
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin N => lower ≤ j.val ∧ j.val < upper),
        P.assignedPhysicalBands alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) :=
      (P.assignedPhysicalBands_interval_sum packets assigned T oldSlope alt hAlt b v f
        L A z top lower upper).symm
    _ = ((Q).withProfile alts halt).rawInterval
        (fun j l u => (T top).mask L A z •
          (Q).physicalMultiplierCoefficient (T top).slope (fun j l => b j (orig j l)) v f j l u)
        0 lower upper z.1 (z.2-(T top).slope*z.1) := by
      rw [((Q).withProfile alts halt).rawInterval_eq_band_sum _ _ _ _ hlu]
      apply Finset.sum_congr rfl
      intro j _
      exact (P.assignedReference_rawBand_original packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt b v f L A z top j hcondition).symm
    _ = _ := by
      rw [((Q).withProfile alts halt).rawInterval_coeff_smul]
      exact congrArg (fun v => (T top).mask L A z • v) hraw

theorem assignedPhysicalInterval_norm_le
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (C : ℝ) (hinterval : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1)‖ ≤ C)
    (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) :
    ‖∑ q ∈ packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper),
      original q‖ ≤ C := by
  rw [P.assignedPhysicalInterval_eq_maskedRawInterval packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z top hcondition lower upper hlu,
    norm_smul,Real.norm_eq_abs]
  have hm : |(T top).mask L A z| ≤ 1 :=
    topSincMask_abs_le_one L A ((T top).horizontal z) ((T top).transverse z)
  exact (mul_le_of_le_one_left (norm_nonneg _) hm).trans (hinterval lower upper hlu hu)

theorem assignedPhysicalStoppingPrefix_norm_le
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (C : ℝ) (hinterval : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1)‖ ≤ C)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (k : ℕ) :
    ‖∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => stop q.1 ≤ k),
      original q‖ ≤ C := by
  apply packet_stopping_prefix_bound (packets.filter (fun q => assigned q = top))
    (fun q => q.1) stop hstop original C _ k
  intro lower upper hlu hu
  have heq : (packets.filter (fun q => assigned q = top)).filter
      (fun q => lower ≤ q.1.val ∧ q.1.val < upper) =
      packets.filter (fun q => assigned q = top ∧ lower ≤ q.1.val ∧ q.1.val < upper) := by
    ext q
    simp only [Finset.mem_filter,and_assoc]
  rw [heq]
  exact P.assignedPhysicalInterval_norm_le packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z top hcondition C hinterval
    lower upper hlu hu

theorem assignedPhysicalSourcePrefix_norm_le
    (hcondition : ∀ q ∈ packets, assigned q = top →
      P.referenceCondition oldSlope (T top).slope (R top) cone w q.1 q.2.1)
    (C : ℝ) (hinterval : ∀ lower upper, lower ≤ upper → upper ≤ N →
      ‖((Q).withProfile alts halt).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u.val)
        0 lower upper z.1 (z.2-(T top).slope*z.1)‖ ≤ C)
    (g : AngularGrid) (cutoff : ℝ)
    (hstart : ∀ j, g.eligible cutoff (w/P.length j) 0) (k : ℕ) :
    let stop := fun j : Fin N => g.lastEligible cutoff (w/P.length j) (div_pos hw (P.length_pos j))
    ‖∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => stop q.1 ≤ k),
      original q‖ ≤ C := by
  intro stop
  exact P.assignedPhysicalStoppingPrefix_norm_le packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f L A z top hcondition C hinterval stop
    (P.stopping_antitone g cutoff w hw hstart) k

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
