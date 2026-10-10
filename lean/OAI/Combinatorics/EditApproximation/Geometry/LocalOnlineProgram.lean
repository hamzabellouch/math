import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalRefinement
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalOnlineLocality
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Direct online queries use one rounded center per allowed scale. The
integer argument denotes the accepted output of the exact rejection sampler;
reduction modulo the requested range merely makes the finite rule total. -/

namespace EditApproximation

open Finset

theorem rationalRefinementUpdate_online_mem_ext {ι : Type*}
    (left right : List ι) (value : ι → ℚ) (delta cone : ℚ)
    (hmem : ∀ action, action ∈ left ↔ action ∈ right) :
    rationalRefinementUpdate delta cone (rationalOnlineMinimum (left.map value)) =
      rationalRefinementUpdate delta cone (rationalOnlineMinimum (right.map value)) := by
  simp only [rationalRefinementUpdate_online_list, List.map_map, Function.comp_def]
  apply rationalMinimum_local_complete right left
  · exact fun action ha => (hmem action).mp ha
  · exact fun action ha _ => (hmem action).mpr ha



theorem keyedOnlineBandG_positive {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H b : ℕ) (tau : ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length) :
    0 < keyedOnlineBandG source target parent P exponent H b tau child r := by
  unfold keyedOnlineBandG
  omega



theorem boundedOnlineInteger_val (n : ℕ) (hn : 0 < n) (integer : Fin n) :
    boundedOnlineInteger n hn integer.val = integer :=
  Fin.ext (Nat.mod_eq_of_lt integer.isLt)





theorem localOnlineCandidates_length {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length) :
    (localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q).length ≤
      (dyadicQueryWindow N (parentInitial q) a F).length :=
  List.length_filterMap_le _ _

theorem localOnlineCandidates_mem {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H : ℕ) (tau a eta kappa : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (q : TargetInterval target.length)
    (action : PhysicalRationalAction M target.length) :
    action ∈ localOnlineCandidates source target parent N P F exponent H tau a eta kappa
      parentInitial child initial children t integer q ↔
    ∃ b, b ∈ dyadicQueryWindow N (parentInitial q) a F ∧
      (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a parentInitial ∧
      keyedOnlineCandidate source target parent P F exponent H b tau eta kappa child initial
        children t (roundInterval (seedGridSpacing b P) q)
        (integer b (roundInterval (seedGridSpacing b P) q)) = some action := by
  unfold localOnlineCandidates
  constructor
  · intro ha
    obtain ⟨b, hb, hselected⟩ := List.mem_filterMap.mp ha
    dsimp only at hselected
    split_ifs at hselected with heligible
    refine ⟨b, hb, ?_, hselected⟩
    exact representativeList_mem a parentInitial _ (List.mem_filter.mp hb).1
      (roundInterval_on_grid _ q) heligible.1 heligible.2
  · rintro ⟨b, hb, hrep, hselected⟩
    have hc := representativeList_conditions a parentInitial hrep
    apply List.mem_filterMap.mpr
    refine ⟨b, hb, ?_⟩
    dsimp only
    rw [ite_eq_left hc.2.2.2]
    exact hselected

section Physical

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent H T : ℕ) (A tau eta kappa : ℚ)

theorem keyedOnlineCandidate_eq_physical
    (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (integer : Fin (optimizerTriangularMass
      (physicalProgramBandK source target U N P F A T exponent H tau node representative))) :
    keyedOnlineCandidate source target (physicalSourceInterval source.length node.1)
      P F exponent H ((stageRepresentatives source target U N P F A node.1).get representative).1
      tau eta kappa (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2) children t
      ((stageRepresentatives source target U N P F A node.1).get representative).2 integer.val =
    physicalProgramOnlineCandidate source target U N P F A T exponent H tau eta kappa
      node representative children t integer := by
  let G := keyedOnlineBandG source target (physicalSourceInterval source.length node.1)
    P exponent H ((stageRepresentatives source target U N P F A node.1).get representative).1 tau
    (physicalBandChildMassTable source target U N P F A T node.1 node.2)
    ((stageRepresentatives source target U N P F A node.1).get representative).2
  have hG : 0 < G := keyedOnlineBandG_positive source target
    (physicalSourceInterval source.length node.1) P exponent H
    ((stageRepresentatives source target U N P F A node.1).get representative).1 tau
    (physicalBandChildMassTable source target U N P F A T node.1 node.2)
    ((stageRepresentatives source target U N P F A node.1).get representative).2
  have haccept : boundedOnlineInteger (optimizerTriangularMass (G ^ 80))
      (optimizerTriangularMass_positive (G ^ 80) (pow_pos hG 80)) integer.val = integer := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt integer.isLt
  unfold keyedOnlineCandidate physicalProgramOnlineCandidate physicalBandOnlineCandidate
  dsimp only
  rw [haccept]
  dsimp only [physicalBandEnvelope, physicalProgramBandK, physicalProgramBandG,
    physicalBandActions, keyedOnlineBandG] at integer ⊢
  unfold physicalBandEnvelope
  dsimp only [physicalBandActions]
  congr 1
  funext hband
  split <;> simp_all only

def physicalLocalOnline {R : ℕ} [NeZero R]
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (children : PhysicalChildTables M target.length)
    (t : ℕ) (q : TargetInterval target.length) : List (PhysicalRationalAction M target.length) :=
  if hbelow : node.1.val < J then
    localOnlineCandidates source target (physicalSourceInterval source.length node)
      N P F exponent H tau (refinementFactor A F) eta kappa
      (fun r => stageInitial source target U N P F A (node, r))
      (physicalLocalChildMass source target U N P F A T node hbelow)
      (physicalBandChildInitial source target U N P F A node hbelow)
      children (t - 1) (integer ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q
  else []

end Physical

end EditApproximation

end OAI
