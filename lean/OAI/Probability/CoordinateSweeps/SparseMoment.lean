import Mathlib
import OAI.Probability.CoordinateSweeps.TrajectoryMoment
import OAI.Combinatorics.Graphs.Coverage
import OAI.RepresentationTheory.Placement.Occurrence

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}
open Coverage

def holeHeavy (H : G.Holes h) (η : ℝ) (j : Fin G.b) : Finset (G.Line j) :=
  heavySet (H.lineCount j) ((2^G.bits j : ℕ)*η/2)

def particleHeavy (p : Fin k → G.Slot × G.Slot) (η : ℝ) (j : Fin G.b) : Finset (G.Line j) :=
  heavySet (occupancy (fun a : G.Slot × G.Slot => G.pathLine a.1 a.2 j) p)
    ((2^G.bits j : ℕ)*η/2)

def holeHeavyHits (H : G.Holes h) (p : Fin k → G.Slot × G.Slot) (η : ℝ) (j : Fin G.b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => G.pathLine (p i).1 (p i).2 j ∈ H.holeHeavy η j)

def particleHeavyHits (p : Fin k → G.Slot × G.Slot) (η : ℝ) (j : Fin G.b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => G.pathLine (p i).1 (p i).2 j ∈ particleHeavy p η j)

theorem probability_holeHeavy_single (H : G.Holes h) {η : ℝ} (hη : 0 < η) (j : Fin G.b) :
    (∑ p : G.Slot × G.Slot, if G.pathLine p.1 p.2 j ∈ H.holeHeavy η j then G.endpointWeight p else 0) ≤
      2*h/((G.size : ℝ)*η) := by
  have hs : 0 < (G.size : ℝ) := by unfold Grid.size; positivity
  have hm : 0 < ((2^G.bits j : ℕ) : ℝ) := by positivity
  have ht : ∑ l, (H.lineCount j l : ℝ) = h := by exact_mod_cast H.sum_lineCount j
  have hc := heavySet_card_mul_le (H.lineCount j) (((2^G.bits j : ℕ) : ℝ)*η/2)
  rw [ht] at hc
  have hline : ∀ l : G.Line j,
      (∑ p : G.Slot × G.Slot, if G.pathLine p.1 p.2 j = l then G.endpointWeight p else 0) ≤
        ((2^G.bits j : ℕ) : ℝ)/G.size := by
    intro l
    exact le_of_eq (by simpa using G.probability_path_line j l)
  apply (probability_lineSet_le G.endpointWeight (fun p : G.Slot × G.Slot => G.pathLine p.1 p.2 j)
    (H.holeHeavy η j) (((2^G.bits j : ℕ) : ℝ)/G.size) hline).trans
  change ((heavySet (H.lineCount j) _).card : ℝ) * _ ≤ _
  apply (le_div_iff₀ (mul_pos hs hη)).mpr
  field_simp at ⊢
  nlinarith

theorem probability_holeHeavyHits_le (H : G.Holes h) {η : ℝ} (hη : 0 < η)
    (hp : 2*h/((G.size : ℝ)*η) ≤ 1) (j : Fin G.b) (u : ℝ) (hu : 0 ≤ u) :
    Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
      u ≤ ((H.holeHeavyHits p η j).card : ℝ)) ≤
      (2 : ℝ)^k * (2*h/((G.size : ℝ)*η))^u := by
  convert (probability_many_hits_le_rpow (I := Fin k) G.endpointWeight G.endpointWeight_nonneg
      G.endpointWeight_total (fun p : G.Slot × G.Slot => G.pathLine p.1 p.2 j ∈ H.holeHeavy η j)
      _ (by positivity) hp (by convert H.probability_holeHeavy_single hη j using 1; congr!) u hu) using 1 <;>
    simp only [holeHeavyHits, Fintype.card_fin]
  congr!

theorem probability_particleHeavyHits_le {η : ℝ} (hη : 0 < η)
    (hp : 2*k/((G.size : ℝ)*η) ≤ 1) (j : Fin G.b) (u : ℝ) (hu : 0 ≤ u) :
    Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
      u ≤ ((particleHeavyHits p η j).card : ℝ)) ≤
      ((Fintype.card (G.Line j)+1 : ℕ) : ℝ)^⌊2*k/(((2^G.bits j : ℕ) : ℝ)*η)⌋₊ *
        (2 : ℝ)^k * (2*k/((G.size : ℝ)*η))^u := by
  have hs : 0 < (G.size : ℝ) := by unfold Grid.size; positivity
  have hm : 0 < ((2^G.bits j : ℕ) : ℝ) := by positivity
  have hv : 0 < ((2^G.bits j : ℕ) : ℝ)*η/2 := by positivity
  have he : (k : ℝ)/(((2^G.bits j : ℕ) : ℝ)*η/2) = 2*k/(((2^G.bits j : ℕ) : ℝ)*η) := by ring
  have hf : (⌊(k : ℝ)/(((2^G.bits j : ℕ) : ℝ)*η/2)⌋₊ : ℝ)*
      (((2^G.bits j : ℕ) : ℝ)/G.size) ≤ 2*k/((G.size : ℝ)*η) := by
    apply le_trans (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity))
    apply le_of_eq
    field_simp
  have hb := probability_heavy_occupancy_le (I := Fin k)
    G.endpointWeight G.endpointWeight_nonneg G.endpointWeight_total
    (fun p : G.Slot × G.Slot => G.pathLine p.1 p.2 j) hv
    (2*k/((G.size : ℝ)*η)) (((2^G.bits j : ℕ) : ℝ)/G.size)
    (by positivity) (by positivity) hp
    (fun l => le_of_eq (by simpa using G.probability_path_line j l))
    (by simpa using hf) u hu
  convert hb using 1 <;>
    simp only [particleHeavyHits, particleHeavy, Fintype.card_fin, he]
  congr!

theorem not_vertexIsolated_iff (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (i : Fin k) :
    ¬ H.VertexIsolated (fun i => (p i).1) (fun i => (p i).2) i ↔
      i ∈ sharingCoverage G.vertexShares H.endpointData p := by
  simp only [VertexIsolated, sharingCoverage, mem_covered, Grid.vertexShares]
  constructor
  · intro hi
    by_cases ha : ∀ a s, G.pathBetween (p i).1 (p i).2 s ≠ H.path a s
    · have hj : ¬ ∀ j, i ≠ j → ∀ s, G.pathBetween (p i).1 (p i).2 s ≠ G.pathBetween (p j).1 (p j).2 s := fun h => hi ⟨ha,h⟩
      push Not at hj
      obtain ⟨j,hij,t,hjt⟩ := hj
      exact Or.inl ⟨j,hij,t,hjt⟩
    · push Not at ha
      obtain ⟨a,t,hat⟩ := ha
      exact Or.inr ⟨a,t,hat.trans (H.path_eq_pathBetween hH a t)⟩
  · rintro (⟨j,hij,t,he⟩ | ⟨a,t,he⟩) hv
    · exact hv.2 j hij t he
    · exact hv.1 a t (he.trans (H.path_eq_pathBetween hH a t).symm)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}
open Coverage

theorem not_good_cover (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (η : ℝ) (i : Fin k)
    (hi : i ∉ H.goodSet (fun i => (p i).1) (fun i => (p i).2) η) :
    i ∈ sharingCoverage G.vertexShares H.endpointData p ∨
      ∃ j, i ∈ H.holeHeavyHits p η j ∨ i ∈ particleHeavyHits p η j := by
  have hn : ¬ H.Good (fun i => (p i).1) (fun i => (p i).2) η i := by simpa using hi
  by_cases hv : H.VertexIsolated (fun i => (p i).1) (fun i => (p i).2) i
  · right
    have hj : ¬ ∀ j, H.Light (fun i => (p i).1) (fun i => (p i).2) η
        (G.stagePath (fun i => (p i).1) (fun i => (p i).2) i j) := fun ht => hn ⟨hv,ht⟩
    push Not at hj
    obtain ⟨j,hj⟩ := hj
    refine ⟨j,?_⟩
    simp only [Light, Grid.stagePath, Nat.cast_add, not_le] at hj
    simp only [holeHeavyHits, particleHeavyHits, holeHeavy, particleHeavy,
      heavySet, Finset.mem_filter, Finset.mem_univ, true_and]
    change ((2^G.bits j : ℕ) : ℝ)*η/2 < (H.lineCount j (G.pathLine (p i).1 (p i).2 j) : ℝ) ∨
      ((2^G.bits j : ℕ) : ℝ)*η/2 < (auxCount (fun i => (p i).1) (fun i => (p i).2)
        Finset.univ j (G.pathLine (p i).1 (p i).2 j) : ℝ)
    by_contra hc
    push Not at hc
    linarith
  · exact Or.inl ((H.not_vertexIsolated_iff hH p i).mp hv)

theorem card_covered_by_good_and_bad (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (η : ℝ) :
    k ≤ (H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card +
      (sharingCoverage G.vertexShares H.endpointData p).card +
      ∑ j, ((H.holeHeavyHits p η j).card + (particleHeavyHits p η j).card) := by
  let A := H.goodSet (fun i => (p i).1) (fun i => (p i).2) η
  let V := sharingCoverage G.vertexShares H.endpointData p
  let B := (Finset.univ : Finset (Fin G.b)).biUnion
    (fun j => H.holeHeavyHits p η j ∪ particleHeavyHits p η j)
  have hc : (Finset.univ : Finset (Fin k)) ⊆ (A ∪ V) ∪ B := by
    intro i _
    by_cases hi : i ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
    · rcases H.not_good_cover hH p η i hi with hv | ⟨j,hj⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨j,Finset.mem_univ _, Finset.mem_union.mpr hj⟩)
  calc
    k = (Finset.univ : Finset (Fin k)).card := by simp
    _ ≤ ((A ∪ V) ∪ B).card := Finset.card_le_card hc
    _ ≤ (A ∪ V).card + B.card := Finset.card_union_le _ _
    _ ≤ (A.card+V.card) + B.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (A.card+V.card) + ∑ j, ((H.holeHeavyHits p η j).card + (particleHeavyHits p η j).card) := by
      apply Nat.add_le_add_left
      apply (Finset.card_biUnion_le).trans
      exact Finset.sum_le_sum (fun j _ => Finset.card_union_le _ _)

theorem fewGood_cover (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (η : ℝ)
    (he : ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2) :
    (k : ℝ)/4 ≤ ((sharingCoverage G.vertexShares H.endpointData p).card : ℝ) ∨
      ∃ j, (k : ℝ)/(8*G.b) ≤ ((H.holeHeavyHits p η j).card : ℝ) ∨
        (k : ℝ)/(8*G.b) ≤ ((particleHeavyHits p η j).card : ℝ) := by
  have hb : 0 < (G.b : ℝ) := by exact_mod_cast G.positive
  by_contra hf
  push Not at hf
  have hc : (k : ℝ) ≤ (H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card +
      (sharingCoverage G.vertexShares H.endpointData p).card +
      ∑ j, (((H.holeHeavyHits p η j).card : ℝ) + (particleHeavyHits p η j).card) := by
    exact_mod_cast H.card_covered_by_good_and_bad hH p η
  have hsum : (∑ j, (((H.holeHeavyHits p η j).card : ℝ) + (particleHeavyHits p η j).card)) ≤
      (G.b : ℝ)*((k : ℝ)/(4*G.b)) := by
    calc
      _ ≤ ∑ _j : Fin G.b, (k : ℝ)/(4*G.b) := by
        apply Finset.sum_le_sum
        intro j _
        have h1 := (hf.2 j).1
        have h2 := (hf.2 j).2
        have hid : (k : ℝ)/(4*G.b) = 2*((k : ℝ)/(8*G.b)) := by ring
        rw [hid]
        linarith
      _ = _ := by simp
  have hid : (G.b : ℝ)*((k : ℝ)/(4*G.b)) = k/4 := by field_simp
  rw [hid] at hsum
  linarith [hf.1]

/- Source04:eq12 prior to choosing absolute parameters and absorbing
subpolynomial factors. There is no conditioning on a particle-selected line set. -/
theorem probability_fewGood_le (H : G.Holes h) (hH : H.Feasible) {η : ℝ} (hη : 0 < η)
    (hh : 2*h/((G.size : ℝ)*η) ≤ 1) (hk : 2*k/((G.size : ℝ)*η) ≤ 1)
    (hv : ((k+h : ℕ) : ℝ)*G.vertexSharingRate ≤ 1) :
    Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
      ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2) ≤
      (2 : ℝ)^k * (((k+h : ℕ) : ℝ)*G.vertexSharingRate)^((k : ℝ)/8) +
      ∑ j : Fin G.b, ((2 : ℝ)^k * (2*h/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b)) +
        ((Fintype.card (G.Line j)+1 : ℕ) : ℝ)^⌊2*k/(((2^G.bits j : ℕ) : ℝ)*η)⌋₊ *
          (2 : ℝ)^k * (2*k/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b))) := by
  let V := fun p : Fin k → G.Slot × G.Slot =>
    (k : ℝ)/4 ≤ ((sharingCoverage G.vertexShares H.endpointData p).card : ℝ)
  let B := fun (j : Fin G.b) (p : Fin k → G.Slot × G.Slot) =>
    (k : ℝ)/(8*G.b) ≤ ((H.holeHeavyHits p η j).card : ℝ) ∨
      (k : ℝ)/(8*G.b) ≤ ((particleHeavyHits p η j).card : ℝ)
  have hu := probability_coverage_le_real (I := Fin k) G.vertexShares G.vertexShares_symm
    H.endpointData G.endpointWeight G.endpointWeight_nonneg G.endpointWeight_total
    G.vertexSharingRate G.vertexSharingRate_nonneg G.probability_vertexShares_le
    (by simpa using hv) ((k : ℝ)/4) (by positivity)
  have hV : Coverage.probability G.endpointWeight V ≤
      (2 : ℝ)^k * (((k+h : ℕ) : ℝ)*G.vertexSharingRate)^((k : ℝ)/8) := by
    simpa only [V, Fintype.card_fin, div_div, show (4:ℝ)*2=8 by norm_num] using hu
  have hB (j : Fin G.b) : Coverage.probability G.endpointWeight (B j) ≤
      (2 : ℝ)^k * (2*h/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b)) +
        ((Fintype.card (G.Line j)+1 : ℕ) : ℝ)^⌊2*k/(((2^G.bits j : ℕ) : ℝ)*η)⌋₊ *
          (2 : ℝ)^k * (2*k/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b)) := by
    apply (probability_or_le G.endpointWeight G.endpointWeight_nonneg _ _).trans
    exact add_le_add (H.probability_holeHeavyHits_le hη hh j _ (by positivity))
      (probability_particleHeavyHits_le hη hk j _ (by positivity))
  calc
    _ ≤ Coverage.probability G.endpointWeight (fun p => V p ∨ ∃ j, B j p) :=
      probability_mono G.endpointWeight G.endpointWeight_nonneg (fun p hp => H.fewGood_cover hH p η hp)
    _ ≤ Coverage.probability G.endpointWeight V +
        Coverage.probability G.endpointWeight (fun p => ∃ j, B j p) :=
      probability_or_le G.endpointWeight G.endpointWeight_nonneg _ _
    _ ≤ Coverage.probability G.endpointWeight V +
        ∑ j, Coverage.probability G.endpointWeight (B j) :=
      add_le_add le_rfl (probability_exists_le G.endpointWeight G.endpointWeight_nonneg B)
    _ ≤ _ := add_le_add hV (Finset.sum_le_sum (fun j _ => hB j))
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

/- An explicit absolute prefactor used before asymptotic absorption. -/
def uniformSparsePrefactor (G : Grid) (h k : ℕ) : ℝ :=
  (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b) *
    (16*Real.exp 2)^(G.b*k) * (1+16*Real.exp 2)^(G.b*k)

/- The source's good/bad entry split, in counting HS normalization. -/
theorem placementHSsq_uniform_le_fewGood (H : G.Holes h) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1/8) :
    H.placementHSsq (k := k) (fun _ => FiniteLaw.uniform _) ≤
      (uniformSparsePrefactor G h k)^2 *
        (η^((k : ℝ)/2) + Coverage.probability G.endpointWeight
          (fun p : Fin k → G.Slot × G.Slot =>
            ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2)) := by
  let M := uniformSparsePrefactor G h k
  let Bad := fun p : Fin k → G.Slot × G.Slot =>
    ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2
  have hM : 0 ≤ M := by dsimp [M, uniformSparsePrefactor]; positivity
  have hη1 : η ≤ 1 := by linarith
  have hsum : ∑ p : Fin k → G.Slot × G.Slot, Coverage.productMass G.endpointWeight p = 1 := by
    unfold Coverage.productMass
    rw [← Fintype.prod_sum]
    simp only [G.endpointWeight_total, Finset.prod_const_one]
  rw [H.placementHSsq_eq_full]
  calc
    _ ≤ ∑ p : Fin k → G.Slot × G.Slot,
        Coverage.productMass G.endpointWeight p * (M^2 *
          (η^((k : ℝ)/2) + if Bad p then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _
        (Coverage.productMass_nonneg G.endpointWeight G.endpointWeight_nonneg p)
      by_cases hp : H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2)
      · rw [ite_eq_left hp]
        have he := H.scaled_placementKernel_good_bound (fun i => (p i).1) (fun i => (p i).2)
          hp.1 hη hηsmall
        change |(G.size : ℝ)^k * H.placementKernel _ _ _| ≤ M *
          η^(((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ)/2) at he
        have hpow : η^(((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ)/2) ≤ 1 :=
          Real.rpow_le_one hη hη1 (by positivity)
        by_cases hb : Bad p
        · rw [ite_eq_left hb]
          have hf : |(G.size : ℝ)^k * H.placementKernel _ _ _| ≤ M :=
            he.trans (mul_le_of_le_one_right hM hpow)
          have hsq := (sq_le_sq₀ (abs_nonneg _) hM).mpr hf
          rw [sq_abs] at hsq
          have he0 := Real.rpow_nonneg hη ((k : ℝ)/2)
          nlinarith [sq_nonneg M]
        · rw [ite_eq_right hb, add_zero]
          have hc : (k : ℝ)/4 ≤ ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ)/2 := by
            dsimp [Bad] at hb
            linarith
          have hmono := Real.rpow_le_rpow_of_exponent_ge' hη hη1 (by positivity) hc
          have hf := he.trans (mul_le_mul_of_nonneg_left hmono hM)
          have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hM (Real.rpow_nonneg hη _))).mpr hf
          simp only [sq_abs, mul_pow] at hsq
          have hid : (η^((k : ℝ)/4))^2 = η^((k : ℝ)/2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
            congr 1
            ring
          simpa only [mul_pow, hid] using hsq
      · rw [ite_eq_right hp]
        positivity
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hsum, one_mul]
      rw [Coverage.probability, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
end CoordinateSweeps.Grid.Holes

/- Required top-placement compression for the conditional main. The top space
is the annihilator of all functions depending on a proper set of coordinates.
This is the exact top level used in source04 around eq7. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

abbrev InputPlacements (H : G.Holes h) (k : ℕ) := {x : Fin k → G.Slot // H.ValidInput x}
abbrev OutputPlacements (H : G.Holes h) (k : ℕ) := {y : Fin k → G.Slot // H.ValidOutput y}

def placementTop (H : G.Holes h) (k : ℕ) : Submodule ℂ (H.OutputPlacements k → ℂ) :=
  Placement.topSpace (fun y : H.OutputPlacements k => y.val)

def transitionMatrix (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    Matrix (H.InputPlacements k) (H.OutputPlacements k) ℂ :=
  fun x y => (H.extraProbability x.val y.val Finset.univ μ : ℂ)

theorem extraProbability_dependsOn (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (A : Finset (Fin k))
    (x : H.InputPlacements k) :
    Placement.DependsOn (fun y : H.OutputPlacements k => y.val) A
      (fun y => (H.extraProbability x.val y.val A μ : ℂ)) := by
  intro y y' hy
  apply congrArg Complex.ofReal
  rw [H.extraProbability_eq_conditionalEndpoint, H.extraProbability_eq_conditionalEndpoint]
  have he (ω : G.Choices) : G.endpointEvent x.val y.val A ω ↔ G.endpointEvent x.val y'.val A ω := by
    constructor <;> intro hw i hi
    · exact (hw i hi).trans (hy i hi)
    · exact (hw i hi).trans (hy i hi).symm
  simp only [conditionalEndpointProbability, he]

theorem alternatingKernel_eq_placementKernel (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (x : H.InputPlacements k) (y : H.OutputPlacements k) :
    Placement.alternatingKernel (G.size : ℝ)
      (fun A (x : H.InputPlacements k) (y : H.OutputPlacements k) => H.extraProbability x.val y.val A μ)
      x y = (H.placementKernel x.val y.val μ : ℂ) := by
  simp only [Placement.alternatingKernel, placementKernel, Fintype.card_fin]

theorem placementHSsq_eq_subtype (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    H.placementHSsq (k := k) μ =
      ∑ x : H.InputPlacements k, ∑ y : H.OutputPlacements k,
        ‖(H.placementKernel x.val y.val μ : ℂ)‖^2 := by
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold placementHSsq
  symm
  rw [sum_subtype_eq_sum_ite_of_iff (p := H.ValidInput) (q := H.ValidInput)
    (fun x : Fin k → G.Slot => Iff.rfl)
    (fun x => ∑ y : H.OutputPlacements k, H.placementKernel x y.val μ ^ 2)]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · rw [sum_subtype_eq_sum_ite_of_iff (p := H.ValidOutput) (q := H.ValidOutput)
      (fun y : Fin k → G.Slot => Iff.rfl) (fun y => H.placementKernel x y μ ^ 2)]
    apply Finset.sum_congr rfl
    intro y _
    simp only [hx, true_and]
  · apply Eq.symm
    simp only [hx, false_and, ite_false, Finset.sum_const_zero]

/- Exact top-placement restriction of the ACTUAL conditioned sweep, bounded
by the already proved path-weight Q counting norm. No representation-theoretic
conclusion is inserted as a hypothesis. -/
theorem transitionMatrix_top_norm_le (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (v : EuclideanSpace ℂ (H.OutputPlacements k))
    (hv : (fun y => v y) ∈ H.placementTop k) :
    ‖(EuclideanSpace.equiv (H.InputPlacements k) ℂ).symm ((H.transitionMatrix μ).mulVec v)‖ ≤
      Real.sqrt (H.placementHSsq (k := k) μ) * ‖v‖ := by
  have hs : (G.size : ℝ) ≠ 0 := by unfold Grid.size; positivity
  have hh := Placement.fullKernel_top_norm_le (fun y : H.OutputPlacements k => y.val)
    (G.size : ℝ) hs
    (fun A (x : H.InputPlacements k) (y : H.OutputPlacements k) => H.extraProbability x.val y.val A μ)
    (H.extraProbability_dependsOn μ) v hv
  change ‖(EuclideanSpace.equiv (H.InputPlacements k) ℂ).symm
    (Matrix.mulVec (fun x y => (H.extraProbability x.val y.val Finset.univ μ : ℂ)) v)‖ ≤ _
  simpa only [H.alternatingKernel_eq_placementKernel, ← H.placementHSsq_eq_subtype] using hh
end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
