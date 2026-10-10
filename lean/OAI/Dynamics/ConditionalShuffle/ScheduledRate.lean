import OAI.Dynamics.ConditionalShuffle.ScheduledCost

namespace OAI

noncomputable section
open scoped Classical
open Filter Topology
namespace Revealed.Scheduled
open Thorp Thorp.Conditional Thorp.Conditional.Hybrid Thorp.Conditional.OverlayEnergy
open Revealed.Split Revealed.Instrument Revealed.Disintegration Thorp.Specht

@[reducible] instance symbolFintype (ι α : Type) [Fintype ι] [Fintype α] (d : ℕ) :
    Fintype (Symbol ι α d) := inferInstanceAs (Fintype (Outside ι α (Position d) × Option (Coins d)))

def segmentLength (g : ℕ) := periodLength g * 800

def segmentSchedule (g s : ℕ) : Bool :=
  if h : s < segmentLength g then repeatedSchedule g 800 ⟨s,h⟩ else false

lemma segmentSchedule_fin (g : ℕ) :
    (fun i : Fin (segmentLength g) => segmentSchedule g i.val) = repeatedSchedule g 800 := by
  funext i
  simp only [segmentSchedule, dite_eq_left i.isLt]
  rfl

lemma segment_marginal_rate {ι : Type} [Fintype ι] (d : ℕ)
    (hs : 256*(d+1+2+4) ≤ Fintype.card (Position (d+1+2+3)))
    (e : Outside ι (Position (d+1+2)) (Position (d+1+2+3)))
    (a : Fin (7*2^d) → Position (d+1+2)) (ha : Function.Injective a) :
    (∑ p, probability (interval (d+1+2+3) (segmentLength (d+1+2)) (segmentSchedule (d+1+2))) e p *
      tv (Trim.push (kernel (interval (d+1+2+3) (segmentLength (d+1+2)) (segmentSchedule (d+1+2))) e p)
        (fun g => g ∘ a)) (fairMass (fun g : State (d+1+2) => g ∘ a))) ≤ OverlayEnergy.marginalRate (d+1+2) := by
  let g := d+1+2
  have hN : Fintype.card (Position (g+3)) = 64*2^d := by
    simp only [g, card_position, pow_add]; norm_num; omega
  have hq : Fintype.card (Position g) = 8*2^d := by
    simp only [g, card_position, pow_add]; norm_num; omega
  have hE (B : Position (g+3) → Bool) (tag) (ht : B tag = true)
      (hm : 2^d ≤ freeCount B) (hk : freeCount B ≤ Fintype.card (Position g)) :
      energy (g+2) (initialState (g+3) B tag ht).raw (segmentLength g)
        (repeatedSchedule g 800) ≤ OverlayEnergy.coefficient g^800 := by
    apply repeated_point_energy g B tag ht
    · rw [hN]; omega
    · simpa only [card_position] using hk
    · exact hs
  have hh := marginal_bound (g+2) (segmentLength g) (2^d) (repeatedSchedule g 800)
    (OverlayEnergy.coefficient g^800) hE (sectionFrame e) (7*2^d)
    (by rw [hq]; omega) a ha
  refine interval_cost_le (g+3) (segmentLength g) (segmentSchedule g) e
    (fun μ => tv (Trim.push μ (fun r : State g => r ∘ a)) (fairMass (fun r : State g => r ∘ a)))
    (OverlayEnergy.marginalRate g) ?_ inferInstance
  rw [segmentSchedule_fin]
  apply hh.trans
  unfold OverlayEnergy.marginalRate
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hNr : (Fintype.card (Position (g+3)) : ℝ) = 8*(2^g : ℝ) := by
    rw [card_position]; push_cast; rw [pow_add]; norm_num; ring
  have hgr : (2^g : ℝ) = 8*(2^d : ℝ) := by unfold g; rw [pow_add, pow_add]; norm_num; ring
  rw [hNr, hgr]
  push_cast
  have hc := pow_nonneg (coefficient_nonneg g) 800
  have hp : 0 ≤ (2^d : ℝ)^3 * OverlayEnergy.coefficient g^800 := mul_nonneg (by positivity) hc
  dsimp only [g] at *
  nlinarith

lemma segment_discarded_le {ι : Type} [Fintype ι] (d : ℕ)
    (hs : 256*(d+1+2+4) ≤ Fintype.card (Position (d+1+2+3)))
    (e : Outside ι (Position (d+1+2)) (Position (d+1+2+3))) :
    (∑ p, probability (interval (d+1+2+3) (segmentLength (d+1+2)) (segmentSchedule (d+1+2))) e p *
      Trim.discarded (Block.embedding (Block.eightEquiv d))
        (kernel (interval (d+1+2+3) (segmentLength (d+1+2)) (segmentSchedule (d+1+2))) e p)) ≤
        16*OverlayEnergy.marginalRate (d+1+2) := by
  let I := interval (ι:=ι) (α:=Position (d+1+2)) (d+1+2+3) (segmentLength (d+1+2)) (segmentSchedule (d+1+2))
  have hp (p) := Block.discarded_ordered_bound (Block.eightEquiv d) (Block.ordering d) (kernel I e p)
    (kernel_nonneg I e p) (kernel_sum I e p)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_left (hp p) (probability_nonneg I e p))
  simp only [Block.push_uniform_ordered] at hb
  have hswap : (∑ p, probability I e p * (2*∑ i, tv
      (Trim.push (kernel I e p) (fun g => g ∘ Block.domain d i))
      (fairMass (fun g : State (d+1+2) => g ∘ Block.domain d i)))) =
        2*∑ i, ∑ p, probability I e p * tv
          (Trim.push (kernel I e p) (fun g => g ∘ Block.domain d i))
          (fairMass (fun g : State (d+1+2) => g ∘ Block.domain d i)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro p _; ring
  change (∑ p, probability I e p * Trim.discarded _ (kernel I e p)) ≤
    ∑ p, probability I e p * (2*∑ i, tv (Trim.push (kernel I e p) (fun r => r ∘ Block.domain d i))
      (fairMass (fun r : State (d+1+2) => r ∘ Block.domain d i))) at hb
  rw [hswap] at hb
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    segment_marginal_rate d hs e (Block.domain d i) (Block.domain_injective d i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi
  norm_num only [Nat.cast_ofNat] at hi
  exact hb.trans (by dsimp only [I] at *; linarith)

def groupRate (d : ℕ) : ℝ := 512 * OverlayEnergy.marginalRate (d+1+2) + (1/2 : ℝ) *
  Real.sqrt ((96 : ℝ)^8 * exceptionalReciprocalSum (2^(d+1+2)))

lemma groupRate_tendsto : Tendsto groupRate atTop (nhds 0) := by
  have hm := OverlayEnergy.marginalRate_tendsto.comp (tendsto_add_atTop_nat 3)
  have he := Block.exceptional_cube_tendsto.comp (tendsto_add_atTop_nat 3)
  have hh := (hm.const_mul 512).add (((he.const_mul ((96 : ℝ)^8)).sqrt).const_mul (1/2 : ℝ))
  unfold groupRate
  simpa only [Function.comp_def, Nat.add_assoc, mul_zero, Real.sqrt_zero, add_zero] using hh

lemma group_distance_bound {ι : Type} [Fintype ι] (d : ℕ) (hd : 1 ≤ d)
    (hR : (permutationFamily (Position d)).reciprocalSum ≤ 3)
    (hs : 256*(d+1+2+4) ≤ Fintype.card (Position (d+1+2+3)))
    (e : Outside ι (Position (d+1+2)) (Position (d+1+2+3))) :
    Instrument.distance (interval (d+1+2+3) (segmentLength (d+1+2)) (segmentSchedule (d+1+2))) e 8 ≤
      groupRate d := by
  have hn : 16 ≤ Fintype.card (Position (d+1+2)) := by
    rw [card_position]
    exact (by norm_num : 16 = 2^4).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  let : Nontrivial (Position (d+1+2)) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let I := interval (ι:=ι) (α:=Position (d+1+2)) (d+1+2+3) (segmentLength (d+1+2)) (segmentSchedule (d+1+2))
  have hh := distance_eight_le I hn (Block.embedding (Block.eightEquiv d))
    (Physical.eight_block_coset_ratio d)
    (interval_dichotomy (d+1+2+2) (segmentLength (d+1+2)) (segmentSchedule (d+1+2)))
    (16*OverlayEnergy.marginalRate (d+1+2)) (segment_discarded_le d hs) e
  apply hh.trans
  unfold groupRate
  have hp : (32*(permutationFamily (Position d)).reciprocalSum)^8 ≤ (96 : ℝ)^8 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) (permutationFamily (Position d)).reciprocalSum_nonneg)
      (by linarith only [hR]) 8
  have he : 0 ≤ exceptionalReciprocalSum (2^(d+1+2)) := by
    exact Finset.sum_nonneg (fun p _ => by
      change 0 ≤ (if 0 < defect p then inverseDegree p else 0)
      split_ifs <;> first | exact inverseDegree_nonneg p | exact le_rfl)
  rw [card_position]
  have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hp he)
  rw [show (32 : ℝ)*(16*OverlayEnergy.marginalRate (d+1+2)) =
    512*OverlayEnergy.marginalRate (d+1+2) by ring]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1/2))

end Revealed.Scheduled

end

end OAI
