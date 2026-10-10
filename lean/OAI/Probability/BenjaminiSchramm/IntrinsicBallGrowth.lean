import OAI.Probability.BenjaminiSchramm.SmallWitness
import OAI.Probability.BenjaminiSchramm.OperatorSusceptibility
import OAI.Probability.BenjaminiSchramm.EventMeasurability

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem intrinsicBall_small_witness (G : BondGraph V E) (S : Set E)
    (x y : V) (r : ℕ) (ω : Finset E)
    (hy : y ∈ intrinsicBall G ((ω : Set E) ∩ S) x r) :
    ∃ s ⊆ ω, s.card ≤ r ∧ ∀ η : Finset E, s ⊆ η →
      y ∈ intrinsicBall G ((η : Set E) ∩ S) x r := by
  obtain ⟨l,hl,hlen,ho⟩ := hy
  refine ⟨l.toFinset, ?_, l.toFinset_card_le.trans hlen, ?_⟩
  · intro e he
    exact (ho e (List.mem_toFinset.mp he)).1
  · intro η hη
    exact ⟨l,hl,hlen,fun e he => ⟨hη (List.mem_toFinset.mpr he),(ho e he).2⟩⟩

noncomputable def intrinsicBallPolynomial (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Set E) (x y : V) (r : ℕ) : ℝ → ℝ :=
  bernoulliPolynomial (intrinsicBondSupport G hloc S x r)
    (fun ω => if y ∈ intrinsicBall G ((ω : Set E) ∩ S) x r then 1 else 0)

theorem intrinsicBallPolynomial_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x y : V) (r : ℕ) (p : unitInterval) :
    intrinsicBallPolynomial G hloc S x y r p =
      (law p {ω | y ∈ intrinsicBall G (ω ∩ S) x r}).toReal := by
  change finiteEventPolynomial (intrinsicBondSupport G hloc S x r)
    {ω | y ∈ intrinsicBall G (ω ∩ S) x r} p = _
  rw [finiteEventPolynomial_restrict]
  congr 2
  ext ω
  have hsub : (intrinsicBondSupport G hloc S x r : Set E) ⊆ S := by
    rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
  change (y ∈ intrinsicBall G ((ω ∩ _) ∩ S) x r) ↔ _
  rw [Set.inter_assoc,Set.inter_eq_left.mpr hsub,intrinsicBall_domain_restrict]

theorem intrinsicBall_probability_transfer (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Set E) (x y : V) (r : ℕ)
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : p ≤ q) :
    intrinsicBallPolynomial G hloc S x y r q ≤
      Real.exp ((r : ℝ) / p * ((q : ℝ) - p)) *
        intrinsicBallPolynomial G hloc S x y r p := by
  apply small_witness_probability_transfer _ _ _ r _ p q hp hpq
  · intro ω η hωη hy
    exact intrinsicBall_mono G (Set.inter_subset_inter_left S
      (show (ω : Set E) ⊆ η from hωη)) x r hy
  · intro ω _ hy
    exact intrinsicBall_small_witness G S x y r ω hy

noncomputable def intrinsicBallMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p : ℝ) : ℝ :=
  ∑ y ∈ (finite_reachBall hloc x r).toFinset, intrinsicBallPolynomial G hloc S x y r p

theorem intrinsicBallMoment_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (S : Set E) (x : V) (r : ℕ) (p : unitInterval) (hp : p < pc G) :
    intrinsicBallMoment G hloc S x r p ≤ susceptibility G p x := by
  apply (Finset.sum_le_sum (fun y _ => ?_)).trans
    ((summable_twoPoint_subcritical G hloc hqt p hp x).sum_le_tsum _
      (fun y _ => twoPoint_nonneg G p x y))
  rw [intrinsicBallPolynomial_eq]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  rintro ω ⟨l,hl,_,ho⟩
  exact hl.conn (fun e he => (ho e he).1)

theorem intrinsicBallMoment_transfer (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p q : unitInterval)
    (hp : 0 < (p : ℝ)) (hpq : p ≤ q) :
    intrinsicBallMoment G hloc S x r q ≤
      Real.exp ((r : ℝ) / p * ((q : ℝ) - p)) *
        intrinsicBallMoment G hloc S x r p := by
  unfold intrinsicBallMoment
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y _ => intrinsicBall_probability_transfer G hloc S x y r p q hp hpq)

theorem intrinsicBall_ncard_eq_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (r : ℕ) :
    ((intrinsicBall G ω x r).ncard : ℝ) =
      ∑ y ∈ (finite_reachBall hloc x r).toFinset,
        if y ∈ intrinsicBall G ω x r then (1 : ℝ) else 0 := by
  let B := (finite_reachBall hloc x r).toFinset.filter (fun y => y ∈ intrinsicBall G ω x r)
  have he : (B : Set V) = intrinsicBall G ω x r := by
    ext y
    simp only [B,Finset.mem_coe,Finset.mem_filter]
    exact and_iff_right_of_imp (fun hy => (finite_reachBall hloc x r).mem_toFinset.mpr
      (intrinsicBall_subset_reachBall G ω x r hy))
  rw [←he,Set.ncard_coe_finset]
  change (B.card : ℝ) = _
  rw [Finset.card_filter,Nat.cast_sum]
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he]

theorem measurableSet_mem_intrinsicBall_domain (G : BondGraph V E)
    (hloc : LocallyFinite G) (S : Set E) (x y : V) (r : ℕ) :
    MeasurableSet {ω | y ∈ intrinsicBall G (ω ∩ S) x r} := by
  let Q := intrinsicBondSupport G hloc S x r
  have he : {ω | y ∈ intrinsicBall G (ω ∩ S) x r} =
      {ω | ω ∩ (Q : Set E) ∈ {η | y ∈ intrinsicBall G (η ∩ S) x r}} := by
    ext ω
    have hsub : (Q : Set E) ⊆ S := by
      dsimp [Q]; rw [intrinsicBondSupport_coe]; exact Set.inter_subset_right
    change (y ∈ intrinsicBall G (ω ∩ S) x r) ↔
      (y ∈ intrinsicBall G ((ω ∩ (Q : Set E)) ∩ S) x r)
    rw [Set.inter_assoc,Set.inter_eq_left.mpr hsub,intrinsicBall_domain_restrict]
  rw [he]
  exact measurableSet_finite_restriction Q _

theorem integral_intrinsicBall_ncard_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p : unitInterval) :
    (∫ ω, ((intrinsicBall G (ω ∩ S) x r).ncard : ℝ) ∂law p) =
      intrinsicBallMoment G hloc S x r p := by
  simp_rw [intrinsicBall_ncard_eq_sum G hloc]
  rw [integral_finsetSum]
  · unfold intrinsicBallMoment
    apply Finset.sum_congr rfl
    intro y _
    rw [intrinsicBallPolynomial_eq]
    have heq : (fun ω : Set E => if y ∈ intrinsicBall G (ω ∩ S) x r then (1 : ℝ) else 0) =
        {ω | y ∈ intrinsicBall G (ω ∩ S) x r}.indicator 1 := by
      funext ω
      by_cases hy : y ∈ intrinsicBall G (ω ∩ S) x r <;> simp [Set.indicator,hy]
    rw [heq,integral_indicator_one (measurableSet_mem_intrinsicBall_domain G hloc S x y r)]
    rfl
  · intro y _
    have heq : (fun ω : Set E => if y ∈ intrinsicBall G (ω ∩ S) x r then (1 : ℝ) else 0) =
        {ω | y ∈ intrinsicBall G (ω ∩ S) x r}.indicator (fun _ => 1) := by
      funext ω
      by_cases hy : y ∈ intrinsicBall G (ω ∩ S) x r <;> simp [Set.indicator,hy]
    rw [heq]
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_mem_intrinsicBall_domain G hloc S x y r)

theorem integrable_intrinsicBall_ncard (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Set E) (x : V) (r : ℕ) (p : unitInterval) :
    Integrable (fun ω => ((intrinsicBall G (ω ∩ S) x r).ncard : ℝ)) (law p) := by
  simp_rw [intrinsicBall_ncard_eq_sum G hloc]
  apply integrable_finsetSum
  intro y _
  have heq : (fun ω : Set E => if y ∈ intrinsicBall G (ω ∩ S) x r then (1 : ℝ) else 0) =
      {ω | y ∈ intrinsicBall G (ω ∩ S) x r}.indicator (fun _ => 1) := by
    funext ω
    by_cases hy : y ∈ intrinsicBall G (ω ∩ S) x r <;> simp [Set.indicator,hy]
  rw [heq]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_mem_intrinsicBall_domain G hloc S x y r)

theorem critical_intrinsicBallMoment_linear [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (A : ℝ) (hA : 0 < A)
    (hχ : ∀ p : unitInterval, p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Set E) x (r : ℕ), 0 < r →
      intrinsicBallMoment G hloc S x r (pc G) ≤ C * r := by
  have hpc : 0 < (pc G : ℝ) := pc_pos G hloc hqt
  refine ⟨2 * Real.exp 1 * A / (pc G : ℝ),by positivity,fun S x r hr => ?_⟩
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  let p : unitInterval := ⟨(pc G : ℝ) * r / (r+1), by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < r+1)).mpr
      have hc := mul_le_mul_of_nonneg_right (pc G).2.2 hrR.le
      nlinarith⟩
  have hp0 : 0 < (p : ℝ) := by dsimp [p]; positivity
  have hp : p < pc G := by
    change (pc G : ℝ) * r / (r+1) < (pc G : ℝ)
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < r+1)).mpr
    nlinarith
  have hgap : (pc G : ℝ) - p = (pc G : ℝ) / (r+1) := by dsimp [p]; field_simp; ring
  have hexp : (r : ℝ) / p * ((pc G : ℝ) - p) = 1 := by
    rw [hgap]
    dsimp [p]
    field_simp
  calc
    _ ≤ Real.exp ((r : ℝ) / p * ((pc G : ℝ) - p)) *
        intrinsicBallMoment G hloc S x r p := intrinsicBallMoment_transfer G hloc S x r p (pc G) hp0 hp.le
    _ ≤ Real.exp 1 * (A / ((pc G : ℝ) - p)) := by
      rw [hexp]
      exact mul_le_mul_of_nonneg_left
        ((intrinsicBallMoment_le_susceptibility G hloc hqt S x r p hp).trans (hχ p hp x))
        (Real.exp_pos 1).le
    _ = Real.exp 1 * A / (pc G : ℝ) * (r+1) := by rw [hgap]; field_simp
    _ ≤ _ := by
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
      have hn : 0 ≤ Real.exp 1 * A / (pc G : ℝ) := by positivity
      calc
        _ ≤ (Real.exp 1 * A / (pc G : ℝ)) * (2*r) :=
          mul_le_mul_of_nonneg_left (by linarith) hn
        _ = _ := by ring

end Percolation.BenjaminiSchramm

end OAI
