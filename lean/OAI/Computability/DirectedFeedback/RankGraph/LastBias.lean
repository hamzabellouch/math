import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.PrefixBit

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (deleted : OutputVertex (M := M) G ψLaw → Bool)
variable (ord : OutputVertex (M := M) G ψLaw → ℕ)
variable (hord : ∀ {a b}, deleted a = false → deleted b = false →
  OutputArc G ψLaw hYX fiber a b → ord a < ord b)
variable (hrank : ∀ r, deleted (.inl r) = false)
variable {η ρ : ℝ} (hη : 0 ≤ η)
variable (haccuracy : 3*η*(rankLength X T : ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
variable (hs : Spreads ψLaw η)
include hord hrank hη haccuracy hs in
theorem big_badness :
    ((common (M := M) G ψLaw).product (bigMarginal G)).probability
      (fun a => decide (¬bigGood G ψLaw ord a.1 a.2)) ≤ ρ := by
  let prefLaw := (uniform (Fin T)).sigma (fun t =>
    (atomLaw (bigMarginal G) (subsetLaw (X := X) (M := M))).iid t.val)
  have hh := sampled_goodness hYX rankLength_ge hη haccuracy ψLaw hs
    (prefLaw.product (bigMarginal G))
    (fun a => Sum.inl ⟨⟨a.1.1.val+1, by have := a.1.1.isLt; omega⟩,
      Fin.snoc (vertices a.1.2) a.2⟩)
    (rankOrder G ψLaw ord) (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
  simp only [probability_eq_expect, expectation_product, common, commonLaw,
    bigGood, prefLaw] at hh ⊢
  apply le_trans (le_of_eq ?_) hh
  apply expectation_congr
  intro psi
  apply expectation_congr
  intro pre
  apply expectation_congr
  intro u
  rfl

include hord hrank hη haccuracy hs in
theorem small_badness :
    ((common (M := M) G ψLaw).product (smallMarginal G)).probability
      (fun a => decide (¬smallGood G ψLaw ord a.1 a.2)) ≤ ρ := by
  let prefLaw := (uniform (Fin T)).sigma (fun t =>
    (atomLaw (bigMarginal G) (subsetLaw (X := X) (M := M))).iid t.val)
  have hh := sampled_goodness hYX rankLength_ge hη haccuracy ψLaw hs
    (prefLaw.product (smallMarginal G))
    (fun a => Sum.inr ⟨a.1.1,vertices a.1.2,a.2⟩)
    (rankOrder G ψLaw ord) (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
  simp only [probability_eq_expect, expectation_product, common, commonLaw,
    smallGood, prefLaw] at hh ⊢
  apply le_trans (le_of_eq ?_) hh
  apply expectation_congr
  intro psi
  apply expectation_congr
  intro pre
  apply expectation_congr
  intro v
  rfl

include hord hrank hη haccuracy hs in
theorem edge_badness :
    ((common (M := M) G ψLaw).product G.edgeLaw).probability
      (fun a => decide (¬bigGood G ψLaw ord a.1 (G.left a.2))) ≤ ρ ∧
    ((common (M := M) G ψLaw).product G.edgeLaw).probability
      (fun a => decide (¬smallGood G ψLaw ord a.1 (G.right a.2))) ≤ ρ := by
  constructor
  · have hh := big_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hs
    simpa only [probability_eq_expect, expectation_product, bigMarginal,
      expectation_pushforward] using hh
  · have hh := small_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hs
    simpa only [probability_eq_expect, expectation_product, smallMarginal,
      expectation_pushforward] using hh

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Soundness
open DirectedFeedback.SourceProbability
open FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem acceptance_forces_tail (μ : FiniteDistribution Ω) (p : ℝ) (hp : 0 < p)
    (a b B : Ω → ℝ) (ha0 : ∀ ω, 0 ≤ a ω) (ha1 : ∀ ω, a ω ≤ 1)
    (hb1 : ∀ ω, b ω ≤ 1) (hbB : ∀ ω, b ω ≤ 2 * p * B ω)
    (hlower : p / 4 ≤ μ.expectation a)
    (hcomp : μ.expectation (fun ω => a ω * (1 - b ω)) ≤ p / 16) :
    p / 8 ≤ μ.probability (fun ω => decide (1 / (4 * p) ≤ B ω)) := by
  have hp4 : 0 < 4 * p := by positivity
  have hpoint (ω) : a ω ≤ 2 * (a ω * (1 - b ω)) +
      if 1 / (4 * p) ≤ B ω then 1 else 0 := by
    by_cases hh : 1 / (4 * p) ≤ B ω
    · simp only [hh, ↓reduceIte]
      have hz : 0 ≤ a ω * (1 - b ω) := mul_nonneg (ha0 ω) (sub_nonneg.mpr (hb1 ω))
      linarith [ha1 ω]
    · simp only [hh, ↓reduceIte, add_zero]
      have hsmall : 4 * p * B ω < 1 := by
        have hh' := (lt_div_iff₀ hp4).mp (lt_of_not_ge hh)
        nlinarith
      have hbhalf : b ω < 1 / 2 := by nlinarith [hbB ω]
      nlinarith [mul_nonneg (ha0 ω) (show 0 ≤ 1 / 2 - b ω by linarith)]
  have he := μ.expectation_mono hpoint
  have heq : μ.expectation (fun ω => 2 * (a ω * (1 - b ω)) +
      if 1 / (4 * p) ≤ B ω then 1 else 0) =
      2 * μ.expectation (fun ω => a ω * (1 - b ω)) +
        μ.probability (fun ω => decide (1 / (4 * p) ≤ B ω)) := by
    unfold expectation probability
    simp only [mul_add, Finset.sum_add_distrib, decide_eq_true_eq, mul_ite, mul_one, mul_zero]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [heq] at he
  linarith

theorem geometric_half_sum (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (2 : ℝ)^i / 2 =
    2^n - 1 / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem dyadic_layer_cake (M : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 * if 2^i ≤ x then 1 else 0) ≤ x := by
  induction M with
  | zero => simpa using hx
  | succ n ih =>
      by_cases hh : (2 : ℝ)^n ≤ x
      · calc
          _ ≤ ∑ i ∈ Finset.range (n + 1), (2 : ℝ)^i / 2 := by
            apply Finset.sum_le_sum
            intro i _
            split_ifs
            · simp
            · simp only [mul_zero]
              positivity
          _ = 2^n - 1 / 2 := geometric_half_sum n
          _ ≤ x := by linarith
      · simpa only [Finset.sum_range_succ, hh, ↓reduceIte, mul_zero, add_zero] using ih

theorem dyadic_tails_expectation (μ : FiniteDistribution Ω) (M : ℕ) (B : Ω → ℝ)
    (hB : ∀ ω, 0 ≤ B ω)
    (htail : ∀ i < M, (2 : ℝ)⁻¹ ^ (i + 2) / 8 ≤
      μ.probability (fun ω => decide (2^i ≤ B ω))) :
    (M : ℝ) / 64 ≤ μ.expectation B := by
  have he := μ.expectation_mono (fun ω => dyadic_layer_cake M (B ω) (hB ω))
  have heq : μ.expectation (fun ω =>
      ∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 * if 2^i ≤ B ω then 1 else 0) =
      ∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 *
        μ.probability (fun ω => decide (2^i ≤ B ω)) := by
    unfold expectation probability
    simp only [Finset.mul_sum, decide_eq_true_eq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [heq] at he
  calc
    _ = ∑ i ∈ Finset.range M, (2 : ℝ)^i / 2 * ((2 : ℝ)⁻¹ ^ (i + 2) / 8) := by
      have hterm (i : ℕ) : (2 : ℝ)^i / 2 * ((2 : ℝ)⁻¹ ^ (i + 2) / 8) = 1 / 64 := by
        rw [inv_pow, pow_add]
        have hz : (2 : ℝ)^i ≠ 0 := by positivity
        field_simp
        ring
      simp_rw [hterm]
      simp
      ring
    _ ≤ _ := (Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (htail i (Finset.mem_range.mp hi)) (by positivity))).trans he

theorem dyadic_contradiction (μ : FiniteDistribution Ω) (D : ℝ) (hD : 0 ≤ D)
    (M : ℕ) (hM : (M : ℝ) = 128 * (D + 1)) (B : Ω → ℝ)
    (hB0 : ∀ ω, 0 ≤ B ω) (hB : μ.expectation B ≤ D + 1)
    (a b : Fin M → Ω → ℝ) (ha0 : ∀ i ω, 0 ≤ a i ω) (ha1 : ∀ i ω, a i ω ≤ 1)
    (hb1 : ∀ i ω, b i ω ≤ 1)
    (hbB : ∀ i ω, b i ω ≤ 2 * ((2 : ℝ)⁻¹ ^ (i.val + 2)) * B ω)
    (hlower : ∀ i, (2 : ℝ)⁻¹ ^ (i.val + 2) / 4 ≤ μ.expectation (a i))
    (hcomp : ∀ i, μ.expectation (fun ω => a i ω * (1 - b i ω)) ≤
      (2 : ℝ)⁻¹ ^ (i.val + 2) / 16) : False := by
  have ht (i : ℕ) (hi : i < M) := acceptance_forces_tail μ ((2 : ℝ)⁻¹ ^ (i + 2))
    (by positivity) (a ⟨i, hi⟩) (b ⟨i, hi⟩) B (ha0 ⟨i, hi⟩) (ha1 ⟨i, hi⟩) (hb1 ⟨i, hi⟩) (hbB ⟨i, hi⟩)
    (hlower ⟨i, hi⟩) (hcomp ⟨i, hi⟩)
  have hthreshold (i : ℕ) : 1 / (4 * ((2 : ℝ)⁻¹ ^ (i + 2))) = 2^i := by
    rw [pow_add, inv_pow]
    have hz : (2 : ℝ)^i ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [hthreshold] at ht
  have hh := dyadic_tails_expectation μ M B hB0 ht
  rw [hM] at hh
  linarith

end DirectedFeedback.Soundness

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open PrefixExperiment Pivotal Games
variable {M : ℕ} [NeZero M]

def lastBias (M : ℕ) : ℝ := (2:ℝ)⁻¹^(M+1)

omit [NeZero M] in
theorem lastBias_le (i : Fin M) : lastBias M ≤ bias i := by
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have := i.isLt
  omega

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

theorem weighted_soundness
    (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
    (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
    (hproj : ∀ e x, (fiber e x).1 = G.project e x)
    (D H K η ρ γ θ : ℝ) (hD : 0 ≤ D) (hH : 0 < H) (hK : 0 < K)
    (hη : 0 ≤ η) (hγ : 0 < γ) (hM : (M:ℝ) = 128*(D+1))
    (haccuracy : 3*η*(rankLength X T : ℝ)^3*2^((Fintype.card X)^T) ≤ ρ)
    (hspreads : Spreads ψLaw η) (hρ : Fintype.card X * ρ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hfull : ρ+D/H ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (hJunta : DyadicJuntaBound M ((D+1)/γ) γ J)
    (hcomp : 2*ρ + M*(2:ℝ)^T*D/K + 6*γ + θ*(J:ℝ)^2 ≤ lastBias M/16)
    (hsound : G.Sound θ)
    (F : Finset (OutputVertex (M := M) G ψLaw))
    (hF : FeedbackR (OutputArc G ψLaw hYX fiber) F) :
    D < totalDeletionCost G ψLaw D H K (fun v => decide (v ∈ F)) := by
  by_contra hn
  have hcost := not_lt.mp hn
  let deleted : OutputVertex (M := M) G ψLaw → Bool := fun v => decide (v ∈ F)
  obtain ⟨ord, hord', _⟩ := exists_topological_order (OutputArc G ψLaw hYX fiber) F hF
  have hord : ∀ {a b}, deleted a = false → deleted b = false →
      OutputArc G ψLaw hYX fiber a b → ord a < ord b := by
    intro a b ha hb hab
    exact hord' a b (by simpa [deleted] using ha) (by simpa [deleted] using hb) hab
  have hrank := rank_retained G ψLaw D H K hD hH hK deleted hcost
  obtain ⟨hf,hb,hv,hc⟩ := family_costs G ψLaw deleted D H K hD hH.le hK.le hcost
  have hbu := big_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  have hbv := small_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  have hρY : (Fintype.card Y:ℝ)*ρ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hYX) hρ0).trans hρ
  let fx : X := Classical.choice inferInstance
  let fy : Y := Classical.choice inferInstance
  have hBu' := big_budget G ψLaw hYX fiber deleted ord hord hrank fx D ρ hρ hbu hb
  have hBv' := small_budget G ψLaw hYX fiber deleted ord hord hrank fy D ρ hρY hbv hv
  have hBu : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (bigBudget G ψLaw hYX fiber deleted ord hord hrank fx) ≤ D+1 := by
    simpa only [bigBudget, expectation_product, bigMarginal, expectation_pushforward] using hBu'
  have hBv : ((common (M := M) G ψLaw).product G.edgeLaw).expectation
      (smallBudget G ψLaw hYX fiber deleted ord hord hrank fy) ≤ D+1 := by
    simpa only [smallBudget, expectation_product, smallMarginal, expectation_pushforward] using hBv'
  have hbad := full_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  have hgoodprob := favorable_probability G ψLaw deleted ord D H ρ hH hf hbad hfull
  obtain ⟨hebu,hebv⟩ := edge_badness G ψLaw hYX fiber deleted ord hord hrank hη haccuracy hspreads
  apply Soundness.dyadic_contradiction ((common (M := M) G ψLaw).product G.edgeLaw)
    D hD M hM (smallBudget G ψLaw hYX fiber deleted ord hord hrank fy)
    (fun a => budget_nonneg _) hBv
    (bigAcceptance G ψLaw hYX fiber deleted ord hord hrank fx)
    (smallAcceptance G ψLaw hYX fiber deleted ord hord hrank fy)
  · intro i a
    exact probability_nonnegative _ _
  · intro i a
    exact probability_le_one _ _
  · intro i a
    exact probability_le_one _ _
  · intro i a
    have hp := smallFunction_properties G ψLaw hYX fiber deleted ord hord hrank fy a.1 (G.right a.2)
    exact acceptance_le_mul_budget _ hp.1 hp.2.1 (2*bias i)
      (mul_nonneg (by norm_num) (bias_pos i).le) (by linarith [bias_le_quarter i])
  · intro i
    have ha := full_acceptance G ψLaw hYX fiber deleted ord hord hrank fx hgoodprob i
    simpa only [bigAcceptance, expectation_product, bigMarginal, expectation_pushforward, bias] using ha
  · intro i
    have hh := independent_comparison G ψLaw hYX fiber deleted ord hord hrank fx fy i
      D K ρ γ θ hD hK hγ hsound hproj J hJ hJunta hBu hBv hc hebu hebv
    exact hh.trans (hcomp.trans (div_le_div_of_nonneg_right (lastBias_le i) (by norm_num)))

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I : Type*} [Fintype I]

theorem expectation_iid_prod (μ : FiniteDistribution I) (T : ℕ) (f : I → ℝ) :
    (μ.iid T).expectation (fun a => ∏ t, f (a t)) = (μ.expectation f)^T := by
  simp only [expectation, iid]
  simpa only [Finset.prod_mul_distrib] using
    (Fintype.sum_pow (fun i => μ.weight i * f i) T).symm

theorem probability_sublevel_exp (μ : FiniteDistribution I) (count : I → ℝ) (b : ℝ) :
    μ.probability (fun a => decide (count a < b)) ≤
      Real.exp b * μ.expectation (fun a => Real.exp (-count a)) := by
  rw [probability_eq_expect, ← expectation_mul_left]
  apply expectation_mono
  intro a
  by_cases ha : count a < b
  · simp only [ha, decide_true, ↓reduceIte]
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte]
    positivity

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution

def countTrue {T : ℕ} (a : Fin T → Bool) : ℝ := ∑ t, bitValue (a t)

theorem exp_neg_count {T : ℕ} (a : Fin T → Bool) :
    Real.exp (-countTrue a) = ∏ t, Real.exp (-bitValue (a t)) := by
  simp only [countTrue, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem expMoment_count (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (T : ℕ) :
    ((coin a ha0 ha1).iid T).expectation (fun x => Real.exp (-countTrue x)) =
      (1-a+a*Real.exp (-1))^T := by
  simp_rw [exp_neg_count]
  rw [expectation_iid_prod (coin a ha0 ha1) T (fun b => Real.exp (-bitValue b))]
  congr 1
  simp [expectation, coin, bitValue]
  ring

theorem expMoment_count_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (T : ℕ) :
    ((coin a ha0 ha1).iid T).expectation (fun x => Real.exp (-countTrue x)) ≤
      Real.exp (-(a*T)*(1-Real.exp (-1))) := by
  rw [expMoment_count]
  have hbase : 0 ≤ 1-a+a*Real.exp (-1) := by positivity
  have hbound : 1-a+a*Real.exp (-1) ≤ Real.exp (a*(Real.exp (-1)-1)) := by
    nlinarith [Real.add_one_le_exp (a*(Real.exp (-1)-1))]
  have hp := pow_le_pow_left₀ hbase hbound T
  calc
    _ ≤ (Real.exp (a*(Real.exp (-1)-1)))^T := hp
    _ = Real.exp (-(a*T)*(1-Real.exp (-1))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem exp_neg_one_le : Real.exp (-1) ≤ (3:ℝ)/8 := by
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 by norm_num) 4
  norm_num [Finset.sum_range_succ] at h
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith)

theorem bernoulli_lower_tail (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (T : ℕ) :
    ((coin a ha0 ha1).iid T).probability (fun x => decide (countTrue x < (a*T)/2)) ≤
      Real.exp (-(a*T)/8) := by
  calc
    _ ≤ Real.exp ((a*T)/2) *
        ((coin a ha0 ha1).iid T).expectation (fun x => Real.exp (-countTrue x)) :=
      probability_sublevel_exp _ _ _
    _ ≤ Real.exp ((a*T)/2) * Real.exp (-(a*T)*(1-Real.exp (-1))) :=
      mul_le_mul_of_nonneg_left (expMoment_count_le a ha0 ha1 T) (Real.exp_nonneg _)
    _ ≤ Real.exp (-(a*T)/8) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hμ : 0 ≤ a*T := mul_nonneg ha0 (Nat.cast_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_one_le hμ]

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem pushforward_bool (μ : FiniteDistribution Ω) (event : Ω → Bool) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (he : μ.probability event = p) :
    μ.pushforward event = DirectedFeedback.Pivotal.coin p hp0 hp1 := by
  apply eq_of_weight_eq
  intro b
  have ht : (μ.pushforward event).weight true = p := by
    calc
      _ = μ.probability event := by
        unfold pushforward probability
        apply Finset.sum_congr rfl
        intro x _
        cases event x <;> simp
      _ = p := he
  have hn := (μ.pushforward event).normalized
  simp only [Fintype.sum_bool] at hn
  cases b
  · change (μ.pushforward event).weight false = 1-p
    linarith
  · exact ht

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem iid_event_lower_tail (μ : FiniteDistribution Ω) (event : Ω → Bool)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (he : μ.probability event = p) (T : ℕ) :
    (μ.iid T).probability (fun a => decide (countTrue (fun t => event (a t)) < p*T/2)) ≤
      Real.exp (-(p*T)/8) := by
  rw [← probability_pushforward (μ.iid T) (fun a t => event (a t))
      (fun b => decide (countTrue b < p*T/2)), ← iid_pushforward,
    pushforward_bool μ event p hp0 hp1 he]
  exact bernoulli_lower_tail p hp0 hp1 T

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Coupling
open DirectedFeedback.SourceProbability FiniteDistribution
variable {X Y : Type} [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem support_inclusion (e : X ≃ Y × Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (z : Y → Block) (hz : (law p hp0 hp).weight z ≠ 0) (x : X) :
    bigBits e z x = true → smallBits z (e x).1 = true := by
  have hprod : (∏ y, blockWeight p (z y)) ≠ 0 := hz
  have hblock : blockWeight p (z (e x).1) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hprod) _ (Finset.mem_univ _)
  intro hx
  apply block_inclusion p _ hblock
  change (if (e x).2 = true then (z (e x).1).1.2 else (z (e x).1).1.1) = true at hx
  split at hx
  · exact Or.inr hx
  · exact Or.inl hx

end DirectedFeedback.Coupling

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (fiber : E → X ≃ Y × Bool) (hproject : ∀ e x, (fiber e x).1 = G.project e x)

omit [Fintype V] [Nonempty X] [Nonempty Y] in
theorem comparison_support_coupling (d : ComparisonSupport (M := M) G ψLaw) :
    (Coupling.law (Y := Y) (bias d.val.2.2.1) (bias_pos _).le
      (by linarith [bias_le_quarter d.val.2.2.1])).weight d.val.2.2.2.2 ≠ 0 := by
  intro hz
  have he : (comparisonLaw G ψLaw).weight d.val = 0 := by
    simp only [comparisonLaw, sigma, product, hz, mul_zero]
  linarith [d.property]

include hproject in
omit [Fintype V] [Nonempty X] [Nonempty Y] in

theorem comparison_label_increases (ellU : U → X) (ellV : V → Y)
    (d : ComparisonSupport (M := M) G ψLaw)
    (hsat : G.project d.val.2.1 (ellU (G.left d.val.2.1)) = ellV (G.right d.val.2.1)) :
    eval ellU ellV (comparison G fiber d.val).source <
      eval ellU ellV (comparison G fiber d.val).target := by
  let pref : Fin d.val.1.2.1.val → X := fun j => ellU (vertices d.val.1.2.2 j)
  let xu := ellU (G.left d.val.2.1)
  let yv := ellV (G.right d.val.2.1)
  have himp : Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2 xu = true →
      Coupling.smallBits d.val.2.2.2.2 yv = true := by
    have he : (fiber d.val.2.1 xu).1 = yv := (hproject _ _).trans hsat
    rw [← he]
    exact Coupling.support_inclusion _ _ _ _ _ (comparison_support_coupling G ψLaw d) _
  have hlabels : labels ellU ellV
      (.inl ⟨⟨d.val.1.2.1.val+1, by exact Nat.succ_lt_succ d.val.1.2.1.isLt⟩,
        Fin.snoc (vertices d.val.1.2.2) (G.left d.val.2.1)⟩) = Fin.snoc pref xu := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [labels, pref, xu]
    · simp [labels, pref, xu]
  simp only [comparison, twoLevel, eval_vertex, hlabels, Set.mem_preimage, splitLast,
    Equiv.coe_fn_mk, Fin.init_snoc, Fin.snoc_last]
  change (if (pref,yv) ∈ conditionedSet (cell d.val.1.2.2) d.val.2.2.2.1
      {y | Coupling.smallBits d.val.2.2.2.2 y = true} then d.val.1.1.val ⟨1,_⟩ else d.val.1.1.val ⟨16,_⟩) <
    (if (pref,xu) ∈ conditionedSet (cell d.val.1.2.2) d.val.2.2.2.1
      {x | Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2 x = true} then d.val.1.1.val ⟨2,_⟩ else d.val.1.1.val ⟨17,_⟩)
  by_cases hbefore : (cell d.val.1.2.2 pref).val < d.val.2.2.2.1.val
  · simp only [conditionedSet, Set.mem_ofPred_eq, hbefore, true_or, ↓reduceIte]
    apply d.val.1.1.property; change (1 : ℕ) < 2; omega
  · by_cases heq : cell d.val.1.2.2 pref = d.val.2.2.2.1
    · simp only [conditionedSet, Set.mem_ofPred_eq, heq, lt_self_iff_false, false_or, true_and]
      by_cases hu : Coupling.bigBits (fiber d.val.2.1) d.val.2.2.2.2 xu = true
      · simp only [hu, himp hu, ↓reduceIte]
        apply d.val.1.1.property; change (1 : ℕ) < 2; omega
      · simp only [hu]
        split
        · apply d.val.1.1.property; change (1 : ℕ) < 17; omega
        · apply d.val.1.1.property; change (16 : ℕ) < 17; omega
    · simp only [conditionedSet, Set.mem_ofPred_eq, hbefore, false_or, heq, false_and, ↓reduceIte]
      apply d.val.1.1.property; change (16 : ℕ) < 17; omega

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open PrefixExperiment Pivotal Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [NeZero M] [Nonempty X] in
theorem subset_eval_probability (i : Fin M) (x : X) :
    (subsetLaw i).probability (fun b => b x) = bias i := by
  rw [probability_eq_expect]
  unfold subsetLaw Pivotal.law
  rw [expectation_table_eval (fun _ : X => coin (bias i) (bias_pos i).le
    (by linarith [bias_le_quarter i])) x (fun b : Bool => if b then 1 else 0)]
  simp [expectation, coin]

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] in

theorem slot_label_probability (G : Game U V E X Y) (ell : U → X) (i : Fin M) :
    (atomLaw (bigMarginal G) subsetLaw).probability
      (fun a => decide (a.2.1 = i) && a.2.2 (ell a.1)) = bias i / M := by
  rw [probability_eq_expect]
  have hind (a : Slot U X M) :
      (if decide (a.2.1 = i) && a.2.2 (ell a.1) then (1:ℝ) else 0) =
      if a.2.1 = i then (if a.2.2 (ell a.1) then 1 else 0) else 0 := by
    by_cases hi : a.2.1 = i <;> cases a.2.2 (ell a.1) <;> simp [hi]
  simp_rw [hind]
  have he := fresh_index_expectation (bigMarginal G) subsetLaw i
    (fun u b => if b (ell u) then 1 else 0)
  calc
    _ = (1 / (Fintype.card (Fin M) : ℝ)) * (bigMarginal G).expectation
        (fun u => (subsetLaw i).expectation (fun b => if b (ell u) then 1 else 0)) := by
      convert he using 1
      apply expectation_congr
      intro a
      by_cases hi : a.2.1 = i <;> simp [hi]
    _ = bias i / M := by
      simp_rw [← probability_eq_expect, subset_eval_probability, expectation_const]
      simp [div_eq_mul_inv, mul_comm]

omit [NeZero T] [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] in

theorem fullCount_lower_tail (G : Game U V E X Y) (ell : U → X) (i : Fin M) :
    ((atomLaw (bigMarginal G) subsetLaw).iid T).probability (fun a =>
      decide ((fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M))) ≤
      Real.exp (-(bias i*T/(8*M))) := by
  have hM : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hp0 : 0 ≤ bias i / M := (div_pos (bias_pos i) hM).le
  have hp1 : bias i / M ≤ 1 := (div_le_one hM).mpr (by linarith [bias_le_quarter i])
  have hh := iid_event_lower_tail (atomLaw (bigMarginal G) subsetLaw)
    (fun a => decide (a.2.1 = i) && a.2.2 (ell a.1)) (bias i / M) hp0 hp1
    (slot_label_probability G ell i) T
  have hc (a : PrefixData U X M T) :
      countTrue (fun t => decide ((a t).2.1 = i) && (a t).2.2 (ell (a t).1)) =
        (fullCount a i (fun t => ell (vertices a t)) : ℝ) := by
    simp only [countTrue, fullCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hi : (a t).2.1 = i <;> cases hb : (a t).2.2 (ell (a t).1) <;> simp [hi,hb,bitValue,vertices]
  simp_rw [hc] at hh
  have he1 : bias i / (M:ℝ) * T / 2 = bias i*T/(2*M) := by ring
  have he2 : -(bias i / (M:ℝ) * T) / 8 = -(bias i*T/(8*M)) := by ring
  simpa only [he1, he2] using hh

omit [Fintype V] [Fintype Y] [Nonempty X] [Nonempty Y] [NeZero T] in

theorem fullStars_probability (G : Game U V E X Y)
    (ψLaw : FiniteDistribution (Emb (rankLength X T) N)) (ell : U → X) :
    (fullLaw (M := M) G ψLaw).probability (fun d =>
      decide ((fun t => ell (vertices d.2 t)) ∈ fullStars d.2)) ≤
      M * Real.exp (-(lastBias M * T/(8*M))) := by
  rw [fullLaw, probability_eq_expect, expectation_product]
  dsimp only
  have he : (ψLaw.expectation fun _ =>
      ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T).probability (fun a =>
        decide ((fun t => ell (vertices a t)) ∈ fullStars a))) =
      ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T).probability (fun a =>
        decide ((fun t => ell (vertices a t)) ∈ fullStars a)) := expectation_const _ _
  apply le_trans (le_of_eq (Eq.trans ?_ he))
  swap
  · simp only [probability_eq_expect]
  have hu := probability_exists_le_sum ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T)
    (fun i a => decide ((fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M)))
  simp only [decide_eq_true_eq] at hu
  apply le_trans (b := ∑ i : Fin M, ((atomLaw (bigMarginal G) (subsetLaw (M := M))).iid T).probability
    (fun a => decide ((fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M))))
  · have hev : (fun a : PrefixData U X M T =>
          decide ((fun t => ell (vertices a t)) ∈ fullStars a)) =
        (fun a => decide (∃ i : Fin M,
          (fullCount a i (fun t => ell (vertices a t)) : ℝ) < bias i*T/(2*M))) := by
      funext a
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, decide_eq_true_eq]
      rfl
    rw [hev]
    exact hu
  calc
    _ ≤ ∑ i : Fin M, Real.exp (-(bias i*T/(8*M))) :=
      Finset.sum_le_sum (fun i _ => fullCount_lower_tail G ell i)
    _ ≤ ∑ _i : Fin M, Real.exp (-(lastBias M*T/(8*M))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (lastBias_le i)
        (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by simp

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem labelOrder_label_probability (x : I) :
    labelOrderLaw.probability (fun o : LabelOrder I => decide (x = o.1)) =
      1 / Fintype.card I := by
  rw [probability_eq_expect, labelOrderLaw, expectation_sigma]
  simp only [expectation_const, decide_eq_true_eq]
  rw [expectation_uniform]
  simp

end DirectedFeedback.Pivotal

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]
variable (G : Game U V E X Y) (ψLaw : FiniteDistribution (Emb (rankLength X T) N))
variable (hYX : Fintype.card Y ≤ Fintype.card X) (fiber : E → X ≃ Y × Bool)
variable (ellU : U → X) (ellV : V → Y)

def labelDeleted : OutputVertex (M := M) G ψLaw → Bool :=
  fun v => decide (TestGraph.LabelDeleted (wildSupport G ψLaw hYX)
    (compSupport G ψLaw fiber) ellU ellV v)

def labelFeedback : Finset (OutputVertex (M := M) G ψLaw) :=
  Finset.univ.filter (TestGraph.LabelDeleted (wildSupport G ψLaw hYX)
    (compSupport G ψLaw fiber) ellU ellV)

theorem labelFeedback_spec :
    FeedbackR (OutputArc G ψLaw hYX fiber) (labelFeedback (M := M) G ψLaw hYX fiber ellU ellV) := by
  exact TestGraph.labelDeleted_feedback _ _ ellU ellV

theorem labelFeedback_indicator :
    (fun v => decide (v ∈ labelFeedback (M := M) G ψLaw hYX fiber ellU ellV)) =
      labelDeleted (M := M) G ψLaw hYX fiber ellU ellV := by
  funext v
  simp only [labelFeedback, Finset.mem_filter, Finset.mem_univ, true_and, labelDeleted]

theorem full_label_cost :
    (fullLaw (M := M) G ψLaw).probability
      (fullDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) ≤
      M * Real.exp (-(lastBias M*T/(8*M))) := by
  rw [fullDeleted, probability_extend]
  have he : (fullLaw (M := M) G ψLaw).supported.probability (fun d =>
      labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inl (.inl d)))) =
      (fullLaw (M := M) G ψLaw).probability (fun d =>
        decide ((fun t => ellU (vertices d.2 t)) ∈ fullStars d.2)) := by
    exact probability_supported (fullLaw (M := M) G ψLaw)
      (fun d => decide ((fun t => ellU (vertices d.2 t)) ∈ fullStars d.2))
  rw [he]
  exact fullStars_probability G ψLaw ellU

theorem big_label_cost :
    Fintype.card X * (bigLaw (M := M) G ψLaw).probability
      (bigDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) = 1 := by
  rw [bigDeleted, probability_extend]
  have he : (bigLaw (M := M) G ψLaw).supported.probability (fun d =>
      labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inl (.inr (.inl d))))) =
      (bigLaw (M := M) G ψLaw).probability (fun d => decide (ellU d.2.1 = d.2.2.1)) := by
    convert probability_supported (bigLaw (M := M) G ψLaw)
      (fun d => decide (ellU d.2.1 = d.2.2.1)) using 1
    apply congrArg (fun f => (bigLaw (M := M) G ψLaw).supported.probability f)
    funext d
    apply Bool.eq_iff_iff.mpr
    simp only [labelDeleted, decide_eq_true_eq]
    change (ellU (Fin.snoc (α := fun _ => U) (vertices d.val.1.2.2) d.val.2.1
      (Fin.last d.val.1.2.1.val)) = d.val.2.2.1) ↔ _
    simp only [Fin.snoc_last]
  rw [he, bigLaw, probability_eq_expect]
  simp only [expectation_product]
  simp_rw [← probability_eq_expect, labelOrder_label_probability, expectation_const]
  have hc : (Fintype.card X:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem small_label_cost :
    Fintype.card Y * (smallLaw (M := M) G ψLaw).probability
      (smallDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) = 1 := by
  rw [smallDeleted, probability_extend]
  have he : (smallLaw (M := M) G ψLaw).supported.probability (fun d =>
      labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inl (.inr (.inr d))))) =
      (smallLaw (M := M) G ψLaw).probability (fun d => decide (ellV d.2.1 = d.2.2.1)) := by
    exact probability_supported (smallLaw (M := M) G ψLaw)
      (fun d => decide (ellV d.2.1 = d.2.2.1))
  rw [he, smallLaw, probability_eq_expect]
  simp only [expectation_product]
  simp_rw [← probability_eq_expect, labelOrder_label_probability, expectation_const]
  have hc : (Fintype.card Y:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

include fiber in
theorem comparison_label_cost (hproject : ∀ e x, (fiber e x).1 = G.project e x) :
    (comparisonLaw (M := M) G ψLaw).probability
      (comparisonDeleted G ψLaw (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV)) ≤
      1-G.score ellU ellV := by
  rw [comparisonDeleted, probability_extend]
  have hm := probability_mono (μ := (comparisonLaw (M := M) G ψLaw).supported)
    (event := fun d => labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inr (.inr d)))
    (event' := fun d => decide (G.project d.val.2.1 (ellU (G.left d.val.2.1)) ≠ ellV (G.right d.val.2.1))) (by
      intro d hd
      apply decide_eq_true
      intro hs
      have hi := comparison_label_increases G ψLaw fiber hproject ellU ellV d hs
      have hd' : TestGraph.LabelDeleted (wildSupport G ψLaw hYX)
        (compSupport G ψLaw fiber) ellU ellV (.inr (.inr d)) := of_decide_eq_true hd
      exact not_le.mpr hi hd')
  apply hm.trans_eq
  have he := probability_supported (comparisonLaw (M := M) G ψLaw)
    (fun d => decide (G.project d.2.1 (ellU (G.left d.2.1)) ≠ ellV (G.right d.2.1)))
  rw [he, comparisonLaw, probability_eq_expect, expectation_sigma]
  trans (common (M := M) G ψLaw).expectation (fun _ =>
    G.edgeLaw.probability (fun e => decide (G.project e (ellU (G.left e)) ≠ ellV (G.right e))))
  · apply expectation_congr
    intro d
    rw [expectation_product, probability_eq_expect]
    apply expectation_congr
    intro e
    exact expectation_const ((uniform (Fin M)).sigma (fun i =>
      (uniform (Fin (cellCount d.2.1.val))).product
        (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i]))))
      (if decide (G.project e (ellU (G.left e)) ≠ ellV (G.right e)) then 1 else 0)
  rw [expectation_const]
  have hh := probability_not G.edgeLaw
    (fun e => decide (G.project e (ellU (G.left e)) = ellV (G.right e)))
  simpa only [decide_not, Game.score] using hh

theorem weighted_completeness (hproject : ∀ e x, (fiber e x).1 = G.project e x)
    (D H K : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K) :
    totalDeletionCost G ψLaw D H K (labelDeleted (M := M) G ψLaw hYX fiber ellU ellV) ≤
      H * (M * Real.exp (-(lastBias M*T/(8*M)))) + 2 + K*(1-G.score ellU ellV) := by
  rw [deletionCost_decomposition]
  have hr : (∑ r : Rank U V X Y T N,
      if labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inl r) then D+1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    have h : labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inl r) = false := by
      cases e : labelDeleted (M := M) G ψLaw hYX fiber ellU ellV (.inl r) with
      | false => rfl
      | true => exact False.elim (of_decide_eq_true e : TestGraph.LabelDeleted
          (wildSupport G ψLaw hYX) (compSupport G ψLaw fiber) ellU ellV (.inl r))
    rw [h]
    rfl
  rw [hr, zero_add, big_label_cost, small_label_cost]
  have hf := mul_le_mul_of_nonneg_left (full_label_cost (M := M) G ψLaw hYX fiber ellU ellV) hH
  have hc := mul_le_mul_of_nonneg_left
    (comparison_label_cost (M := M) G ψLaw hYX fiber ellU ellV hproject) hK
  linarith

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open Pivotal

structure Parameters (D : ℕ) where
  M : ℕ
  T : ℕ
  K : ℕ
  J : ℕ
  M_eq : M = 128*(D+1)
  T_pos : 0 < T
  K_pos : 0 < K
  J_pos : 1 ≤ J
  theta : ℚ
  theta_pos : 0 < theta
  theta_half : (theta : ℝ) < 1/2
  fullChernoff : (8*((D:ℝ)+1)) * (M * Real.exp (-(lastBias M*T/(8*M)))) ≤ 1
  comparison : (M:ℝ)*2^T*D/K ≤ lastBias M/1000
  junta : DyadicJuntaBound M (((D:ℝ)+1)/(lastBias M/1000)) (lastBias M/1000) J
  Ktheta : (K:ℝ)*theta ≤ 1
  Jtheta : (theta:ℝ)*(J:ℝ)^2 ≤ lastBias M/1000

theorem exists_parameters (D : ℕ) : Nonempty (Parameters D) := by
  let M := 128*(D+1)
  let H : ℝ := 8*((D:ℝ)+1)
  let p := lastBias M
  let γ := p/1000
  have hM : (0:ℝ) < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hp : 0 < p := by dsimp [p, lastBias]; positivity
  have hg : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨T, hT⟩ := exists_nat_gt (8*M*(H*M)/p)
  have hT0 : 0 < T := by
    have ht : (0:ℝ) < T := lt_of_le_of_lt (by positivity) hT
    exact_mod_cast ht
  have hprefix : H * (M * Real.exp (-(p*T/(8*M)))) ≤ 1 := by
    have harg : H*M ≤ p*T/(8*M) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have hh := (div_lt_iff₀ hp).mp hT
      nlinarith
    calc
      _ = (H*M)/Real.exp (p*T/(8*M)) := by rw [Real.exp_neg]; ring
      _ ≤ 1 := (div_le_one (Real.exp_pos _)).mpr
        (harg.trans (by linarith [Real.add_one_le_exp (p*T/(8*M))]))
  obtain ⟨K, hK⟩ := exists_nat_gt (max 0 ((M:ℝ)*2^T*D/γ))
  have hK0 : (0:ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
  have hKnat : 0 < K := by exact_mod_cast hK0
  have hcomparison : (M:ℝ)*2^T*D/K ≤ γ := by
    apply (div_le_iff₀ hK0).mpr
    have hh := (div_lt_iff₀ hg).mp (lt_of_le_of_lt (le_max_right _ _) hK)
    linarith
  obtain ⟨J,hJ,hjunta⟩ := uniform_dyadic_junta M (((D:ℝ)+1)/γ) γ (by positivity) hg
  have hJ0 : (0:ℝ) < J := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  let t : ℝ := min (1/4) (min (1/K) (γ/(J:ℝ)^2))
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨θ,hθ0,hθ⟩ := exists_rat_btwn ht
  have hθnat : (0:ℚ) < θ := by exact_mod_cast hθ0
  have ht1 : (θ:ℝ) < 1/4 := hθ.trans_le (min_le_left _ _)
  have htK : (θ:ℝ) < 1/(K:ℝ) := hθ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htJ : (θ:ℝ) < γ/(J:ℝ)^2 := hθ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨⟨M,T,K,J,rfl,hT0,hKnat,hJ,θ,hθnat,by linarith,hprefix,hcomparison,hjunta,?_,?_⟩⟩
  · have hh := (lt_div_iff₀ hK0).mp htK
    nlinarith
  · exact ((lt_div_iff₀ (sq_pos_of_pos hJ0)).mp htJ).le

namespace Parameters
variable {D : ℕ} (P : Parameters D)

instance : NeZero P.M := ⟨by rw [P.M_eq]; omega⟩
instance : NeZero P.T := ⟨ne_of_gt P.T_pos⟩

theorem gamma_pos : 0 < lastBias P.M/1000 := by unfold lastBias; positivity

theorem gamma_le : lastBias P.M/1000 ≤ 1/1000 := by
  have hp : lastBias P.M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

theorem full_error (ρ : ℝ) (hρ : ρ ≤ lastBias P.M/1000) :
    ρ + (D:ℝ)/(8*((D:ℝ)+1)) ≤ 1/2 := by
  have hsmall : (D:ℝ)/(8*((D:ℝ)+1)) ≤ 1/8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  linarith [P.gamma_le]

theorem product_error (ρ : ℝ) (hρ : ρ ≤ lastBias P.M/1000) :
    2*ρ + P.M*(2:ℝ)^P.T*D/P.K + 6*(lastBias P.M/1000) +
      (P.theta:ℝ)*(P.J:ℝ)^2 ≤ lastBias P.M/16 := by
  have hp : 0 < lastBias P.M := by unfold lastBias; positivity
  linarith [P.comparison,P.Jtheta]

end Parameters
end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks

structure RankParameters {D : ℕ} (P : Parameters D) (X : Type) [Fintype X] where
  N : ℕ
  law : FiniteDistribution (Emb (rankLength X P.T) N)
  eta : ℝ
  rho : ℝ
  eta_pos : 0 < eta
  rho_nonneg : 0 ≤ rho
  rho_small : rho ≤ lastBias P.M/1000
  rho_alphabet : Fintype.card X * rho ≤ 1
  accuracy : 3*eta*(rankLength X P.T : ℝ)^3*2^((Fintype.card X)^P.T) ≤ rho
  spreads : Spreads law eta
  rational : ∀ ψ, ∃ q : ℚ, law.weight ψ = q

theorem exists_rankParameters {D : ℕ} (P : Parameters D) (X : Type)
    [Fintype X] [Nonempty X] : Nonempty (RankParameters P X) := by
  let m : ℝ := Fintype.card X
  let ρ := min (lastBias P.M/1000) (1/m)
  let L := rankLength X P.T
  let η := ρ / (3*(L:ℝ)^3*2^((Fintype.card X)^P.T))
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  have hρ : 0 < ρ := lt_min P.gamma_pos (div_pos (by norm_num) hm)
  have hL : 3 ≤ L := by dsimp [L, rankLength]; omega
  have hLc : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N,_,μ,hs,hr⟩ := exists_spreading_law L hL η hη
  refine ⟨⟨N,μ,η,ρ,hη,hρ.le,min_le_left _ _,?_,?_,hs,hr⟩⟩
  · have hh := min_le_right (lastBias P.M/1000) (1/m)
    have hb := (le_div_iff₀ hm).mp hh
    dsimp [m] at hb ⊢
    nlinarith
  · dsimp only [η]
    have hden : (3:ℝ)*(L:ℝ)^3*2^((Fintype.card X)^P.T) ≠ 0 := by positivity
    field_simp
    ring_nf
    rfl

variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

end DirectedFeedback.Construction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
