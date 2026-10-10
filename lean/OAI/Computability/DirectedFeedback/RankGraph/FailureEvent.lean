import Mathlib
import OAI.Computability.DirectedFeedback.RankGraph.Bias

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
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal
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

theorem bigFunction_properties (fallback : X) (d : Common U X M T N) (u : U) :
    Monotone (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u) ∧
      bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u (fun _ => false) = false ∧
      bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback d u (fun _ => true) = true := by
  obtain ⟨hm,h0,h1⟩ := conditionedBig_properties (rankOrder G ψLaw ord) d.1.val rankLength_ge
    d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
    d.2.1 (vertices d.2.2) (cell d.2.2) u fallback
  exact subset_function_properties _ hm h0 h1

theorem smallFunction_properties (fallback : Y) (d : Common U X M T N) (v : V) :
    Monotone (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d v) ∧
      smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d v (fun _ => false) = false ∧
      smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback d v (fun _ => true) = true := by
  obtain ⟨hm,h0,h1⟩ := conditionedSmall_properties (rankOrder G ψLaw ord) d.1.val rankLength_ge
    d.1.property (rankOrder_arc G ψLaw hYX fiber deleted ord hord hrank)
    d.2.1 (vertices d.2.2) (cell d.2.2) v fallback
  exact subset_function_properties _ hm h0 h1

theorem family_costs (D H K : ℝ) (hD : 0 ≤ D) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hcost : totalDeletionCost G ψLaw D H K deleted ≤ D) :
    H * (fullLaw G ψLaw).probability (fullDeleted G ψLaw deleted) ≤ D ∧
    Fintype.card X * (bigLaw G ψLaw).probability (bigDeleted G ψLaw deleted) ≤ D ∧
    Fintype.card Y * (smallLaw G ψLaw).probability (smallDeleted G ψLaw deleted) ≤ D ∧
    K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D := by
  rw [deletionCost_decomposition] at hcost
  have hr : 0 ≤ ∑ r : Rank U V X Y T N, if deleted (.inl r) then D+1 else 0 := by
    apply Finset.sum_nonneg
    intro r _
    split <;> linarith
  have hf := mul_nonneg hH (probability_nonnegative (fullLaw G ψLaw) (fullDeleted G ψLaw deleted))
  have hb := mul_nonneg (Nat.cast_nonneg (Fintype.card X) : (0:ℝ) ≤ Fintype.card X)
    (probability_nonnegative (bigLaw G ψLaw) (bigDeleted G ψLaw deleted))
  have hs := mul_nonneg (Nat.cast_nonneg (Fintype.card Y) : (0:ℝ) ≤ Fintype.card Y)
    (probability_nonnegative (smallLaw G ψLaw) (smallDeleted G ψLaw deleted))
  have hc := mul_nonneg hK (probability_nonnegative (comparisonLaw G ψLaw) (comparisonDeleted G ψLaw deleted))
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem big_budget (fallback : X) (D ρ : ℝ) (hρ : Fintype.card X * ρ ≤ 1)
    (hbad : ((common (M := M) G ψLaw).product (bigMarginal G)).probability
      (fun a => decide (¬bigGood G ψLaw ord a.1 a.2)) ≤ ρ)
    (hcost : Fintype.card X * (bigLaw G ψLaw).probability (bigDeleted G ψLaw deleted) ≤ D) :
    ((common (M := M) G ψLaw).product (bigMarginal G)).expectation
      (fun a => budget (bigFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 a.2)) ≤ D+1 := by
  apply averaged_budget_charge_support _ _ (fun a => decide (bigGood G ψLaw ord a.1 a.2))
    (fun a o => bigDeleted G ψLaw deleted (a.1,(a.2,o))) D ρ hρ
  · simpa using hbad
  · simpa only [bigLaw, probability_eq_expect, expectation_product] using hcost
  · intro a ha hg o hh
    have hd : 0 < (bigLaw G ψLaw).weight (a.1,(a.2,o)) := by
      change 0 < (common G ψLaw).weight a.1 * ((bigMarginal G).weight a.2 * labelOrderLaw.weight o)
      rw [← mul_assoc]
      exact mul_pos ha (labelOrder_weight_pos o)
    change (bigLaw G ψLaw).extend _ _ = true
    rw [show (a.1,(a.2,o)) = (⟨(a.1,(a.2,o)),hd⟩ : (bigLaw G ψLaw).Support).val from rfl,
        extend_at_support]
    exact big_forces_deletion G ψLaw hYX fiber deleted ord hord hrank _ fallback
      (of_decide_eq_true hg) hh

theorem small_budget (fallback : Y) (D ρ : ℝ) (hρ : Fintype.card Y * ρ ≤ 1)
    (hbad : ((common (M := M) G ψLaw).product (smallMarginal G)).probability
      (fun a => decide (¬smallGood G ψLaw ord a.1 a.2)) ≤ ρ)
    (hcost : Fintype.card Y * (smallLaw G ψLaw).probability (smallDeleted G ψLaw deleted) ≤ D) :
    ((common (M := M) G ψLaw).product (smallMarginal G)).expectation
      (fun a => budget (smallFunction G ψLaw hYX fiber deleted ord hord hrank fallback a.1 a.2)) ≤ D+1 := by
  apply averaged_budget_charge_support _ _ (fun a => decide (smallGood G ψLaw ord a.1 a.2))
    (fun a o => smallDeleted G ψLaw deleted (a.1,(a.2,o))) D ρ hρ
  · simpa using hbad
  · simpa only [smallLaw, probability_eq_expect, expectation_product] using hcost
  · intro a ha hg o hh
    have hd : 0 < (smallLaw G ψLaw).weight (a.1,(a.2,o)) := by
      change 0 < (common G ψLaw).weight a.1 * ((smallMarginal G).weight a.2 * labelOrderLaw.weight o)
      rw [← mul_assoc]
      exact mul_pos ha (labelOrder_weight_pos o)
    change (smallLaw G ψLaw).extend _ _ = true
    rw [show (a.1,(a.2,o)) = (⟨(a.1,(a.2,o)),hd⟩ : (smallLaw G ψLaw).Support).val from rfl,
        extend_at_support]
    exact small_forces_deletion G ψLaw hYX fiber deleted ord hord hrank _ fallback
      (of_decide_eq_true hg) hh

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I Z : Type*} [Fintype I] [Nonempty I] [Fintype Z]

theorem uniform_single_le (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) (i : I) :
    f i ≤ Fintype.card I * (uniform I).expectation f := by
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card I : ℝ) * (uniform I).expectation f = ∑ j, f j := by
    rw [expectation_uniform]
    field_simp
  rw [he]
  exact Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

theorem fixed_choice_charge (μ : FiniteDistribution Z) (event : Z → Bool)
    (deleted : I → Z → Bool) (i : I)
    (hforce : ∀ z, 0 < μ.weight z → event z = true → deleted i z = true) :
    μ.probability event ≤ Fintype.card I * ((uniform I).product μ).probability
      (fun a => deleted a.1 a.2) := by
  have h := probability_mono_support μ hforce
  have he : ((uniform I).product μ).probability (fun a => deleted a.1 a.2) =
      (uniform I).expectation (fun i => μ.probability (deleted i)) := by
    simp only [probability_eq_expect, expectation_product]
  rw [he]
  exact h.trans (uniform_single_le _ (fun j => probability_nonnegative μ (deleted j)) i)

omit [Fintype I] [Nonempty I] in
theorem probability_good_restrict (μ : FiniteDistribution Z) (event : Z → Bool) (P Q : Prop) :
    μ.probability event ≤ μ.probability (fun z => decide (P ∧ Q) && event z) +
      (if ¬P then 1 else 0) + (if ¬Q then 1 else 0) := by
  have h := probability_le_one μ event
  rw [probability_eq_expect] at h
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP,hQ] <;> linarith

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games
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

def failureEvent (fallbackX : X) (fallbackY : Y) (a : Common U X M T N × E)
    (z : Y → Coupling.Block) : Bool :=
  bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX a.1 (G.left a.2)
    (Coupling.bigBits (fiber a.2) z) &&
  !(smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY a.1 (G.right a.2)
    (Coupling.smallBits z))

def scaleDeletion (i : Fin M) (a : Common U X M T N × E) : ℝ :=
  ((uniform (Fin (cellCount a.1.2.1.val))).product
    (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i]))).probability
    (fun q => comparisonDeleted G ψLaw deleted ⟨a.1,a.2,⟨i,q⟩⟩)

theorem scaleDeletion_nonneg (i : Fin M) (a : Common U X M T N × E) :
    0 ≤ scaleDeletion G ψLaw deleted i a := probability_nonnegative _ _

theorem comparison_probability_decomposition :
    (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) =
      ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
        (uniform (Fin M)).expectation (fun i => scaleDeletion G ψLaw deleted i a)) := by
  simp only [comparisonLaw, scaleDeletion, probability_eq_expect, expectation_sigma, expectation_product]

theorem single_scale_cost (i : Fin M) :
    ((common (M := M) G ψLaw).product G.edgeLaw).expectation (scaleDeletion G ψLaw deleted i) ≤
      M * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) := by
  rw [comparison_probability_decomposition, ← expectation_mul_left]
  apply expectation_mono
  intro a
  simpa only [Fintype.card_fin] using uniform_single_le
    (fun j => scaleDeletion G ψLaw deleted j a) (fun j => scaleDeletion_nonneg G ψLaw deleted j a) i

theorem good_failure_charge (fallbackX : X) (fallbackY : Y) (i : Fin M)
    (a : Common U X M T N × E)
    (ha : 0 < ((common (M := M) G ψLaw).product G.edgeLaw).weight a) :
    (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
      (fun z => decide (bigGood G ψLaw ord a.1 (G.left a.2) ∧
        smallGood G ψLaw ord a.1 (G.right a.2)) &&
        failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a z) ≤
      (2:ℝ)^T * scaleDeletion G ψLaw deleted i a := by
  let ν := Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])
  have hf := fixed_choice_charge ν
    (fun z => decide (bigGood G ψLaw ord a.1 (G.left a.2) ∧ smallGood G ψLaw ord a.1 (G.right a.2)) &&
      failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a z)
    (fun r z => comparisonDeleted G ψLaw deleted ⟨a.1,a.2,⟨i,r,z⟩⟩)
    (commonTransition G ψLaw hYX fiber deleted ord hord hrank a.1) (by
      intro z hz he
      let d : Compare U E X Y M T N := ⟨a.1,a.2,⟨i,commonTransition G ψLaw hYX fiber deleted ord hord hrank a.1,z⟩⟩
      have hp : 0 < (comparisonLaw G ψLaw).weight d := by
        have hp1 : 0 < (common G ψLaw).weight a.1 :=
          pos_of_mul_pos_left ha (G.edgeLaw.nonnegative a.2)
        have hp2 : 0 < G.edgeLaw.weight a.2 :=
          pos_of_mul_pos_right ha ((common G ψLaw).nonnegative a.1)
        simp only [d, comparisonLaw, sigma, product, uniform, Fintype.card_fin]
        change 0 < (common G ψLaw).weight a.1 * (G.edgeLaw.weight a.2 *
          (1/(M:ℝ) * (1/(cellCount a.1.2.1.val : ℝ) * ν.weight z)))
        have hM : (0:ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
        have hcell : (0:ℝ) < cellCount a.1.2.1.val := by
          exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (cellCount a.1.2.1.val))
        exact mul_pos hp1 (mul_pos hp2 (mul_pos (div_pos zero_lt_one hM)
          (mul_pos (div_pos zero_lt_one hcell) hz)))
      have he' : decide (bigGood G ψLaw ord a.1 (G.left a.2) ∧
          smallGood G ψLaw ord a.1 (G.right a.2)) = true ∧
          failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a z = true := by
        simpa only [Bool.and_eq_true] using he
      obtain ⟨hg,he⟩ := he'
      obtain ⟨hgU,hgV⟩ := of_decide_eq_true hg
      have he' : bigFunction G ψLaw hYX fiber deleted ord hord hrank fallbackX a.1 (G.left a.2)
          (Coupling.bigBits (fiber a.2) z) = true ∧
          smallFunction G ψLaw hYX fiber deleted ord hord hrank fallbackY a.1 (G.right a.2)
          (Coupling.smallBits z) = false := by
        simpa only [failureEvent, Bool.and_eq_true, Bool.not_eq_true'] using he
      obtain ⟨hu,hv⟩ := he'
      have hh := comparison_forces_deletion G ψLaw hYX fiber deleted ord hord hrank ⟨d,hp⟩
        fallbackX fallbackY hgU hgV rfl hu (by simpa using hv)
      change (comparisonLaw G ψLaw).extend _ d = true
      rw [show d = (⟨d,hp⟩ : (comparisonLaw G ψLaw).Support).val from rfl, extend_at_support]
      exact hh)
  change _ ≤ (2:ℝ)^T * scaleDeletion G ψLaw deleted i a
  apply hf.trans
  change (Fintype.card (Fin (cellCount a.1.2.1.val)) : ℝ) * scaleDeletion G ψLaw deleted i a ≤ _
  apply mul_le_mul_of_nonneg_right _ (scaleDeletion_nonneg G ψLaw deleted i a)
  simp only [Fintype.card_fin, cellCount_eq, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_of_lt a.1.2.1.isLt)

theorem comparison_charge (fallbackX : X) (fallbackY : Y) (i : Fin M)
    (D K ρ : ℝ) (hK : 0 < K)
    (hcost : K * (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D)
    (hbU : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬bigGood G ψLaw ord a.1 (G.left a.2))) ≤ ρ)
    (hbV : ((common (M := M) G ψLaw).product G.edgeLaw).probability (fun a =>
      decide (¬smallGood G ψLaw ord a.1 (G.right a.2))) ≤ ρ) :
    ((common (M := M) G ψLaw).product G.edgeLaw).expectation (fun a =>
      (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
        (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a)) ≤
      2*ρ + M*(2:ℝ)^T*D/K := by
  let μ := (common (M := M) G ψLaw).product G.edgeLaw
  have hh := expectation_mono_support μ (f := fun a =>
      (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i])).probability
        (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a))
    (g := fun a => (2:ℝ)^T * scaleDeletion G ψLaw deleted i a +
      (if ¬bigGood G ψLaw ord a.1 (G.left a.2) then 1 else 0) +
      (if ¬smallGood G ψLaw ord a.1 (G.right a.2) then 1 else 0)) (by
      intro a ha
      have hp := probability_good_restrict
        (Coupling.law (Y := Y) (bias i) (bias_pos i).le (by linarith [bias_le_quarter i]))
        (failureEvent G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY a)
        (bigGood G ψLaw ord a.1 (G.left a.2)) (smallGood G ψLaw ord a.1 (G.right a.2))
      have hc := good_failure_charge G ψLaw hYX fiber deleted ord hord hrank fallbackX fallbackY i a ha
      linarith)
  rw [expectation_add, expectation_add, expectation_mul_left] at hh
  have hbi : μ.expectation (fun a => if ¬bigGood G ψLaw ord a.1 (G.left a.2) then 1 else 0) ≤ ρ := by
    simpa only [probability_eq_expect, decide_eq_true_eq] using hbU
  have hsi : μ.expectation (fun a => if ¬smallGood G ψLaw ord a.1 (G.right a.2) then 1 else 0) ≤ ρ := by
    simpa only [probability_eq_expect, decide_eq_true_eq] using hbV
  have hc : (comparisonLaw G ψLaw).probability (comparisonDeleted G ψLaw deleted) ≤ D/K :=
    (le_div_iff₀ hK).mpr (by simpa [mul_comm] using hcost)
  have hs := (single_scale_cost G ψLaw deleted i).trans
    (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg M))
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2:ℝ)^T by positivity)
  change _ ≤ _ at hh
  have he : (2:ℝ)^T * ((M:ℝ) * (D/K)) = M*(2:ℝ)^T*D/K := by ring
  rw [he] at hmul
  linarith

end DirectedFeedback.Construction

noncomputable section
namespace DirectedFeedback.JuntaSupport

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

theorem bitSign_xor (b c : Bool) :
    bitSign (b ^^ c) = bitSign b * bitSign c := by
  cases b <;> cases c <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

theorem walsh_xor {I : Type*} [Fintype I] [DecidableEq I] (s x y : Cube I) :
    walsh s (cubeXor x y) = walsh s x * walsh s y := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [cubeXor]
  cases s i <;> cases x i <;> cases y i <;> norm_num [bitSign]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp []
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

def coefficient {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (s : Cube I) : ℝ :=
  𝔼 x, f x * walsh s x

theorem walsh_inversion {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (x : Cube I) :
    (∑ s, coefficient f s * walsh s x) = f x := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : Cube I) :
      (∑ s, (f y * walsh s y) * walsh s x) =
        f y * (if y = x then (Fintype.card (Cube I) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [walsh_symm (x := y), walsh_symm (x := x)]
    exact walsh_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

theorem walsh_inner {I : Type*} [Fintype I] [DecidableEq I] (f g : Cube I → ℝ) :
    (∑ s, coefficient f s * coefficient g s) = 𝔼 x, f x * g x := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  have h : (∑ s, (𝔼 y, f y * walsh s y) * (g x * walsh s x)) =
      g x * (∑ s, coefficient f s * walsh s x) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h, walsh_inversion]
  ring

theorem walsh_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) :
    (∑ s, coefficient f s ^ 2) = 𝔼 x, f x ^ 2 := by
  simpa [pow_two] using walsh_inner f f

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

end DirectedFeedback.JuntaSupport

namespace DFVSMaxCut.Analytic
open Finset DirectedFeedback.JuntaSupport
def degree {I : Type*} [Fintype I] (s : Cube I) : ℕ :=
  (Finset.univ.filter fun i => s i = true).card
end DFVSMaxCut.Analytic

namespace DFVSMaxCut.BooleanFourthMoment
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport

 theorem sum_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    ∑ x, F x = ∑ b : Bool, ∑ y : Cube (Fin n), F (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  exact Fintype.sum_prod_type _

 theorem expect_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, F x) = 𝔼 b : Bool, 𝔼 y : Cube (Fin n), F (Fin.cons b y) := by
  calc
    _ = 𝔼 p : Bool × Cube (Fin n), F (Fin.cons p.1 p.2) :=
      (Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) _ F (fun _ => rfl)).symm
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]

 theorem expect_bool (F : Bool → ℝ) : (𝔼 b, F b) = (F false + F true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [add_comm]

noncomputable def polynomial {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (x : Cube I) : ℝ := ∑ s, c s * walsh s x

noncomputable def energy {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) : ℝ :=
  ∑ s, (∏ i, if s i then (3 : ℝ) else 1) * c s ^ 2

 theorem energy_nonneg {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    0 ≤ energy c := by
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg _ (sq_nonneg _)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> norm_num

 theorem walsh_cons {n : ℕ} (s x : Cube (Fin n)) (a b : Bool) :
    walsh (Fin.cons a s) (Fin.cons b x) = (if a then bitSign b else 1) * walsh s x := by
  cases a <;> simp [walsh, Fin.prod_univ_succ, bitSign]

 theorem polynomial_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) (x : Cube (Fin n)) (b : Bool) :
    polynomial c (Fin.cons b x) = polynomial (fun s => c (Fin.cons false s)) x +
      bitSign b * polynomial (fun s => c (Fin.cons true s)) x := by
  unfold polynomial
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [walsh_cons, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

 theorem energy_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    energy c = energy (fun s => c (Fin.cons false s)) +
      3 * energy (fun s => c (Fin.cons true s)) := by
  unfold energy
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
    one_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

 theorem fourth_moment_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) =
      (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 4) +
      6 * (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 2 *
        polynomial (fun s => c (Fin.cons true s)) x ^ 2) +
      (𝔼 x, polynomial (fun s => c (Fin.cons true s)) x ^ 4) := by
  rw [expect_cube_succ, Finset.expect_comm]
  simp_rw [expect_bool]
  simp only [polynomial_cons, bitSign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  simp_rw [show ∀ a b : ℝ, ((a + b) ^ 4 + (a + -b) ^ 4) / 2 = a ^ 4 + 6 * (a ^ 2 * b ^ 2) + b ^ 4 by
    intro a b; ring]
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect]

 theorem fourth_moment_bound (n : ℕ) (c : Cube (Fin n) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) ≤ energy c ^ 2 := by
  induction n with
  | zero => simp [polynomial, energy, walsh]; exact le_of_eq (by ring)
  | succ n ih =>
    let c₀ : Cube (Fin n) → ℝ := fun s => c (Fin.cons false s)
    let c₁ : Cube (Fin n) → ℝ := fun s => c (Fin.cons true s)
    have h₀ := ih c₀
    have h₁ := ih c₁
    have he₀ := energy_nonneg c₀
    have he₁ := energy_nonneg c₁
    have hm₀ : 0 ≤ 𝔼 x, polynomial c₀ x ^ 4 := by positivity
    have hm₁ : 0 ≤ 𝔼 x, polynomial c₁ x ^ 4 := by positivity
    have hc := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => polynomial c₀ x ^ 2) (fun x => polynomial c₁ x ^ 2)
    simp only [← pow_mul, Nat.reduceMul] at hc
    have hc' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ^ 2 ≤
        (energy c₀ * energy c₁) ^ 2 := by
      calc _ ≤ _ := hc
           _ ≤ energy c₀ ^ 2 * energy c₁ ^ 2 := mul_le_mul h₀ h₁ hm₁ (sq_nonneg _)
           _ = _ := by ring
    have hc'' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ≤ energy c₀ * energy c₁ :=
      (sq_le_sq₀ (by positivity) (mul_nonneg he₀ he₁)).mp hc'
    rw [fourth_moment_cons, energy_cons]
    change (𝔼 x, polynomial c₀ x ^ 4) +
      6 * (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) +
      (𝔼 x, polynomial c₁ x ^ 4) ≤ (energy c₀ + 3 * energy c₁) ^ 2
    nlinarith [sq_nonneg (energy c₁)]

 theorem weight_eq_degree {I : Type*} [Fintype I] [DecidableEq I] (s : Cube I) :
    (∏ i, if s i then (3 : ℝ) else 1) = 3 ^ Analytic.degree s := by
  simp [Finset.prod_ite, Analytic.degree]

 theorem energy_truncated {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (c : Cube I → ℝ) (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    energy c ≤ 3 ^ K * ∑ s, c s ^ 2 := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [weight_eq_degree]
  by_cases hs : Analytic.degree s ≤ K
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (sq_nonneg _)
  · rw [hc s (lt_of_not_ge hs)]; simp

 theorem coefficient_polynomial {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (a : Cube I) : coefficient (polynomial c) a = c a := by
  unfold coefficient polynomial
  simp only [Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_expect, walsh_orthogonality]
  simp

 theorem polynomial_second_moment {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    (𝔼 x, polynomial c x ^ 2) = ∑ s, c s ^ 2 := by
  rw [← walsh_parseval]
  simp only [coefficient_polynomial]

 theorem degree_fourth_moment_bound {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    (𝔼 x, polynomial c x ^ 4) ≤ (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 := by
  rw [polynomial_second_moment]
  exact (fourth_moment_bound n c).trans
    ((sq_le_sq₀ (energy_nonneg c) (by positivity)).mpr (energy_truncated K c hc))

 theorem degree_third_moment_bound {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsmall : (𝔼 x, polynomial c x ^ 2) ≤ τ ^ 2) :
    (𝔼 x, |polynomial c x| ^ 3) ≤ 3 ^ K * τ * (𝔼 x, polynomial c x ^ 2) := by
  have hsecond : 0 ≤ 𝔼 x, polynomial c x ^ 2 := by positivity
  have hfourth := degree_fourth_moment_bound c hc
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |polynomial c x|) (fun x => polynomial c x ^ 2)
  have hp (a : ℝ) : |a| * a ^ 2 = |a| ^ 3 := by rw [← sq_abs]; ring
  simp_rw [hp, sq_abs, ← pow_mul, Nat.reduceMul] at hCS
  have hbound : (𝔼 x, |polynomial c x| ^ 3) ^ 2 ≤
      (3 ^ K * τ * (𝔼 x, polynomial c x ^ 2)) ^ 2 := by
    calc
      _ ≤ (𝔼 x, polynomial c x ^ 2) * (𝔼 x, polynomial c x ^ 4) := hCS
      _ ≤ (𝔼 x, polynomial c x ^ 2) * (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourth hsecond
      _ = (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 * (𝔼 x, polynomial c x ^ 2) := by ring
      _ ≤ (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 * τ ^ 2 :=
        mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hbound

 theorem walsh_flip {I : Type*} [Fintype I] [DecidableEq I]
    (s x : Cube I) (i : I) :
    walsh s (Function.update x i (!x i)) = (if s i then -1 else 1) * walsh s x := by
  classical
  have hp (j : I) : bitSign (s j && Function.update x i (!x i) j) =
      (if j = i then (if s i then (-1 : ℝ) else 1) else 1) * bitSign (s j && x j) := by
    by_cases h : j = i
    · subst j; cases s i <;> cases x i <;> simp [bitSign]
    · simp [h]
  simp only [walsh, hp, Finset.prod_mul_distrib]
  simp

noncomputable def discreteDiff {I : Type*} [Fintype I] [DecidableEq I]
    (f : Cube I → ℝ) (i : I) (x : Cube I) : ℝ := (f x - f (Function.update x i (!x i))) / 2

 theorem polynomial_diff {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (i : I) :
    discreteDiff (polynomial c) i = polynomial (fun s => if s i then c s else 0) := by
  funext x
  simp only [discreteDiff, polynomial, walsh_flip, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  cases s i <;> simp

 theorem total_diff_second {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) :
    (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) =
      ∑ s, (Analytic.degree s : ℝ) * c s ^ 2 := by
  simp only [polynomial_diff, polynomial_second_moment]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [ite_pow, zero_pow (by omega : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp [Analytic.degree]

 theorem total_diff_second_truncated {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (c : Cube I → ℝ) (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤
      K * (𝔼 x, polynomial c x ^ 2) := by
  rw [total_diff_second, polynomial_second_moment, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : Analytic.degree s ≤ K
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg _)
  · rw [hc s (lt_of_not_ge hs)]; simp

 theorem total_diff_third_truncated {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsmall : ∀ i, (𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤ τ ^ 2) :
    (∑ i, 𝔼 x, |discreteDiff (polynomial c) i x| ^ 3) ≤
      3 ^ K * τ * K * (𝔼 x, polynomial c x ^ 2) := by
  calc
    _ ≤ ∑ i, 3 ^ K * τ * (𝔼 x, discreteDiff (polynomial c) i x ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hsmall i
      rw [polynomial_diff] at hi ⊢
      exact degree_third_moment_bound _ (fun s hs => by rw [hc s hs]; split_ifs <;> rfl)
        hτ hi
    _ = 3 ^ K * τ * (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 3 ^ K * τ * (K * (𝔼 x, polynomial c x ^ 2)) :=
      mul_le_mul_of_nonneg_left (total_diff_second_truncated K c hc) (by positivity)
    _ = _ := by ring

end DFVSMaxCut.BooleanFourthMoment

namespace DirectedFeedback.Junta
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport DFVSMaxCut.BooleanFourthMoment
open DFVSMaxCut.Analytic

def influence {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n) : ℝ :=
  𝔼 x, (f x - f (Function.update x i (!x i))) ^ 2

def totalInfluence {n : ℕ} (f : Cube (Fin n) → ℝ) : ℝ := ∑ i, influence f i

def IsBoolean {n : ℕ} (f : Cube (Fin n) → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

def OnCoordinates {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → f x = f y

def error {n : ℕ} (f g : Cube (Fin n) → ℝ) : ℝ :=
  𝔼 x, if f x = g x then 0 else 1

theorem polynomial_coefficients {n : ℕ} (f : Cube (Fin n) → ℝ) :
    polynomial (coefficient f) = f := by
  funext x
  exact walsh_inversion f x

theorem influence_nonneg {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n) :
    0 ≤ influence f i := by unfold influence; positivity

theorem influence_eq_diff {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n) :
    influence f i = 4 * (𝔼 x, discreteDiff f i x ^ 2) := by
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro x _
  unfold discreteDiff
  ring

theorem totalInfluence_spectral {n : ℕ} (f : Cube (Fin n) → ℝ) :
    totalInfluence f = 4 * ∑ s, (degree s : ℝ) * coefficient f s ^ 2 := by
  unfold totalInfluence
  simp_rw [influence_eq_diff]
  rw [← Finset.mul_sum]
  conv_lhs => rw [← polynomial_coefficients f]
  rw [total_diff_second]

theorem spectral_tail {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) :
    4 * (K + 1 : ℝ) *
      (∑ s ∈ Finset.univ.filter (fun s => K < degree s), coefficient f s ^ 2) ≤
      totalInfluence f := by
  rw [totalInfluence_spectral, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ s ∈ Finset.univ.filter (fun s => K < degree s),
          (degree s : ℝ) * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_filter.mp hs).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

def pivotal {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n)
    (x : Cube (Fin n)) : ℝ := if f x = f (Function.update x i (!x i)) then 0 else 1

theorem pivotal_sq {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n)
    (x : Cube (Fin n)) : pivotal f i x ^ 2 = pivotal f i x := by
  unfold pivotal
  split_ifs <;> norm_num

theorem diff_mul_pivotal {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n)
    (x : Cube (Fin n)) : discreteDiff f i x * pivotal f i x = discreteDiff f i x := by
  unfold pivotal discreteDiff
  split_ifs with h
  · simp [h]
  · ring

theorem pivotal_eq_difference_sq {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f)
    (i : Fin n) (x : Cube (Fin n)) :
    pivotal f i x = (f x - f (Function.update x i (!x i))) ^ 2 := by
  unfold pivotal
  rcases hf x with h | h <;>
    rcases hf (Function.update x i (!x i)) with h' | h' <;> simp [h, h']

theorem expect_pivotal {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f) (i : Fin n) :
    (𝔼 x, pivotal f i x) = influence f i := by
  unfold influence
  simp only [pivotal_eq_difference_sq f hf]

def lowDiffCoeff {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n)
    (s : Cube (Fin n)) : ℝ := if s i = true ∧ degree s ≤ K then coefficient f s else 0

def lowDiff {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n) :=
  polynomial (lowDiffCoeff f K i)

theorem coefficient_discreteDiff {n : ℕ} (f : Cube (Fin n) → ℝ)
    (i : Fin n) (s : Cube (Fin n)) :
    coefficient (discreteDiff f i) s = if s i then coefficient f s else 0 := by
  conv_lhs => rw [← polynomial_coefficients f]
  rw [polynomial_diff, coefficient_polynomial]

theorem inner_lowDiff {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n) :
    (𝔼 x, discreteDiff f i x * lowDiff f K i x) =
      (𝔼 x, lowDiff f K i x ^ 2) := by
  rw [← walsh_inner]
  simp only [lowDiff, coefficient_polynomial, coefficient_discreteDiff,
    polynomial_second_moment]
  apply Finset.sum_congr rfl
  intro s _
  unfold lowDiffCoeff
  by_cases hs : s i = true <;> by_cases hk : degree s ≤ K <;> simp [hs, hk, pow_two]

theorem lowDiff_fourth {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n) :
    (𝔼 x, lowDiff f K i x ^ 4) ≤
      (3 ^ K * (𝔼 x, lowDiff f K i x ^ 2)) ^ 2 := by
  apply degree_fourth_moment_bound
  intro s hs
  simp [lowDiffCoeff, not_le.mpr hs]

theorem lowDiff_energy_le {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f)
    (K : ℕ) (i : Fin n) (τ : ℝ) (hτ : 0 ≤ τ) (hsmall : influence f i ≤ τ ^ 2) :
    (𝔼 x, lowDiff f K i x ^ 2) ≤ 3 ^ K * τ * influence f i / 4 := by
  let s := (𝔼 x, lowDiff f K i x ^ 2)
  let X := (𝔼 x, pivotal f i x * lowDiff f K i x ^ 2)
  let I := influence f i
  let a : ℝ := 3 ^ K
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hI0 : 0 ≤ I := influence_nonneg f i
  have hX : 0 ≤ X := by
    apply Finset.expect_nonneg
    intro x _
    apply mul_nonneg _ (sq_nonneg _)
    unfold pivotal
    split_ifs <;> norm_num
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hc₁ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (discreteDiff f i) (fun x => pivotal f i x * lowDiff f K i x)
  have hinner : (𝔼 x, discreteDiff f i x *
      (pivotal f i x * lowDiff f K i x)) = s := by
    simp only [← mul_assoc, diff_mul_pivotal, inner_lowDiff]
    rfl
  have hprod : (𝔼 x, (pivotal f i x * lowDiff f K i x) ^ 2) = X := by
    simp only [mul_pow, pivotal_sq]
    rfl
  rw [hinner, hprod] at hc₁
  have hIdiff : (𝔼 x, discreteDiff f i x ^ 2) = I / 4 := by
    have hh := influence_eq_diff f i
    dsimp [I]
    linarith
  rw [hIdiff] at hc₁
  have hc₂ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (pivotal f i) (fun x => lowDiff f K i x ^ 2)
  simp only [pivotal_sq, expect_pivotal f hf, ← pow_mul, Nat.reduceMul] at hc₂
  have hc₂' : X ^ 2 ≤ I * (a * s) ^ 2 := by
    exact hc₂.trans (mul_le_mul_of_nonneg_left (lowDiff_fourth f K i) hI0)
  by_cases hs : s = 0
  · change s ≤ a * τ * I / 4
    rw [hs]
    positivity
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hsq : s ^ 4 ≤ (I / 4) ^ 2 * (I * (a * s) ^ 2) := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ ≤ (I / 4 * X) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg _) (by positivity)).mpr hc₁
      _ = (I / 4) ^ 2 * X ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc₂' (sq_nonneg _)
  have hcancel : s ^ 2 ≤ a ^ 2 * I ^ 3 / 16 := by
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hspos)).mp
    nlinarith only [hsq]
  have hsmall' : a ^ 2 * I ^ 3 / 16 ≤ (a * τ * I / 4) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ a ^ 2 * I ^ 2 / 16)
    dsimp [I] at *
    nlinarith only [hh]
  exact (sq_le_sq₀ hs0 (by positivity)).mp (hcancel.trans hsmall')

def support {n : ℕ} (s : Cube (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s i = true)

def projectCoeff {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ)
    (s : Cube (Fin n)) : ℝ := if support s ⊆ J then coefficient f s else 0

def project {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) :=
  polynomial (projectCoeff J f)

theorem walsh_eq_on_support {n : ℕ} (s x y : Cube (Fin n))
    (hxy : ∀ i ∈ support s, x i = y i) : walsh s x = walsh s y := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : s i = true
  · rw [hxy i (by simp [support, hi])]
  · simp [Bool.eq_false_of_not_eq_true hi]

theorem project_onCoordinates {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) :
    OnCoordinates J (project J f) := by
  intro x y hxy
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : support s ⊆ J
  · rw [walsh_eq_on_support s x y (fun i hi => hxy i (hs hi))]
  · simp [projectCoeff, hs]

theorem coefficient_sub {n : ℕ} (f g : Cube (Fin n) → ℝ) (s : Cube (Fin n)) :
    coefficient (fun x => f x - g x) s = coefficient f s - coefficient g s := by
  unfold coefficient
  simp only [sub_mul, Finset.expect_sub_distrib]

theorem project_squared_error {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) :
    (𝔼 x, (f x - project J f x) ^ 2) =
      ∑ s, if support s ⊆ J then 0 else coefficient f s ^ 2 := by
  rw [← walsh_parseval]
  simp only [coefficient_sub, project, coefficient_polynomial]
  apply Finset.sum_congr rfl
  intro s _
  unfold projectCoeff
  split_ifs <;> simp

theorem project_squared_error_le {n : ℕ} (J : Finset (Fin n))
    (f : Cube (Fin n) → ℝ) (K : ℕ) :
    (𝔼 x, (f x - project J f x) ^ 2) ≤
      (∑ s ∈ Finset.univ.filter (fun s => K < degree s), coefficient f s ^ 2) +
      ∑ i ∈ Finset.univ \ J, (𝔼 x, lowDiff f K i x ^ 2) := by
  rw [project_squared_error]
  simp only [lowDiff, polynomial_second_moment]
  rw [Finset.sum_filter, Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : support s ⊆ J
  · rw [ite_eq_left hs]
    positivity
  · rw [ite_eq_right hs]
    by_cases hk : K < degree s
    · rw [ite_eq_left hk]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    · rw [ite_eq_right hk, zero_add]
      obtain ⟨i, hi, hiJ⟩ := Finset.not_subset.mp hs
      have his : s i = true := (Finset.mem_filter.mp hi).2
      have hiout : i ∈ Finset.univ \ J := by simp [hiJ]
      have hterm : lowDiffCoeff f K i s = coefficient f s := by
        simp [lowDiffCoeff, his, Nat.le_of_not_gt hk]
      rw [← hterm]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (lowDiffCoeff f K i s)) hiout

def highInfluences {n : ℕ} (f : Cube (Fin n) → ℝ) (τ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ ^ 2 < influence f i)

theorem highInfluences_card_bound {n : ℕ} (f : Cube (Fin n) → ℝ) (τ : ℝ) :
    (highInfluences f τ).card * τ ^ 2 ≤ totalInfluence f := by
  calc
    _ = ∑ i ∈ highInfluences f τ, τ ^ 2 := by simp
    _ ≤ ∑ i ∈ highInfluences f τ, influence f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      influence_nonneg f i

theorem lowDiff_sum_outside {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f)
    (K : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ i ∈ Finset.univ \ highInfluences f τ, (𝔼 x, lowDiff f K i x ^ 2)) ≤
      3 ^ K * τ * totalInfluence f / 4 := by
  calc
    _ ≤ ∑ i ∈ Finset.univ \ highInfluences f τ, 3 ^ K * τ * influence f i / 4 := by
      apply Finset.sum_le_sum
      intro i hi
      apply lowDiff_energy_le f hf K i τ hτ
      have hnot := (Finset.mem_sdiff.mp hi).2
      simpa only [highInfluences, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hnot
    _ ≤ ∑ i, 3 ^ K * τ * influence f i / 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset.trans (Finset.subset_univ _))
        (fun i _ _ => by have := influence_nonneg f i; positivity)
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]; rfl

end DirectedFeedback.Junta
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
