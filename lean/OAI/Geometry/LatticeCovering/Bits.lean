import OAI.Geometry.LatticeCovering.SamplingBounds

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Bits
universe u v w
variable {I : Type u} {J : Type v} {G : Type w} [Fintype I] [Fintype J]
  [AddCommGroup G] [Fintype G]


def groupShift (w : I → G) (e : I → Bool) : G := ∑ i, if e i then w i else 0

def fairAverage (w : I → G) (f : G → ℝ) (x : G) : ℝ :=
  (∑ e, f (x-groupShift w e))/(2 : ℝ)^(Fintype.card I)

def biasedAverage (q : I → ℝ) (w : I → G) (f : G → ℝ) (x : G) : ℝ :=
  integral q (fun e => f (x-groupShift w e))

lemma groupShift_reindex {I : Type u} {J : Type v} {G : Type w} [Fintype I] [Fintype J] [AddCommGroup G] [Fintype G] (E : I ≃ J) (w : J → G) (e : J → Bool) :
    groupShift (fun i => w (E i)) (fun i => e (E i)) = groupShift w e :=
  Fintype.sum_equiv E _ _ (fun _ => rfl)

lemma fairAverage_reindex {I : Type u} {J : Type v} {G : Type w} [Fintype I] [Fintype J] [AddCommGroup G] [Fintype G] (E : I ≃ J) (w : J → G) (f : G → ℝ) (x : G) :
    fairAverage (fun i => w (E i)) f x = fairAverage w f x := by
  classical
  unfold fairAverage
  rw [Fintype.card_congr E]
  congr 1
  let D := Equiv.piCongrLeft (fun _ : J => Bool) E
  apply Fintype.sum_equiv D
  intro e
  congr 2
  unfold groupShift
  apply Fintype.sum_equiv E
  intro i
  simp [D]

lemma filled_groupShift {I : Type u} {G : Type w} [Fintype I] [AddCommGroup G] [Fintype G] (q : I → ℝ) (s : I → Bool) (a : Selected s → Bool) (w : I → G) :
    groupShift w (filled q s a) =
      groupShift (fun j : Selected s => w j) a +
        ∑ j : Frozen s, if likelyBit (q j) then w j else 0 := by
  classical
  unfold groupShift
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => s i=true)]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;>
    simp [filled, cubeSplit, Equiv.piEquivPiSubtypeProd, j.property]

lemma conditional_shift_average (q : I → ℝ) (s : I → Bool) (w : I → G) (f : G → ℝ) (x : G) :
    (∑ e, conditionalMass q s e*f (x-groupShift w e)) =
      fairAverage (fun j : Selected s => w j) f
        (x-∑ j : Frozen s, if likelyBit (q j) then w j else 0) := by
  rw [conditional_integral_eq_subcube]
  unfold fairAverage
  congr 1
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [filled_groupShift]
  congr 1
  abel


lemma sampler_finite_index {b : ℝ} (f : G → ℝ) (A δ : ℝ) (hthreshold :
    ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ δ)
    (hs : b^(69/100 : ℝ) ≤ (Fintype.card I : ℝ)) (hsb : (Fintype.card I : ℝ) ≤ b) :
    SingleLatticeCovering.Sampler.probability (fun w : I → G => ∃ x, fairAverage w f x < A) ≤ δ := by
  classical
  let E : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let D := Equiv.piCongrLeft (fun _ : I => G) E
  have he : SingleLatticeCovering.Sampler.probability (fun w : I → G => ∃ x, fairAverage w f x < A) =
      SingleLatticeCovering.Sampler.probability (fun w : Fin (Fintype.card I) → G => ∃ x,
        (∑ e : Fin (Fintype.card I) → Bool,
          f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^(Fintype.card I) < A) := by
    unfold SingleLatticeCovering.Sampler.probability
    apply (Fintype.expect_equiv D _ _ _).symm
    intro w
    have ha (x : G) : fairAverage (D w) f x =
        (∑ e : Fin (Fintype.card I) → Bool,
          f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^(Fintype.card I) := by
      rw [← fairAverage_reindex E]
      simp only [D, fairAverage, groupShift, SingleLatticeCovering.Sampler.subsetShift]
      simp only [Fintype.card_fin]
      congr 1
      apply Finset.sum_congr (by ext; simp)
      intro e he
      congr 2
      apply Finset.sum_congr (by ext; simp)
      intro i hi
      simp
    congr 1
    apply propext
    constructor <;> rintro ⟨x, hx⟩ <;> refine ⟨x, ?_⟩
    · rw [ha]
      convert hx using 2
    · rw [ha] at hx
      convert hx using 2
  rw [he]
  exact hthreshold _ hs hsb



def componentGood (b A : ℝ) (f : G → ℝ) (w : I → G) (s : I → Bool) : Prop :=
  b^(69/100 : ℝ) ≤ (Fintype.card (Selected s) : ℝ) ∧
    ∀ x, A ≤ fairAverage (fun j : Selected s => w j) f x

def badMixture (b A : ℝ) (q : I → ℝ) (f : G → ℝ) (w : I → G) : ℝ :=
  integral (fun i => fairRate (q i)) (fun s => if componentGood b A f w s then 0 else 1)

lemma badMixture_nonneg {I : Type u} {G : Type w} [Fintype I] [AddCommGroup G] [Fintype G] (b A : ℝ) {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (f : G → ℝ) (w : I → G) :
    0 ≤ badMixture b A q f w := by
  unfold badMixture integral
  exact Finset.sum_nonneg (fun s _ => mul_nonneg
    (productMass_nonneg (fun i => fairRate_nonneg (hq i) (hq1 i))
      (fun i => fairRate_le_one (q i)) s) (by dsimp; split_ifs <;> norm_num))

lemma badMixture_le_one {I : Type u} {G : Type w} [Fintype I] [AddCommGroup G] [Fintype G] (b A : ℝ) {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (f : G → ℝ) (w : I → G) :
    badMixture b A q f w ≤ 1 := by
  conv_rhs => rw [← integral_const (fun i => fairRate (q i)) 1]
  apply integral_mono (fun i => fairRate_nonneg (hq i) (hq1 i))
    (fun i => fairRate_le_one (q i))
  intro s
  split_ifs <;> norm_num

lemma component_failure_mean_le {b A δ : ℝ} (f : G → ℝ) (hδ : 0 ≤ δ)
    (hthreshold : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ δ)
    (hb : (Fintype.card I : ℝ) ≤ b) (s : I → Bool) :
    (𝔼 w : I → G, if componentGood b A f w s then (0 : ℝ) else 1) ≤
      (if count s < b^(69/100 : ℝ) then 1 else 0)+δ := by
  classical
  by_cases hs : b^(69/100 : ℝ) ≤ (Fintype.card (Selected s) : ℝ)
  · have hcard : (Fintype.card (Selected s) : ℝ) ≤ b :=
      (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hb
    have hfail := sampler_finite_index (I := Selected s) f A δ hthreshold hs hcard
    have he (w : I → G) : (if componentGood b A f w s then (0 : ℝ) else 1) =
        if ∃ x, fairAverage (fun j : Selected s => w j) f x < A then 1 else 0 := by
      have hg : componentGood b A f w s ↔
          ¬∃ x, fairAverage (fun j : Selected s => w j) f x < A := by
        simp only [componentGood, hs, true_and, not_exists, not_lt]
      simp only [hg, ite_not]
    simp_rw [he]
    have hs' : ¬ count s < b^(69/100 : ℝ) := by rw [count_eq_card_selected]; exact not_lt_of_ge hs
    simp only [hs', ↓reduceIte, zero_add]
    calc
      _ = 𝔼 v : Selected s → G, if ∃ x, fairAverage v f x < A then (1 : ℝ) else 0 :=
        expect_restrict s (fun v => if ∃ x, fairAverage v f x < A then (1 : ℝ) else 0)
      _ ≤ δ := by
        unfold SingleLatticeCovering.Sampler.probability at hfail
        convert hfail using 1
        congr 1
        · ext v; simp
        · congr! 10
  · have hs' : count s < b^(69/100 : ℝ) := by rw [count_eq_card_selected]; exact lt_of_not_ge hs
    simp only [componentGood, hs, false_and, ↓reduceIte, hs', Fintype.expect_const]
    linarith



theorem expected_badMixture_le {b A δ : ℝ} {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (f : G → ℝ) (hδ : 0 ≤ δ)
    (hthreshold : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ δ)
    (hb : (Fintype.card I : ℝ) ≤ b)
    (hmean : 0 < meanCount (fun i => fairRate (q i)))
    (ht : b^(69/100 : ℝ) ≤ meanCount (fun i => fairRate (q i))/2) :
    (𝔼 w : I → G, badMixture b A q f w) ≤ 4/meanCount (fun i => fairRate (q i))+δ := by
  classical
  have hex : (𝔼 w : I → G, badMixture b A q f w) =
      integral (fun i => fairRate (q i)) (fun s =>
        𝔼 w : I → G, if componentGood b A f w s then (0 : ℝ) else 1) := by
    unfold badMixture integral
    rw [Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact (Finset.mul_expect _ _ _).symm
  rw [hex]
  calc
    _ ≤ integral (fun i => fairRate (q i)) (fun s =>
        (if count s < b^(69/100 : ℝ) then 1 else 0)+δ) :=
      integral_mono (fun i => fairRate_nonneg (hq i) (hq1 i))
        (fun i => fairRate_le_one (q i)) (component_failure_mean_le f hδ hthreshold hb)
    _ = integral (fun i => fairRate (q i)) (fun s =>
        if count s < b^(69/100 : ℝ) then 1 else 0)+δ := by rw [integral_add, integral_const]
    _ ≤ _ := add_le_add_left (few_selected_probability
      (fun i => fairRate_nonneg (hq i) (hq1 i)) (fun i => fairRate_le_one (q i)) hmean ht) δ



theorem biasedAverage_of_badMixture_le {b A ε : ℝ} {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hA : 0 ≤ A) (w : I → G) (hw : badMixture b A q f w ≤ ε) (x : G) :
    (1-ε)*A ≤ biasedAverage q w f x := by
  have h := mixture_lower_bound hq hq1 (componentGood b A f w)
    (fun e => f (x-groupShift w e)) (fun e => hf _) A hA (by
      intro s hs
      rw [conditional_shift_average]
      exact hs.2 _)
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hw 1) hA).trans h

end SingleLatticeCovering.Bits





noncomputable section

open scoped BigOperators
open Classical
namespace SingleLatticeCovering.WeightedSelection
universe u v
variable {Z : Type u} {W : Type v} [Fintype Z] [Fintype W] [Nonempty W]


def mass (F : Z → ℝ) (E : Finset Z) : ℝ := 𝔼 z, if z ∈ E then F z else 0

def loss (F : Z → ℝ) (E : Finset Z) (q : W → Z → ℝ) (w : W) : ℝ :=
  𝔼 z, if z ∈ E then F z*q w z else 0

lemma mean_loss_le {Z : Type u} {W : Type v} [Fintype Z] [Fintype W] [Nonempty W] (F : Z → ℝ) (E : Finset Z) (q : W → Z → ℝ) (δ : ℝ)
    (hF : ∀ z, 0 ≤ F z) (hqavg : ∀ z ∈ E, (𝔼 w, q w z) ≤ δ) :
    (𝔼 w, loss F E q w) ≤ δ*mass F E := by
  unfold loss mass
  rw [Finset.expect_comm, Finset.mul_expect]
  apply Finset.expect_le_expect
  intro z _
  by_cases hz : z ∈ E
  · simp only [hz, ↓reduceIte, ← Finset.mul_expect]
    exact (mul_le_mul_of_nonneg_left (hqavg z hz) (hF z)).trans_eq (mul_comm _ _)
  · simp only [hz, ↓reduceIte, Finset.expect_const_zero, mul_zero, le_refl]



theorem choose_usable (F : Z → ℝ) (E : Finset Z) (q : W → Z → ℝ) (δ ε : ℝ)
    (hF : ∀ z, 0 ≤ F z) (hq : ∀ w z, 0 ≤ q w z)
    (hqavg : ∀ z ∈ E, (𝔼 w, q w z) ≤ δ) (hε : 0 < ε) :
    ∃ w : W, ∃ U : Finset Z, U ⊆ E ∧
      (∀ z ∈ U, q w z ≤ ε) ∧
      mass F (E \ U) ≤ δ*mass F E/ε ∧
      mass F E - δ*mass F E/ε ≤ mass F U ∧ mass F U ≤ mass F E := by
  classical
  have havg := mean_loss_le F E q δ hF hqavg
  obtain ⟨w,_,hw⟩ := Finset.exists_le_of_expect_le (s := Finset.univ)
    Finset.univ_nonempty havg
  let U := E.filter (fun z => q w z ≤ ε)
  have hsub : U ⊆ E := Finset.filter_subset _ _
  have hgood : ∀ z ∈ U, q w z ≤ ε := fun _ h => (Finset.mem_filter.mp h).2
  have hdisc : ε*mass F (E \ U) ≤ loss F E q w := by
    rw [mass, Finset.mul_expect, loss]
    apply Finset.expect_le_expect
    intro z _
    by_cases hz : z ∈ E \ U
    · obtain ⟨hzE,hzU⟩ := Finset.mem_sdiff.mp hz
      have hbad : ε < q w z := lt_of_not_ge (fun h => hzU (Finset.mem_filter.mpr ⟨hzE,h⟩))
      simp only [hz, hzE, ↓reduceIte]
      nlinarith [mul_le_mul_of_nonneg_left hbad.le (hF z)]
    · simp only [hz, ↓reduceIte, mul_zero]
      split_ifs <;> first | exact mul_nonneg (hF z) (hq w z) | rfl
  have hsplit : mass F (E \ U)+mass F U=mass F E := by
    unfold mass
    rw [← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro z _
    by_cases hzU : z ∈ U
    · have hzE := hsub hzU
      simp only [hzU, hzE, Finset.mem_sdiff, not_true_eq_false, and_false,
        ↓reduceIte, zero_add]
    · by_cases hzE : z ∈ E <;> simp [hzU, hzE]
  have hdisc' : mass F (E \ U) ≤ δ*mass F E/ε :=
    (le_div_iff₀ hε).mpr (by linarith [hdisc.trans hw])
  have hdisc0 : 0 ≤ mass F (E \ U) := Finset.expect_nonneg (fun z _ => by
    split_ifs <;> first | exact hF z | rfl)
  exact ⟨w,U,hsub,hgood,hdisc',by linarith,by linarith⟩

end SingleLatticeCovering.WeightedSelection

namespace SingleLatticeCovering.Bits
universe u v w
open Filter
open scoped Topology


def alpha : ℝ := (1+Real.exp 1)⁻¹
lemma alpha_pos : 0 < alpha := inv_pos.mpr (by positivity)
lemma alpha_le_half : alpha ≤ 1/2 := by
  unfold alpha
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  rw [← one_div]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

lemma eventually_mixture_parameters : ∀ᶠ b : ℝ in atTop,
    1 < b ∧ b^(69/100 : ℝ) ≤ alpha*b^(70/100 : ℝ) ∧ 3*b^(-1/10 : ℝ) ≤ 1 := by
  have hr := SingleLatticeCovering.Sampler.Numeric.tendsto_rpow_ratio
    (show (69/100 : ℝ) < 70/100 by norm_num)
  have hp := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1/10 by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_order.1 hr).2 alpha alpha_pos,
    (tendsto_order.1 hp).2 (1/3) (by norm_num)] with b hb hr hp
  refine ⟨hb, ?_, by linarith⟩
  have hb0 : 0 < b := zero_lt_one.trans hb
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hb0 _)).mp hr.le

variable {I : Type u} {Z : Type v} {G : Type w}
  [Fintype I] [Fintype Z] [AddCommGroup G] [Fintype G]

lemma expected_badMixture_uniform_le {b A : ℝ} (hb : 1 ≤ b) (f : G → ℝ)
    (hthreshold : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ b^(-1/2 : ℝ))
    (hcard : (Fintype.card I : ℝ) ≤ b) {q : I → ℝ}
    (hq : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hmean : 2*alpha*b^(70/100 : ℝ) ≤ meanCount (fun i => fairRate (q i)))
    (ht : b^(69/100 : ℝ) ≤ alpha*b^(70/100 : ℝ)) :
    (𝔼 w : I → G, badMixture b A q f w) ≤ (2/alpha+1)*b^(-1/2 : ℝ) := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hm0 : 0 < 2*alpha*b^(70/100 : ℝ) := mul_pos (mul_pos (by norm_num) alpha_pos) (Real.rpow_pos_of_pos hb0 _)
  have hm : 0 < meanCount (fun i => fairRate (q i)) := hm0.trans_le hmean
  have hbound := expected_badMixture_le hq hq1 f (Real.rpow_nonneg hb0.le _)
    hthreshold hcard hm (by nlinarith)
  have hrec : 4/meanCount (fun i => fairRate (q i)) ≤
      (2/alpha)*b^(-1/2 : ℝ) := by
    calc
      _ ≤ 4/(2*alpha*b^(70/100 : ℝ)) := div_le_div_of_nonneg_left (by norm_num) hm0 hmean
      _ = (2/alpha)*b^(-70/100 : ℝ) := by
        rw [show (-70/100 : ℝ) = -(70/100 : ℝ) by ring, Real.rpow_neg hb0.le]
        field_simp ; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hb (by norm_num)) (div_nonneg (by norm_num) alpha_pos.le)
  nlinarith





theorem usable_anchor_selection :
    ∃ B : ℝ, 1 < B ∧ ∀ b : ℝ, B ≤ b →
      (Fintype.card I : ℝ) ≤ b → Real.log (Fintype.card G) ≤ b^4 →
      ∀ f : G → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ Real.exp (b^(65/100 : ℝ))) →
      (1/2 ≤ 𝔼 x, f x) → (𝔼 x, f x) ≤ 2 →
      ∀ (F : Z → ℝ) (E : Finset Z) (q : Z → I → ℝ), (∀ z, 0 ≤ F z) →
        (∀ z i, 0 ≤ q z i) → (∀ z i, q z i ≤ 1) →
        (∀ z ∈ E, 2*alpha*b^(70/100 : ℝ) ≤ meanCount (fun i => fairRate (q z i))) →
      ∃ w : I → G, ∃ U : Finset Z, U ⊆ E ∧
        (∀ z ∈ U, ∀ x, (1-b^(-1/20 : ℝ))*(1-3*b^(-1/10 : ℝ))*(𝔼 y, f y) ≤
          biasedAverage (q z) w f x) ∧
        SingleLatticeCovering.WeightedSelection.mass F (E \ U) ≤
          (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E ∧
        SingleLatticeCovering.WeightedSelection.mass F E -
          (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E ≤
            SingleLatticeCovering.WeightedSelection.mass F U ∧
        SingleLatticeCovering.WeightedSelection.mass F U ≤ SingleLatticeCovering.WeightedSelection.mass F E := by
  classical
  obtain ⟨B₀,hB₀,hS⟩ := SingleLatticeCovering.Sampler.uniform_boolean_sampling.{w}
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp eventually_mixture_parameters
  refine ⟨max B₀ B₁, hB₀.trans_le (le_max_left _ _), ?_⟩
  intro b hb hcard hG f hf hfcap hflo hfhi F E q hF hq hq1 hmean
  obtain ⟨hb1,ht,hδ⟩ := hB₁ b ((le_max_right _ _).trans hb)
  have hb0 : 0 < b := zero_lt_one.trans hb1
  let A : ℝ := (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y)
  have hA : 0 ≤ A := mul_nonneg (by linarith) (by linarith)
  have hsam : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ b^(-1/2 : ℝ) := by
    intro s hs hsb
    exact (hS b ((le_max_left _ _).trans hb) G hG f hf hfcap hflo hfhi s hs hsb).2
  have hbad : ∀ z ∈ E, (𝔼 w : I → G, badMixture b A (q z) f w) ≤
      (2/alpha+1)*b^(-1/2 : ℝ) := fun z hz =>
    expected_badMixture_uniform_le hb1.le f hsam hcard (hq z) (hq1 z) (hmean z hz) ht
  obtain ⟨w,U,hUE,hU,hdisc,hmass,hmass'⟩ :=
    SingleLatticeCovering.WeightedSelection.choose_usable F E
      (fun w z => badMixture b A (q z) f w)
      ((2/alpha+1)*b^(-1/2 : ℝ)) (b^(-1/20 : ℝ)) hF
      (fun w z => badMixture_nonneg b A (hq z) (hq1 z) f w) hbad (Real.rpow_pos_of_pos hb0 _)
  have hid : (2/alpha+1)*b^(-1/2 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E /
      b^(-1/20 : ℝ) = (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hb0.le]
    have he : b^(-1/2 : ℝ)*b^((1/20 : ℝ))=b^(-9/20 : ℝ) := by
      rw [← Real.rpow_add hb0]; norm_num
    calc
      _ = (2/alpha+1)*(b^(-1/2 : ℝ)*b^(1/20 : ℝ))*SingleLatticeCovering.WeightedSelection.mass F E := by
        norm_num; ring
      _ = _ := by rw [he]
  refine ⟨w,U,hUE,?_,hid ▸ hdisc,hid ▸ hmass,hmass'⟩
  intro z hz x
  have h := biasedAverage_of_badMixture_le (hq z) (hq1 z) f hf hA w (hU z hz) x
  simpa only [A, mul_assoc] using h

end SingleLatticeCovering.Bits


namespace SingleLatticeCovering.Bits
universe u v w
open Filter
open scoped Topology
theorem usable_anchor_selection_uniform :
    ∃ B : ℝ, 1 < B ∧ ∀ b : ℝ, B ≤ b →
      ∀ (I : Type u) [Fintype I] (Z : Type v) [Fintype Z]
        (G : Type w) [AddCommGroup G] [Fintype G],
      (Fintype.card I : ℝ) ≤ b → Real.log (Fintype.card G) ≤ b^4 →
      ∀ f : G → ℝ, (∀ x, 0 ≤ f x) → (∀ x, f x ≤ Real.exp (b^(65/100 : ℝ))) →
      (1/2 ≤ 𝔼 x, f x) → (𝔼 x, f x) ≤ 2 →
      ∀ (F : Z → ℝ) (E : Finset Z) (q : Z → I → ℝ), (∀ z, 0 ≤ F z) →
        (∀ z i, 0 ≤ q z i) → (∀ z i, q z i ≤ 1) →
        (∀ z ∈ E, 2*alpha*b^(70/100 : ℝ) ≤ meanCount (fun i => fairRate (q z i))) →
      ∃ w : I → G, ∃ U : Finset Z, U ⊆ E ∧
        (∀ z ∈ U, ∀ x, (1-b^(-1/20 : ℝ))*(1-3*b^(-1/10 : ℝ))*(𝔼 y, f y) ≤
          biasedAverage (q z) w f x) ∧
        SingleLatticeCovering.WeightedSelection.mass F (E \ U) ≤
          (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E ∧
        SingleLatticeCovering.WeightedSelection.mass F E -
          (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E ≤
            SingleLatticeCovering.WeightedSelection.mass F U ∧
        SingleLatticeCovering.WeightedSelection.mass F U ≤ SingleLatticeCovering.WeightedSelection.mass F E := by
  classical
  obtain ⟨B₀,hB₀,hS⟩ := SingleLatticeCovering.Sampler.uniform_boolean_sampling.{w}
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp eventually_mixture_parameters
  refine ⟨max B₀ B₁, hB₀.trans_le (le_max_left _ _), ?_⟩
  intro b hb I _ Z _ G _ _ hcard hG f hf hfcap hflo hfhi F E q hF hq hq1 hmean
  obtain ⟨hb1,ht,hδ⟩ := hB₁ b ((le_max_right _ _).trans hb)
  have hb0 : 0 < b := zero_lt_one.trans hb1
  let A : ℝ := (1-3*b^(-1/10 : ℝ))*(𝔼 y, f y)
  have hA : 0 ≤ A := mul_nonneg (by linarith) (by linarith)
  have hsam : ∀ s : ℕ, b^(69/100 : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ b →
      SingleLatticeCovering.Sampler.probability (fun w : Fin s → G => ∃ x,
        (∑ e : Fin s → Bool, f (x-SingleLatticeCovering.Sampler.subsetShift w e))/(2 : ℝ)^s < A) ≤ b^(-1/2 : ℝ) := by
    intro s hs hsb
    exact (hS b ((le_max_left _ _).trans hb) G hG f hf hfcap hflo hfhi s hs hsb).2
  have hbad : ∀ z ∈ E, (𝔼 w : I → G, badMixture b A (q z) f w) ≤
      (2/alpha+1)*b^(-1/2 : ℝ) := fun z hz =>
    expected_badMixture_uniform_le hb1.le f hsam hcard (hq z) (hq1 z) (hmean z hz) ht
  obtain ⟨w,U,hUE,hU,hdisc,hmass,hmass'⟩ :=
    SingleLatticeCovering.WeightedSelection.choose_usable F E
      (fun w z => badMixture b A (q z) f w)
      ((2/alpha+1)*b^(-1/2 : ℝ)) (b^(-1/20 : ℝ)) hF
      (fun w z => badMixture_nonneg b A (hq z) (hq1 z) f w) hbad (Real.rpow_pos_of_pos hb0 _)
  have hid : (2/alpha+1)*b^(-1/2 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E /
      b^(-1/20 : ℝ) = (2/alpha+1)*b^(-9/20 : ℝ)*SingleLatticeCovering.WeightedSelection.mass F E := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hb0.le]
    have he : b^(-1/2 : ℝ)*b^((1/20 : ℝ))=b^(-9/20 : ℝ) := by
      rw [← Real.rpow_add hb0]; norm_num
    calc
      _ = (2/alpha+1)*(b^(-1/2 : ℝ)*b^(1/20 : ℝ))*SingleLatticeCovering.WeightedSelection.mass F E := by
        norm_num; ring
      _ = _ := by rw [he]
  refine ⟨w,U,hUE,?_,hid ▸ hdisc,hid ▸ hmass,hmass'⟩
  intro z hz x
  have h := biasedAverage_of_badMixture_le (hq z) (hq1 z) f hf hA w (hU z hz) x
  simpa only [A, mul_assoc] using h

end SingleLatticeCovering.Bits





noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Blocks
local instance : (p : Prop) → Decidable p := Classical.propDecidable

universe u v
variable {K : Type u} {V : Type v} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]

abbrev Direction (V : Type v) [Zero V] := {v : V // v ≠ 0}


def lineSum (f : V → ℝ) (v x : V) : ℝ := ∑ a : K, f (x-a • v)


def lineMax (f : V → ℝ) (v x : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : K => f (x-a • v))

lemma lineMax_nonneg {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (v x : V) :
    0 ≤ lineMax (K := K) f v x :=
  (hf (x-(0 : K) • v)).trans (Finset.le_sup' (fun a : K => f (x-a • v)) (Finset.mem_univ (0 : K)))

lemma lineMax_le {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {f : V → ℝ} {c : ℝ} (hf : ∀ x, f x ≤ c) (v x : V) :
    lineMax (K := K) f v x ≤ c := Finset.sup'_le _ _ (fun _ _ => hf _)

lemma lineMax_le_sum {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (v x : V) :
    lineMax (K := K) f v x ≤ lineSum (K := K) f v x := by
  apply Finset.sup'_le
  intro a ha
  exact Finset.single_le_sum (f := fun b : K => f (x-b • v)) (fun b _ => hf _) ha

lemma mean_lineSum (f : V → ℝ) (v : V) :
    (𝔼 x, lineSum (K := K) f v x) = (Fintype.card K : ℝ) * (𝔼 x, f x) := by
  unfold lineSum
  rw [Finset.expect_sum_comm]
  have ht (a : K) : (𝔼 x, f (x-a • v)) = 𝔼 x, f x :=
    Fintype.expect_equiv (Equiv.subRight (a • v)) _ _ (fun _ => rfl)
  simp only [ht, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


def collision (U : Finset V) (v z : V) : Prop :=
  ∃ w ∈ U, w ≠ z ∧ ∃ a : K, a • v = w-z

lemma collision_of_two {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] {U : Finset V} {v x : V} (hv : v ≠ 0)
    {a b : K} (hab : a ≠ b) (hb : x-b • v ∈ U) :
    collision (K := K) U v (x-a • v) := by
  refine ⟨x-b • v,hb, ?_, a-b, ?_⟩
  · intro heq
    have heq' : b • v = a • v := by exact (sub_right_inj.mp heq)
    exact hab ((smul_left_injective K hv heq').symm)
  · rw [sub_smul]
    abel



lemma line_loss_le_collision {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0)
    (v : Direction V) (x : V) :
    lineSum (K := K) f v x - lineMax (K := K) f v x ≤
      ∑ a : K, if collision (K := K) U v (x-a • (v : V)) then f (x-a • (v : V)) else 0 := by
  classical
  by_cases hall : ∀ a : K, x-a • (v : V) ∈ U → collision (K := K) U v (x-a • (v : V))
  · have heq : (∑ a : K, if collision (K := K) U v (x-a • (v : V)) then f (x-a • (v : V)) else 0) =
        lineSum (K := K) f v x := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : x-a • (v : V) ∈ U
      · simp only [hall a ha, ↓reduceIte]
      · simp only [hsupp _ ha, ite_self]
    rw [heq]
    exact sub_le_self _ (lineMax_nonneg hf _ _)
  · push Not at hall
    obtain ⟨a,ha,hac⟩ := hall
    have hzero (b : K) (hb : b ≠ a) : f (x-b • (v : V)) = 0 := by
      apply hsupp
      intro hu
      exact hac (collision_of_two v.property (Ne.symm hb) hu)
    have hsum : lineSum (K := K) f v x = f (x-a • (v : V)) := by
      rw [lineSum, Finset.sum_eq_single a]
      · intro b _ hb
        exact hzero b hb
      · simp
    have hmax : f (x-a • (v : V)) ≤ lineMax (K := K) f v x :=
      Finset.le_sup' (fun a : K => f (x-a • (v : V))) (Finset.mem_univ a)
    apply le_trans (b := 0)
    · rw [hsum]
      exact sub_nonpos.mpr hmax
    · exact Finset.sum_nonneg (fun b _ => by split_ifs <;> simp only [hf, le_refl])


lemma direction_point_prob (z : V) :
    (𝔼 v : Direction V, if (v : V)=z then (1 : ℝ) else 0) ≤
      1 / (Fintype.card (Direction V) : ℝ) := by
  classical
  by_cases hz : z=0
  · subst z
    have he (v : Direction V) : (if (v : V)=0 then (1 : ℝ) else 0) = 0 := ite_eq_right v.property
    simp only [he, Finset.expect_const_zero]
    positivity
  · have heq (v : Direction V) : (v : V)=z ↔ v=⟨z,hz⟩ := ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [heq, Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, le_refl]

lemma collision_indicator_le {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] (U : Finset V) (v : Direction V) (z : V) :
    (if collision (K := K) U v z then (1 : ℝ) else 0) ≤
      ∑ w ∈ U, ∑ a : Direction K,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0 := by
  classical
  by_cases hc : collision (K := K) U v z
  · obtain ⟨w,hw,hwz,a,ha⟩ := hc
    have ha0 : a ≠ 0 := by
      intro h; rw [h,zero_smul] at ha
      exact hwz (sub_eq_zero.mp ha.symm)
    have hv : (v : V)=a⁻¹ • (w-z) := by rw [← ha, inv_smul_smul₀ ha0]
    calc
      _ = 1 := ite_eq_left ⟨w,hw,hwz,a,ha⟩
      _ ≤ ∑ b : Direction K, if (v : V)=(b : K)⁻¹ • (w-z) then (1 : ℝ) else 0 := by
        apply le_trans (b := if (v : V)=a⁻¹ • (w-z) then (1 : ℝ) else 0)
        · simp only [hv, ↓reduceIte, le_refl]
        · exact Finset.single_le_sum (f := fun b : Direction K =>
            if (v : V)=(b : K)⁻¹ • (w-z) then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ ⟨a,ha0⟩)
      _ ≤ _ := Finset.single_le_sum (f := fun w => ∑ a : Direction K,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0)
        (fun w _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) hw
  · simp only [hc, ↓reduceIte]
    exact Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))



lemma collision_probability_le (U : Finset V) (z : V) :
    (𝔼 v : Direction V, if collision (K := K) U v z then (1 : ℝ) else 0) ≤
      (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ) := by
  classical
  calc
    _ ≤ 𝔼 v : Direction V, ∑ w ∈ U, ∑ a : Direction K,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0 :=
      Finset.expect_le_expect (fun v _ => collision_indicator_le U v z)
    _ = ∑ w ∈ U, ∑ a : Direction K, 𝔼 v : Direction V,
        if (v : V)=(a : K)⁻¹ • (w-z) then (1 : ℝ) else 0 := by
      rw [Finset.expect_sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      exact Finset.expect_sum_comm _ _ _
    _ ≤ ∑ w ∈ U, ∑ a : Direction K, 1/(Fintype.card (Direction V) : ℝ) :=
      Finset.sum_le_sum (fun w _ => Finset.sum_le_sum (fun a _ => direction_point_prob _))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

lemma mean_line_loss_le {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0)
    (v : Direction V) :
    (Fintype.card K : ℝ)*(𝔼 x, f x) - (𝔼 x, lineMax (K := K) f v x) ≤
      (Fintype.card K : ℝ)*(𝔼 z, if collision (K := K) U v z then f z else 0) := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun x : V => fun _ => line_loss_le_collision (K := K) hf hsupp v x)
  rw [Finset.expect_sub_distrib, mean_lineSum] at h
  change (Fintype.card K : ℝ)*(𝔼 x, f x) - (𝔼 x, lineMax (K := K) f v x) ≤
    (𝔼 x, lineSum (K := K) (fun z => if collision (K := K) U v z then f z else 0) v x) at h
  rwa [mean_lineSum] at h



lemma mean_direction_loss_le {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0) :
    (𝔼 v : Direction V,
      ((Fintype.card K : ℝ)*(𝔼 x, f x) - (𝔼 x, lineMax (K := K) f v x))) ≤
      ((U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)) *
        ((Fintype.card K : ℝ)*(𝔼 x, f x)) := by
  classical
  let e : ℝ := (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)
  calc
    (𝔼 v : Direction V, ((Fintype.card K : ℝ)*(𝔼 x, f x) -
      (𝔼 x, lineMax (K := K) f (v : V) x))) ≤ 𝔼 v : Direction V,
        (Fintype.card K : ℝ)*(𝔼 z, if collision (K := K) U v z then f z else 0) :=
      Finset.expect_le_expect (fun v _ => mean_line_loss_le (K := K) hf hsupp v)
    _ = (Fintype.card K : ℝ) * (𝔼 z, f z * (𝔼 v : Direction V,
        if collision (K := K) U v z then (1 : ℝ) else 0)) := by
      rw [← Finset.mul_expect, Finset.expect_comm]
      congr 1
      apply Finset.expect_congr rfl
      intro z _
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro v _
      split_ifs <;> simp
    _ ≤ (Fintype.card K : ℝ) * (𝔼 z, f z * e) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.expect_le_expect (fun z _ => mul_le_mul_of_nonneg_left
        (collision_probability_le U z) (hf z))
    _ = ((U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)) *
        ((Fintype.card K : ℝ)*(𝔼 x, f x)) := by rw [← Finset.expect_mul]; dsimp [e]; ring




theorem exists_sparse_line [Nontrivial V] {U : Finset V} {f : V → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsupp : ∀ x, x ∉ U → f x = 0) :
    ∃ v : Direction V,
      (1-(U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ)) *
        ((Fintype.card K : ℝ)*(𝔼 x, f x)) ≤ (𝔼 x, lineMax (K := K) f v x) ∧
      (𝔼 x, lineMax (K := K) f v x) ≤ (Fintype.card K : ℝ)*(𝔼 x, f x) := by
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  let : Nonempty (Direction V) := ⟨⟨v,hv⟩⟩
  obtain ⟨v,_,hv⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty
    (mean_direction_loss_le (K := K) hf hsupp)
  refine ⟨v, by linarith, ?_⟩
  rw [← mean_lineSum (K := K) f v]
  exact Finset.expect_le_expect (fun x _ => lineMax_le_sum hf _ _)

lemma card_direction (W : Type*) [Zero W] [Fintype W] :
    Fintype.card (Direction W) = Fintype.card W - 1 := by
  classical
  simpa only [Direction, Fintype.card_unique] using Fintype.card_subtype_compl (fun w : W => w=0)

lemma collision_factor_le_twice {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] [Nontrivial V] (U : Finset V) :
    (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ) ≤
      2*(Fintype.card K : ℝ)*((U.card : ℝ)/(Fintype.card V : ℝ)) := by
  have hV : 2 ≤ Fintype.card V := Fintype.one_lt_card
  have hK : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [card_direction K, card_direction V, Nat.cast_sub hK, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
  norm_num only [Nat.cast_one]
  have hV' : (2 : ℝ) ≤ Fintype.card V := Nat.cast_le.mpr hV
  have hK' : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast hK
  have hc : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < (Fintype.card V : ℝ)-1)).mpr
  have hVp : (0 : ℝ) < Fintype.card V := by linarith
  field_simp
  nlinarith [mul_nonneg hc (by linarith : 0 ≤ (Fintype.card K : ℝ)),
    mul_nonneg hc (by nlinarith : 0 ≤ (Fintype.card K : ℝ)*((Fintype.card V : ℝ)-2))]


def usableMass (U : Finset V) (F : V → ℝ) : ℝ :=
  𝔼 z, if z ∈ U then F z else 0



def sparseWeight (U : Finset V) (F : V → ℝ) (z : V) : ℝ :=
  if z ∈ U then F z / (Fintype.card K : ℝ) else 0

lemma mean_sparseWeight {K : Type u} {V : Type v} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Fintype V] (U : Finset V) (F : V → ℝ) :
    (Fintype.card K : ℝ)*(𝔼 z, sparseWeight (K := K) U F z) = usableMass U F := by
  have hp : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro z _
  simp only [sparseWeight]
  split_ifs <;> field_simp ; simp

lemma usable_density_le {V : Type v} [AddCommGroup V] [Fintype V] {U : Finset V} {F : V → ℝ} {a : ℝ} (ha : 0 < a)
    (hF : ∀ z ∈ U, a ≤ F z) :
    (U.card : ℝ)/(Fintype.card V : ℝ) ≤ usableMass U F / a := by
  have hm : (𝔼 z, if z ∈ U then (1 : ℝ) else 0) = (U.card : ℝ)/(Fintype.card V : ℝ) := by
    simp [Fintype.expect_eq_sum_div_card]
  rw [← hm, le_div_iff₀ ha, Finset.expect_mul]
  apply Finset.expect_le_expect
  intro z _
  by_cases hz : z ∈ U
  · simp only [hz, ↓reduceIte, one_mul]
    exact hF z hz
  · simp only [hz, ↓reduceIte, zero_mul, le_refl]




theorem gaussian_window_sparse_line [Nontrivial V] (U : Finset V) (F : V → ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (t r : ℝ)
    (hFl : ∀ z ∈ U, Real.exp (t-r) ≤ F z)
    (hFu : ∀ z ∈ U, F z ≤ Real.exp (t+r))
    (hpl : Real.exp (t-4*r) ≤ (Fintype.card K : ℝ))
    (hpu : (Fintype.card K : ℝ) ≤ Real.exp (t-3*r))
    (hM : usableMass U F ≤ 2) :
    ∃ v : Direction V,
      usableMass U F - 4*usableMass U F*Real.exp (-2*r) ≤
        (𝔼 x, lineMax (K := K) (sparseWeight (K := K) U F) v x) ∧
      (𝔼 x, lineMax (K := K) (sparseWeight (K := K) U F) v x) ≤ usableMass U F ∧
      ∀ x, 0 ≤ lineMax (K := K) (sparseWeight (K := K) U F) v x ∧
        lineMax (K := K) (sparseWeight (K := K) U F) v x ≤ Real.exp (5*r) := by
  classical
  have hp : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hweight0 (z : V) : 0 ≤ sparseWeight (K := K) U F z := by
    unfold sparseWeight
    split_ifs
    · exact div_nonneg (hF0 z) hp.le
    · rfl
  have hweightsupp (z : V) (hz : z ∉ U) : sparseWeight (K := K) U F z = 0 := by
    simp only [sparseWeight, hz, ↓reduceIte]
  have hM0 : 0 ≤ usableMass U F := Finset.expect_nonneg (fun z _ => by
    split_ifs <;> simp only [hF0, le_refl])
  have hratio : (Fintype.card K : ℝ)/Real.exp (t-r) ≤ Real.exp (-2*r) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    convert hpu using 1 ; congr 1 ; ring
  have hsmall : (U.card : ℝ)*(Fintype.card (Direction K) : ℝ)/(Fintype.card (Direction V) : ℝ) ≤
      4*Real.exp (-2*r) := by
    calc
      _ ≤ 2*(Fintype.card K : ℝ)*((U.card : ℝ)/(Fintype.card V : ℝ)) := collision_factor_le_twice U
      _ ≤ 2*(Fintype.card K : ℝ)*(usableMass U F / Real.exp (t-r)) :=
        mul_le_mul_of_nonneg_left (usable_density_le (Real.exp_pos _) hFl) (by positivity)
      _ = 2*usableMass U F*((Fintype.card K : ℝ)/Real.exp (t-r)) := by ring
      _ ≤ 2*usableMass U F*Real.exp (-2*r) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ 4*Real.exp (-2*r) := by nlinarith [Real.exp_pos (-2*r)]
  obtain ⟨v,hv,hvu⟩ := exists_sparse_line (K := K) hweight0 hweightsupp
  rw [mean_sparseWeight] at hv hvu
  refine ⟨v, ?_, hvu, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hsmall hM0
    nlinarith
  · intro x
    refine ⟨lineMax_nonneg hweight0 _ _, lineMax_le (fun z => ?_) _ _⟩
    unfold sparseWeight
    split_ifs with hz
    · calc
        F z / (Fintype.card K : ℝ) ≤ Real.exp (t+r) / (Fintype.card K : ℝ) :=
          div_le_div_of_nonneg_right (hFu z hz) hp.le
        _ ≤ Real.exp (t+r) / Real.exp (t-4*r) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hpl
        _ = Real.exp (5*r) := by rw [← Real.exp_sub]; congr 1; ring
    · exact (Real.exp_pos _).le

end SingleLatticeCovering.Blocks





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
