import Mathlib
import OAI.Combinatorics.UniformKServer.LogPrimitive

namespace OAI

                                         
section

                                                                          
                                                                                

noncomputable section
namespace UniformKServer.UniformIntegrals
open MeasureTheory Set Filter
open scoped Topology

def height (u : ℝ) : ℝ := 1 + Real.log (1/u)
def regular (h y : ℝ) : ℝ := (h+y)^2/h
def marked (u y : ℝ) : ℝ := u + height u*y*(1+y)

theorem height_ge_one {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) : 1 ≤ height u := by
  unfold height
  have hh := Real.log_nonneg ((le_div_iff₀ hu).mpr (by simpa using hu₁))
  linarith

theorem regular_deriv {h : ℝ} (hh : 0 < h) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun z => -h/(h+z)) (1/regular h y) y := by
  have hd := (hasDerivAt_const y (-h)).div ((hasDerivAt_id y).const_add h) (by linarith : h+y ≠ 0)
  convert! hd using 1
  simp [regular]

theorem regular_tendsto (h : ℝ) : Tendsto (fun y : ℝ => -h/(h+y)) atTop (𝓝 0) := by
  have hh : Tendsto (fun y : ℝ => h+y) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  simpa [div_eq_mul_inv] using hh.inv_tendsto_atTop.const_mul (-h)

theorem regular_integrable {h : ℝ} (hh : 1 ≤ h) :
    IntegrableOn (fun y => 1 / regular h y) (Ioi 0) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (fun y hy => regular_deriv (by linarith) hy) _ (regular_tendsto h)
  intro y hy
  dsimp [regular]
  positivity

theorem regular_integral {h : ℝ} (hh : 1 ≤ h) :
    (∫ y in Ioi (0:ℝ), 1 / regular h y) = 1 := by
  have hx := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y (hy : y ∈ Ici (0:ℝ)) => regular_deriv (show 0 < h by linarith) hy)
    (regular_integrable hh) (regular_tendsto h)
  simpa [ne_of_gt (show 0 < h by linarith)] using hx

theorem marked_pos {u y : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hy : 0 ≤ y) : 0 < marked u y := by
  dsimp [marked]
  have hh := height_ge_one hu hu₁
  positivity

theorem marked_local {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntegrableOn (fun y => 1/marked u y) (Ioc 0 1) volume := by
  apply (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  apply continuousOn_const.div
  · unfold marked; fun_prop
  · intro y hy; exact ne_of_gt (marked_pos hu hu₁ hy.1)

theorem tail_deriv {y : ℝ} (hy : 1 ≤ y) : HasDerivAt (fun z : ℝ => -1/z) (1/y^2) y := by
  convert! (hasDerivAt_const y (-1:ℝ)).div (hasDerivAt_id y) (by linarith : y ≠ 0) using 1
  simp

theorem tail_tendsto : Tendsto (fun y : ℝ => -1/y) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).const_mul (-1)

theorem tail_integrable : IntegrableOn (fun y : ℝ => 1/y^2) (Ioi 1) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun y hy => tail_deriv hy) (fun y hy => by positivity) tail_tendsto

theorem tail_integral : (∫ y in Ioi (1:ℝ), 1/y^2) = 1 := by
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun y hy => tail_deriv hy) tail_integrable tail_tendsto

theorem marked_tail_bound {u y : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hy : 1 ≤ y) :
    1/marked u y ≤ 1/height u * (1/y^2) := by
  have hh := height_ge_one hu hu₁
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le
  · positivity
  · dsimp [marked]
    nlinarith [mul_nonneg (show 0 ≤ height u by linarith) (show 0 ≤ y by linarith)]

theorem marked_tail {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntegrableOn (fun y => 1/marked u y) (Ioi 1) volume := by
  refine (tail_integrable.const_mul (1/height u)).mono' ?_ ?_
  · apply (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    apply continuousOn_const.div
    · unfold marked; fun_prop
    · intro y hy; exact ne_of_gt (marked_pos hu hu₁ (by have := (show 1 < y from hy); linarith))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (one_div_pos.mpr (marked_pos hu hu₁ (by have := (show 1 < y from hy); linarith))))]
    exact marked_tail_bound hu hu₁ (le_of_lt hy)

theorem marked_integrable {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntegrableOn (fun y => 1 / marked u y) (Ioi 0) volume := by
  have hs : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext y
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hy : y ≤ 1
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr (lt_of_not_ge hy)
  rw [← hs]
  exact (marked_local hu hu₁).union (marked_tail hu hu₁)

theorem linear_local {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntervalIntegrable (fun y => 1/(u+height u*y)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply continuousOn_const.div (by fun_prop)
  intro y hy
  have hh := height_ge_one hu hu₁
  exact ne_of_gt (by nlinarith [hy.1] : 0 < u+height u*y)

theorem linear_integral {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in (0:ℝ)..1, 1/(u+height u*y)) = (Real.log (u+height u)-Real.log u)/height u := by
  have hh := height_ge_one hu hu₁
  have hd : ∀ y ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun z => Real.log (u+height u*z)/height u) (1/(u+height u*y)) y := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
    have hp : 0 < u+height u*y := by nlinarith [hy.1]
    convert! (((hasDerivAt_id y).const_mul (height u)).const_add u).log hp.ne' |>.div_const (height u) using 1
    simp only [id_eq, mul_one]
    field_simp
  convert! intervalIntegral.integral_eq_sub_of_hasDerivAt hd (linear_local hu hu₁) using 1
  simp
  ring

theorem log_bound {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (Real.log (u+height u)-Real.log u)/height u ≤ 2 := by
  have hh := height_ge_one hu hu₁
  have hm : Real.log (u+height u) ≤ Real.log (1+height u) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+height u by linarith)
  have he : Real.log u = 1-height u := by simp [height, one_div, Real.log_inv]
  apply (div_le_iff₀ (show 0 < height u by linarith)).mpr
  linarith

theorem marked_local_integral {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in Ioc (0:ℝ) 1, 1/marked u y) ≤ 2 := by
  have hh := height_ge_one hu hu₁
  have hi : IntegrableOn (fun y => 1/(u+height u*y)) (Ioc 0 1) volume := (linear_local hu hu₁).1
  calc
    _ ≤ ∫ y in Ioc (0:ℝ) 1, 1/(u+height u*y) := by
      apply setIntegral_mono_on (marked_local hu hu₁) hi measurableSet_Ioc
      intro y hy
      apply one_div_le_one_div_of_le
      · nlinarith [hy.1]
      · unfold marked
        nlinarith [mul_nonneg (show 0 ≤ height u by linarith) (sq_nonneg y)]
    _ = (Real.log (u+height u)-Real.log u)/height u := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact linear_integral hu hu₁
    _ ≤ 2 := log_bound hu hu₁

theorem marked_tail_integral {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in Ioi (1:ℝ), 1/marked u y) ≤ 1 := by
  calc
    _ ≤ ∫ y in Ioi (1:ℝ), 1/height u * (1/y^2) :=
      setIntegral_mono_on (marked_tail hu hu₁) (tail_integrable.const_mul _) measurableSet_Ioi
        (fun y hy => marked_tail_bound hu hu₁ (le_of_lt hy))
    _ = 1/height u := by rw [integral_const_mul, tail_integral, mul_one]
    _ ≤ 1 := (div_le_one (show 0 < height u by linarith [height_ge_one hu hu₁])).mpr (height_ge_one hu hu₁)

theorem marked_integral_uniform {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in Ioi (0:ℝ), 1 / marked u y) ≤ 3 := by
  have hs : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext y; simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hy : y ≤ 1
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr (lt_of_not_ge hy)
  have hd : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := Set.disjoint_left.mpr (fun y hy hz => not_lt_of_ge hy.2 hz)
  rw [← hs, setIntegral_union hd measurableSet_Ioi
    (marked_local hu hu₁) (marked_tail hu hu₁)]
  linarith [marked_local_integral hu hu₁, marked_tail_integral hu hu₁]

end UniformKServer.UniformIntegrals

namespace UniformKServer.AlphaBounds
open MeasureTheory Set Filter
open scoped Topology
open UniformKServer.LogPrimitive

local notation "reg" => UniformKServer.Denominators.regular
local notation "mark" => UniformKServer.Denominators.marked

theorem logarithmic_substitution (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    (∫ x in a..1, 1/(x * F (Real.log (1/x)))) =
      ∫ y in (0:ℝ)..Real.log (1/a), 1/F y := by
  have hI : uIcc a 1 = Icc a 1 := uIcc_of_le ha₁
  have hf : ContinuousOn (fun x : ℝ => -Real.log x) (uIcc a 1) := by
    rw [hI]
    exact (continuousOn_id.log (fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1))).neg
  have hd : ∀ x ∈ Ioo (min a 1) (max a 1), HasDerivAt (fun x : ℝ => -Real.log x) (-1/x) x := by
    intro x hx
    rw [min_eq_left ha₁, max_eq_right ha₁] at hx
    convert! (Real.hasDerivAt_log (ne_of_gt (lt_trans ha hx.1))).neg using 1
    simp [div_eq_mul_inv]
  have hn : ∀ x ∈ Ioo (min a 1) (max a 1), -1/x ≤ (0:ℝ) := by
    intro x hx
    rw [min_eq_left ha₁, max_eq_right ha₁] at hx
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt (lt_trans ha hx.1))
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := fun y => 1/F y) hf hd hn
  have hl : (fun x : ℝ => ((fun y => 1/F y) ∘ (fun x => -Real.log x)) x * (-1/x)) =
      fun x => -(1/(x * F (Real.log (1/x)))) := by
    funext x
    simp only [Function.comp_apply, one_div, Real.log_inv, neg_div]
    ring
  rw [hl, intervalIntegral.integral_neg] at he
  simp only [Real.log_one, neg_zero] at he
  rw [intervalIntegral.integral_symm (f := fun y => 1/F y) 0] at he
  simpa only [neg_inj, ← Real.log_inv, ← one_div] using he

theorem weighted_integral_positive {F : ℝ → ℝ} {C a : ℝ}
    (hint : IntegrableOn (fun y => 1/F y) (Ioi 0) volume)
    (hpos : ∀ y, 0 ≤ y → 0 < F y)
    (hbound : (∫ y in Ioi (0:ℝ), 1/F y) ≤ C) (ha : 0 < a) (ha₁ : a ≤ 1) :
    (∫ x in a..1, 1/(x*F (Real.log (1/x)))) ≤ C := by
  rw [logarithmic_substitution F ha ha₁,
    intervalIntegral.integral_of_le (UniformKServer.Denominators.log_nonneg ha.le ha₁)]
  apply le_trans (setIntegral_mono_set hint ?_ ?_) hbound
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (one_div_pos.mpr (hpos y (le_of_lt hy))).le
  · exact Filter.Eventually.of_forall fun y hy => hy.1

theorem weighted_integral_closed {D : ℝ → ℝ} {C : ℝ}
    (hc : ContinuousOn (fun a => ∫ x in a..1, 1/(x*D x)) (Icc 0 1))
    (hb : ∀ a, 0 < a → a ≤ 1 → (∫ x in a..1, 1/(x*D x)) ≤ C)
    {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) : (∫ x in a..1, 1/(x*D x)) ≤ C := by
  apply le_on_closure (s := Ioc (0:ℝ) 1) (f := fun a => ∫ x in a..1, 1/(x*D x))
    (g := fun _ => C) (fun a ha => hb a ha.1 ha.2)
  · simpa only [closure_Ioc (by norm_num : (0:ℝ) ≠ 1)] using hc
  · exact continuousOn_const
  · simpa only [closure_Ioc (by norm_num : (0:ℝ) ≠ 1)] using ha

theorem weight_continuous {D : ℝ → ℝ}
    (hc : ContinuousOn (primitive D 1 1 0 (-1)) (Icc 0 1)) :
    ContinuousOn (fun a => ∫ x in a..1, 1/(x*D x)) (Icc 0 1) := by
  apply hc.neg.congr
  intro a ha
  change (∫ x in a..1, 1/(x*D x)) = -(primitive D 1 1 0 (-1) a)
  simp only [primitive, one_mul, zero_sub, neg_div, neg_neg, div_div]
  exact intervalIntegral.integral_symm _ _

theorem regular_weight {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Icc (0:ℝ) 1) :
    (∫ x in a..1, 1/(x*reg h x)) ≤ 1 := by
  apply weighted_integral_closed _ _ ha
  · apply weight_continuous
    -- Contracts at either base follow from the same integrable density.
    have hc := (regular_contract h 1 0 (-1) hh).1
    have hi : IntervalIntegrable (fun x => (0-(-1)/x)/reg h x) volume 0 1 :=
      integrand_integrable (by unfold UniformKServer.Denominators.regular; fun_prop)
        (by positivity : (0:ℝ) < 1/h) (fun x hx hx₁ => regular_lower hh hx hx₁) 0 (-1)
    have he : ∀ a ∈ Icc (0:ℝ) 1, primitive (reg h) 1 1 0 (-1) a =
        primitive (reg h) 0 1 0 (-1) a - primitive (reg h) 0 1 0 (-1) 1 := by
      intro a ha
      unfold primitive
      simp only [one_mul]
      exact (intervalIntegral.integral_interval_sub_left
        (hi.mono_set (by simpa only [uIcc_of_le ha.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
          (Icc_subset_Icc (a₁ := (0:ℝ)) le_rfl ha.2))) hi).symm
    apply (hc.sub continuousOn_const).congr
    intro a ha
    exact he a ha
  · intro a ha ha₁
    exact weighted_integral_positive (UniformKServer.UniformIntegrals.regular_integrable hh)
      (fun y hy => by unfold UniformKServer.UniformIntegrals.regular; positivity)
      (le_of_eq (UniformKServer.UniformIntegrals.regular_integral hh)) ha ha₁

theorem marked_weight {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : a ∈ Icc (0:ℝ) 1) :
    (∫ x in a..1, 1/(x*mark u x)) ≤ 3 := by
  apply weighted_integral_closed (weight_continuous (marked_contract u 1 0 (-1) hu hu₁).1) _ ha
  intro a ha ha₁
  exact weighted_integral_positive (UniformKServer.UniformIntegrals.marked_integrable hu hu₁)
    (fun y hy => by
      unfold UniformKServer.UniformIntegrals.marked
      have := UniformKServer.UniformIntegrals.height_ge_one hu hu₁
      positivity)
    (UniformKServer.UniformIntegrals.marked_integral_uniform hu hu₁) ha ha₁

theorem regular_weight_integrable {h : ℝ} (hh : 1 ≤ h) :
    IntervalIntegrable (fun x => 1/(x*reg h x)) volume 0 1 := by
  have hp : 0 < h := by linarith
  simpa only [zero_sub, neg_div, neg_neg, div_div] using
    (integrand_integrable (by unfold UniformKServer.Denominators.regular; fun_prop)
      (by positivity : (0:ℝ) < 1/h) (fun x hx hx₁ => regular_lower hh hx hx₁) 0 (-1))

theorem marked_weight_integrable {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntervalIntegrable (fun x => 1/(x*mark u x)) volume 0 1 := by
  simpa only [zero_sub, neg_div, neg_neg, div_div] using
    (integrand_integrable (by unfold UniformKServer.Denominators.marked; fun_prop)
      (by positivity : (0:ℝ) < u/4) (fun x hx hx₁ => marked_lower hu hu₁ hx hx₁) 0 (-1))

theorem regular_ge_one {h x : ℝ} (hh : 1 ≤ h) (hx : x ∈ Icc (0:ℝ) 1) :
    1 ≤ reg h x := by
  have hp : 0 < h := by linarith
  have hl := UniformKServer.Denominators.log_nonneg hx.1 hx.2
  unfold UniformKServer.Denominators.regular
  apply (le_div_iff₀ hp).mpr
  nlinarith [mul_nonneg hp.le hl, sq_nonneg (Real.log (1/x))]

theorem regular_component {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q : ℝ) :
    |primitive (reg h) 0 scale S Q a| ≤ |scale| * (|S| *a + |Q|) := by
  have hi := regular_weight_integrable hh
  have hia : IntervalIntegrable (fun x => 1/(x*reg h x)) volume 0 a := hi.mono_set (by
    simpa only [uIcc_of_le ha.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      (Icc_subset_Icc (a₁ := (0:ℝ)) le_rfl ha.2))
  have hweight : (∫ x in (0:ℝ)..a, 1/(x*reg h x)) ≤ 1 := by
    apply le_trans (intervalIntegral.integral_mono_interval le_rfl ha.1 ha.2 ?_ hi)
      (regular_weight hh (show (0:ℝ) ∈ Icc 0 1 by simp))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact div_nonneg (by norm_num) (mul_nonneg hx.1.le (by linarith [regular_ge_one hh ⟨hx.1.le,hx.2⟩]))
  have hb : |∫ x in (0:ℝ)..a, (S-Q/x)/reg h x| ≤
      ∫ x in (0:ℝ)..a, |S| + |Q| *(1/(x*reg h x)) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le ha.1 _
      (intervalIntegrable_const.add (hia.const_mul _))
    apply Filter.Eventually.of_forall
    intro x hx
    have hx₁ : x ≤ 1 := le_trans hx.2 ha.2
    have hD := regular_ge_one hh ⟨hx.1.le,hx₁⟩
    have hDp : 0 < reg h x := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hDp]
    calc
      _ ≤ (|S|+|Q|/x)/reg h x := div_le_div_of_nonneg_right
        (by simpa only [abs_div, abs_of_pos hx.1] using abs_sub S (Q/x)) hDp.le
      _ = |S|/reg h x + |Q| *(1/(x*reg h x)) := by ring
      _ ≤ |S| + |Q| *(1/(x*reg h x)) := by
        gcongr
        exact (div_le_self (abs_nonneg S) hD)
  rw [intervalIntegral.integral_add intervalIntegrable_const (hia.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hb
  simp only [sub_zero, smul_eq_mul] at hb
  rw [primitive, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg scale)
  nlinarith [mul_le_mul_of_nonneg_left hweight (abs_nonneg Q)]

theorem marked_component {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q : ℝ) :
    |primitive (mark u) 1 scale S Q a| ≤ 3*|scale| * (|S| *(1-a) + |S-Q|) := by
  have hi := marked_weight_integrable hu hu₁
  have hia : IntervalIntegrable (fun x => 1/(x*mark u x)) volume a 1 := hi.mono_set (by
    rw [uIcc_of_le ha.2, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro x hx
    exact ⟨le_trans ha.1 hx.1, hx.2⟩)
  let K := |S| *(1-a)+|S-Q|
  have hK : 0 ≤ K := add_nonneg (mul_nonneg (abs_nonneg S) (sub_nonneg.mpr ha.2)) (abs_nonneg _)
  have hb : |∫ x in a..1, (S-Q/x)/mark u x| ≤
      ∫ x in a..1, K*(1/(x*mark u x)) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le ha.2 _ (hia.const_mul _)
    apply Filter.Eventually.of_forall
    intro x hx
    have hx₀ : 0 < x := lt_of_le_of_lt ha.1 hx.1
    have hD := UniformKServer.Denominators.marked_pos hu hu₁ hx₀.le hx.2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hD]
    have he : S-Q/x = (S*(x-1)+(S-Q))/x := by field_simp; ring
    rw [he, abs_div, abs_of_pos hx₀]
    calc
      _ ≤ ((|S| *|x-1|+|S-Q|)/x)/mark u x := by
        gcongr
        simpa only [abs_mul] using abs_add_le (S*(x-1)) (S-Q)
      _ ≤ (K/x)/mark u x := by
        gcongr
        rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
        dsimp [K]
        nlinarith [abs_nonneg S, hx.1]
      _ = K*(1/(x*mark u x)) := by ring
  rw [intervalIntegral.integral_const_mul] at hb
  have hw := marked_weight hu hu₁ ha
  have hb' : |∫ x in a..1, (S-Q/x)/mark u x| ≤ K*3 :=
    hb.trans (mul_le_mul_of_nonneg_left hw hK)
  rw [primitive, abs_mul, intervalIntegral.integral_symm, abs_neg]
  calc
    _ ≤ |scale| *(K*3) := mul_le_mul_of_nonneg_left hb' (abs_nonneg scale)
    _ = 3*|scale| *(|S| *(1-a)+|S-Q|) := by dsimp [K]; ring

end UniformKServer.AlphaBounds

end


end

end OAI
