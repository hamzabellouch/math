import Mathlib
import OAI.Analysis.HardSphere.Geometry.PairHistory

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

lemma radiusActivity_smul (c : ℝ≥0∞) (a : ℕ → ℝ≥0∞) :
    radiusActivity (fun l ↦ c*a l) = c*radiusActivity a := by
  unfold radiusActivity
  simp only [mul_assoc]
  rw [ENNReal.tsum_mul_left]
  ac_rfl

lemma ofReal_exp_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (Real.exp (∑ i ∈ s, f i)) = ∏ i ∈ s, ENNReal.ofReal (Real.exp (f i)) := by
  rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact (Real.exp_pos _).le

theorem radius_exponential_bound (m T : ℕ) (hT : T ≤ 3^m)
    (a : ℕ → ℝ≥0∞) (U : ℤ × ℤ → ℝ)
    (hU0 : ∀ z, 0 ≤ U z) (hU1 : ∀ z, U z ≤ 1)
    (hUa : ∀ z, ENNReal.ofReal (U z) ≤ radiusEnvelope a z)
    (ha : ENNReal.ofReal (2*Real.exp 2) * radiusActivity a ≤ (1/2:ℝ≥0∞)) :
    (∑' w, fourLaw m w * ENNReal.ofReal
      (Real.exp (2 * ∑ u ∈ Finset.range (T+1), U (differenceAt m u w)))) ≤ 2 := by
  let c := ENNReal.ofReal (2*Real.exp 2)
  let b := fun l ↦ c*a l
  let f := fun z ↦ ENNReal.ofReal (Real.exp (2*U z)-1)
  have hba : radiusActivity b ≤ (1/2:ℝ≥0∞) := by
    simpa only [b, radiusActivity_smul, c] using ha
  have hbf : ∀ z, f z ≤ radiusEnvelope b z := by
    intro z
    calc
      f z ≤ ENNReal.ofReal (2*Real.exp 2 * U z) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          exp_sub_one_le_slope (by linarith [hU0 z] : 0 ≤ 2*U z) (by linarith [hU1 z] : 2*U z ≤ 2)
      _ = c * ENNReal.ofReal (U z) := by rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ c * radiusEnvelope a z := mul_le_mul' le_rfl (hUa z)
      _ = radiusEnvelope b z := (radiusEnvelope_smul c a z).symm
  have he (z : ℤ × ℤ) : 1+f z = ENNReal.ofReal (Real.exp (2*U z)) := by
    have hx : 0 ≤ Real.exp (2*U z)-1 := by
      have := Real.one_le_exp_iff.mpr (by linarith [hU0 z] : 0 ≤ 2*U z)
      linarith
    change 1+ENNReal.ofReal (Real.exp (2*U z)-1) = _
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hx]
    congr 1
    ring
  have h := (ordered_product_bound m T hT b f hbf (hba.trans_lt (by norm_num))).1
  have hh : (∑' w, fourLaw m w * ENNReal.ofReal
      (Real.exp (2 * ∑ u ∈ Finset.range (T+1), U (differenceAt m u w)))) =
      ∑' w, fourLaw m w * ∏ u ∈ Finset.range (T+1), (1+f (differenceAt m u w)) := by
    apply tsum_congr
    intro w
    congr 1
    rw [Finset.mul_sum, ofReal_exp_finset_sum]
    exact Finset.prod_congr rfl (fun u _ ↦ (he _).symm)
  rw [hh]
  refine h.trans ?_
  have hd : (1/2:ℝ≥0∞) ≤ 1-radiusActivity b := by
    simpa using tsub_le_tsub_left hba (1:ℝ≥0∞)
  exact (ENNReal.inv_le_inv.mpr hd).trans_eq (by norm_num)

lemma orderedEncounterConstant_one_le : 1 ≤ orderedEncounterConstant := by
  have hn : (4 * ∑' k, gapKernel k) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) gapKernel_sum_ne_top
  have h : (1:ℝ≥0∞) ≤ 4 * ∑' k, gapKernel k := by
    calc
      (1:ℝ≥0∞) ≤ 4*1 := by norm_num
      _ ≤ _ := mul_le_mul' le_rfl gapKernel_sum_one_le
  exact_mod_cast (ENNReal.toReal_mono hn h)

lemma radiusEnvelope_le_activity (a : ℕ → ℝ≥0∞) (z : ℤ × ℤ) :
    radiusEnvelope a z ≤ radiusActivity a := by
  have hc : 1 ≤ ENNReal.ofReal orderedEncounterConstant := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal orderedEncounterConstant_one_le
  calc
    _ ≤ ∑' l, a l := by
      apply ENNReal.tsum_le_tsum
      intro l
      split_ifs <;> simp
    _ ≤ ∑' l, a l * ((1+l : ℕ) : ℝ≥0∞)^2 := by
      apply ENNReal.tsum_le_tsum
      intro l
      have h : (1:ℝ≥0∞) ≤ ((1+l : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 1 ≤ 1+l)
      simpa using mul_le_mul' (le_refl (a l)) (one_le_pow₀ (n:=2) h)
    _ ≤ _ := by simpa [radiusActivity] using
      mul_le_mul' hc (le_refl (∑' l, a l * ((1+l : ℕ) : ℝ≥0∞)^2))

def radiusPotential (a : ℕ → ℝ≥0∞) (z : ℤ × ℤ) : ℝ := (radiusEnvelope a z).toReal

lemma radiusPotential_nonneg (a : ℕ → ℝ≥0∞) (z : ℤ × ℤ) : 0 ≤ radiusPotential a z :=
  ENNReal.toReal_nonneg

lemma expSlope_one_le : 1 ≤ ENNReal.ofReal (2*Real.exp 2) := by
  have h : (1:ℝ) ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (by linarith : (1:ℝ) ≤ 2*Real.exp 2)

lemma small_activity_envelope_le_one (a : ℕ → ℝ≥0∞)
    (ha : ENNReal.ofReal (2*Real.exp 2) * radiusActivity a ≤ (1/2:ℝ≥0∞))
    (z : ℤ × ℤ) : radiusEnvelope a z ≤ 1 := by
  refine (radiusEnvelope_le_activity a z).trans ?_
  calc
    radiusActivity a ≤ ENNReal.ofReal (2*Real.exp 2)*radiusActivity a := by
      simpa using mul_le_mul' expSlope_one_le (le_refl (radiusActivity a))
    _ ≤ (1/2:ℝ≥0∞) := ha
    _ ≤ 1 := by norm_num

lemma radiusPotential_cast (a : ℕ → ℝ≥0∞) (z : ℤ × ℤ)
    (h : radiusEnvelope a z ≤ 1) : ENNReal.ofReal (radiusPotential a z) = radiusEnvelope a z :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by norm_num) h)

theorem small_radius_potential_moment (m T : ℕ) (hT : T ≤ 3^m) (a : ℕ → ℝ≥0∞)
    (ha : ENNReal.ofReal (2*Real.exp 2) * radiusActivity a ≤ (1/2:ℝ≥0∞)) :
    (∑' w, fourLaw m w * ENNReal.ofReal (Real.exp
      (2 * ∑ u ∈ Finset.range (T+1), radiusPotential a (differenceAt m u w)))) ≤ 2 := by
  apply radius_exponential_bound m T hT a (radiusPotential a) (radiusPotential_nonneg a)
  · intro z
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using small_activity_envelope_le_one a ha z)
  · intro z
    exact (radiusPotential_cast a z (small_activity_envelope_le_one a ha z)).le
  · exact ha

def geometricRadiusWeights (A R : ℕ) (b q : ℝ≥0∞) (l : ℕ) : ℝ≥0∞ :=
  (if l=R then b else 0) + ∑' m : ℕ, if l=A*(m+1) then q^(m+1) else 0

lemma geometricRadiusWeights_activity (A R : ℕ) (b q : ℝ≥0∞) :
    radiusActivity (geometricRadiusWeights A R b q) =
      ENNReal.ofReal orderedEncounterConstant *
        (b*((1+R : ℕ) : ℝ≥0∞)^2 +
          ∑' m : ℕ, q^(m+1) * ((1+A*(m+1) : ℕ) : ℝ≥0∞)^2) := by
  unfold radiusActivity geometricRadiusWeights
  congr 1
  simp_rw [add_mul, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_add, ENNReal.tsum_comm]
  simp only [ite_mul, zero_mul, tsum_ite_eq]

lemma geometricRadiusWeights_envelope (A R : ℕ) (b q : ℝ≥0∞) (z : ℤ × ℤ) :
    radiusEnvelope (geometricRadiusWeights A R b q) z =
      (if z ∈ square R then b else 0) +
        ∑' m : ℕ, if z ∈ square (A*(m+1)) then q^(m+1) else 0 := by
  unfold radiusEnvelope geometricRadiusWeights
  have he (l : ℕ) :
      (if z ∈ square l then
        (if l=R then b else 0) + ∑' m : ℕ, if l=A*(m+1) then q^(m+1) else 0 else 0) =
      (if l=R then (if z ∈ square R then b else 0) else 0) +
        ∑' m : ℕ, if l=A*(m+1) then (if z ∈ square (A*(m+1)) then q^(m+1) else 0) else 0 := by
    by_cases hz : z ∈ square l
    · simp only [ite_eq_left hz]
      congr 1
      · rcases eq_or_ne l R with rfl | hl
        · simp [hz]
        · simp [hl]
      · apply tsum_congr
        intro m
        rcases eq_or_ne l (A*(m+1)) with rfl | hl
        · simp [hz]
        · simp [hl]
    · rw [ite_eq_right hz]
      have hb : (if l=R then (if z ∈ square R then b else 0) else 0) = 0 := by
        rcases eq_or_ne l R with rfl | hl
        · simp [hz]
        · simp [hl]
      rw [hb, zero_add]
      symm
      apply ENNReal.tsum_eq_zero.mpr
      intro m
      rcases eq_or_ne l (A*(m+1)) with rfl | hl
      · simp [hz]
      · simp [hl]
  simp_rw [he]
  rw [ENNReal.tsum_add, ENNReal.tsum_comm]
  simp only [tsum_ite_eq]

lemma succ_le_two_pow (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by norm_num)
    omega

lemma radius_polynomial_le (A m : ℕ) :
    (1+A*(m+1))^2 ≤ (1+A)^2 * 4^m := by
  calc
    _ ≤ ((1+A)*2^m)^2 := Nat.pow_le_pow_left (by
      calc
        1+A*(m+1) ≤ (1+A)*(m+1) := by nlinarith
        _ ≤ (1+A)*2^m := Nat.mul_le_mul_left _ (succ_le_two_pow m)) 2
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 2, pow_mul]; norm_num

lemma geometric_radius_tail_le (A : ℕ) (q : ℝ≥0∞) (hq : q ≤ 1/8) :
    (∑' m : ℕ, q^(m+1) * ((1+A*(m+1) : ℕ) : ℝ≥0∞)^2) ≤
      2*q*((1+A : ℕ) : ℝ≥0∞)^2 := by
  have h4q : (4:ℝ≥0∞)*q ≤ 1/2 := by
    calc
      _ ≤ 4*(1/8:ℝ≥0∞) := mul_le_mul' le_rfl hq
      _ = _ := by
        have h : (4:ℝ≥0)*(1/8)=1/2 := by norm_num
        have hh := congrArg (fun x : ℝ≥0 ↦ (x:ℝ≥0∞)) h
        simpa only [ENNReal.coe_mul, ENNReal.coe_div (show (8:ℝ≥0) ≠ 0 by norm_num),
          ENNReal.coe_div (show (2:ℝ≥0) ≠ 0 by norm_num), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hh
  calc
    _ ≤ ∑' m : ℕ, q * ((1+A : ℕ) : ℝ≥0∞)^2 * ((1/2:ℝ≥0∞)^m) := by
      apply ENNReal.tsum_le_tsum
      intro m
      calc
        _ ≤ q^(m+1) * (((1+A : ℕ) : ℝ≥0∞)^2 * 4^m) := by
          apply mul_le_mul' le_rfl
          exact_mod_cast radius_polynomial_le A m
        _ = q * ((1+A : ℕ) : ℝ≥0∞)^2 * ((4*q)^m) := by
          rw [pow_succ, mul_pow]
          ring
        _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left' h4q m)
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num
      ring

lemma small_parameters (A R : ℕ) (C S : ℝ) (hC : 0 ≤ C) (hS : 0 ≤ S) :
    ∃ κ p₀ : ℝ, 0 < κ ∧ 0 < p₀ ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ p₀ →
        let q := (A:ℝ)*p*Real.exp (κ*C)
        0 ≤ q ∧ q ≤ 1/8 ∧
          S * (C*κ*((1+R:ℕ):ℝ)^2 + 2*q*((1+A:ℕ):ℝ)^2) ≤ 1/2 := by
  let B : ℝ := S*(C*((1+R:ℕ):ℝ)^2+2*((1+A:ℕ):ℝ)^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨η, hη, hηB⟩ := exists_pos_mul_lt (by norm_num : (0:ℝ) < 1/2) B
  let κ := min η (1/8:ℝ)
  have hκ : 0 < κ := lt_min hη (by norm_num)
  have hκ8 : κ ≤ 1/8 := min_le_right _ _
  have hκB : B*κ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hB).trans hηB.le
  obtain ⟨p₀, hp₀, hp₀κ⟩ := exists_pos_mul_lt hκ ((A:ℝ)*Real.exp (κ*C))
  refine ⟨κ, p₀, hκ, hp₀, ?_⟩
  intro p hp hpp
  dsimp only
  have hq0 : 0 ≤ (A:ℝ)*p*Real.exp (κ*C) := by positivity
  have hqκ : (A:ℝ)*p*Real.exp (κ*C) ≤ κ := by
    calc
      _ = ((A:ℝ)*Real.exp (κ*C))*p := by ring
      _ ≤ ((A:ℝ)*Real.exp (κ*C))*p₀ := mul_le_mul_of_nonneg_left hpp (by positivity)
      _ ≤ κ := hp₀κ.le
  refine ⟨hq0, hqκ.trans hκ8, ?_⟩
  calc
    _ ≤ S*(C*κ*((1+R:ℕ):ℝ)^2+2*κ*((1+A:ℕ):ℝ)^2) := by
      apply mul_le_mul_of_nonneg_left _ hS
      linarith [mul_le_mul_of_nonneg_right hqκ (by positivity : 0 ≤ 2*((1+A:ℕ):ℝ)^2)]
    _ = B*κ := by dsimp [B]; ring
    _ ≤ 1/2 := hκB

def foldIndex (n : ℕ) (j : Fin (n+1)) : Fin (n/2+1) × Bool :=
  if hj : j.val ≤ n/2 then (⟨j.val, by omega⟩, false)
  else (⟨n-j.val, by omega⟩, true)

lemma foldIndex_value (n : ℕ) (j : Fin (n+1)) :
    (foldIndex n j).1.val = min j.val (n-j.val) := by
  unfold foldIndex
  split_ifs with h <;> simp only
  · omega
  · omega

lemma foldIndex_injective (n : ℕ) : Function.Injective (foldIndex n) := by
  intro i j h
  have h₁ := congrArg (fun x : Fin (n/2+1) × Bool ↦ x.1.val) h
  have h₂ := congrArg Prod.snd h
  unfold foldIndex at h₁ h₂
  split_ifs at h₁ h₂ <;> simp_all only
  all_goals apply Fin.ext; omega

lemma folded_sum_le (n : ℕ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ Finset.range (n+1), f (min j (n-j))) ≤
      2 * ∑ j ∈ Finset.range (n/2+1), f j := by
  let g : Fin (n/2+1) × Bool → ℝ := fun x ↦ f x.1.val
  have hs : (∑ x ∈ Finset.univ.image (foldIndex n), g x) ≤ ∑ x, g x := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ ↦ hf _)
  rw [Finset.sum_image (fun i _ j _ hij ↦ foldIndex_injective n hij)] at hs
  have hleft : (∑ i : Fin (n+1), g (foldIndex n i)) =
      ∑ j ∈ Finset.range (n+1), f (min j (n-j)) := by
    simp only [g, foldIndex_value]
    exact Fin.sum_univ_eq_sum_range (fun j ↦ f (min j (n-j))) (n+1)
  have hright : (∑ x : Fin (n/2+1) × Bool, g x) =
      2 * ∑ j ∈ Finset.range (n/2+1), f j := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, g, ← two_mul, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range]
  simpa only [hleft, hright] using hs

lemma geometricRadiusWeights_activity_le (A R : ℕ) (b q : ℝ≥0∞) (hq : q ≤ 1/8) :
    radiusActivity (geometricRadiusWeights A R b q) ≤
      ENNReal.ofReal orderedEncounterConstant *
        (b*((1+R:ℕ):ℝ≥0∞)^2 + 2*q*((1+A:ℕ):ℝ≥0∞)^2) := by
  rw [geometricRadiusWeights_activity]
  exact mul_le_mul' le_rfl (add_le_add le_rfl (geometric_radius_tail_le A q hq))

lemma folded_radius_potential_moment (m n : ℕ) (hn : n/2 ≤ 3^m)
    (a : ℕ → ℝ≥0∞)
    (ha : ENNReal.ofReal (2*Real.exp 2)*radiusActivity a ≤ (1/2:ℝ≥0∞)) :
    (∑' w, fourLaw m w * ENNReal.ofReal (Real.exp
      (∑ j ∈ Finset.range (n+1), radiusPotential a (differenceAt m (min j (n-j)) w)))) ≤ 2 := by
  refine le_trans ?_ (small_radius_potential_moment m (n/2) hn a ha)
  apply ENNReal.tsum_le_tsum
  intro w
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact folded_sum_le n (fun u ↦ radiusPotential a (differenceAt m u w))
    (fun _ ↦ radiusPotential_nonneg a _)

theorem geometric_folded_moment (A R : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ κ p₀ : ℝ, 0 < κ ∧ 0 < p₀ ∧
      ∀ p : ℝ, 0 ≤ p → p ≤ p₀ →
      ∀ m n : ℕ, n/2 ≤ 3^m →
        let a := geometricRadiusWeights A R (ENNReal.ofReal (C*κ))
          (ENNReal.ofReal ((A:ℝ)*p*Real.exp (κ*C)))
        (∑' w, fourLaw m w * ENNReal.ofReal (Real.exp
          (∑ j ∈ Finset.range (n+1), radiusPotential a (differenceAt m (min j (n-j)) w)))) ≤ 2 := by
  have hcan := orderedEncounterConstant_pos
  let S : ℝ := (2*Real.exp 2)*orderedEncounterConstant
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨κ, p₀, hκ, hp₀, hpars⟩ := small_parameters A R C S hC hS
  refine ⟨κ, p₀, hκ, hp₀, ?_⟩
  intro p hp hpp m n hn
  dsimp only
  rcases hpars p hp hpp with ⟨hq0, hq8, hbound⟩
  let q := (A:ℝ)*p*Real.exp (κ*C)
  have hq0' : 0 ≤ q := hq0
  have hq8' : ENNReal.ofReal q ≤ (1/8:ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq8
  apply folded_radius_potential_moment m n hn
  calc
    _ ≤ ENNReal.ofReal (2*Real.exp 2) * (ENNReal.ofReal orderedEncounterConstant *
        (ENNReal.ofReal (C*κ)*((1+R:ℕ):ℝ≥0∞)^2 +
          2*ENNReal.ofReal q*((1+A:ℕ):ℝ≥0∞)^2)) := by
      exact mul_le_mul' le_rfl (geometricRadiusWeights_activity_le A R _ _ hq8')
    _ = ENNReal.ofReal (S*(C*κ*((1+R:ℕ):ℝ)^2+2*q*((1+A:ℕ):ℝ)^2)) := by
      dsimp only [S]
      simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_add,
        ENNReal.ofReal_pow, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      ring
    _ ≤ (1/2:ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hbound

lemma integer_step_lipschitz (f : ℕ → ℤ) (H : ℕ) (L : ℤ)
    (hstep : ∀ i<H, |f (i+1)-f i|≤L) {i j : ℕ} (hi : i≤H) (hj : j≤H) :
    |f i-f j|≤L*|(i:ℤ)-j| := by
  have hforward : ∀ a b, a≤b → b≤H → |f b-f a|≤L*((b:ℤ)-a) := by
    intro a b hab hb
    induction b,hab using Nat.le_induction with
    | base => simp
    | @succ b hab ih =>
      have h := hstep b (by omega)
      have hh := ih (by omega)
      calc
        |f (b+1)-f a| ≤ |f (b+1)-f b|+|f b-f a| := abs_sub_le _ _ _
        _ ≤ L+L*((b:ℤ)-a) := add_le_add h hh
        _ = _ := by push_cast; ring
  rcases le_total i j with h|h
  · rw [abs_sub_comm (f i),abs_sub_comm (i:ℤ),abs_of_nonneg (by omega : 0≤(j:ℤ)-i)]
    exact hforward i j h hj
  · rw [abs_of_nonneg (by omega : 0≤(i:ℤ)-j)]
    exact hforward j i h hi

lemma walk_lipschitz (m : ℕ) (w : TreeNoise m) {i j : ℕ} (hi : i≤3^m) (hj : j≤3^m) :
    |walk m w i-walk m w j|≤|(i:ℤ)-j| := by
  simpa only [one_mul] using integer_step_lipschitz (walk m w) (3^m) 1
    (fun k hk ↦ (walk_increment m w k hk).le) hi hj

lemma walk_abs_le (m : ℕ) (w : TreeNoise m) {j : ℕ} (hj : j≤3^m) : |walk m w j|≤j := by
  simpa using walk_lipschitz m w hj (show 0≤3^m by omega)

lemma folded_index_lipschitz (n : ℕ) (i j : Fin (n+1)) :
    |((min i.val (n-i.val):ℕ):ℤ)-(min j.val (n-j.val):ℕ)|≤|(i.val:ℤ)-j.val| := by
  have hi := i.isLt
  have hj := j.isLt
  have h := abs_min_sub_min_le_max (i.val:ℤ) ((n:ℤ)-i.val) (j.val:ℤ) ((n:ℤ)-j.val)
  have he : |((n:ℤ)-i.val)-((n:ℤ)-j.val)|=|(i.val:ℤ)-j.val| := by
    rw [sub_sub_sub_cancel_left,abs_sub_comm]
  simpa only [Nat.cast_min,Int.natCast_sub (show i.val≤n by omega),
    Int.natCast_sub (show j.val≤n by omega),he,max_self] using h

end HardSphere.Lattice
end

end OAI
