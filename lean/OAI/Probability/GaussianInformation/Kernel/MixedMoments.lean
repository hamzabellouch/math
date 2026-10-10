import Mathlib
import OAI.Probability.GaussianInformation.Kernel.SmallBalls

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Geometry
section MixedGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma tube_ball_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {a k : ℕ} {B R t : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) (ht : 0 < t) (ht1 : t ≤ 1)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction + (k+1) ≤ a) :
    μ {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*t} ≤
      ENNReal.ofReal (B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a * t^(k+1)) := by
  classical
  let j := Module.finrank ℝ V.direction
  obtain ⟨s, hs, hcard⟩ := exists_affine_tube_cover V hV hR.le (mul_pos hR ht)
  have hsub : {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*t} ⊆
      ⋃ c ∈ s, ball c (3*(R*t)) := by
    intro x hx
    obtain ⟨c,hc,hxc⟩ := hs x hx.1 hx.2
    exact mem_iUnion₂.mpr ⟨c,hc,lt_of_le_of_lt hxc (by nlinarith)⟩
  have hc : (s.card : ℝ) ≤ (9/t)^j := by
    apply hcard.trans
    apply pow_le_pow_left₀ (by positivity)
    calc
      (4*R+5*(R*t))/(R*t) ≤ (9*R)/(R*t) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left ht1 hR.le]
      _ = 9/t := by field_simp
  have halg : (9/t)^j * (B*(3*(R*t))^a) ≤
      B*9^j*3^a*R^a*t^(k+1) := by
    obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hdim
    have htj : t^j ≠ 0 := pow_ne_zero _ ht.ne'
    have hte : t^e ≤ 1 := pow_le_one₀ ht.le ht1
    have heq : (9/t)^j * (B*(3*(R*t))^a) =
        (B*9^j*3^a*R^a*t^(k+1))*t^e := by
      simp only [he, j, mul_pow, div_pow, pow_add]
      field_simp
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) hte

  calc
    _ ≤ ∑ c ∈ s, μ (ball c (3*(R*t))) := (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _c ∈ s, ENNReal.ofReal (B*(3*(R*t))^a) := by gcongr; exact hball _ _ (by positivity)
    _ = ENNReal.ofReal ((s.card:ℝ)*(B*(3*(R*t))^a)) := by
      simp [ENNReal.ofReal_mul, hB]
    _ ≤ ENNReal.ofReal (B*9^j*3^a*R^a*t^(k+1)) := by
      apply ENNReal.ofReal_le_ofReal
      exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans halg

lemma inverseMoment_extended_of_tails {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (D : E → ℝ)
    (hD : Measurable D) (hD0 : ∀ x, 0 ≤ D x) (k : ℕ) (hk : 0 < k)
    (A : ℝ≥0∞) (hA : A ≠ ∞)
    (htail : ∀ j : ℕ, μ {x | D x ≤ (1/2:ℝ)^j} ≤
      A * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j))) :
    (∫⁻ x, (ENNReal.ofReal (D x))⁻¹^k ∂μ) ≤
      μ univ + A*ENNReal.ofReal ((2:ℝ)^(k+1)) := by
  have hz : ∀ᵐ x ∂μ, D x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using zeroSet_null_of_dyadic_tails μ D k A hA htail
  have heq : (fun x => (ENNReal.ofReal (D x))⁻¹^k) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((D x)⁻¹^k)) := by
    filter_upwards [hz] with x hx
    rw [ENNReal.ofReal_pow (inv_nonneg.mpr (hD0 x)),
      ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne (hD0 x) hx.symm)]
  rw [lintegral_congr_ae heq]
  exact inverseMoment_of_dyadic_tails μ D hD hD0 k hk A htail

lemma angular_integral_ball (μ : Measure E) {a k : ℕ} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) (hk : 0 < k)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction + (k+1) ≤ a) :
    (∫⁻ x in closedBall 0 R, (ENNReal.ofReal (infDist x (V : Set E)/R))⁻¹^k ∂μ) ≤
      ENNReal.ofReal (B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a * 2^(k+2)) := by
  let C := B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : (μ.restrict (closedBall 0 R)) univ ≤ ENNReal.ofReal C := by
    rw [Measure.restrict_apply_univ]
    calc
      μ (closedBall 0 R) ≤ μ (ball 0 (2*R)) := measure_mono (closedBall_subset_ball (by linarith))
      _ ≤ ENNReal.ofReal (B*(2*R)^a) := hball _ _ (by positivity)
      _ ≤ ENNReal.ofReal C := by
        apply ENNReal.ofReal_le_ofReal
        have h9 : (1:ℝ) ≤ 9^(Module.finrank ℝ V.direction) := one_le_pow₀ (by norm_num)
        dsimp [C]
        rw [mul_pow]
        calc
          B * (2^a * R^a) ≤ B * (3^a * R^a) := by gcongr; norm_num
          _ ≤ B * 9^(Module.finrank ℝ V.direction) * 3^a * R^a := by
            nlinarith [mul_nonneg (mul_nonneg hB (pow_nonneg (by norm_num : (0:ℝ) ≤ 3) a))
              (pow_nonneg hR.le a)]
  have ht : ∀ j : ℕ, (μ.restrict (closedBall 0 R)) {x | infDist x (V : Set E)/R ≤ (1/2:ℝ)^j} ≤
      ENNReal.ofReal C * ENNReal.ofReal ((1/2:ℝ)^((k+1)*j)) := by
    intro j
    rw [Measure.restrict_apply (measurableSet_le ((continuous_infDist_pt _).measurable.div_const R) measurable_const)]
    have heq : {x | infDist x (V : Set E)/R ≤ (1/2:ℝ)^j} ∩ closedBall 0 R =
        {x | ‖x‖ ≤ R ∧ infDist x (V : Set E) ≤ R*(1/2:ℝ)^j} := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_closedBall, dist_zero_right]
      rw [div_le_iff₀ hR, mul_comm ((1/2:ℝ)^j) R]
      tauto
    rw [heq]
    convert tube_ball_bound μ hB hR (by positivity : 0 < (1/2:ℝ)^j)
      (pow_le_one₀ (by norm_num) (by norm_num)) hball V hV hdim using 1
    rw [← ENNReal.ofReal_mul hC]
    dsimp [C]
    congr 1
    rw [← pow_mul, Nat.mul_comm j (k+1)]
  have hh := inverseMoment_extended_of_tails (μ.restrict (closedBall 0 R))
    (fun x => infDist x (V : Set E)/R) ((continuous_infDist_pt _).measurable.div_const R)
    (fun _ => div_nonneg infDist_nonneg hR.le) k hk (ENNReal.ofReal C) ENNReal.ofReal_ne_top ht
  calc
    _ ≤ (μ.restrict (closedBall 0 R)) univ + ENNReal.ofReal C*ENNReal.ofReal ((2:ℝ)^(k+1)) := hh
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal C*ENNReal.ofReal ((2:ℝ)^(k+1)) := by gcongr
    _ ≤ ENNReal.ofReal (C * 2^(k+2)) := by
      rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_add hC (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hp : (1:ℝ) ≤ 2^(k+1) := one_le_pow₀ (by norm_num)
      have he : (2:ℝ)^(k+2) = 2^(k+1)*2 := by rw [show k+2=(k+1)+1 by omega,pow_succ]
      rw [he]
      nlinarith

lemma inverse_normalized (y R : ℝ) (hR : 0 < R) (k : ℕ) :
    (ENNReal.ofReal y)⁻¹^k = ENNReal.ofReal (R⁻¹^k) *
      (ENNReal.ofReal (y/R))⁻¹^k := by
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  rw [ENNReal.ofReal_pow (inv_nonneg.mpr hR.le), ENNReal.ofReal_inv_of_pos hR,
    ENNReal.ofReal_div_of_pos hR,
    ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hR0),
    div_eq_mul_inv, mul_pow, ← mul_assoc, ← mul_pow,
    ENNReal.inv_mul_cancel hR0 ENNReal.ofReal_ne_top]
  simp

lemma mixed_integral_shell (μ : Measure E) {a k : ℕ} {B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) (hk : 0 < k) (ha : 2*k ≤ a)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction + (k+1) ≤ a) :
    (∫⁻ x in {x | R/2 < ‖x‖ ∧ ‖x‖ ≤ R},
      (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k ∂μ) ≤
      ENNReal.ofReal (B * 9^(Module.finrank ℝ V.direction) * 3^a * 2^(2*k+2) * R^(a-2*k)) := by
  let g : E → ℝ≥0∞ := fun x => (ENNReal.ofReal (infDist x (V : Set E)/R))⁻¹^k
  have hg : Measurable g := ((continuous_infDist_pt _).measurable.div_const R).ennreal_ofReal.inv.pow_const _
  let c : ℝ := (R/2)⁻¹^k * R⁻¹^k
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint : ∀ x ∈ {x : E | R/2 < ‖x‖ ∧ ‖x‖ ≤ R},
      (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k ≤
      ENNReal.ofReal c * g x := by
    intro x hx
    calc
      _ ≤ (ENNReal.ofReal (R/2))⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k := by
        gcongr
        exact hx.1.le
      _ = ENNReal.ofReal c * g x := by
        rw [inverse_normalized (infDist x (V : Set E)) R hR k,
          ← ENNReal.ofReal_inv_of_pos (show 0 < R/2 by positivity),
          ← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x : E | R/2 < ‖x‖ ∧ ‖x‖ ≤ R}, ENNReal.ofReal c*g x ∂μ :=
      setLIntegral_mono (measurable_const.mul hg) hpoint
    _ ≤ ∫⁻ x in closedBall 0 R, ENNReal.ofReal c*g x ∂μ :=
      lintegral_mono_set (fun x hx => by simpa only [mem_closedBall,dist_zero_right] using hx.2)
    _ = ENNReal.ofReal c * ∫⁻ x in closedBall 0 R, g x ∂μ := lintegral_const_mul _ hg
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (B*9^(Module.finrank ℝ V.direction)*3^a*R^a*2^(k+2)) :=
      mul_le_mul_right (angular_integral_ball μ hB hR hk hball V hV hdim) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le ha
      simp only [he, Nat.add_sub_cancel_left, c, inv_pow, div_pow,
        pow_add, pow_mul, pow_succ]
      field_simp
      ring_nf
      simp only [Nat.mul_comm k 2, pow_mul]
      norm_num

lemma ball_bound_zero_null {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) {a : ℕ} {B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hball : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^a)) :
    μ {x | ‖x‖ = 0} = 0 := by
  have hr : ENNReal.ofReal ((1/2:ℝ)^a) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact pow_lt_one₀ (by norm_num) (by norm_num) ha.ne'
  have ht := ENNReal.Tendsto.const_mul
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr ENNReal.ofReal_ne_top :
      (0:ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal B ≠ ∞)
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' (show Tendsto (fun j : ℕ => ENNReal.ofReal B *
    ENNReal.ofReal ((1/2:ℝ)^a)^j) atTop (𝓝 (0:ℝ≥0∞)) from by simpa using ht)
  intro j
  calc
    μ {x | ‖x‖ = 0} ≤ μ (ball 0 ((1/2:ℝ)^j)) := by
      apply measure_mono
      intro x hx
      change ‖x‖ = 0 at hx
      simpa only [mem_ball, dist_zero_right, hx] using (by positivity : (0:ℝ) < (1/2:ℝ)^j)
    _ ≤ ENNReal.ofReal (B*(((1/2:ℝ)^j)^a)) := hball _ _ (by positivity)
    _ = _ := by rw [ENNReal.ofReal_mul hB, ← pow_mul, Nat.mul_comm j a, pow_mul,
      ENNReal.ofReal_pow (by positivity)]

lemma logarithmic_series_bound (f : ℕ → ℝ≥0∞) {A D : ℝ} (hA : 0 ≤ A) (_hD : 0 ≤ D)
    (L : ℕ) (hDA : D ≤ A*2^L)
    (hfirst : ∀ j, f j ≤ ENNReal.ofReal A)
    (hsecond : ∀ j, f j ≤ ENNReal.ofReal (D*(1/2:ℝ)^j)) :
    (∑' j, f j) ≤ ENNReal.ofReal (A*((L:ℝ)+2)) := by
  rw [← (ENNReal.summable (f := fun i => f (i+L))).sum_add_tsum_nat_add']
  have ht : ∀ i : ℕ, f (i+L) ≤ ENNReal.ofReal A * ENNReal.ofReal ((1/2:ℝ)^i) := by
    intro i
    apply (hsecond _).trans
    rw [← ENNReal.ofReal_mul hA]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (A*2^L)*(1/2:ℝ)^(i+L) := mul_le_mul_of_nonneg_right hDA (by positivity)
      _ = _ := by
        rw [pow_add]
        simp only [one_div,inv_pow]
        field_simp
  calc
    _ ≤ (∑ _i ∈ Finset.range L, ENNReal.ofReal A) +
        ∑' i, ENNReal.ofReal A * ENNReal.ofReal ((1/2:ℝ)^i) := by
      exact add_le_add (Finset.sum_le_sum (fun i _ => hfirst i)) (ENNReal.tsum_le_tsum ht)
    _ = ENNReal.ofReal (A*((L:ℝ)+2)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2), ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric]
      norm_num [ENNReal.ofReal_div_of_pos]
      rw [← ENNReal.ofReal_natCast L, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul hA,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma mixed_integral_logarithmic (μ : Measure E) {n k : ℕ} {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hk : 0 < k) (hn : 2*k < n)
    (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ 2)
    (hballB : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (B*r^(2*k)))
    (hballD : ∀ z r, 0 < r → μ (ball z r) ≤ ENNReal.ofReal (D*r^n))
    (V : AffineSubspace ℝ E) (hV : (V : Set E).Nonempty)
    (hdim : Module.finrank ℝ V.direction ≤ k-1) (L : ℕ) (hDB : D ≤ B*2^L) :
    (∫⁻ x, (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k ∂μ) ≤
      ENNReal.ofReal ((9^(Module.finrank ℝ V.direction) * 3^n * 2^(n+2*k+2)) * B * ((L:ℝ)+2)) := by
  let K : ℝ := 9^(Module.finrank ℝ V.direction) * 3^n * 2^(n+2*k+2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let R : ℕ → ℝ := fun j => 2*(1/2:ℝ)^j
  let S : ℕ → Set E := fun j => {x | R j/2 < ‖x‖ ∧ ‖x‖ ≤ R j}
  let f : E → ℝ≥0∞ := fun x => (ENNReal.ofReal ‖x‖)⁻¹^k * (ENNReal.ofReal (infDist x (V : Set E)))⁻¹^k
  have hdimB : Module.finrank ℝ V.direction + (k+1) ≤ 2*k := by omega
  have hdimD : Module.finrank ℝ V.direction + (k+1) ≤ n := by omega
  have hz : ∀ᵐ x ∂μ, ‖x‖ ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using ball_bound_zero_null μ (by omega : 0 < 2*k) hB hballB
  have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ j, S j := by
    filter_upwards [hsupport,hz] with x hx hx0
    obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near_of_lt_one
      (div_pos (lt_of_le_of_ne (norm_nonneg _) hx0.symm) (by norm_num : (0:ℝ) < 2))
      (by linarith : ‖x‖/2 ≤ 1) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
    apply mem_iUnion.mpr ⟨j,?_⟩
    dsimp [S,R]
    rw [pow_succ] at hj
    constructor <;> linarith
  have hiB : ∀ j, (∫⁻ x in S j, f x ∂μ) ≤ ENNReal.ofReal (K*B) := by
    intro j
    apply (mixed_integral_shell μ hB (by dsimp [R]; positivity : 0 < R j) hk le_rfl hballB V hV hdimB).trans
    apply ENNReal.ofReal_le_ofReal
    simp only [Nat.sub_self, pow_zero, mul_one]
    have h3 : (3:ℝ)^(2*k) ≤ 3^n := pow_le_pow_right₀ (by norm_num) hn.le
    have h2 : (2:ℝ)^(2*k+2) ≤ 2^(n+2*k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [K]
    calc
      _ ≤ B*9^(Module.finrank ℝ V.direction)*3^n*2^(n+2*k+2) := by gcongr
      _ = _ := by ring
  have hiD : ∀ j, (∫⁻ x in S j, f x ∂μ) ≤ ENNReal.ofReal ((K*D)*(1/2:ℝ)^j) := by
    intro j
    apply (mixed_integral_shell μ hD (by dsimp [R]; positivity : 0 < R j) hk hn.le hballD V hV hdimD).trans
    apply ENNReal.ofReal_le_ofReal
    have hp : R j^(n-2*k) ≤ 2^n*(1/2:ℝ)^j := by
      dsimp [R]
      rw [mul_pow]
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      · simpa only [pow_one] using pow_le_pow_of_le_one
          (by positivity : 0 ≤ (1/2:ℝ)^j) (pow_le_one₀ (by norm_num) (by norm_num)) (by omega : 1 ≤ n-2*k)
      · positivity
      · positivity
    calc
      _ ≤ D*9^(Module.finrank ℝ V.direction)*3^n*2^(2*k+2)*(2^n*(1/2:ℝ)^j) := by gcongr
      _ = _ := by dsimp [K]; rw [show n+2*k+2=n+(2*k+2) by omega,pow_add]; ring
  calc
    (∫⁻ x, f x ∂μ) = ∫⁻ x in ⋃ j,S j, f x ∂μ := by rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ ∑' j, ∫⁻ x in S j,f x ∂μ := lintegral_iUnion_le S f
    _ ≤ ENNReal.ofReal ((K*B)*((L:ℝ)+2)) := logarithmic_series_bound _
      (mul_nonneg hK hB) (mul_nonneg hK hD) L
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hDB hK) hiB hiD

end MixedGeometry

end Geometry

end KernelPotential

end OAI
