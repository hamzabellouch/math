import OAI.Analysis.SignedDisk.ScalarCancellation1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PlanePotential

/-- Hölder followed by Tonelli gives the integral-kernel Minkowski estimate at
p=3/2. Both measures and the actual joint kernel remain explicit. -/
theorem kernel_lp_three_halves {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α × β → ℝ≥0∞} (hK : Measurable K) {C : ℝ≥0∞}
    (hC : ∀ y, (∫⁻ x, (K (x,y))^(3/2:ℝ) ∂μ) ≤ C^(3/2:ℝ)) :
    (∫⁻ x, (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ∂μ) ≤ (C*ν univ)^(3/2:ℝ) := by
  have hpq : Real.HolderConjugate (3/2) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hpoint (x : α) : (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ≤
      (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun y => K (x,y)) (g := fun _ => 1)
      ((hK.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (aemeasurable_const (b := (1:ℝ≥0∞)))
    simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
    have h' := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 3/2)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),← ENNReal.rpow_mul,
      show (1/(3/2:ℝ))*(3/2)=1 by norm_num,
      show (1/(3:ℝ))*(3/2)=1/2 by norm_num,ENNReal.rpow_one,one_mul] using h'
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) ∂μ :=
      lintegral_mono (fun x => hpoint x)
    _ = (∫⁻ y, ∫⁻ x, K (x,y)^(3/2:ℝ) ∂μ ∂ν)*(ν univ)^(1/2:ℝ) := by
      rw [lintegral_mul_const _ (hK.pow_const _).lintegral_prod_right,
        lintegral_lintegral_swap (hK.pow_const _).aemeasurable]
    _ ≤ (C^(3/2:ℝ)*ν univ)*(ν univ)^(1/2:ℝ) := by
      apply mul_le_mul_left
      exact (lintegral_mono hC).trans_eq (lintegral_const _)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),mul_assoc]
      congr 1
      calc
        _ = (ν univ)^(1:ℝ)*(ν univ)^(1/2:ℝ) := by rw [ENNReal.rpow_one]
        _ = (ν univ)^((1:ℝ)+1/2) := (ENNReal.rpow_add_of_nonneg 1 (1/2) (by norm_num) (by norm_num)).symm
        _ = _ := by norm_num

end PlanePotential

open Finset
open scoped RealInnerProductSpace

namespace FiniteLabels
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

structure Law (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  nonneg : ∀ i, 0 ≤ mass i
  total : ∑ i, mass i = 1

instance : CoeFun (Law ι) (fun _ => ι → ℝ) := ⟨Law.mass⟩

def delta [DecidableEq ι] (i : ι) : Law ι where
  mass j := if j=i then 1 else 0
  nonneg j := by split_ifs <;> norm_num
  total := by simp

lemma law_le_one (μ : Law ι) (i : ι) : μ i ≤ 1 := by
  rw [← μ.total]
  exact single_le_sum (fun j _ => μ.nonneg j) (mem_univ i)

def move (μ : Law ι) (P : ι → Law κ) : Law κ where
  mass j := ∑ i, μ i*P i j
  nonneg j := sum_nonneg fun i _ => mul_nonneg (μ.nonneg i) ((P i).nonneg j)
  total := by
    rw [sum_comm]
    simp_rw [← mul_sum,(P _).total,mul_one]
    exact μ.total

lemma move_apply (μ : Law ι) (P : ι → Law κ) (j : κ) :
    move μ P j = ∑ i, μ i*P i j := rfl

def l1dist (a b : ι → ℝ) : ℝ := ∑ i, |a i-b i|
lemma l1dist_nonneg (a b : ι → ℝ) : 0 ≤ l1dist a b := sum_nonneg (fun _ _ => abs_nonneg _)
lemma l1dist_triangle (a b c : ι → ℝ) : l1dist a c ≤ l1dist a b+l1dist b c := by
  unfold l1dist
  rw [← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

/-- Stochastic matrices contract the l1 norm of every signed row difference. -/
theorem move_contract (μ ν : Law ι) (P : ι → Law κ) :
    l1dist (move μ P) (move ν P) ≤ l1dist μ ν := by
  unfold l1dist
  calc
    _ = ∑ j, |∑ i, (μ i-ν i)*P i j| := by
      apply sum_congr rfl
      intro j _
      congr 1
      simp only [move_apply,sub_mul,sum_sub_distrib]
    _ ≤ ∑ j, ∑ i, |μ i-ν i| *P i j := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i, |(μ i-ν i)*P i j| := abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul,abs_of_nonneg ((P _).nonneg _)]
    _ = _ := by
      rw [sum_comm]
      simp_rw [← mul_sum,(P _).total,mul_one]

lemma move_rows (μ : Law ι) (P Q : ι → Law κ) :
    l1dist (move μ P) (move μ Q) ≤ ∑ i, μ i*l1dist (P i) (Q i) := by
  unfold l1dist
  calc
    _ = ∑ j, |∑ i, μ i*(P i j-Q i j)| := by
      apply sum_congr rfl
      intro j _
      congr 1
      simp only [move_apply,mul_sub,sum_sub_distrib]
    _ ≤ ∑ j, ∑ i, μ i*|P i j-Q i j| := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i, |μ i*(P i j-Q i j)| := abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul,abs_of_nonneg (μ.nonneg _)]
    _ = _ := by rw [sum_comm]; simp_rw [mul_sum]

lemma move_compare (μ ν : Law ι) (P Q : ι → Law κ) :
    l1dist (move μ P) (move ν Q) ≤ l1dist μ ν+∑ i, ν i*l1dist (P i) (Q i) := by
  exact (l1dist_triangle _ (move ν P) _).trans (add_le_add (move_contract μ ν P) (move_rows ν P Q))

lemma expectation_difference (μ ν : Law ι) {a : ι → ℝ} {C : ℝ}
    (ha : ∀ i, |a i| ≤ C) :
    |(∑ i, μ i*a i)-(∑ i, ν i*a i)| ≤ C*l1dist μ ν := by
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ i, |(μ i-ν i)*a i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C*|μ i-ν i| := sum_le_sum fun i _ => by
      rw [abs_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (ha i) (abs_nonneg _)
    _ = _ := by rw [← mul_sum]; rfl

def switchRow [DecidableEq ι] (old : ι) (sample : Law κ) (target : κ → ι)
    (p : κ → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) : Law ι where
  mass j := (1-∑ z, sample z*p z)*(delta old j)+∑ z, sample z*p z*(delta (target z) j)
  nonneg j := by
    apply add_nonneg
    · apply mul_nonneg _ ((delta old).nonneg j)
      apply sub_nonneg.mpr
      calc
        _ ≤ ∑ z, sample z*1 := sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hp1 z) (sample.nonneg z)
        _ = 1 := by simp only [mul_one]; exact sample.total
    · exact sum_nonneg fun z _ => mul_nonneg (mul_nonneg (sample.nonneg z) (hp0 z)) ((delta _).nonneg j)
  total := by
    rw [sum_add_distrib,← mul_sum,(delta old).total,sum_comm]
    simp_rw [← mul_sum,(delta _).total,mul_one]
    ring

lemma switchRow_formula [DecidableEq ι] (old : ι) (sample : Law κ) (target : κ → ι)
    (p : κ → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (j : ι) :
    switchRow old sample target p hp0 hp1 j =
      delta old j+∑ z, sample z*p z*(delta (target z) j-delta old j) := by
  change (_-_) * _ + _ = _
  simp only [mul_sub,sum_sub_distrib,← sum_mul]
  ring

lemma delta_distance [DecidableEq ι] (i j : ι) : l1dist (delta i) (delta j) ≤ 2 := by
  unfold l1dist
  calc
    _ ≤ ∑ k, (delta i k+delta j k) := sum_le_sum fun k _ => by
      exact abs_sub_le_iff.mpr ⟨by linarith [(delta j).nonneg k],by linarith [(delta i).nonneg k]⟩
    _ = 2 := by rw [sum_add_distrib,(delta i).total,(delta j).total]; norm_num

/-- The row difference is paid by the actual switched mass, not by a bare
Lipschitz constant. This is essential to the spatial comparison argument. -/
theorem switchRow_distance [DecidableEq ι] (old : ι) (sample sample' : Law κ)
    (target : κ → ι) (p : κ → ℝ) (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) :
    l1dist (switchRow old sample target p hp0 hp1) (switchRow old sample' target p hp0 hp1)
      ≤ 2*∑ z, |sample z-sample' z| *p z := by
  unfold l1dist
  simp_rw [switchRow_formula,add_sub_add_left_eq_sub,← sum_sub_distrib]
  calc
    _ = ∑ j, |∑ z, (sample z-sample' z)*p z*(delta (target z) j-delta old j)| := by
      apply sum_congr rfl
      intro j _
      congr 1
      apply sum_congr rfl
      intro z _
      ring
    _ ≤ ∑ j, ∑ z, |sample z-sample' z| *p z*|delta (target z) j-delta old j| := by
      apply sum_le_sum
      intro j _
      calc
        _ ≤ ∑ z, |(sample z-sample' z)*p z*(delta (target z) j-delta old j)| := abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul,abs_of_nonneg (hp0 _)]
    _ = ∑ z, (|sample z-sample' z| *p z)*l1dist (delta (target z)) (delta old) := by
      rw [sum_comm]
      simp only [l1dist,mul_sum]
    _ ≤ ∑ z, (|sample z-sample' z| *p z)*2 := sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (delta_distance _ _) (mul_nonneg (abs_nonneg _) (hp0 z))
    _ = _ := by rw [← sum_mul,mul_comm]

end FiniteLabels

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace PlanePotential

def greenScalar (ψ : ℂ → ℝ) (x y : ℂ) : ℝ :=
  ∫ t in Ioc (0:ℝ) 1, ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)
def green (ψ : ℂ → ℝ) (x y : ℂ) : ℂ := -greenScalar ψ x y • (y-x)

lemma segment_support {ψ : ℂ → ℝ} {R X : ℝ}
    (hψ : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ X)
    {t : ℝ} (ht : 0 < t) (hn : ψ (x+t⁻¹ • (y-x)) ≠ 0) :
    ‖y-x‖ ≤ t*(R+X) := by
  have heq : y-x = t • ((x+t⁻¹ • (y-x))-x) := by
    simp [ht.ne']
  calc
    ‖y-x‖ = t*‖(x+t⁻¹ • (y-x))-x‖ := by
      conv_lhs => rw [heq]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    _ ≤ t*(‖x+t⁻¹ • (y-x)‖+‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht.le
    _ ≤ t*(R+X) := mul_le_mul_of_nonneg_left (add_le_add (hψ _ hn) hx) ht.le

lemma integrable_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    Integrable ((Ioi δ).indicator (fun t : ℝ => B*t^q)) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  exact (integrableOn_Ioi_rpow_of_lt hq hδ).const_mul B

lemma integral_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    (∫ t : ℝ, (Ioi δ).indicator (fun t : ℝ => B*t^q) t) = B*(-δ^(q+1)/(q+1)) := by
  rw [integral_indicator measurableSet_Ioi,integral_const_mul,integral_Ioi_rpow_of_lt hq hδ]

/-- A singular segment integral is genuinely integrable because of its geometric
lower cutoff. The bound retains the exact power, rather than a supremum times 1. -/
lemma singular_integral_bound {F : ℝ → ℝ} (hFm : Measurable F)
    {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → F t = 0)
    (hbound : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ B*t^q) :
    IntegrableOn F (Ioc (0:ℝ) 1) ∧
      |∫ t in Ioc (0:ℝ) 1, F t| ≤ B*(-(δ/2)^(q+1)/(q+1)) := by
  let H := (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q)
  have hH : Integrable H := integrable_power_cutoff hq (by linarith)
  have hH0 (t : ℝ) : 0 ≤ H t := by
    unfold H
    apply indicator_nonneg
    intro t ht
    exact mul_nonneg hB (Real.rpow_nonneg (by change δ/2 < t at ht; linarith) _)
  have hle : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ H t := by
    intro t ht
    by_cases hd : t < δ
    · rw [hzero t ht hd]
      simpa only [abs_zero] using hH0 t
    · have htδ : t ∈ Ioi (δ/2) := by change δ/2 < t; linarith
      change |F t| ≤ (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q) t
      rw [indicator_of_mem htδ]
      exact hbound t ht
  have hFi : IntegrableOn F (Ioc (0:ℝ) 1) := by
    apply hH.integrableOn.mono' hFm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hle t ht
  refine ⟨hFi,?_⟩
  calc
    _ ≤ ∫ t in Ioc (0:ℝ) 1, |F t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioc (0:ℝ) 1, H t := integral_mono_ae hFi.abs hH.integrableOn (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hle t ht)
    _ ≤ ∫ t, H t := integral_mono_measure Measure.restrict_le_self (ae_of_all _ hH0) hH
    _ = _ := integral_power_cutoff hq (by linarith)

lemma greenScalar_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => greenScalar ψ p.1 p.2) := by
  unfold greenScalar
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  have harg : Measurable (fun p : (ℂ × ℂ) × ℝ => p.1.1+p.2⁻¹ • (p.1.2-p.1.1)) := by measurability
  exact ((hψ.comp harg).mul (measurable_snd.pow_const _)).stronglyMeasurable

lemma green_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => green ψ p.1 p.2) := by
  exact (greenScalar_measurable ψ hψ).neg.smul (measurable_snd.sub measurable_fst)

/-- Quantitative kernel size on every observation ball, with an explicit constant. -/
theorem green_norm_bound {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) (hxy : y ≠ x) :
    ‖green ψ x y‖ ≤ 2*B*(R+X)^2/‖y-x‖ := by
  have hd : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let δ := ‖y-x‖/(R+X)
  have hδ : 0 < δ := div_pos hd hM
  have hFm : Measurable (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) := by
    apply Measurable.mul
    · apply hψm.comp
      measurability
    · exact measurable_id.pow_const _
  have hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ) = 0 := by
    intro t ht hlt
    have hψ0 : ψ (x+t⁻¹ • (y-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have : t*(R+X) < ‖y-x‖ := (lt_div_iff₀ hM).mp hlt
      linarith
    rw [hψ0,zero_mul]
  have hb : ∀ t ∈ Ioc (0:ℝ) 1,
      |ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)| ≤ B*t^(-3:ℝ) := by
    intro t ht
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hψB _) (Real.rpow_nonneg ht.1.le _)
  have h := (singular_integral_bound hFm (by norm_num : (-3:ℝ) < -1) hδ hB hzero hb).2
  change |greenScalar ψ x y| ≤ _ at h
  have hrpow : (δ/2)^((-3:ℝ)+1) = (δ/2)^(-2:ℤ) := by norm_num [Real.rpow_intCast]
  rw [hrpow,zpow_neg,zpow_ofNat] at h
  have hs : |greenScalar ψ x y| ≤ 2*B*(R+X)^2/‖y-x‖^2 := by
    convert h using 1
    dsimp [δ]
    field_simp
    ring
  rw [green,norm_smul,Real.norm_eq_abs,abs_neg]
  calc
    _ ≤ (2*B*(R+X)^2/‖y-x‖^2)*‖y-x‖ := mul_le_mul_of_nonneg_right hs hd.le
    _ = _ := by field_simp

lemma segment_integrand_measurable {ψ : ℂ → ℝ} (hψ : Measurable ψ) (x y : ℂ) :
    Measurable (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) := by
  apply Measurable.mul
  · apply hψ.comp
    measurability
  · exact measurable_id.pow_const _

lemma scalar_data {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B δ : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hδ : 0 < δ)
    {x y : ℂ} (hx : ‖x‖ ≤ X) (hd : δ*(R+X) ≤ ‖y-x‖) :
    IntegrableOn (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) (Ioc (0:ℝ) 1) ∧
      |greenScalar ψ x y| ≤ 2*B/δ^2 := by
  have hz : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ) = 0 := by
    intro t ht hlt
    have : ψ (x+t⁻¹ • (y-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have := mul_lt_mul_of_pos_right hlt hM
      linarith
    rw [this,zero_mul]
  have hb : ∀ t ∈ Ioc (0:ℝ) 1,
      |ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)| ≤ B*t^(-3:ℝ) := by
    intro t ht
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hψB _) (Real.rpow_nonneg ht.1.le _)
  obtain ⟨hi,h⟩ := singular_integral_bound (segment_integrand_measurable hψm x y)
    (by norm_num : (-3:ℝ) < -1) hδ hB hz hb
  refine ⟨hi, h.trans_eq ?_⟩
  rw [show (-3:ℝ)+1 = -2 by norm_num, show (δ/2)^(-2:ℝ) = (δ/2)^(-2:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
  norm_num
  field_simp

/-- A difference bound proves the needed cancellation estimate without hiding
any differentiation under the singular integral. -/
theorem green_difference_bound {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B L : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hψL : ∀ u v, |ψ u-ψ v| ≤ L*‖u-v‖)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hL : 0 ≤ L)
    {x y z : ℂ} (hx : ‖x‖ ≤ X) (hzx : z ≠ x) (hyz : ‖y-z‖ ≤ ‖z-x‖/2) :
    ‖green ψ x y-green ψ x z‖ ≤
      (8*B*(R+X)^2+(64/3:ℝ)*L*(R+X)^3)*‖y-z‖/‖z-x‖^2 := by
  let d := ‖z-x‖
  let a := ‖y-z‖
  let M := R+X
  let δ := d/(2*M)
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  have ha : 0 ≤ a := norm_nonneg _
  have hδ : 0 < δ := div_pos hd (mul_pos (by norm_num) hM)
  have hnear : d/2 ≤ ‖y-x‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z y x
    rw [norm_sub_rev z y] at ht
    dsimp [d] at *
    linarith
  have hcut : δ*M = d/2 := by dsimp [δ]; field_simp [show M ≠ 0 from hM.ne']
  have hdy : δ*(R+X) ≤ ‖y-x‖ := by change δ*M ≤ _; rw [hcut]; exact hnear
  have hdz : δ*(R+X) ≤ ‖z-x‖ := by change δ*M ≤ d; rw [hcut]; linarith
  obtain ⟨hIy,hKy⟩ := scalar_data hψm hψs hψB hM hB hδ hx hdy
  obtain ⟨hIz,_⟩ := scalar_data hψm hψs hψB hM hB hδ hx hdz
  let F := fun t : ℝ => (ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ)
  have hFm : Measurable F := by
    change Measurable (fun t : ℝ => _)
    have hm (v : ℂ) : Measurable (fun t : ℝ => ψ (x+t⁻¹ • (v-x))) := by
      apply hψm.comp
      measurability
    exact ((hm y).sub (hm z)).mul (measurable_id.pow_const _)
  have hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → F t = 0 := by
    intro t ht htδ
    have h0 (v : ℂ) (hv : δ*M ≤ ‖v-x‖) : ψ (x+t⁻¹ • (v-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have := mul_lt_mul_of_pos_right htδ hM
      dsimp [M] at hv
      linarith
    change (ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ) = 0
    rw [h0 y hdy,h0 z hdz,sub_self,zero_mul]
  have hbound : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ (L*a)*t^(-4:ℝ) := by
    intro t ht
    have harg : (x+t⁻¹ • (y-x))-(x+t⁻¹ • (z-x)) = t⁻¹ • (y-z) := by module
    have hLip := hψL (x+t⁻¹ • (y-x)) (x+t⁻¹ • (z-x))
    rw [harg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht.1)] at hLip
    calc
      |F t| = |ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x))| *t^(-3:ℝ) := by
        change |(ψ (x+t⁻¹ • (y-x))-ψ (x+t⁻¹ • (z-x)))*t^(-3:ℝ)| = _
        rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      _ ≤ (L*(t⁻¹*a))*t^(-3:ℝ) := mul_le_mul_of_nonneg_right hLip (Real.rpow_nonneg ht.1.le _)
      _ = (L*a)*t^(-4:ℝ) := by
        rw [← Real.rpow_neg_one t]
        calc
          _ = (L*a)*(t^(-1:ℝ)*t^(-3:ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add ht.1]; norm_num
  have hdiff := (singular_integral_bound hFm (by norm_num : (-4:ℝ) < -1)
    hδ (mul_nonneg hL ha) hzero hbound).2
  have hIF : (∫ t in Ioc (0:ℝ) 1, F t) = greenScalar ψ x y-greenScalar ψ x z := by
    simp only [F,sub_mul,greenScalar]
    exact integral_sub hIy hIz
  rw [hIF] at hdiff
  have hKd : |greenScalar ψ x y-greenScalar ψ x z| ≤ (64/3:ℝ)*L*a*M^3/d^3 := by
    refine hdiff.trans_eq ?_
    rw [show (-4:ℝ)+1 = -3 by norm_num, show (δ/2)^(-3:ℝ) = (δ/2)^(-3:ℤ) by norm_num [Real.rpow_intCast],zpow_neg,zpow_ofNat]
    dsimp [δ]
    field_simp
    ring
  have hKy' : |greenScalar ψ x y| ≤ 8*B*M^2/d^2 := by
    refine hKy.trans_eq ?_
    dsimp [δ]
    field_simp
    ring
  have heq : green ψ x y-green ψ x z =
      (-greenScalar ψ x y) • (y-z) - (greenScalar ψ x y-greenScalar ψ x z) • (z-x) := by
    unfold green
    module
  rw [heq]
  calc
    _ ≤ ‖(-greenScalar ψ x y) • (y-z)‖ +
        ‖(greenScalar ψ x y-greenScalar ψ x z) • (z-x)‖ := norm_sub_le _ _
    _ = |greenScalar ψ x y| *a + |greenScalar ψ x y-greenScalar ψ x z| *d := by
      simp only [norm_smul,Real.norm_eq_abs,abs_neg,a,d]
    _ ≤ (8*B*M^2/d^2)*a + ((64/3:ℝ)*L*a*M^3/d^3)*d :=
      add_le_add (mul_le_mul_of_nonneg_right hKy' ha) (mul_le_mul_of_nonneg_right hKd hd.le)
    _ = _ := by change _ = (8*B*M^2+(64/3:ℝ)*L*M^3)*a/d^2; field_simp

end PlanePotential

end SignedDisk

end

end OAI
