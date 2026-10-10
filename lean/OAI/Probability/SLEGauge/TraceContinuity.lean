import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadialMoments

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
noncomputable section
open Set Filter Real
open scoped Topology
open Set MeasureTheory ProbabilityTheory Topology Function Filter
open scoped NNReal ENNReal ContinuousMapZero
noncomputable section
namespace SLEExactGauge.LiteralTrace
theorem inverseFlow_time_modulus {κ s t T y : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) (hy : 0 < y) (hy1 : y ≤ 1)
    (hΔ : t-s ≤ y^2) (b : Driver) :
    ‖inverseFlow κ b t (driverValue b t+y*Complex.I)-
        inverseFlow κ b s (driverValue b s+y*Complex.I)‖ ≤
      (2*(2+a κ+2*a κ*T)/y)*(|driverValue b t-driverValue b s|+a κ*(t-s)/y) := by
  let z := inverseFlow κ b t (driverValue b t+y*Complex.I)
  have ht : 0 ≤ t := hs.trans hst
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hw : 0 < ((driverValue b t:ℂ)+y*Complex.I).im := by simpa using hy
  have hf := surviving_flow_positiveSolution ht (inverseFlow_surviving hκ b ht hw)
  change PositiveSolution κ b z t (flow κ b z) at hf
  let v := flow κ b z s
  have hfT : flow κ b z t = (driverValue b t:ℂ)+y*Complex.I := flow_inverseFlow hκ b ht hw
  have his : s ∈ Icc 0 t := ⟨hs,hst⟩
  have hit : t ∈ Icc 0 t := ⟨ht,le_rfl⟩
  have hvis : y ≤ v.im := by simpa only [hfT,v,Complex.add_im,Complex.ofReal_im,Complex.ofReal_re,
    Complex.mul_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero] using hf.im_antitone hκ his hit hst
  have hdist : ‖v-((driverValue b t:ℂ)+y*Complex.I)‖ ≤ a κ*(t-s)/y := by
    have hh := hf.displacement_le hκ his hit hst
    rw [hfT] at hh
    simpa only [v,norm_sub_rev,Complex.add_im,Complex.ofReal_im,Complex.ofReal_re,Complex.mul_im,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero,div_mul_eq_mul_div] using hh
  have hsmall : a κ*(t-s)/y ≤ a κ*y := by
    apply (div_le_iff₀ hy).mpr
    nlinarith [mul_le_mul_of_nonneg_left hΔ ha.le]
  have hiv : v.im ≤ 1+a κ := by
    have hh := Complex.im_le_norm (v-((driverValue b t:ℂ)+y*Complex.I))
    simp only [Complex.sub_im,Complex.add_im,Complex.ofReal_im,Complex.ofReal_re,Complex.mul_im,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero] at hh
    nlinarith [mul_le_mul_of_nonneg_left hy1 ha.le]
  have hvmap : inverseFlow κ b s v = z := inverseFlow_flow hs (hf.restrict hs hst).surviving
  have hh := inverseFlow_lipschitz_strip hκ hs (hst.trans htT) hy b
    (v := v) (w := (driverValue b s:ℂ)+y*Complex.I) ⟨hvis,hiv⟩
    (by simp only [Complex.add_im,Complex.ofReal_im,Complex.ofReal_re,Complex.mul_im,Complex.I_im,
          Complex.I_re,mul_one,mul_zero,zero_add,add_zero]; exact ⟨le_rfl,by linarith⟩)
  have hinput : ‖v-((driverValue b s:ℂ)+y*Complex.I)‖ ≤
      |driverValue b t-driverValue b s|+a κ*(t-s)/y := by
    calc
      _ ≤ ‖v-((driverValue b t:ℂ)+y*Complex.I)‖+
          ‖((driverValue b t:ℂ)+y*Complex.I)-((driverValue b s:ℂ)+y*Complex.I)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        rw [add_sub_add_right_eq_sub,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
        linarith
  rw [hvmap] at hh
  have hT0 : 0 ≤ T := ht.trans htT
  calc
    _ ≤ (2*(1+a κ+2*a κ*T+1)/y)*‖v-((driverValue b s:ℂ)+y*Complex.I)‖ := hh
    _ ≤ (2*(1+a κ+2*a κ*T+1)/y)*(|driverValue b t-driverValue b s|+a κ*(t-s)/y) :=
      mul_le_mul_of_nonneg_left hinput (by positivity)
    _ = _ := by ring
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.BrownianCalculus

def gaussianMoment (n : ℕ) : ℝ := ∫ x : ℝ, |x|^n ∂gaussianReal 0 1

lemma gaussianMoment_nonneg (n : ℕ) : 0 ≤ gaussianMoment n :=
  integral_nonneg (fun _ => by positivity)

lemma gaussian_abs_pow_integrable (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => |x|^n) (gaussianReal 0 v) := by
  simpa only [id_eq,Real.norm_eq_abs] using
    (memLp_id_gaussianReal' (μ := 0) (v := v) (n:ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma gaussian_abs_pow_scaled (σ : ℝ≥0) (n : ℕ) :
    (∫ x : ℝ, |x|^n ∂gaussianReal 0 (σ^2)) = (σ:ℝ)^n*gaussianMoment n := by
  have he : (gaussianReal 0 1).map (fun x : ℝ => (σ:ℝ)*x) =
      gaussianReal 0 (σ^2) := by
    convert gaussianReal_map_const_mul (μ := 0) (v := 1) (σ:ℝ) using 1; simp
    congr 1
  rw [← he,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul,abs_of_nonneg σ.coe_nonneg,mul_pow]
  exact integral_const_mul _ _

lemma increment_abs_pow_scaled {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s σ : ℝ≥0) (n : ℕ) :
    (∫ b, |increment s (σ^2) b|^n ∂W) = (σ:ℝ)^n*gaussianMoment n := by
  exact ((increment_law hW s (σ^2)).integral_comp (by fun_prop)).trans
    (gaussian_abs_pow_scaled σ n)

lemma increment_abs_pow_integrable {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s h : ℝ≥0) (n : ℕ) : Integrable (fun b => |increment s h b|^n) W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hm := (increment_law hW s h).hasGaussianLaw.memLp (p := (n : ℝ≥0∞)) (by simp)
  simpa only [Real.norm_eq_abs] using hm.integrable_norm_pow'

lemma increment_scaled_tail {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (s σ : ℝ≥0) (hσ : 0 < σ) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    W {b : Driver | (σ:ℝ)*r ≤ |increment s (σ^2) b|} ≤
      ENNReal.ofReal (gaussianMoment n/r^n) := by
  have hsr : 0 < ((σ:ℝ)*r)^n := pow_pos (mul_pos (by exact_mod_cast hσ) hr) _
  calc
    _ ≤ W {b : Driver | ENNReal.ofReal (((σ:ℝ)*r)^n) ≤
        ENNReal.ofReal (|increment s (σ^2) b|^n)} := by
      apply measure_mono
      intro b hb
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hb _)
    _ ≤ (∫⁻ b : Driver, ENNReal.ofReal (|increment s (σ^2) b|^n) ∂W)/
        ENNReal.ofReal (((σ:ℝ)*r)^n) :=
      meas_ge_le_lintegral_div (((measurable_increment s (σ^2)).abs.pow_const n).ennreal_ofReal.aemeasurable) (ne_of_gt (ENNReal.ofReal_pos.mpr hsr)) ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (((σ:ℝ)^n*gaussianMoment n)/(((σ:ℝ)*r)^n)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (increment_abs_pow_integrable hW s (σ^2) n)
        (ae_of_all _ (fun _ => by positivity)),increment_abs_pow_scaled hW,
        ← ENNReal.ofReal_div_of_pos hsr]
    _ = _ := by
      congr 1
      rw [mul_pow]
      field_simp
end SLEExactGauge.BrownianCalculus
namespace SLEExactGauge.BrownianCalculus

def modulusBase (K : ℕ) : ℕ := 2^(2*K)
def modulusStd (K n : ℕ) : ℝ≥0 := ((1/2:ℝ≥0)^K)^n
def modulusRate (K : ℕ) : ℝ := 2*(1/2:ℝ)^K

def modulusGridBad (K M n : ℕ) : Set Driver :=
  ⋃ k : Fin (M*(modulusBase K)^n), {b : Driver |
    (modulusRate K)^n ≤ |increment ((k:ℝ≥0)*(modulusStd K n)^2) ((modulusStd K n)^2) b|}

lemma modulus_grid_measure {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (K M n : ℕ) : W (modulusGridBad K M n) ≤
      ENNReal.ofReal (((M:ℝ)*gaussianMoment (2*K+1))*(1/2:ℝ)^n) := by
  have hs : 0 < modulusStd K n := by unfold modulusStd; positivity
  have he : (modulusRate K)^n = (modulusStd K n:ℝ)*(2:ℝ)^n := by
    simp only [modulusRate,modulusStd,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,mul_pow]
    ring
  calc
    _ ≤ ∑ k : Fin (M*(modulusBase K)^n), W {b : Driver |
      (modulusRate K)^n ≤ |increment ((k:ℝ≥0)*(modulusStd K n)^2) ((modulusStd K n)^2) b|} :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin (M*(modulusBase K)^n), ENNReal.ofReal (gaussianMoment (2*K+1)/((2:ℝ)^n)^(2*K+1)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [he]
      exact increment_scaled_tail hW _ _ hs (by positivity) _
    _ = ENNReal.ofReal (((M*(modulusBase K)^n:ℕ):ℝ)*
        (gaussianMoment (2*K+1)/((2:ℝ)^n)^(2*K+1))) := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = _ := by
      congr 1
      simp only [modulusBase,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [← pow_mul,← pow_mul,show n*(2*K+1) = (2*K)*n+n by ring,pow_add]
      field_simp
      rw [mul_assoc,← mul_pow]
      norm_num

lemma modulus_grid_eventually {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (K M : ℕ) :
    ∀ᵐ b ∂W, ∀ᶠ n : ℕ in atTop, ∀ k : Fin (M*(modulusBase K)^n),
      |increment ((k:ℝ≥0)*(modulusStd K n)^2) ((modulusStd K n)^2) b| < (modulusRate K)^n := by
  have hs : (∑' n : ℕ, W (modulusGridBad K M n)) ≠ (∞:ℝ≥0∞) := by
    apply ne_top_of_le_ne_top
      (((summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)).mul_left
        ((M:ℝ)*gaussianMoment (2*K+1))).tsum_ofReal_ne_top)
    exact ENNReal.tsum_le_tsum (modulus_grid_measure hW K M)
  filter_upwards [ae_eventually_notMem hs] with b hb
  filter_upwards [hb] with n hn
  intro k
  exact lt_of_not_ge (fun h => hn (mem_iUnion.mpr ⟨k,h⟩))

lemma modulus_std_square (K n : ℕ) :
    ((modulusStd K n:ℝ≥0):ℝ)^2 = 1/(modulusBase K:ℝ)^n := by
  simp only [modulusStd,modulusBase,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
    NNReal.coe_ofNat,Nat.cast_pow,Nat.cast_ofNat,div_pow,one_pow]
  rw [← pow_mul,← pow_mul,← pow_mul]
  congr 2
  ring

lemma modulus_rate_pos (K : ℕ) : 0 < modulusRate K := by
  unfold modulusRate; positivity

lemma modulus_rate_lt_one {K : ℕ} (hK : 2 ≤ K) : modulusRate K < 1 := by
  have hh : (1/2:ℝ)^K ≤ (1/2:ℝ)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
  dsimp [modulusRate]
  linarith

end SLEExactGauge.BrownianCalculus

 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace SLEExactGauge.TraceChaining

def grid (q n k : ℕ) : ℝ := (k:ℝ)/(q:ℝ)^n

def index (q n : ℕ) (t : ℝ) : ℕ := ⌊(q:ℝ)^n*t⌋₊

def approx (q n : ℕ) (t : ℝ) : ℝ := grid q n (index q n t)

lemma approx_bounds {q : ℕ} (hq : 0 < q) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ approx q n t ∧ approx q n t ≤ t ∧ t < approx q n t+1/(q:ℝ)^n := by
  have hp : 0 < (q:ℝ)^n := pow_pos (by exact_mod_cast hq) _
  refine ⟨by unfold approx grid; positivity,?_,?_⟩
  · exact (div_le_iff₀ hp).mpr (by
      simpa only [index,mul_comm] using Nat.floor_le (mul_nonneg hp.le ht))
  · have hh := Nat.lt_floor_add_one ((q:ℝ)^n*t)
    dsimp [approx,grid,index]
    rw [← add_div]
    exact (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)

lemma approx_tendsto {q : ℕ} (hq : 1 < q) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => approx q n t) atTop (𝓝 t) := by
  have hqp : 0 < q := by omega
  have hqR : 1 < (q:ℝ) := by exact_mod_cast hq
  have hz : Tendsto (fun n : ℕ => 1/(q:ℝ)^n) atTop (𝓝 0) := by
    simpa only [one_div,inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : 0 ≤ (q:ℝ)⁻¹) ((inv_lt_one₀ (by positivity)).mpr hqR)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => t-1/(q:ℝ)^n) (h := fun _ => t)
    (by simpa using tendsto_const_nhds.sub hz) tendsto_const_nhds
    (fun n => by linarith [(approx_bounds hqp n ht).2.2])
    (fun n => (approx_bounds hqp n ht).2.1)

lemma index_le {q M n : ℕ} (_hq : 0 < q) {t : ℝ} (ht : t ≤ M) :
    index q n t ≤ M*q^n := by
  apply Nat.floor_le_of_le
  simp only [Nat.cast_mul,Nat.cast_pow]
  nlinarith [pow_nonneg (Nat.cast_nonneg q : (0:ℝ) ≤ q) n]

lemma index_refine {q n : ℕ} (hq : 0 < q) (t : ℝ) :
    index q (n+1) t / q = index q n t := by
  unfold index
  rw [pow_succ,mul_right_comm _ _ t,Nat.mul_cast_floor_div_cancel (by omega)]

lemma grid_refine {q : ℕ} (hq : 0 < q) (n k : ℕ) :
    grid q (n+1) (q*k) = grid q n k := by
  unfold grid
  push_cast
  rw [pow_succ]
  field_simp

lemma grid_distance_le {E : Type*} [PseudoMetricSpace E] (f : ℝ → E)
    (q n L : ℕ) {c : ℝ} (_hc : 0 ≤ c)
    (hb : ∀ k < L, dist (f (grid q n k)) (f (grid q n (k+1))) ≤ c)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) :
    dist (f (grid q n i)) (f (grid q n j)) ≤ (j-i:ℕ)*c := by
  calc
    _ ≤ ∑ k ∈ Finset.Ico i j, c := dist_le_Ico_sum_of_dist_le (f := fun k => f (grid q n k)) hij
      (fun {k} _hk hk => hb k (hk.trans_le hj))
    _ = _ := by simp

lemma approx_step {E : Type*} [PseudoMetricSpace E] (f : ℝ → E)
    {q : ℕ} (hq : 0 < q) (M n : ℕ) {t : ℝ} (ht : t ≤ M)
    {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ k < M*q^(n+1), dist (f (grid q (n+1) k))
      (f (grid q (n+1) (k+1))) ≤ c) :
    dist (f (approx q n t)) (f (approx q (n+1) t)) ≤ (q:ℝ)*c := by
  have hi := index_refine (n := n) hq t
  have hlow : q*index q n t ≤ index q (n+1) t := by
    rw [← hi,mul_comm]
    exact Nat.div_mul_le_self _ _
  have hupp : index q (n+1) t - q*index q n t ≤ q := by
    have he := Nat.mod_add_div (index q (n+1) t) q
    have hm := Nat.mod_lt (index q (n+1) t) hq
    rw [hi] at he
    omega
  have h := grid_distance_le f q (n+1) (M*q^(n+1)) hc hb hlow (index_le hq ht)
  rw [grid_refine hq] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hupp) hc)

lemma approx_distance {E : Type*} [PseudoMetricSpace E] (f : ℝ → E)
    (hf : Continuous f) {q : ℕ} (hq : 1 < q) (M n₀ : ℕ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hb : ∀ n, n₀ ≤ n → ∀ k < M*q^n,
      dist (f (grid q n k)) (f (grid q n (k+1))) ≤ ρ^n)
    {t : ℝ} (ht0 : 0 ≤ t) (htM : t ≤ M) {n : ℕ} (hn : n₀ ≤ n) :
    dist (f (approx q n t)) (f t) ≤ (q:ℝ)*ρ^(n+1)/(1-ρ) := by
  have hl := (hf.tendsto t).comp ((approx_tendsto hq ht0).comp (tendsto_add_atTop_nat n))
  have hs (j : ℕ) : dist (f (approx q (j+n) t)) (f (approx q (j+1+n) t)) ≤
      ((q:ℝ)*ρ^(n+1))*ρ^j := by
    have hh := approx_step f (by omega : 0 < q) M (j+n) htM
      (pow_nonneg hρ0 (j+n+1)) (hb (j+n+1) (by omega))
    rw [show j+1+n = j+n+1 by omega]
    simpa only [show j+n+1 = (n+1)+j by omega,pow_add,mul_assoc] using hh
  have hh := dist_le_of_le_geometric_of_tendsto₀ ρ ((q:ℝ)*ρ^(n+1)) hρ1 hs hl
  simpa only [Nat.zero_add] using hh

 

lemma grid_modulus {E : Type*} [PseudoMetricSpace E] (f : ℝ → E)
    (hf : Continuous f) {q : ℕ} (hq : 1 < q) (M n₀ : ℕ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hb : ∀ n, n₀ ≤ n → ∀ k < M*q^n,
      dist (f (grid q n k)) (f (grid q n (k+1))) ≤ ρ^n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ M) {n : ℕ} (hn : n₀ ≤ n)
    (hclose : t-s ≤ 1/(q:ℝ)^n) :
    dist (f s) (f t) ≤ (2+2*(q:ℝ)*ρ/(1-ρ))*ρ^n := by
  have hqp : 0 < q := by omega
  have hp : 0 < (q:ℝ)^n := pow_pos (by exact_mod_cast hqp) _
  have hi : index q n s ≤ index q n t :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hst hp.le)
  have hj : index q n t - index q n s ≤ 2 := by
    have h1 := Nat.floor_le (mul_nonneg hp.le (hs.trans hst))
    have h2 := Nat.lt_floor_add_one ((q:ℝ)^n*s)
    have h3 := (le_div_iff₀ hp).mp hclose
    have h4 : (index q n t:ℝ) < (index q n s:ℝ)+2 := by
      dsimp [index]
      nlinarith
    have h5 : index q n t < index q n s+2 := by exact_mod_cast h4
    omega
  have hg := grid_distance_le f q n (M*q^n) (pow_nonneg hρ0 n)
    (hb n hn) hi (index_le hqp ht)
  have hg' : dist (f (approx q n s)) (f (approx q n t)) ≤ 2*ρ^n :=
    hg.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (pow_nonneg hρ0 n))
  have hs' := approx_distance f hf hq M n₀ hρ0 hρ1 hb hs (hst.trans ht) hn
  have ht' := approx_distance f hf hq M n₀ hρ0 hρ1 hb (hs.trans hst) ht hn
  calc
    _ ≤ dist (f s) (f (approx q n s)) + dist (f (approx q n s)) (f (approx q n t)) +
        dist (f (approx q n t)) (f t) := dist_triangle4 _ _ _ _
    _ ≤ (q:ℝ)*ρ^(n+1)/(1-ρ)+2*ρ^n+(q:ℝ)*ρ^(n+1)/(1-ρ) := by
      rw [dist_comm (f s)]
      gcongr
    _ = _ := by rw [pow_succ]; ring
end SLEExactGauge.TraceChaining
namespace SLEExactGauge.BrownianCalculus
open SLEExactGauge.TraceChaining

lemma increment_grid_eq (K n k : ℕ) (b : Driver) :
    increment ((k:ℝ≥0)*(modulusStd K n)^2) ((modulusStd K n)^2) b =
      b ((grid (modulusBase K) n (k+1)).toNNReal)-
        b ((grid (modulusBase K) n k).toNNReal) := by
  have he (j : ℕ) : (grid (modulusBase K) n j).toNNReal =
      (j:ℝ≥0)*(modulusStd K n)^2 := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by unfold grid; positivity)]
    simp only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_pow,modulus_std_square,grid]
    ring
  rw [increment,he,he]
  congr 2
  push_cast
  ring

 

theorem brownian_uniform_modulus {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W) :
    ∀ᵐ b ∂W, ∀ K M : ℕ, 2 ≤ K → ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ M → t-s ≤ 1/(modulusBase K:ℝ)^n →
      |b t.toNNReal-b s.toNNReal| ≤
        (2+2*(modulusBase K:ℝ)*modulusRate K/(1-modulusRate K))*(modulusRate K)^n := by
  have hh := ae_all_iff.mpr (fun K => ae_all_iff.mpr (fun M => modulus_grid_eventually hW K M))
  filter_upwards [hh] with b hb
  intro K M hK
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (hb K M)
  refine ⟨n₀,?_⟩
  intro n hn s t hs hst ht hclose
  have hg (m : ℕ) (hm : n₀ ≤ m) (k : ℕ) (hk : k < M*(modulusBase K)^m) :
      dist (b ((grid (modulusBase K) m k).toNNReal))
        (b ((grid (modulusBase K) m (k+1)).toNNReal)) ≤ (modulusRate K)^m := by
    have hi := (hn₀ m hm ⟨k,hk⟩).le
    rw [increment_grid_eq] at hi
    simpa only [Real.dist_eq,abs_sub_comm] using hi
  have hq : 1 < modulusBase K := by
    dsimp [modulusBase]
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hu := grid_modulus (fun t : ℝ => b t.toNNReal)
    ((map_continuous b).comp continuous_real_toNNReal) hq M n₀
    (modulus_rate_pos K).le (modulus_rate_lt_one hK) hg hs hst ht hn hclose
  simpa only [Real.dist_eq,abs_sub_comm] using hu
end SLEExactGauge.BrownianCalculus
namespace SLEExactGauge.LiteralTrace

abbrev radialValue (κ : ℝ) (b : Driver) (t y : ℝ) : ℂ :=
  inverseFlow κ b t (driverValue b t+y*Complex.I)

lemma radial_increment_real {κ s y z R : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hz : 0 < z) (hzy : z ≤ y) (b : Driver)
    (hR : radialLength κ b s y ≤ ENNReal.ofReal R) (hR0 : 0 ≤ R) :
    ‖radialValue κ b s y-radialValue κ b s z‖ ≤ R := by
  exact (ENNReal.ofReal_le_ofReal_iff hR0).mp ((radial_increment_le hκ hs hz hzy b).trans hR)

lemma time_bound_below {κ s t T y v D : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) (hv : 0 < v) (hvy : v ≤ y) (hy1 : y ≤ 1)
    (hΔ : t-s ≤ v^2) (b : Driver) (hD : |driverValue b t-driverValue b s| ≤ D) :
    ‖radialValue κ b t y-radialValue κ b s y‖ ≤
      (2*(2+a κ+2*a κ*T)/v)*(D+a κ*(t-s)/v) := by
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hy := hv.trans_le hvy
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have ht : 0 ≤ t-s := sub_nonneg.mpr hst
  have hc : 0 ≤ 2*(2+a κ+2*a κ*T) := by positivity
  apply (inverseFlow_time_modulus hκ hs hst htT hy hy1
    (hΔ.trans (pow_le_pow_left₀ hv.le hvy 2)) b).trans
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left hc hv hvy
  · exact add_le_add hD (div_le_div_of_nonneg_left (mul_nonneg ha.le ht) hv hvy)
  · positivity
  · positivity

 

lemma radial_interpolation {κ s t T v y z D R : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s)
    (hst : s ≤ t) (htT : t ≤ T) (hv : 0 < v) (hvy : v ≤ y) (hyz : y ≤ z) (hz1 : z ≤ 1)
    (hΔ : t-s ≤ v^2) (b : Driver) (hD : |driverValue b t-driverValue b s| ≤ D)
    (hR : radialLength κ b s z ≤ ENNReal.ofReal R) (hR0 : 0 ≤ R) :
    ‖radialValue κ b t y-radialValue κ b t z‖ ≤
      2*((2*(2+a κ+2*a κ*T)/v)*(D+a κ*(t-s)/v))+R := by
  have h1 := time_bound_below hκ hs hst htT hv hvy (hyz.trans hz1) hΔ b hD
  have h2 := time_bound_below hκ hs hst htT hv (hvy.trans hyz) hz1 hΔ b hD
  have h3 := radial_increment_real hκ hs (hv.trans_le hvy) hyz b hR hR0
  have hh := dist_triangle4 (radialValue κ b t y) (radialValue κ b s y)
    (radialValue κ b s z) (radialValue κ b t z)
  simp only [dist_eq_norm] at hh
  rw [norm_sub_rev] at h2 h3
  linarith
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open BrownianCalculus

def traceRatio (N : ℕ) : ℝ := (1/2:ℝ)^(4*N)
def traceMeshBase (N : ℕ) : ℕ := modulusBase (4*N+2)
def brownianModulusConst (K : ℕ) : ℝ :=
  2+2*(modulusBase K:ℝ)*modulusRate K/(1-modulusRate K)

def traceError (κ : ℝ) (N H n : ℕ) : ℝ :=
  4*(2+a κ+2*a κ*H)*
    (brownianModulusConst (4*N+2)/traceRatio N*(1/2:ℝ)^n+
      a κ/(traceRatio N)^2*(1/16:ℝ)^n)+((traceRatio N)^(traceBeta κ))^n

end SLEExactGauge.LiteralTrace
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
