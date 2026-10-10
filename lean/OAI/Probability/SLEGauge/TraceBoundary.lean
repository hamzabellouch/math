import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.TraceContinuity

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
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace SLEExactGauge.LiteralTrace
open BrownianCalculus
lemma traceRatio_pos (N : ℕ) : 0 < traceRatio N := by unfold traceRatio; positivity

lemma traceRatio_lt_one {N : ℕ} (hN : 0 < N) : traceRatio N < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

lemma traceMeshBase_eq (N : ℕ) : traceMeshBase N = (2^(2*N+1))^4 := by
  unfold traceMeshBase modulusBase
  rw [← pow_mul]
  congr 1
  omega

lemma traceRate_eq (N : ℕ) : modulusRate (4*N+2) = traceRatio N/2 := by
  unfold modulusRate traceRatio
  rw [pow_add]
  norm_num
  ring

lemma traceMesh_inv (N : ℕ) : 1/(traceMeshBase N:ℝ) = (traceRatio N)^2/16 := by
  unfold traceMeshBase modulusBase traceRatio
  push_cast
  rw [← pow_mul,show 2*(4*N+2) = (4*N)*2+4 by omega,pow_add,div_pow,one_pow]
  norm_num
  ring

lemma traceHeight_eq (N n : ℕ) : refinedHeight N (4*n) = (traceRatio N)^n := by
  unfold refinedHeight traceRatio
  rw [← pow_mul,← pow_mul]
  congr 1
  ring

lemma traceGridTime_eq (δ : ℝ) (N n k : ℕ) :
    refinedGridTime δ N (4*n) k = δ+TraceChaining.grid (traceMeshBase N) n k := by
  unfold refinedGridTime TraceChaining.grid
  rw [traceMeshBase_eq]
  push_cast
  simp only [← pow_mul]
  congr 3; ring

lemma traceGridCard_eq (M N n : ℕ) :
    M*(2^(2*N+1))^(4*n) = M*(traceMeshBase N)^n := by
  rw [traceMeshBase_eq]
  simp only [← pow_mul]
  congr 2; ring

lemma traceRate_div (N n : ℕ) :
    (modulusRate (4*N+2))^n/(traceRatio N)^(n+1) =
      1/traceRatio N*(1/2:ℝ)^n := by
  rw [traceRate_eq,div_pow,pow_succ,div_pow,one_pow]
  field_simp [ne_of_gt (traceRatio_pos N)]

lemma traceMesh_div (N n : ℕ) :
    (1/(traceMeshBase N:ℝ)^n)/((traceRatio N)^(n+1))^2 =
      1/(traceRatio N)^2*(1/16:ℝ)^n := by
  rw [← one_div_pow,traceMesh_inv,div_pow,
    show (traceRatio N)^(n+1) = (traceRatio N)^n*traceRatio N by rfl,mul_pow,div_pow,one_pow]
  rw [pow_right_comm (traceRatio N) 2 n]
  field_simp [ne_of_gt (traceRatio_pos N)]

lemma traceMesh_eventually (N : ℕ) : ∀ᶠ n : ℕ in atTop,
    1/(traceMeshBase N:ℝ)^n ≤ ((traceRatio N)^(n+1))^2 := by
  have hh : Tendsto (fun n : ℕ => 1/(traceRatio N)^2*(1/16:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/16:ℝ))
      (by norm_num : (1/16:ℝ) < 1)).const_mul (1/(traceRatio N)^2)
  filter_upwards [hh.eventually (Iio_mem_nhds zero_lt_one)] with n hn
  rw [← traceMesh_div] at hn
  have hr := traceRatio_pos N
  exact ((div_lt_one (by positivity : 0 < ((traceRatio N)^(n+1))^2)).mp hn).le

lemma traceError_summable {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {N : ℕ} (hN : 0 < N) (H : ℕ) :
    Summable (traceError κ N H) := by
  have hp := trace_exponents hκ hκ8
  have hr : |(traceRatio N)^(traceBeta κ)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (traceRatio_pos N) _)]
    exact Real.rpow_lt_one (traceRatio_pos N).le (traceRatio_lt_one hN) hp.1
  have hs := (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)| < 1)).mul_left
    (brownianModulusConst (4*N+2)/traceRatio N)
  have ht := (summable_geometric_of_abs_lt_one (by norm_num : |(1/16:ℝ)| < 1)).mul_left
    (a κ/(traceRatio N)^2)
  have hu := (((hs.add ht).mul_left (4*(2+a κ+2*a κ*H))).add (summable_geometric_of_abs_lt_one hr))
  change Summable (fun n : ℕ => 4*(2+a κ+2*a κ*H)*
    (brownianModulusConst (4*N+2)/traceRatio N*(1/2:ℝ)^n+
      a κ/(traceRatio N)^2*(1/16:ℝ)^n)+((traceRatio N)^(traceBeta κ))^n)
  exact hu
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open BrownianCalculus TraceChaining

 

theorem radial_uniform_bands {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∃ N : ℕ, 0 < N ∧ ∀ᵐ b ∂W, ∀ m H : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, 1/((m:ℝ)+1) ≤ t → t ≤ H →
      ∀ y : ℝ, (traceRatio N)^(n+1) ≤ y → y ≤ (traceRatio N)^n →
      ‖radialValue κ b t y-radialValue κ b t ((traceRatio N)^n)‖ ≤
        traceError κ N H n := by
  obtain ⟨N,hN,hNeta,hgrid⟩ := radial_length_all_refined_grids hκ hκ8 hW
  refine ⟨N,hN,?_⟩
  filter_upwards [hgrid,brownian_uniform_modulus hW] with b hb hB
  intro m H
  let δ : ℝ := 1/((m:ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hr := traceRatio_pos N
  have hr1 := traceRatio_lt_one hN
  have hq : 0 < traceMeshBase N := by unfold traceMeshBase modulusBase; positivity
  have hsub : Tendsto (fun n : ℕ => 4*n) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => by omega) tendsto_id
  have hg := hsub.eventually (hb m H)
  obtain ⟨n₀,hn₀⟩ := hB (4*N+2) H (by omega)
  filter_upwards [hg,traceMesh_eventually N,eventually_ge_atTop n₀] with n hn hmesh hn0
  intro t hδt htH y hvy hyz
  let k := index (traceMeshBase N) n (t-δ)
  let s := δ+approx (traceMeshBase N) n (t-δ)
  have hab := approx_bounds hq n (sub_nonneg.mpr hδt)
  have hs : 0 ≤ s := by dsimp [s]; linarith [hab.1]
  have hst : s ≤ t := by dsimp [s]; linarith [hab.2.1]
  have hclose : t-s ≤ 1/(traceMeshBase N:ℝ)^n := by
    dsimp [s]; linarith [hab.2.2]
  have hk : k < H*(traceMeshBase N)^n := by
    have hp : 0 < (traceMeshBase N:ℝ)^n := pow_pos (by exact_mod_cast hq) _
    have hf := Nat.floor_le (mul_nonneg hp.le (sub_nonneg.mpr hδt))
    have hh : (k:ℝ) < (H:ℝ)*(traceMeshBase N:ℝ)^n := by
      dsimp [k,index]
      nlinarith
    exact_mod_cast hh
  have hgk := hn ⟨k,by rwa [traceGridCard_eq]⟩
  rw [traceGridTime_eq,traceHeight_eq] at hgk
  change radialLength κ b s ((traceRatio N)^n) < _ at hgk
  have hR : radialLength κ b s ((traceRatio N)^n) ≤
      ENNReal.ofReal (((traceRatio N)^(traceBeta κ))^n) := by
    have he : ((traceRatio N)^n)^(traceBeta κ) =
        ((traceRatio N)^(traceBeta κ))^n := by
      rw [← Real.rpow_natCast_mul hr.le,mul_comm (n:ℝ) (traceBeta κ),
        Real.rpow_mul_natCast hr.le]
    rw [he] at hgk
    exact hgk.le
  have hbnd := hn₀ n hn0 s t hs hst htH hclose
  change |driverValue b t-driverValue b s| ≤
    brownianModulusConst (4*N+2)*(modulusRate (4*N+2))^n at hbnd
  have hp := radial_interpolation hκ hs hst htH (pow_pos hr _) hvy hyz
    (pow_le_one₀ hr.le hr1.le) (hclose.trans hmesh) b hbnd hR (by positivity)
  have ha : 0 < a κ := div_pos (by norm_num) hκ
  have hc : 0 ≤ 2*(2+a κ+2*a κ*H)/(traceRatio N)^(n+1) := by positivity
  have hstep : a κ*(t-s)/(traceRatio N)^(n+1) ≤
      a κ*(1/(traceMeshBase N:ℝ)^n)/(traceRatio N)^(n+1) := by
    gcongr
  have hp' : ‖radialValue κ b t y-radialValue κ b t ((traceRatio N)^n)‖ ≤
      2*(2*(2+a κ+2*a κ*H)/(traceRatio N)^(n+1)*
        (brownianModulusConst (4*N+2)*(modulusRate (4*N+2))^n+
          a κ*(1/(traceMeshBase N:ℝ)^n)/(traceRatio N)^(n+1)))+
        ((traceRatio N)^(traceBeta κ))^n := by
    apply hp.trans
    gcongr
  apply hp'.trans_eq
  dsimp [traceError]
  rw [show 2*(2*(2+a κ+2*a κ*H)/(traceRatio N)^(n+1)*
      (brownianModulusConst (4*N+2)*(modulusRate (4*N+2))^n+
        a κ*(1/(traceMeshBase N:ℝ)^n)/(traceRatio N)^(n+1))) =
      4*(2+a κ+2*a κ*H)*
        (brownianModulusConst (4*N+2)*
          ((modulusRate (4*N+2))^n/(traceRatio N)^(n+1))+
          a κ*((1/(traceMeshBase N:ℝ)^n)/((traceRatio N)^(n+1))^2)) by ring]
  rw [traceRate_div,traceMesh_div]
  ring
end SLEExactGauge.LiteralTrace

 

noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.TraceChaining

lemma radial_limit_of_bands {E : Type*} [MetricSpace E] [CompleteSpace E]
    (f : ℝ → E) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {e : ℕ → ℝ} (he : Summable e)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, r^(n+1) ≤ y → y ≤ r^n →
      dist (f y) (f (r^n)) ≤ e n) :
    ∃ z : E, Tendsto f (𝓝[>] 0) (𝓝 z) := by
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hb
  have hs (n : ℕ) : dist (f (r^(n+n₀))) (f (r^((n+1)+n₀))) ≤ e (n+n₀) := by
    rw [dist_comm]
    exact hn₀ (n+n₀) (by omega) _ (by simp [Nat.add_assoc,Nat.add_comm])
      (by simpa only [show n+1+n₀ = (n+n₀)+1 by omega] using
        pow_le_pow_of_le_one hr.le hr1.le (Nat.le_succ (n+n₀)))
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable (fun n => e (n+n₀)) hs
      ((summable_nat_add_iff n₀).mpr he))
  have hz' : Tendsto (fun n : ℕ => f (r^n)) atTop (𝓝 z) :=
    (tendsto_add_atTop_iff_nat n₀).mp hz
  refine ⟨z,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  have hε2 : 0 < ε/2 := by linarith
  have hsmall := (he.tendsto_atTop_zero.eventually (Iio_mem_nhds hε2))
  have hnear := (Metric.tendsto_atTop.mp hz') (ε/2) hε2
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp hsmall
  obtain ⟨n₂,hn₂⟩ := hnear
  let n₃ := max n₀ (max n₁ n₂)
  have hv : 0 < r^(n₃+1) := pow_pos hr _
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ y : ℝ in 𝓝[>] 0, y < r^(n₃+1) from
      nhdsWithin_le_nhds (Iio_mem_nhds hv))] with y hy hyv
  have hy1 : y ≤ 1 := hyv.le.trans (pow_le_one₀ hr.le hr1.le)
  obtain ⟨n,hnlow,hnup⟩ := exists_nat_pow_near_of_lt_one hy hy1 hr hr1
  have hn3 : n₃ ≤ n := by
    by_contra hh
    have hnlt : n+1 ≤ n₃+1 := by omega
    have hlo := pow_le_pow_of_le_one hr.le hr1.le hnlt
    linarith
  have hband := hn₀ n (le_trans (le_max_left _ _) hn3) y hnlow.le hnup
  have hen := hn₁ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn3)
  have hzn := hn₂ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn3)
  exact (dist_triangle _ _ _).trans_lt (by linarith)
end SLEExactGauge.TraceChaining
namespace SLEExactGauge.TraceChaining

lemma radial_uniform_limit_of_bands {X E : Type*} [MetricSpace E] [CompleteSpace E]
    (f : X → ℝ → E) (g : X → E) (S : Set X)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {e : ℕ → ℝ} (he : Summable e)
    (hb : ∀ᶠ n : ℕ in atTop, ∀ t ∈ S, ∀ y : ℝ, r^(n+1) ≤ y → y ≤ r^n →
      dist (f t y) (f t (r^n)) ≤ e n)
    (hg : ∀ t ∈ S, Tendsto (f t) (𝓝[>] 0) (𝓝 (g t))) :
    TendstoUniformlyOn (fun n t => f t (r^n)) g atTop S := by
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hb
  have hgeom : Tendsto (fun n : ℕ => r^n) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1,
      Eventually.of_forall (fun n => pow_pos hr n)⟩
  have hd (n : ℕ) (hn : n₀ ≤ n) (t : X) (ht : t ∈ S) :
      dist (f t (r^n)) (g t) ≤ ∑' j : ℕ, e (j+n) := by
    have hstep (j : ℕ) : dist (f t (r^(j+n))) (f t (r^((j+1)+n))) ≤ e (j+n) := by
      rw [dist_comm]
      apply hn₀ (j+n) (by omega) t ht
      · simp [Nat.add_assoc,Nat.add_comm]
      · simpa only [show j+1+n = (j+n)+1 by omega] using
          pow_le_pow_of_le_one hr.le hr1.le (Nat.le_succ (j+n))
    have hh := dist_le_tsum_of_dist_le_of_tendsto₀ (fun j => e (j+n)) hstep
      ((summable_nat_add_iff n).mpr he)
      (((hg t ht).comp hgeom).comp (tendsto_add_atTop_nat n))
    simpa only [Nat.zero_add] using hh
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hh := (tendsto_sum_nat_add e).eventually (Iio_mem_nhds hε)
  filter_upwards [hh,eventually_ge_atTop n₀] with n hn hn0
  intro t ht
  rw [dist_comm]
  exact (hd n hn0 t ht).trans_lt hn
end SLEExactGauge.TraceChaining
namespace SLEExactGauge.LiteralTrace
open TraceChaining

 

theorem trace_limit_all_positive {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W, ∀ t : ℝ, 0 < t →
      Tendsto (fun y : ℝ => inverseFlow κ b (κ*t)
        (driverValue b (κ*t)+y*Complex.I)) (𝓝[>] 0) (𝓝 (trace κ b t)) := by
  obtain ⟨N,hN,hb⟩ := radial_uniform_bands hκ hκ8 hW
  filter_upwards [hb] with b hb
  intro t ht
  have hT : 0 < κ*t := mul_pos hκ ht
  obtain ⟨m,hm⟩ := exists_nat_gt (1/(κ*t))
  have hδ : 1/((m:ℝ)+1) ≤ κ*t := by
    have hmp : 0 < (m:ℝ)+1 := by positivity
    apply (div_le_iff₀ hmp).mpr
    have hh := (div_lt_iff₀ hT).mp hm
    nlinarith
  obtain ⟨H,hH⟩ := exists_nat_gt (κ*t)
  obtain ⟨z,hz⟩ := radial_limit_of_bands (radialValue κ b (κ*t))
    (traceRatio_pos N) (traceRatio_lt_one hN) (traceError_summable hκ hκ8 hN H)
    (by
      filter_upwards [hb m H] with n hn
      intro y hy hy'
      simpa only [dist_eq_norm] using hn (κ*t) hδ hH.le y hy hy')
  have he : trace κ b t = z := hz.limUnder_eq
  rwa [he]
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace

lemma radial_time_modulus_symmetric {κ T y s t : ℝ} (hκ : 0 < κ)
    (hy : 0 < y) (hy1 : y ≤ 1) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hclose : |t-s| ≤ y^2) (b : Driver) :
    ‖radialValue κ b t y-radialValue κ b s y‖ ≤
      2*(2+a κ+2*a κ*T)/y*(|driverValue b t-driverValue b s|+a κ*|t-s|/y) := by
  by_cases hst : s ≤ t
  · rw [abs_of_nonneg (sub_nonneg.mpr hst)] at hclose ⊢
    exact inverseFlow_time_modulus hκ hs.1 hst ht.2 hy hy1 hclose b
  · have hts : t ≤ s := (lt_of_not_ge hst).le
    rw [abs_sub_comm t s,abs_of_nonneg (sub_nonneg.mpr hts)] at hclose ⊢
    rw [norm_sub_rev,abs_sub_comm]
    exact inverseFlow_time_modulus hκ ht.1 hts hs.2 hy hy1 hclose b

 

lemma radialValue_continuousOn {κ y T : ℝ} (hκ : 0 < κ) (hy : 0 < y)
    (hy1 : y ≤ 1) (b : Driver) :
    ContinuousOn (fun t => radialValue κ b t y) (Icc 0 T) := by
  intro t ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hB : Continuous (driverValue b) :=
    (map_continuous b).comp continuous_real_toNNReal
  have h1 : Tendsto (fun s : ℝ => |driverValue b s-driverValue b t|)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
    have hh : Tendsto (driverValue b) (𝓝[Icc 0 T] t) (𝓝 (driverValue b t)) :=
      (hB.tendsto t).mono_left nhdsWithin_le_nhds
    simpa using (hh.sub_const (driverValue b t)).abs
  have h2 : Tendsto (fun s : ℝ => |s-t|) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have hh : Tendsto (fun s : ℝ => s) (𝓝[Icc 0 T] t) (𝓝 t) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    simpa using (hh.sub_const t).abs
  have hb := (h1.add ((h2.const_mul (a κ)).div_const y)).const_mul
    (2*(2+a κ+2*a κ*T)/y)
  have hb' : Tendsto (fun s : ℝ => 2*(2+a κ+2*a κ*T)/y*
      (|driverValue b s-driverValue b t|+a κ*|s-t|/y))
      (𝓝[Icc 0 T] t) (𝓝 0) := by simpa using hb
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hb'
  filter_upwards [self_mem_nhdsWithin,h2.eventually (Iio_mem_nhds (sq_pos_of_pos hy))] with s hs hclose
  exact radial_time_modulus_symmetric hκ hy hy1 ht hs hclose.le b
end SLEExactGauge.LiteralTrace
namespace SLEExactGauge.LiteralTrace
open TraceChaining

 

theorem trace_continuous_positive {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W, ContinuousOn (trace κ b) (Ioi 0) := by
  obtain ⟨N,hN,hb⟩ := radial_uniform_bands hκ hκ8 hW
  filter_upwards [hb,trace_limit_all_positive hκ hκ8 hW] with b hb hlim
  let g : ℝ → ℂ := fun T => limUnder (𝓝[>] (0:ℝ)) (radialValue κ b T)
  have hg (T : ℝ) (hT : 0 < T) : Tendsto (radialValue κ b T) (𝓝[>] 0) (𝓝 (g T)) := by
    have hh := hlim (T/κ) (div_pos hT hκ)
    have he : κ*(T/κ) = T := by field_simp
    rw [he] at hh
    have he' : g T = trace κ b (T/κ) := hh.limUnder_eq
    rwa [he']
  have hc (m H : ℕ) : ContinuousOn g (Icc (1/((m:ℝ)+1)) H) := by
    have hu := radial_uniform_limit_of_bands (fun T => radialValue κ b T) g
      (Icc (1/((m:ℝ)+1)) H) (traceRatio_pos N) (traceRatio_lt_one hN)
      (traceError_summable hκ hκ8 hN H)
      (by
        filter_upwards [hb m H] with n hn
        intro T hT y hy hy'
        simpa only [dist_eq_norm] using hn T hT.1 hT.2 y hy hy')
      (fun T hT => hg T ((by positivity : 0 < 1/((m:ℝ)+1)).trans_le hT.1))
    apply hu.continuousOn
    apply Eventually.frequently
    apply Eventually.of_forall
    intro n
    exact (radialValue_continuousOn hκ (pow_pos (traceRatio_pos N) n)
      (pow_le_one₀ (traceRatio_pos N).le (traceRatio_lt_one hN).le) b).mono
      (Icc_subset_Icc (by positivity) le_rfl)
  have hc' : ContinuousOn g (Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro T hT
    obtain ⟨m,hm⟩ := exists_nat_gt (1/T)
    obtain ⟨H,hH⟩ := exists_nat_gt T
    have hδ : 1/((m:ℝ)+1) < T := by
      apply (div_lt_iff₀ (by positivity : 0 < (m:ℝ)+1)).mpr
      have hh := (div_lt_iff₀ hT).mp hm
      nlinarith
    exact (hc m H).continuousAt (Icc_mem_nhds hδ hH)
  have he : (fun t => g (κ*t)) = trace κ b := by
    funext t
    rfl
  rw [← he]
  exact hc'.comp (continuous_const.mul continuous_id).continuousOn
    (fun t ht => mul_pos hκ ht)
end SLEExactGauge.LiteralTrace
noncomputable section
open Set Filter Metric
open scoped Topology
namespace SLEExactGauge.TraceChaining

 

lemma initial_le_of_outward_deriv {f f' : ℝ → ℝ} {T R : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t)
    (hR : f T ≤ R) (hout : ∀ t ∈ Icc 0 T, R < f t → 0 < f' t) :
    f 0 ≤ R := by
  have hm : MapsTo (fun t : ℝ => T-t) (Icc 0 T) (Icc 0 T) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hc : ContinuousOn (fun t => f (T-t)) (Icc 0 T) :=
    hf.comp (continuous_const.sub continuous_id).continuousOn hm
  have hh (t : ℝ) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (fun t => f (T-t)) (-f' (T-t)) (Ici t) t := by
    have h := (hd (T-t) (hm ⟨ht.1,ht.2.le⟩)).comp t
      ((hasDerivAt_id t).const_sub T).hasDerivWithinAt hm
    have he : Icc (0:ℝ) T ∈ 𝓝[Ici t] t := by
      filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ u : ℝ in 𝓝[Ici t] t, u < T from
          nhdsWithin_le_nhds (Iio_mem_nhds ht.2))] with u hu huT
      exact ⟨ht.1.trans hu,huT.le⟩
    convert! h.mono_of_mem_nhdsWithin he using 1; simp only [mul_neg,mul_one]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hfence := image_le_of_deriv_right_lt_deriv_boundary hc hh
    (B := fun _ => R+ε) (B' := fun _ => 0)
    (by simpa using hR.trans (by linarith : R ≤ R+ε))
    (fun _ => hasDerivAt_const _ _)
    (by
      intro t ht he
      have hp := hout (T-t) (hm ⟨ht.1,ht.2.le⟩) (by linarith)
      linarith)
  simpa using hfence (right_mem_Icc.mpr hT)
end SLEExactGauge.TraceChaining
namespace SLEExactGauge.LiteralTrace
open TraceChaining

lemma PositiveSolution.re_hasDeriv {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun u => (f u).re)
      (a κ*((f t).re-driverValue b t)/‖f t-driverValue b t‖^2) (Icc 0 T) t := by
  have hi := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hf.2.2.2.2 t ht)
  convert! hi using 1; first | rfl |
    (simp only [Complex.reCLM_apply,Complex.div_re,Complex.ofReal_im,Complex.ofReal_re,
     Complex.sub_re,Complex.normSq_eq_norm_sq,zero_mul]; ring)

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
end
end

end OAI
