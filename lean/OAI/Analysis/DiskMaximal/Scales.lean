import OAI.Analysis.DiskMaximal.Cancellation

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real

noncomputable section

namespace DiskScales

def width (δ : ℝ) (n : ℕ) : ℝ := δ*(1/2 : ℝ)^n

lemma width_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < width δ n := by
  unfold width
  positivity

lemma width_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) : width δ n ≤ δ := by
  unfold width
  exact mul_le_of_le_one_right hδ (pow_le_one₀ (by norm_num) (by norm_num))

lemma width_succ (δ : ℝ) (n : ℕ) : width δ (n+1) = width δ n / 2 := by
  simp only [width, pow_succ]
  ring

lemma width_antitone {δ : ℝ} (hδ : 0 ≤ δ) : Antitone (width δ) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [width_succ]
  have : 0 ≤ width δ n := mul_nonneg hδ (pow_nonneg (by norm_num) _)
  linarith

lemma tendsto_width (δ : ℝ) : Tendsto (width δ) atTop (𝓝 0) := by
  change Tendsto (fun n => δ*(1/2 : ℝ)^n) atTop (𝓝 0)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).const_mul δ

lemma width_rpow {δ : ℝ} (hδ : 0 ≤ δ) (p : ℝ) (n : ℕ) :
    (width δ n)^p = δ^p*((1/2 : ℝ)^p)^n := by
  rw [width, Real.mul_rpow hδ (pow_nonneg (by norm_num) n)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    mul_comm (n : ℝ) p, Real.rpow_mul (by norm_num), Real.rpow_natCast]

lemma ratio_norm_lt {p : ℝ} (hp : 0 < p) : ‖(1/2 : ℝ)^p‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
  exact Real.rpow_lt_one (by norm_num) (by norm_num) hp

lemma summable_width_rpow {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) :
    Summable (fun n => (width δ n)^p) := by
  simp_rw [width_rpow hδ]
  exact (summable_geometric_of_norm_lt_one (ratio_norm_lt hp)).mul_left _

lemma tsum_width_rpow {δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 < p) :
    (∑' n, (width δ n)^p) = δ^p / (1-(1/2 : ℝ)^p) := by
  simp_rw [width_rpow hδ]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (ratio_norm_lt hp)]
  rfl

lemma scaled_increment {Cs A t δ M L : ℝ} (hCs : 0 ≤ Cs) (hA : 0 ≤ A)
    (hAt : A ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) (hL : L ≤ 648/δ) :
    2*δ^(1/5 : ℝ)*M+14*(t*δ^(1/10 : ℝ))+
      (L+2*(3*L+1))*Cs*δ^(2*(1-(1/100 : ℝ)))*A ≤
      (16+4538*Cs)*t*δ^(1/10 : ℝ) := by
  have ht : 0 ≤ t := hA.trans hAt
  have hc : L+2*(3*L+1) ≤ 4538/δ := by
    have hh : L*δ ≤ 648 := (le_div_iff₀ hδ).mp hL
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have he1 : δ^(1/5 : ℝ)*δ^(-(1/50 : ℝ)) = δ^(9/50 : ℝ) := by
    rw [← Real.rpow_add hδ]
    norm_num
  have he2 : δ⁻¹*δ^(2*(1-(1/100 : ℝ))) = δ^(49/50 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]
    norm_num
  have hb1 : δ^(9/50 : ℝ) ≤ δ^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hb2 : δ^(49/50 : ℝ) ≤ δ^(1/10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hm : 2*δ^(1/5 : ℝ)*M ≤ 2*t*δ^(1/10 : ℝ) := by
    calc
      _ ≤ 2*δ^(1/5 : ℝ)*(A*δ^(-(1/50 : ℝ))) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 2*A*δ^(9/50 : ℝ) := by rw [← he1]; ring
      _ ≤ 2*t*δ^(1/10 : ℝ) := mul_le_mul (by linarith) hb1
        (Real.rpow_nonneg hδ.le _) (by positivity)
  have hf : (L+2*(3*L+1))*Cs*δ^(2*(1-(1/100 : ℝ)))*A ≤
      4538*Cs*t*δ^(1/10 : ℝ) := by
    calc
      _ ≤ (4538/δ)*Cs*δ^(2*(1-(1/100 : ℝ)))*A := by gcongr
      _ = 4538*Cs*A*δ^(49/50 : ℝ) := by rw [← he2]; ring
      _ ≤ 4538*Cs*t*δ^(1/10 : ℝ) := mul_le_mul (by gcongr) hb2
        (Real.rpow_nonneg hδ.le _) (by positivity)
  nlinarith

/-- A single small width works for both shell geometry and every smaller width. -/
lemma exists_admissible_width : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1/4 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600 := by
  have ht : Tendsto (fun δ : ℝ => δ^(3/5 : ℝ)) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3/5)).tendsto 0
  have hev := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/1600)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  let d := min (u/2) (1/4)
  have hd : 0 < d := lt_min (by linarith [hu.2]) (by norm_num)
  refine ⟨d, hd, min_le_right _ _, fun δ hδ hδd => ?_⟩
  have hdltu : d < u := lt_of_le_of_lt (min_le_left _ _) (by linarith [hu.2])
  have hp : δ^(3/5 : ℝ) < 1/1600 := hs ⟨lt_trans hu.1 hδ, lt_of_le_of_lt hδd hdltu⟩
  have he : δ = δ^(3/5 : ℝ)*(δ^(1/5 : ℝ))^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    norm_num
  calc
    δ = δ^(3/5 : ℝ)*(δ^(1/5 : ℝ))^2 := he
    _ ≤ (δ^(1/5 : ℝ))^2/1600 :=
      (mul_le_mul_of_nonneg_right hp.le (sq_nonneg _)).trans_eq (by ring)

end DiskScales

namespace LocalCancellation
open DiskGeometry DiskKernels DiskScales
variable {ι : Type*} [Fintype ι]

/-- Uniform exceptional sets controlling a whole decreasing sequence of disk
mixtures. Only active increments require the exact balanced moment. -/
theorem size_sequence {Cs d t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, (
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ ^ 2 *
          (ENNReal.ofReal (156*width d n/(width d n)^(1/5 : ℝ))*
            ENNReal.ofReal (coarseMass b (width d n) univ)*ENNReal.ofReal (coarseMass b (width d n) univ)) +
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ *
          ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*width d n/((width d n)^(1/5 : ℝ))^2)))*
            ENNReal.ofReal (coarseMass b (width d n) univ))) ∧
      ∀ x ∉ E, ∀ r ∈ Icc (1 : ℝ) 2,
        ∀ k : ∀ n : ℕ, RadiusDensity (r-width d n) (r+width d n)
          ⟨216/width d n, div_nonneg (by norm_num) (width_pos hd n).le⟩,
        (∀ n, t*(width d n)^(1/10 : ℝ) ≤ coarseMass b (width d n) (thinShell x r (width d n)) →
          (∑ j, ∫ y, star (y-x)*((kernel (k (n+1)) x y : ℂ)-kernel (k n) x y)*(b j).density y) = 0) →
        ‖∑ j, ∫ y in Metric.ball x r, (b j).density y‖ ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          (16+4538*Cs)*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have hd1 : d ≤ 1 := by linarith
  have hwp (n : ℕ) : 0 < width d n := width_pos hd n
  have hw1 (n : ℕ) : width d n ≤ 1 := (width_le hd.le n).trans hd1
  have hρ (n : ℕ) : 0 < (width d n)^(1/5 : ℝ) := Real.rpow_pos_of_pos (hwp n) _
  have hρ1 (n : ℕ) : (width d n)^(1/5 : ℝ) ≤ 1 :=
    Real.rpow_le_one (hwp n).le (hw1 n) (by norm_num)
  have hs (n : ℕ) := size_step b hCs (by norm_num : (1/100 : ℝ) ≤ 1)
    (hwp n) (hρ n) (hρ1 n) (hgeom _ (hwp n) (width_le hd.le n))
    (mul_pos ht (Real.rpow_pos_of_pos (hwp n) (1/10 : ℝ)))
  choose E hE hEv hEst using hs
  refine ⟨⋃ n, E n, MeasurableSet.iUnion hE,
    (measure_iUnion_le E).trans (ENNReal.tsum_le_tsum hEv), ?_⟩
  intro x hx r hr k hz
  have hxE (n : ℕ) : x ∉ E n := fun hn => hx (mem_iUnion.mpr ⟨n,hn⟩)
  let P (n : ℕ) : ℂ := ∑ j, ∫ y, (kernel (k n) x y : ℂ)*(b j).density y
  let B : ℂ := ∑ j, ∫ y in Metric.ball x r, (b j).density y
  have hPi (n : ℕ) (j : ι) : Integrable (fun y => (kernel (k n) x y : ℂ)*(b j).density y) :=
    integrable_bounded_pairing (b j).integrable (complex_kernel_lipschitz (k n) x).continuous.aestronglyMeasurable (complex_kernel_bound (k n) x)
  have hdist (n : ℕ) : dist (P n) (P (n+1)) ≤
      (16+4538*Cs)*t*(width d n)^(1/10 : ℝ) := by
    let F (y : ℂ) : ℂ := (kernel (k (n+1)) x y : ℂ)-kernel (k n) x y
    have hL : 216/width d (n+1)+216/width d n ≤ 648/width d n := by
      rw [width_succ]
      apply le_of_eq
      ring
    have hF := (complex_kernel_lipschitz (k (n+1)) x).sub (complex_kernel_lipschitz (k n) x)
    have hbnd := hEst n x (hxE n) r hr _ F hF
      (difference_bound (k n) (k (n+1)) x)
      (difference_support (k n) (k (n+1)) (width_antitone hd.le (Nat.le_succ n)) x)
      (hz n)
    have hM : coarseMass b (width d n) univ ≤
        errorPrice b (1/100)*(width d n)^(-(1/50 : ℝ)) := by
      have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) (hwp n)
      norm_num at hh
      simpa only [Real.rpow_neg (hwp n).le, div_eq_mul_inv] using hh
    have hstep := scaled_increment hCs (errorPrice_nonneg b (1/100)) hAt (hwp n) (hw1 n) hM hL
    have he : P (n+1)-P n = ∑ j, ∫ y, F y*(b j).density y := by
      change (∑ j, ∫ y, (kernel (k (n+1)) x y : ℂ)*(b j).density y) -
        (∑ j, ∫ y, (kernel (k n) x y : ℂ)*(b j).density y) = _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_sub (hPi (n+1) j) (hPi n j)]
      congr 1
      ext y
      simp only [F, sub_mul]
    rw [dist_eq_norm, norm_sub_rev, he]
    exact hbnd.trans hstep
  have hlim : Tendsto P atTop (𝓝 B) :=
    tendsto_finsetSum Finset.univ (fun j _ => tendsto_kernel_pairing k (tendsto_width d) x (b j).integrable)
  have hsm : Summable (fun n => (16+4538*Cs)*t*(width d n)^(1/10 : ℝ)) :=
    (summable_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)).mul_left _
  have htail := dist_le_tsum_of_dist_le_of_tendsto₀ _ hdist hsm hlim
  rw [tsum_mul_left, tsum_width_rpow hd.le (by norm_num : (0 : ℝ) < 1/10)] at htail
  have hstart : ‖P 0‖ ≤ (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100) := by
    have hh := total_pairing_discount b (by norm_num : (0 : ℝ) ≤ 1/100)
      (by norm_num : (1/100 : ℝ) ≤ 1) (hwp 0) (hw1 0)
      (show 1 ≤ 1+216*Cs by linarith)
      (complex_kernel_lipschitz (k 0) x) (complex_kernel_bound (k 0) x)
      (show (216/width d 0)*Cs ≤ (1+216*Cs)/width d 0 by
        apply (le_div_iff₀ (hwp 0)).mpr
        field_simp [(hwp 0).ne']
        linarith)
    simpa only [P, width, pow_zero, mul_one] using hh
  calc
    ‖B‖ = ‖P 0+(B-P 0)‖ := by congr 1; ring
    _ ≤ ‖P 0‖+‖B-P 0‖ := norm_add_le _ _
    _ = ‖P 0‖+dist (P 0) B := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
        (16+4538*Cs)*t*(d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) :=
      add_le_add hstart htail
    _ = _ := by ring

end LocalCancellation

namespace DiskGeometry

def endpointFailure (ν : Measure ℂ) (δ U : ℝ) : Set ℂ :=
  {x | ENNReal.ofReal U ≤ shellMass ν 1 (2*δ) x} ∪
  {x | ENNReal.ofReal U ≤ shellMass ν 2 (2*δ) x}

lemma endpoint_failure_bound (ν : Measure ℂ) [IsFiniteMeasure ν]
    {δ U : ℝ} (hδ : 0 ≤ δ) (hδq : δ ≤ 1/4) (hU : 0 < U) :
    MeasurableSet (endpointFailure ν δ U) ∧
    volume (endpointFailure ν δ U) ≤ ENNReal.ofReal (24*Real.pi*δ)*ν univ/ENNReal.ofReal U := by
  obtain ⟨h1,hb1⟩ := shellMass_exception ν (show 0 ≤ 2*δ by positivity)
    (show 2*δ ≤ 1 by linarith) hU
  obtain ⟨h2,hb2⟩ := shellMass_exception ν (show 0 ≤ 2*δ by positivity)
    (show 2*δ ≤ 2 by linarith) hU
  refine ⟨h1.union h2, (measure_union_le _ _).trans ((add_le_add hb1 hb2).trans_eq ?_)⟩
  simp only [div_eq_mul_inv]
  rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 3
  ring

lemma active_away_from_endpoints (ν : Measure ℂ) {x : ℂ} {δ U r : ℝ}
    (hx : x ∉ endpointFailure ν δ U) (hr : r ∈ Icc (1 : ℝ) 2)
    (ha : ENNReal.ofReal U ≤ ν (thinShell x r δ)) :
    1+δ ≤ r ∧ r+δ ≤ 2 := by
  constructor
  · by_contra hh
    have he : |r-1| ≤ δ := by rw [abs_of_nonneg (by linarith [hr.1])]; linarith
    exact hx (Or.inl (ha.trans (measure_mono (thinShell_subset_endpoint he))))
  · by_contra hh
    have he : |r-2| ≤ δ := by rw [abs_of_nonpos (by linarith [hr.2])]; linarith
    exact hx (Or.inr (ha.trans (measure_mono (thinShell_subset_endpoint he))))

end DiskGeometry

namespace DiskMoments
open DiskKernels DiskGeometry

def EndpointRadius (g : ℂ → ℝ) (x : ℂ) (r : ℝ) : Prop :=
  r ∈ Icc (1 : ℝ) 2 ∧ (r = 1 ∨ r = 2 ∨
    ∀ t ∈ Icc (1 : ℝ) 2, signedAverage g x t ≤ signedAverage g x r)

/-- Every band-maximizing or forced-endpoint radius has honest mixtures;
balancing is imposed exactly when its width stays inside the band. -/
lemma endpoint_kernel {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {x : ℂ} {r δ : ℝ}
    (hr : EndpointRadius g x r) (hδ : 0 < δ) (hδq : δ ≤ 1/4) :
    ∃ k : RadiusDensity (r-δ) (r+δ) ⟨216/δ, by positivity⟩,
      (1+δ ≤ r ∧ r+δ ≤ 2 →
        (∫ y, kernel k x y • (star (y-x)*gradient g y)) = 0) := by
  by_cases hi : 1+δ ≤ r ∧ r+δ ≤ 2
  · have hm : ∀ t ∈ Icc (1 : ℝ) 2, signedAverage g x t ≤ signedAverage g x r := by
      rcases hr.2 with h | h | h
      · linarith [hi.1]
      · linarith [hi.2]
      · exact h
    obtain ⟨k,hk⟩ := balanced_kernel hg x hr.1 hδ hδq
      (hm _ ⟨by linarith [hi.1], by linarith [hr.1.2]⟩)
      (hm _ ⟨by linarith [hr.1.1], hi.2⟩)
    exact ⟨k, fun _ => hk⟩
  · have ha : (1 : ℝ)/2 ≤ r-δ := by linarith [hr.1.1]
    have hb : r+δ ≤ (3 : ℝ) := by linarith [hr.1.2]
    have hab : r-δ < r+δ := by linarith
    let k := inverseCubeDensity (r-δ) (r+δ) ha hb hab
    refine ⟨enlarge k le_rfl le_rfl ?_, fun h => (hi h).elim⟩
    change 216/(r+δ-(r-δ)) ≤ 216/δ
    apply div_le_div_of_nonneg_left (by norm_num) hδ
    linarith

end DiskMoments

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma moment_pairing_integrable {Cs r δ : ℝ} (b : ErrorPiece Cs)
    {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x : ℂ) (hr : r+δ ≤ 3) :
    Integrable (fun y => star (y-x)*(kernel k x y : ℂ)*b.density y) := by
  apply integrable_bounded_pairing b.integrable
    ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
      (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply position_bound (complex_kernel_bound k x) x (by norm_num : (0 : ℝ) ≤ 3)
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh, Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball, dist_eq_norm] using hyb).le.trans hr

/-- A local equality of genuine densities suffices for all supported moments. -/
lemma moment_pairing_decomposition {Cs r δ : ℝ} (b : ι → ErrorPiece Cs)
    {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x : ℂ) {h : ℂ → ℂ}
    (hr : r+δ ≤ 3) (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = h y) :
    (∑ j, ∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) =
      ∫ y, kernel k x y • (star (y-x)*h y) := by
  rw [← integral_finsetSum _ (fun j _ => moment_pairing_integrable (b j) k x hr)]
  apply integral_congr_ae
  filter_upwards [hh] with y hy
  simp only [← Finset.mul_sum]
  by_cases hmem : y ∈ Metric.ball x 3
  · rw [hy hmem, Complex.real_smul]
    ring
  · have hk : kernel k x y = 0 := kernel_zero k x
      (fun hb => hmem (lt_of_lt_of_le hb hr))
    rw [hk, Complex.ofReal_zero, mul_zero, zero_mul, zero_smul]

lemma moment_difference_decomposition {Cs r δ ε : ℝ} (b : ι → ErrorPiece Cs)
    {M N : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (l : RadiusDensity (r-ε) (r+ε) N) (x : ℂ) {h : ℂ → ℂ}
    (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = h y)
    (hk : (∫ y, kernel k x y • (star (y-x)*h y)) = 0)
    (hl : (∫ y, kernel l x y • (star (y-x)*h y)) = 0) :
    (∑ j, ∫ y, star (y-x)*((kernel l x y : ℂ)-kernel k x y)*(b j).density y) = 0 := by
  have he : ∀ j, (∫ y, star (y-x)*((kernel l x y : ℂ)-kernel k x y)*(b j).density y) =
      (∫ y, star (y-x)*(kernel l x y : ℂ)*(b j).density y) -
      (∫ y, star (y-x)*(kernel k x y : ℂ)*(b j).density y) := by
    intro j
    rw [← integral_sub (moment_pairing_integrable (b j) l x hrε)
      (moment_pairing_integrable (b j) k x hrδ)]
    congr 1
    ext y
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, moment_pairing_decomposition b l x hrε hh,
    moment_pairing_decomposition b k x hrδ hh, hk, hl, sub_self]

lemma ball_pairing_decomposition {Cs r : ℝ} (b : ι → ErrorPiece Cs)
    (x : ℂ) {h : ℂ → ℂ} (hr : r ≤ 3)
    (hh : ∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = h y) :
    (∑ j, ∫ y in Metric.ball x r, (b j).density y) = ∫ y in Metric.ball x r, h y := by
  rw [← integral_finsetSum _ (fun j _ => (b j).integrable.integrableOn)]
  apply setIntegral_congr_ae measurableSet_ball
  filter_upwards [hh] with y hy hyb
  exact hy (lt_of_lt_of_le hyb hr)

/-- The full raw band-endpoint size estimate. All maxima and both forced radii
are simultaneous, with no measurable radius selection required. -/
theorem size_endpoint_raw {Cs d t : ℝ} (b : ι → ErrorPiece Cs)
    (hCs : 0 ≤ Cs) (hd : 0 < d) (hdq : d ≤ 1/4)
    (hgeom : ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ≤ (δ^(1/5 : ℝ))^2/1600)
    (ht : 0 < t) (hAt : errorPrice b (1/100) ≤ t)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    ∃ E : Set ℂ, MeasurableSet E ∧
      volume E ≤ ∑' n : ℕ, (
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ ^ 2 *
          (ENNReal.ofReal (156*width d n/(width d n)^(1/5 : ℝ))*
            ENNReal.ofReal (coarseMass b (width d n) univ)*ENNReal.ofReal (coarseMass b (width d n) univ)) +
        (ENNReal.ofReal (t*(width d n)^(1/10 : ℝ)))⁻¹ *
          ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*width d n/((width d n)^(1/5 : ℝ))^2)))*
            ENNReal.ofReal (coarseMass b (width d n) univ)) +
        ENNReal.ofReal (24*Real.pi*width d n)*ENNReal.ofReal (coarseMass b (width d n) univ)/
          ENNReal.ofReal (t*(width d n)^(1/10 : ℝ))) ∧
      ∀ x ∉ E,
        (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
        ∀ r, EndpointRadius g x r →
        ‖∫ y in Metric.ball x r, gradient g y‖ ≤
          (1+216*Cs)/d^(1/100 : ℝ)*errorPrice b (1/100)+
          (16+4538*Cs)*t*d^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) := by
  have hwp (n : ℕ) : 0 < width d n := width_pos hd n
  have hwq (n : ℕ) : width d n ≤ 1/4 := (width_le hd.le n).trans hdq
  let F (n : ℕ) := endpointFailure (coarseMeasure b (width d n)) (width d n)
    (t*(width d n)^(1/10 : ℝ))
  have hF (n : ℕ) := endpoint_failure_bound (coarseMeasure b (width d n))
    (hwp n).le (hwq n) (mul_pos ht (Real.rpow_pos_of_pos (hwp n) (1/10 : ℝ)))
  obtain ⟨E,hE,hEv,hEst⟩ := size_sequence b hCs hd hdq hgeom ht hAt
  refine ⟨E ∪ ⋃ n, F n, hE.union (MeasurableSet.iUnion fun n => (hF n).1), ?_, ?_⟩
  · apply (measure_union_le _ _).trans
    apply (add_le_add hEv ((measure_iUnion_le F).trans (ENNReal.tsum_le_tsum (fun n => (hF n).2)))).trans_eq
    rw [← ENNReal.tsum_add]
    congr 1
    funext n
    rw [coarseMeasure_apply b (width d n) MeasurableSet.univ]
  · intro x hx hh r hr
    have hxE : x ∉ E := fun h => hx (Or.inl h)
    have hxF (n : ℕ) : x ∉ F n := fun h => hx (Or.inr (mem_iUnion.mpr ⟨n,h⟩))
    choose k hk using fun n => endpoint_kernel hg hr (hwp n) (hwq n)
    rw [← ball_pairing_decomposition b x (by linarith [hr.1.2]) hh]
    apply hEst x hxE r hr.1 k
    intro n ha
    have haway : 1+width d n ≤ r ∧ r+width d n ≤ 2 := by
      apply active_away_from_endpoints (coarseMeasure b (width d n)) (hxF n) hr.1
      rw [coarseMeasure_apply b (width d n) (measurableSet_thinShell x r (width d n))]
      exact ENNReal.ofReal_le_ofReal ha
    have haway' : 1+width d (n+1) ≤ r ∧ r+width d (n+1) ≤ 2 := by
      have hw := width_antitone hd.le (Nat.le_succ n)
      constructor <;> linarith [haway.1,haway.2]
    exact moment_difference_decomposition b (k n) (k (n+1)) x
      (by linarith [hr.1.2,hwq n]) (by linarith [hr.1.2,hwq (n+1)]) hh
      (hk n haway) (hk (n+1) haway')

end LocalCancellation

namespace DiskScales

lemma first_power_identity {δ : ℝ} (hδ : 0 < δ) :
    (δ^(1/10 : ℝ))⁻¹^2 * (δ / δ^(1/5 : ℝ) * δ^(-(1/50 : ℝ)) * δ^(-(1/50 : ℝ))) =
      δ^(14/25 : ℝ) := by
  rw [← Real.rpow_neg hδ.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  have he (a : ℝ) : δ / δ^a = δ^(1-a) := by
    rw [Real.rpow_sub hδ, Real.rpow_one]
  rw [he]
  rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
  norm_num

lemma second_power_identity {δ : ℝ} (hδ : 0 < δ) :
    (δ^(1/10 : ℝ))⁻¹ * (δ / (δ^(1/5 : ℝ))^2 * δ^(-(1/50 : ℝ))) =
      δ^(12/25 : ℝ) := by
  rw [← Real.rpow_neg hδ.le, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  have he (a : ℝ) : δ / δ^a = δ^(1-a) := by
    rw [Real.rpow_sub hδ, Real.rpow_one]
  rw [he]
  rw [← mul_assoc, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
  norm_num

lemma endpoint_power_identity {δ : ℝ} (hδ : 0 < δ) :
    δ * δ^(-(1/50 : ℝ)) / δ^(1/10 : ℝ) = δ^(22/25 : ℝ) := by
  have he : δ * δ^(-(1/50 : ℝ)) = δ^(1-(1/50 : ℝ)) := by
    simp only [Real.rpow_sub hδ, Real.rpow_one, Real.rpow_neg hδ.le, div_eq_mul_inv]
  rw [he, ← Real.rpow_sub hδ]
  norm_num

/-- The two geometric failure mechanisms have integrable superlevel powers. -/
lemma shell_tail_scaled {A t δ M : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
      (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*ENNReal.ofReal M*ENNReal.ofReal M) +
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
      ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*δ/(δ^(1/5 : ℝ))^2)))*ENNReal.ofReal M) ≤
    ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
  have hU : 0 < t*δ^(1/10 : ℝ) := mul_pos ht (Real.rpow_pos_of_pos hδ _)
  rw [← ENNReal.ofReal_inv_of_pos hU, ← ENNReal.ofReal_pow (inv_nonneg.mpr hU.le)]
  have hp : 0 ≤ 156*δ/δ^(1/5 : ℝ) := by positivity
  have hp' : 0 ≤ 2*(200*δ/(δ^(1/5 : ℝ))^2) := by positivity
  rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul (mul_nonneg hp hM0),
    ← ENNReal.ofReal_mul (sq_nonneg _),
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6*Real.pi by positivity),
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hp'),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hU.le),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hfirst : (t*δ^(1/10 : ℝ))⁻¹^2 * (156*δ/δ^(1/5 : ℝ)*M*M) ≤
      156*(A/t)^2*δ^(14/25 : ℝ) := by
    calc
      _ ≤ (t*δ^(1/10 : ℝ))⁻¹^2 *
          (156*δ/δ^(1/5 : ℝ)*(A*δ^(-(1/50 : ℝ)))*(A*δ^(-(1/50 : ℝ)))) := by gcongr
      _ = 156*(A/t)^2*δ^(14/25 : ℝ) := by
        rw [← first_power_identity hδ]
        simp only [mul_inv_rev]
        ring
  have hsecond : (t*δ^(1/10 : ℝ))⁻¹ *
      (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2))*M) ≤
      2400*Real.pi*(A/t)*δ^(9/25 : ℝ) := by
    calc
      _ ≤ (t*δ^(1/10 : ℝ))⁻¹ *
          (6*Real.pi*(2*(200*δ/(δ^(1/5 : ℝ))^2))*(A*δ^(-(1/50 : ℝ)))) := by gcongr
      _ = 2400*Real.pi*(A/t)*δ^(12/25 : ℝ) := by
        rw [← second_power_identity hδ]
        simp only [mul_inv_rev]
        ring
      _ ≤ 2400*Real.pi*(A/t)*δ^(9/25 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)) (by positivity)
  exact add_le_add hfirst hsecond

lemma endpoint_tail_scaled {A t δ M : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    ENNReal.ofReal (24*Real.pi*δ)*ENNReal.ofReal M / ENNReal.ofReal (t*δ^(1/10 : ℝ)) ≤
    ENNReal.ofReal (24*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (24*Real.pi*δ)*(A*δ^(-(1/50 : ℝ)))/(t*δ^(1/10 : ℝ)) := by gcongr
    _ = 24*Real.pi*(A/t)*δ^(22/25 : ℝ) := by
      rw [← endpoint_power_identity hδ]
      ring
    _ ≤ 24*Real.pi*(A/t)*δ^(9/25 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)) (by positivity)

end DiskScales

namespace DiskScales

lemma norm_geometric_rpow_lt {p : ℝ} (hp : 0 < p) : (1/2 : ℝ)^p < 1 :=
  Real.rpow_lt_one (by norm_num) (by norm_num) hp

lemma raw_endpoint_tail_scaled {A t δ M : ℝ} (hA : 0 ≤ A) (ht : 0 < t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M)
    (hM : M ≤ A*δ^(-(1/50 : ℝ))) :
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ ^ 2 *
      (ENNReal.ofReal (156*δ/δ^(1/5 : ℝ))*ENNReal.ofReal M*ENNReal.ofReal M) +
    (ENNReal.ofReal (t*δ^(1/10 : ℝ)))⁻¹ *
      ((ENNReal.ofReal (6*Real.pi)*ENNReal.ofReal (2*(200*δ/(δ^(1/5 : ℝ))^2)))*ENNReal.ofReal M) +
    ENNReal.ofReal (24*Real.pi*δ)*ENNReal.ofReal M/ENNReal.ofReal (t*δ^(1/10 : ℝ)) ≤
    ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2424*Real.pi*(A/t)*δ^(9/25 : ℝ)) := by
  calc
    _ ≤ ENNReal.ofReal (156*(A/t)^2*δ^(14/25 : ℝ)+2400*Real.pi*(A/t)*δ^(9/25 : ℝ)) +
          ENNReal.ofReal (24*Real.pi*(A/t)*δ^(9/25 : ℝ)) :=
      add_le_add (shell_tail_scaled hA ht hδ hδ1 hM0 hM)
        (endpoint_tail_scaled hA ht hδ hδ1 hM)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

lemma geometric_tail_sum {A t d : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (hd : 0 ≤ d) :
    (∑' n : ℕ, ENNReal.ofReal
      (156*(A/t)^2*(width d n)^(14/25 : ℝ)+2424*Real.pi*(A/t)*(width d n)^(9/25 : ℝ))) =
    ENNReal.ofReal (156*(A/t)^2*d^(14/25 : ℝ)/(1-(1/2 : ℝ)^(14/25 : ℝ))+
      2424*Real.pi*(A/t)*d^(9/25 : ℝ)/(1-(1/2 : ℝ)^(9/25 : ℝ))) := by
  have h1 := (summable_width_rpow hd (by norm_num : (0 : ℝ) < 14/25)).mul_left (156*(A/t)^2)
  have h2 := (summable_width_rpow hd (by norm_num : (0 : ℝ) < 9/25)).mul_left (2424*Real.pi*(A/t))
  have hn (n : ℕ) : 0 ≤ width d n := mul_nonneg hd (pow_nonneg (by norm_num) n)
  have hc1 : 0 ≤ 156*(A/t)^2 := by positivity
  have hc2 : 0 ≤ 2424*Real.pi*(A/t) := by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => add_nonneg
    (mul_nonneg hc1 (Real.rpow_nonneg (hn n) _))
    (mul_nonneg hc2 (Real.rpow_nonneg (hn n) _))) (h1.add h2),
    Summable.tsum_add h1 h2, tsum_mul_left, tsum_mul_left,
    tsum_width_rpow hd (by norm_num : (0 : ℝ) < 14/25),
    tsum_width_rpow hd (by norm_num : (0 : ℝ) < 9/25)]
  congr 1
  ring

/-- After the initial-width choice d=A/t, the failure exponents are strictly
larger than one, rather than the nonintegrable weak-(1,1) exponent. -/
lemma starting_width_tail {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    156*(A/t)^2*(A/t)^(14/25 : ℝ)/(1-(1/2 : ℝ)^(14/25 : ℝ))+
      2424*Real.pi*(A/t)*(A/t)^(9/25 : ℝ)/(1-(1/2 : ℝ)^(9/25 : ℝ)) =
    (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ) := by
  have hq : 0 < A/t := div_pos hA ht
  have he1 : (A/t)^2*(A/t)^(14/25 : ℝ) = (A/t)^(64/25 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hq]
    norm_num
  have he2 : (A/t)*(A/t)^(9/25 : ℝ) = (A/t)^(34/25 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (A/t)]
    rw [← Real.rpow_add hq]
    norm_num
  calc
    _ = (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*((A/t)^2*(A/t)^(14/25 : ℝ))+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*((A/t)*(A/t)^(9/25 : ℝ)) := by ring
    _ = _ := by rw [he1,he2]

end DiskScales

namespace DiskScales

lemma size_start_identity {Cs A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (1+216*Cs)/(A/t)^(1/100 : ℝ)*A+
      (16+4538*Cs)*t*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) =
    t*((1+216*Cs)*(A/t)^(99/100 : ℝ)+
      (16+4538*Cs)*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
  have hq : 0 < A/t := div_pos hA ht
  have he : (A/t)/(A/t)^(1/100 : ℝ) = (A/t)^(99/100 : ℝ) := by
    have hh := Real.rpow_sub hq (1 : ℝ) (1/100 : ℝ)
    norm_num at hh
    exact hh.symm
  have hAt : t*(A/t) = A := by field_simp
  calc
    _ = t*((1+216*Cs)*((A/t)/(A/t)^(1/100 : ℝ))+
      (16+4538*Cs)*(A/t)^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) := by
        rw [mul_add]
        congr 1
        · calc
            _ = (1+216*Cs)/(A/t)^(1/100 : ℝ)*(t*(A/t)) := by rw [hAt]
            _ = _ := by ring
        · ring
    _ = _ := by rw [he]

/-- One fixed small-width cutoff enforces geometry and the strict endpoint
size threshold at every smaller positive width. -/
lemma exists_size_parameters (Cs : ℝ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1/4 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ (δ^(1/5 : ℝ))^2/1600) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
        (1+216*Cs)*δ^(99/100 : ℝ)+
          (16+4538*Cs)*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ)) ≤ 1) := by
  obtain ⟨d,hd,hdq,hgeom⟩ := exists_admissible_width
  have ht : Tendsto (fun δ : ℝ => (1+216*Cs)*δ^(99/100 : ℝ)+
      (16+4538*Cs)*δ^(1/10 : ℝ)/(1-(1/2 : ℝ)^(1/10 : ℝ))) (𝓝 0) (𝓝 0) := by
    have h1 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 99/100)).tendsto 0
    have h2 := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/10)).tendsto 0
    simpa using (h1.const_mul (1+216*Cs)).add ((h2.const_mul (16+4538*Cs)).div_const _)
  obtain ⟨l,u,hu,hs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  let d₀ := min d (u/2)
  have hd0 : 0 < d₀ := lt_min hd (by linarith [hu.2])
  refine ⟨d₀,hd0,(min_le_left _ _).trans hdq,fun δ hδ hδd => hgeom δ hδ (hδd.trans (min_le_left _ _)), ?_⟩
  intro δ hδ hδd
  apply le_of_lt
  apply hs
  exact ⟨lt_trans hu.1 hδ, lt_of_le_of_lt hδd ((min_le_right _ _).trans_lt (by linarith [hu.2]))⟩

end DiskScales

namespace DiskScales

def sizeTailConstant : ℝ :=
  156/(1-(1/2 : ℝ)^(14/25 : ℝ))+2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ))

lemma sizeTailConstant_pos : 0 < sizeTailConstant := by
  have h1 : 0 < 1-(1/2 : ℝ)^(14/25 : ℝ) := sub_pos.mpr (norm_geometric_rpow_lt (by norm_num))
  have h2 : 0 < 1-(1/2 : ℝ)^(9/25 : ℝ) := sub_pos.mpr (norm_geometric_rpow_lt (by norm_num))
  unfold sizeTailConstant
  positivity

lemma collapse_size_tail {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    (156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*q^(64/25 : ℝ)+
      (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*q^(34/25 : ℝ) ≤
      sizeTailConstant*q^(34/25 : ℝ) := by
  have hc : 0 ≤ 156/(1-(1/2 : ℝ)^(14/25 : ℝ)) :=
    div_nonneg (by norm_num) (sub_nonneg.mpr ((norm_geometric_rpow_lt (by norm_num)).le))
  have he := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by norm_num : (34/25 : ℝ) ≤ 64/25)) hc
  unfold sizeTailConstant
  nlinarith

end DiskScales

namespace LocalCancellation
open DiskKernels DiskMoments DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The uniform integrable superlevel tail, with both forced band endpoints.
The only decomposition assumption is equality of the specified densities on
each observation disk. No direction positivity is needed for this size bound. -/
theorem size_tail {Cs : ℝ} (hCs : 0 ≤ Cs) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [Fintype ι] (b : ι → ErrorPiece Cs),
      0 < errorPrice b (1/100) → ∀ t : ℝ, L*errorPrice b (1/100) ≤ t →
      ∀ g : ℂ → ℝ, ContDiff ℝ 1 g →
      ∃ E : Set ℂ, MeasurableSet E ∧
        volume E ≤ ENNReal.ofReal (sizeTailConstant*(errorPrice b (1/100)/t)^(34/25 : ℝ)) ∧
        ∀ x ∉ E,
          (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
          ∀ r, EndpointRadius g x r → ‖∫ y in Metric.ball x r, gradient g y‖ ≤ t := by
  obtain ⟨d₀,hd0,hdq,hgeom,hsmall⟩ := exists_size_parameters Cs
  have hL : 1 ≤ (1 : ℝ)/d₀ := (le_div_iff₀ hd0).mpr (by linarith)
  refine ⟨1/d₀,hL,?_⟩
  intro ι _ b hA t ht g hg
  let A := errorPrice b (1/100)
  have hAt : A ≤ t := (le_mul_of_one_le_left hA.le hL).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le hA hAt
  have hqd : A/t ≤ d₀ := by
    apply (div_le_iff₀ ht0).mpr
    have hh : A/d₀ ≤ t := by simpa only [A,one_div, div_eq_mul_inv, mul_comm, mul_one] using ht
    have hh' := (div_le_iff₀ hd0).mp hh
    linarith
  have hq0 : 0 < A/t := div_pos hA ht0
  have hq1 : A/t ≤ 1 := by linarith
  have hqq : A/t ≤ 1/4 := hqd.trans hdq
  obtain ⟨E,hE,hEv,hEst⟩ := size_endpoint_raw b hCs hq0 hqq
    (fun δ hδ hδq => hgeom δ hδ (hδq.trans hqd)) ht0 hAt hg
  refine ⟨E,hE,?_,?_⟩
  · apply hEv.trans
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal
          (156*(A/t)^2*(width (A/t) n)^(14/25 : ℝ)+
            2424*Real.pi*(A/t)*(width (A/t) n)^(9/25 : ℝ)) := by
        apply ENNReal.tsum_le_tsum
        intro n
        have hw0 : 0 < width (A/t) n := width_pos hq0 n
        have hw1 : width (A/t) n ≤ 1 := (width_le hq0.le n).trans hq1
        apply raw_endpoint_tail_scaled hA.le ht0 hw0 hw1 (coarseMass_nonneg b _ _)
        have hh := coarseMass_bound b (by norm_num : (0 : ℝ) ≤ 1/100) hw0
        norm_num at hh
        rw [Real.rpow_neg hw0.le]
        exact hh
      _ = ENNReal.ofReal
          ((156/(1-(1/2 : ℝ)^(14/25 : ℝ)))*(A/t)^(64/25 : ℝ)+
            (2424*Real.pi/(1-(1/2 : ℝ)^(9/25 : ℝ)))*(A/t)^(34/25 : ℝ)) := by
        rw [geometric_tail_sum hA.le ht0 hq0.le, starting_width_tail hA ht0]
      _ ≤ ENNReal.ofReal (sizeTailConstant*(A/t)^(34/25 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (collapse_size_tail hq0 hq1)
  · intro x hx hh r hr
    apply (hEst x hx hh r hr).trans
    rw [size_start_identity hA ht0]
    exact (mul_le_mul_of_nonneg_left (hsmall _ hq0 hqd) ht0.le).trans_eq (mul_one t)

end LocalCancellation

end

end OAI
