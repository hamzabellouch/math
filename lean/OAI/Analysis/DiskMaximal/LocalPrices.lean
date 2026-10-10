import OAI.Analysis.DiskMaximal.Scales

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

namespace DyadicMajorant
variable {X : Type*} [MeasurableSpace X]

/-- A Borel price built from exceptions, rather than a measurability-dependent
selection of maximizing radii. -/
def price (t : ℝ) (E : ℕ → Set X) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal t + ∑' n : ℕ, (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x

lemma measurable_price (t : ℝ) {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n)) :
    Measurable (price t E) := by
  unfold price
  have hs : Measurable (fun x => ∑' n : ℕ, (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x) := Measurable.tsum (fun n =>
    (measurable_const : Measurable (fun _ : X => ENNReal.ofReal (t*2^(n+1)))).indicator (hE n))
  exact measurable_const.add hs

omit [MeasurableSpace X] in
lemma majorizes {t v : ℝ} (ht : 0 < t) {E : ℕ → Set X} {x : X}
    (hv : ∀ n : ℕ, x ∉ E n → v ≤ t*2^n) :
    ENNReal.ofReal v ≤ price t E x := by
  by_cases hvt : v ≤ t
  · exact (ENNReal.ofReal_le_ofReal hvt).trans le_self_add
  · have he : ∃ n : ℕ, v ≤ t*2^n := by
      obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (v/t) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, le_of_lt ((div_lt_iff₀ ht).mp hn |> fun h => by simpa only [mul_comm] using h)⟩
    let n := Nat.find he
    have hn : v ≤ t*2^n := Nat.find_spec he
    have hn0 : n ≠ 0 := by
      intro hz
      have : v ≤ t := by simpa only [hz, pow_zero, mul_one] using hn
      exact hvt this
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hjn : j < n := by omega
    have hmem : x ∈ E j := by
      by_contra h
      exact Nat.find_min he hjn (hv j h)
    have hp : ENNReal.ofReal (t*2^(j+1)) ≤ price t E x := by
      have hs := ENNReal.le_tsum j (f := fun n : ℕ => (E n).indicator (fun _ => ENNReal.ofReal (t*2^(n+1))) x)
      rw [indicator_of_mem hmem] at hs
      exact hs.trans le_add_self
    apply le_trans (ENNReal.ofReal_le_ofReal hn)
    simpa only [hj, Nat.succ_eq_add_one] using hp

lemma lintegral_price (μ : Measure X) {Q : Set X}
    (t : ℝ) {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n)) :
    (∫⁻ x in Q, price t E x ∂μ) ≤
      ENNReal.ofReal t*μ Q + ∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*μ (E n) := by
  simp only [price]
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
    lintegral_tsum (fun n => (measurable_const.indicator (hE n)).aemeasurable)]
  apply add_le_add le_rfl
  apply ENNReal.tsum_le_tsum
  intro n
  rw [lintegral_indicator (hE n), lintegral_const, Measure.restrict_apply_univ,
    Measure.restrict_apply (hE n)]
  exact mul_le_mul_right (measure_mono inter_subset_left) _

end DyadicMajorant

namespace DyadicMajorant

lemma weighted_geometric_sum {t K c : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hc1 : 2*c < 1) :
    (∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n)) =
      ENNReal.ofReal (2*t*K/(1-2*c)) := by
  have he (n : ℕ) : ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n) =
      ENNReal.ofReal (2*t*K*(2*c)^n) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, pow_succ]
    ring
  simp_rw [he]
  have hc' : ‖2*c‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hc1
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_of_norm_lt_one hc').mul_left (2*t*K)),
    tsum_mul_left, tsum_geometric_of_norm_lt_one hc']
  rfl

variable {X : Type*} [MeasurableSpace X]

lemma lintegral_price_geometric (μ : Measure X) {Q : Set X} {q t K c : ℝ}
    (hq : 0 ≤ q) (hQ : μ Q ≤ ENNReal.ofReal q) (ht : 0 ≤ t)
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hc1 : 2*c < 1)
    {E : ℕ → Set X} (hE : ∀ n, MeasurableSet (E n))
    (hEv : ∀ n : ℕ, μ (E n) ≤ ENNReal.ofReal (K*c^n)) :
    (∫⁻ x in Q, price t E x ∂μ) ≤
      ENNReal.ofReal (t*(q+2*K/(1-2*c))) := by
  apply (lintegral_price μ t hE).trans
  calc
    _ ≤ ENNReal.ofReal t*ENNReal.ofReal q+
        ∑' n : ℕ, ENNReal.ofReal (t*2^(n+1))*ENNReal.ofReal (K*c^n) :=
      add_le_add (mul_le_mul_right hQ _) (ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hEv n) _)
    _ = ENNReal.ofReal (t*q)+ENNReal.ofReal (2*t*K/(1-2*c)) := by
      rw [← ENNReal.ofReal_mul ht, weighted_geometric_sum ht hK hc hc1]
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg ht hq) (by positivity [sub_pos.mpr hc1])]
      congr 1
      ring

end DyadicMajorant

namespace LocalCancellation
open DiskScales DiskMoments

lemma errorPrice_zero {ι : Type*} [Fintype ι] {Cs α : ℝ} (b : ι → ErrorPiece Cs)
    (hA : errorPrice b α = 0) : ∀ j, (b j).density =ᵐ[volume] 0 := by
  intro j
  have hterm : (b j).size^α*(b j).mass ≤ errorPrice b α :=
    Finset.single_le_sum (fun k _ => mul_nonneg (Real.rpow_nonneg (b k).size_pos.le _) (b k).mass_nonneg) (Finset.mem_univ j)
  have hm : (b j).mass = 0 := by
    have hp := Real.rpow_pos_of_pos (b j).size_pos α
    rw [hA] at hterm
    nlinarith [(b j).mass_nonneg]
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => norm_nonneg ((b j).density y)) (b j).integrable.norm).mp hm
  filter_upwards [hz] with y hy
  exact norm_eq_zero.mp hy

lemma dyadic_ratio {A L : ℝ} (hA : 0 < A) (hL : 1 ≤ L) (n : ℕ) :
    A/(L*A*2^n) ≤ (1/2 : ℝ)^n := by
  have hLA : 0 < L*A := mul_pos (by linarith) hA
  have hn : 0 < (2 : ℝ)^n := by positivity
  calc
    _ ≤ (L*A)/(L*A*2^n) := div_le_div_of_nonneg_right (le_mul_of_one_le_left hA.le hL) (mul_nonneg hLA.le hn.le)
    _ = (1/2 : ℝ)^n := by rw [div_pow]; field_simp; simp

/-- A simultaneous Borel integrable price for every admissible disk gradient.
The constant is independent of the number of pieces. -/
theorem size_majorant {Cs : ℝ} (hCs : 0 ≤ Cs) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (b : ι → ErrorPiece Cs)
      (g : ℂ → ℝ), ContDiff ℝ 1 g → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
      ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
        (∫⁻ x in Q, F x) ≤ ENNReal.ofReal (C*errorPrice b (1/100)) ∧
        ∀ x, (∀ᵐ y, y ∈ Metric.ball x 3 → ∑ j, (b j).density y = gradient g y) →
          ∀ r, EndpointRadius g x r →
            ENNReal.ofReal ‖∫ y in Metric.ball x r, gradient g y‖ ≤ F x := by
  obtain ⟨L,hL,hsize⟩ := size_tail hCs
  let c : ℝ := (1/2 : ℝ)^(34/25 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : 2*c < 1 := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1/2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 34/25)
    norm_num at hh
    linarith
  let C := L*(1+2*sizeTailConstant/(1-2*c))
  have hC : 0 < C := mul_pos (by linarith) (by
    have := sizeTailConstant_pos
    have := sub_pos.mpr hc1
    positivity)
  refine ⟨C,hC,?_⟩
  intro ι _ b g hg Q hQ
  let A := errorPrice b (1/100)
  by_cases hAz : A = 0
  · refine ⟨0,measurable_const,?_,?_⟩
    · simp only [Pi.zero_apply, lintegral_zero, A, hAz, mul_zero, ENNReal.ofReal_zero, le_refl]
    · intro x hh r hr
      have hz := errorPrice_zero b hAz
      have hs : (∑ j, ∫ y in Metric.ball x r, (b j).density y) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact integral_eq_zero_of_ae ((ae_restrict_of_ae (hz j)))
      have he := ball_pairing_decomposition b x (by linarith [hr.1.2] : r ≤ 3) hh
      rw [← he,hs,norm_zero,ENNReal.ofReal_zero]
      exact le_refl _
  · have hA : 0 < A := lt_of_le_of_ne (errorPrice_nonneg b _) (Ne.symm hAz)
    have ht : 0 < L*A := mul_pos (by linarith) hA
    have hts (n : ℕ) : L*A ≤ L*A*2^n := le_mul_of_one_le_right ht.le (one_le_pow₀ (by norm_num))
    choose E hE hEv hbound using fun n : ℕ => hsize b hA (L*A*2^n) (hts n) g hg
    refine ⟨DyadicMajorant.price (L*A) E, DyadicMajorant.measurable_price _ hE,?_,?_⟩
    · have htail (n : ℕ) : volume (E n) ≤ ENNReal.ofReal (sizeTailConstant*c^n) := by
        apply (hEv n).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ sizeTailConstant_pos.le
        calc
          _ ≤ ((1/2 : ℝ)^n)^(34/25 : ℝ) := Real.rpow_le_rpow (by positivity) (dyadic_ratio hA hL n) (by norm_num)
          _ = c^n := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm (n : ℝ),
              Real.rpow_mul (by norm_num), Real.rpow_natCast]
      have hi := DyadicMajorant.lintegral_price_geometric volume (by norm_num : (0 : ℝ) ≤ 1) hQ ht.le
        sizeTailConstant_pos.le hc hc1 hE htail
      convert hi using 1
      congr 1
      dsimp [C,A]
      ring
    · intro x hh r hr
      apply DyadicMajorant.majorizes ht
      intro n hn
      exact hbound n x hn hh r hr

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry

/-- An integrable aggregate of vectors in a fixed acute cone. It covers the
positive pieces by taking their sum; no direction is imposed on errors. -/
structure ConeDensity (e : ℂ) (κ : ℝ) where
  density : ℂ → ℂ
  integrable : Integrable density
  cone : ∀ᵐ y, κ*‖density y‖ ≤ inner ℝ e (density y)

lemma inner_unit_bound {e p : ℂ} (he : ‖e‖ = 1) : |inner ℝ e p| ≤ ‖p‖ := by
  simpa only [he,one_mul] using abs_real_inner_le_norm e p

lemma negative_projection_le_norm {e p : ℂ} (he : ‖e‖ = 1) :
    max 0 (-inner ℝ e p) ≤ ‖p‖ := by
  exact max_le (norm_nonneg _) ((neg_le_abs _).trans (inner_unit_bound he))

lemma negative_projection_change (e p q : ℂ) (he : ‖e‖ = 1) :
    max 0 (-inner ℝ e q) ≤ max 0 (-inner ℝ e p)+‖q-p‖ := by
  have h := inner_unit_bound (p := q-p) he
  rw [inner_sub_right] at h
  apply max_le
  · positivity
  · have hh := neg_le_abs (inner ℝ e q-inner ℝ e p)
    have hm := le_max_right (0 : ℝ) (-inner ℝ e p)
    linarith

lemma cone_pairing {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    {K : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y)
    (hK1 : ∀ y, K y ≤ 1) :
    κ*(∫ y, K y*‖a.density y‖) ≤ inner ℝ e (∫ y, (K y : ℂ)*a.density y) := by
  have hKn (y : ℂ) : ‖K y‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (hK0 y)]; exact hK1 y
  have hi : Integrable (fun y => K y*‖a.density y‖) := a.integrable.norm.bdd_mul hK (ae_of_all _ hKn)
  have hia : Integrable (fun y => (K y : ℂ)*a.density y) :=
    a.integrable.bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
      (ae_of_all _ (fun y => by simpa only [Complex.norm_real] using hKn y))
  rw [← integral_const_mul, ← integral_inner hia e]
  apply integral_mono_ae (hi.const_mul κ) ((innerSL ℝ e).integrable_comp hia)
  filter_upwards [a.cone] with y hy
  change κ*(K y*‖a.density y‖) ≤ inner ℝ e ((K y : ℂ)*a.density y)
  rw [← Complex.real_smul, inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hy (hK0 y)]

/-- Nonpositive total projection bounds the weighted good mass by the error. -/
lemma cone_mass_of_nonpositive {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 < κ) {K : ℂ → ℝ} (hK : AEStronglyMeasurable K)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) {p : ℂ}
    (hp : inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p) ≤ 0) :
    (∫ y, K y*‖a.density y‖) ≤ ‖p‖/κ := by
  apply (le_div_iff₀ hκ).mpr
  have hh := cone_pairing a hK hK0 hK1
  have hb := inner_unit_bound (p := p) he
  rw [inner_add_right] at hp
  have hn := neg_le_abs (inner ℝ e p)
  nlinarith

/-- Crossing the zero projection selects a genuine convex kernel, not an
arbitrary discontinuous truncation. -/
lemma crossing_interpolation (e p q : ℂ) (hq : inner ℝ e q < 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      inner ℝ e (θ • p+(1-θ) • q) ≤ 0 ∧
      max 0 (-inner ℝ e (θ • p+(1-θ) • q)) = max 0 (-inner ℝ e p) := by
  by_cases hp : inner ℝ e p ≤ 0
  · refine ⟨1,zero_le_one,le_rfl,?_,?_⟩
    · simpa using hp
    · simp
  · obtain ⟨θ,hθ0,hθ1,hzero⟩ := convex_zero (le_of_not_ge hp) hq.le
    refine ⟨θ,hθ0,hθ1,?_,?_⟩
    · simp only [inner_add_right, inner_smul_right, hzero, le_refl]
    · rw [inner_add_right, inner_smul_right, inner_smul_right, hzero,
        neg_zero, max_self, max_eq_left (by linarith : -inner ℝ e p ≤ 0)]

/-- The cap cost of the good density is weighted interior mass, not its
possibly enormous total mass. -/
lemma cone_corrected_cap {a : ℂ → ℂ} (ha : Integrable a)
    {K L : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hL : AEStronglyMeasurable L)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1)
    (hL0 : ∀ y, 0 ≤ L y) (hL1 : ∀ y, L y ≤ 1)
    {D : Set ℂ} (hD : MeasurableSet D) (hsupp : ∀ y, L y-K y ≠ 0 → y ∈ D)
    (x z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖)
    (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∫ y, correction x z y*((L y : ℂ)-K y)*a y‖ ≤
      2*ρ*(∫ y, (L y+K y)*‖a y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖a y‖) := by
  have hi : Integrable (fun y => (L y+K y)*‖a y‖) :=
    ha.norm.bdd_mul (c := 2) (hL.add hK) (ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hL0 y) (hK0 y))]
      linarith [hK1 y,hL1 y]))
  let B := D \ Metric.ball z ρ
  have hB : MeasurableSet B := hD.diff measurableSet_ball
  have hbi : Integrable (B.indicator (fun y => ‖a y‖)) := ha.norm.indicator hB
  have hmaj : ‖∫ y, correction x z y*((L y : ℂ)-K y)*a y‖ ≤
      ∫ y, 2*ρ*((L y+K y)*‖a y‖)+7*B.indicator (fun y => ‖a y‖) y := by
    apply norm_integral_le_of_norm_le ((hi.const_mul _).add (hbi.const_mul _))
    filter_upwards with y
    change ‖correction x z y*((L y : ℂ)-K y)*a y‖ ≤ 2*ρ*((L y+K y)*‖a y‖)+7*B.indicator (fun y => ‖a y‖) y
    have hk := hK0 y
    have hl := hL0 y
    have hb : 0 ≤ B.indicator (fun y => ‖a y‖) y := Set.indicator_nonneg (fun _ _ => norm_nonneg _) y
    have hf : ‖((L y : ℂ)-K y)‖ = |L y-K y| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hsum : |L y-K y| ≤ L y+K y := abs_le.mpr ⟨by linarith [hL0 y], by linarith [hK0 y]⟩
    have hone : |L y-K y| ≤ 1 := abs_le.mpr ⟨by linarith [hL0 y,hK1 y],by linarith [hL1 y,hK0 y]⟩
    by_cases hzero : L y-K y = 0
    · have hc : (L y : ℂ)-K y = 0 := by exact_mod_cast hzero
      rw [hc, mul_zero, zero_mul, norm_zero]
      positivity
    · have hyD := hsupp y hzero
      by_cases hyB : y ∈ Metric.ball z ρ
      · have hc := correction_cap_bound hz (show ‖y-z‖ ≤ ρ from by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hyB).le)
        rw [indicator_of_notMem (show y ∉ B from fun h => h.2 hyB), mul_zero, add_zero,
          norm_mul, norm_mul, hf]
        have hh := mul_le_mul hc hsum (abs_nonneg _) (by positivity : 0 ≤ 2*ρ)
        nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg (a y))]
      · rw [indicator_of_mem (show y ∈ B from ⟨hyD,hyB⟩),norm_mul,norm_mul,hf]
        have hc := mul_le_mul (correction_bounded hz (hD3 y hyD)) hone (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)
        have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg (a y))
        have hn : 0 ≤ 2*ρ*((L y+K y)*‖a y‖) := by positivity
        nlinarith
  rw [integral_add (hi.const_mul _) (hbi.const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator hB] at hmaj
  exact hmaj

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

/-- The error contribution to the corrected first active step; no moment
cancellation for the errors alone is presumed. -/
lemma corrected_error_bound {Cs α δ ρ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hρ : 0 ≤ ρ)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ d, ∫ y, correction x z y*F y*(b d).density y‖ ≤
      2*ρ*coarseMass b δ univ+7*coarseMass b δ (D \ Metric.ball z ρ)+
      ((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have hnorm : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ (3 : ℝ) := fun y hy => hD3 y (hFD y hy)
  have hH : ‖(star (z-x))⁻¹‖ ≤ (2 : ℝ) := by
    rw [norm_inv, norm_star]
    have hn : 0 < ‖z-x‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hn]
    linarith
  have hcorr : LipschitzWith (L+2*(3*L+1)) (fun y => correction x z y*F y) :=
    corrected_lipschitz (M := 1) (R := 3) (H := 2) hF hFb x z hnorm hH
  have hsplit : (∑ d, ∫ y, correction x z y*F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, correction x z y*F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, correction x z y*F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, correction x z y*F y*(b d).density y)).symm
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          ‖∫ y, correction x z y*F y*(b d).density y‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size),
          (2*ρ*(∫ y, ‖(b d).density y‖)+7*(∫ y in D \ Metric.ball z ρ, ‖(b d).density y‖)) :=
        Finset.sum_le_sum (fun d _ => corrected_pairing_cap (b d).integrable hD hFb hFD x z hρ hz hD3)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [coarseMass, Measure.restrict_univ]
  · exact fine_pairing_bound b hCs hα hδ hδ1 hcorr

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales
variable {ι : Type*} [Fintype ι]

lemma increment_bound_general {Cs α δ M : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ M) (hFD : ∀ y, F y ≠ 0 → y ∈ D) :
    ‖∑ d, ∫ y, F y*(b d).density y‖ ≤
      M*coarseMass b δ D+(L : ℝ)*Cs*δ^(2*(1-α))*errorPrice b α := by
  classical
  have he : (∑ d, ∫ y, F y*(b d).density y) =
      (∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ∫ y, F y*(b d).density y)+
      (∑ d ∈ Finset.univ.filter (fun d => (b d).size < δ^2), ∫ y, F y*(b d).density y) := by
    simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d => δ^2 ≤ (b d).size) (fun d => ∫ y, F y*(b d).density y)).symm
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), ‖∫ y, F y*(b d).density y‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.univ.filter (fun d => δ^2 ≤ (b d).size), M*(∫ y in D, ‖(b d).density y‖) := by
        apply Finset.sum_le_sum
        intro d _
        have hh := pairing_majorant (b d).integrable hD 0 M (fun y => by
          by_cases hy : y ∈ D
          · simpa only [indicator_of_mem hy, mul_one, zero_add] using hFb y
          · have hf : F y = 0 := by by_contra h; exact hy (hFD y h)
            simp only [hf,norm_zero,indicator_of_notMem hy,mul_zero,add_zero,le_refl])
        simpa only [zero_mul,zero_add] using hh
      _ = _ := by rw [← Finset.mul_sum]; rfl
  · exact fine_pairing_bound b hCs hα hδ hδ1 hF

lemma correction_kernel_bound {F : ℂ → ℂ} (hFb : ∀ y, ‖F y‖ ≤ 1)
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3) :
    ∀ y, ‖correction x z y*F y‖ ≤ 7 := by
  intro y
  by_cases hy : F y = 0
  · simp only [hy,mul_zero,norm_zero]; norm_num
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul (correction_bounded hz (hD3 y hy)) (hFb y) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 7)

lemma corrected_inactive_bound {Cs α δ : ℝ} (b : ι → ErrorPiece Cs) (hCs : 0 ≤ Cs)
    (hα : α ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {L : ℝ≥0} {F : ℂ → ℂ} (hF : LipschitzWith L F) {D : Set ℂ} (hD : MeasurableSet D)
    (hFb : ∀ y, ‖F y‖ ≤ 1) (hFD : ∀ y, F y ≠ 0 → y ∈ D) (x z : ℂ)
    (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3) :
    ‖∑ d, ∫ y, correction x z y*F y*(b d).density y‖ ≤
      7*coarseMass b δ D+((L : ℝ)+2*(3*(L : ℝ)+1))*Cs*δ^(2*(1-α))*errorPrice b α := by
  have hnorm : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ (3 : ℝ) := fun y hy => hD3 y (hFD y hy)
  have hH : ‖(star (z-x))⁻¹‖ ≤ (2 : ℝ) := by
    rw [norm_inv, norm_star]
    have hn : 0 < ‖z-x‖ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ hn]
    linarith
  have hcorr : LipschitzWith (L+2*(3*L+1)) (fun y => correction x z y*F y) :=
    corrected_lipschitz (M := 1) (R := 3) (H := 2) hF hFb x z hnorm hH
  exact increment_bound_general b hCs hα hδ hδ1 hcorr hD (correction_kernel_bound hFb x z hz hnorm)
    (fun y hy => hFD y (fun h => hy (by rw [h,mul_zero])))

end LocalCancellation

/-- A finite last-active-index induction. Its hypotheses are local gaps, not
an assumed global estimate, and no infinite list of active indices is chosen. -/
lemma last_active_bound (active : ℕ → Prop) (N a : ℕ → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hfirst : ∀ n, (∀ i < n, ¬active i) → N n ≤ B+∑ i ∈ Finset.range n, a i)
    (hgap : ∀ j n, j < n → active j → (∀ i, j < i → i < n → ¬active i) →
      N n ≤ N j+a j) : ∀ n, N n ≤ B+∑ i ∈ Finset.range n, a i := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let S := (Finset.range n).filter active
    by_cases hS : S.Nonempty
    · let j := S.max' hS
      have hjmem : j ∈ S := Finset.max'_mem S hS
      have hjn : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
      have hjact : active j := (Finset.mem_filter.mp hjmem).2
      have hng : ∀ i, j < i → i < n → ¬active i := by
        intro i hji hin hi
        have his : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin,hi⟩
        exact (not_lt_of_ge (Finset.le_max' S i his)) hji
      have hh := hgap j n hjn hjact hng
      have hb := ih j hjn
      have hs : (∑ i ∈ Finset.range (j+1), a i) ≤ ∑ i ∈ Finset.range n, a i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_of_lt hjn)) (fun i _ _ => ha i)
      rw [Finset.sum_range_succ] at hs
      linarith
    · apply hfirst n
      intro i hi hai
      exact hS ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hai⟩⟩

lemma last_active_limit (active : ℕ → Prop) (N a : ℕ → ℝ) (B Z : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsm : Summable a) (hN : Tendsto N atTop (𝓝 Z))
    (hfirst : ∀ n, (∀ i < n, ¬active i) → N n ≤ B+∑ i ∈ Finset.range n, a i)
    (hgap : ∀ j n, j < n → active j → (∀ i, j < i → i < n → ¬active i) →
      N n ≤ N j+a j) : Z ≤ B+∑' i, a i := by
  apply le_of_tendsto hN
  filter_upwards with n
  exact (last_active_bound active N a B ha hfirst hgap n).trans
    (add_le_add le_rfl (hsm.sum_le_tsum (Finset.range n) (fun i _ => ha i)))

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales

lemma real_weight_integrable {a : ℂ → ℂ} (ha : Integrable a) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) :
    Integrable (fun y => (K y : ℂ)*a y) :=
  integrable_bounded_pairing ha (Complex.continuous_ofReal.comp_aestronglyMeasurable hK)
    (fun y => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hK0 y)]; exact hK1 y)

lemma real_weight_norm_integrable {a : ℂ → ℂ} (ha : Integrable a) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) :
    Integrable (fun y => K y*‖a y‖) :=
  ha.norm.bdd_mul hK (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hK0 y)]; exact hK1 y)

lemma convex_pairing {a : ℂ → ℂ} {K L : ℂ → ℝ}
    (hiK : Integrable (fun y => (K y : ℂ)*a y))
    (hiL : Integrable (fun y => (L y : ℂ)*a y)) (θ : ℝ) :
    (∫ y, ((θ*K y+(1-θ)*L y : ℝ) : ℂ)*a y) =
      θ • (∫ y, (K y : ℂ)*a y)+(1-θ) • (∫ y, (L y : ℂ)*a y) := by
  have he : (fun y => ((θ*K y+(1-θ)*L y : ℝ) : ℂ)*a y) =
      (fun y => θ • ((K y : ℂ)*a y)+(1-θ) • ((L y : ℂ)*a y)) := by
    ext y
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.real_smul]
    ring
  rw [he]
  calc
    _ = (∫ y, θ • ((K y : ℂ)*a y))+(∫ y, (1-θ) • ((L y : ℂ)*a y)) :=
      integral_add (hiK.smul θ) (hiL.smul (1-θ))
    _ = _ := by rw [integral_smul,integral_smul]

/-- Analytic comparison of two balanced mixtures at a negative later
projection. The only error term is their fixed-correction difference. -/
lemma negative_gap_cap {e : ℂ} {κ B ρ H : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    {K L : ℂ → ℝ} (hK : AEStronglyMeasurable K) (hL : AEStronglyMeasurable L)
    (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1)
    (hL0 : ∀ y, 0 ≤ L y) (hL1 : ∀ y, L y ≤ 1)
    {D : Set ℂ} (hD : MeasurableSet D) (hsupp : ∀ y, L y-K y ≠ 0 → y ∈ D)
    (x z : ℂ) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) (hD3 : ∀ y ∈ D, ‖y-x‖ ≤ 3)
    (hcap : (∫ y in D \ Metric.ball z ρ, ‖a.density y‖) ≤ H)
    {p q R : ℂ} (hp : ‖p‖ ≤ B) (hq : ‖q‖ ≤ B)
    (hneg : inner ℝ e ((∫ y, (L y : ℂ)*a.density y)+q) < 0)
    (hcor : ((∫ y, (L y : ℂ)*a.density y)+q)-((∫ y, (K y : ℂ)*a.density y)+p) =
      (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y)+R) :
    max 0 (-inner ℝ e ((∫ y, (L y : ℂ)*a.density y)+q)) ≤
      max 0 (-inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p))+
        4*ρ*(B/κ)+7*H+‖R‖ := by
  let P := (∫ y, (K y : ℂ)*a.density y)+p
  let Q := (∫ y, (L y : ℂ)*a.density y)+q
  obtain ⟨θ,hθ0,hθ1,hθneg,hθeq⟩ := crossing_interpolation e P Q hneg
  let J (y : ℂ) := θ*K y+(1-θ)*L y
  have hJ0 (y : ℂ) : 0 ≤ J y := add_nonneg (mul_nonneg hθ0 (hK0 y)) (mul_nonneg (sub_nonneg.mpr hθ1) (hL0 y))
  have hJ1 (y : ℂ) : J y ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left (hK1 y) hθ0
    have h2 := mul_le_mul_of_nonneg_left (hL1 y) (sub_nonneg.mpr hθ1)
    dsimp [J]
    nlinarith
  have hJ : AEStronglyMeasurable J := (hK.const_mul θ).add (hL.const_mul (1-θ))
  have hiK := real_weight_integrable a.integrable hK hK0 hK1
  have hiL := real_weight_integrable a.integrable hL hL0 hL1
  let pstar := θ • p+(1-θ) • q
  have hpstar : ‖pstar‖ ≤ B := by
    calc
      ‖pstar‖ ≤ ‖θ • p‖+‖(1-θ) • q‖ := norm_add_le _ _
      _ = θ*‖p‖+(1-θ)*‖q‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg hθ0,abs_of_nonneg (sub_nonneg.mpr hθ1)]
      _ ≤ θ*B+(1-θ)*B := add_le_add (mul_le_mul_of_nonneg_left hp hθ0)
        (mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hθ1))
      _ = B := by ring
  have hstar : (∫ y, (J y : ℂ)*a.density y)+pstar = θ • P+(1-θ) • Q := by
    rw [show (∫ y, (J y : ℂ)*a.density y) = _ from convex_pairing hiK hiL θ]
    dsimp [P,Q,pstar]
    ring
  have hsmass := cone_mass_of_nonpositive a he hκ hJ hJ0 hJ1
    (show inner ℝ e ((∫ y, (J y : ℂ)*a.density y)+pstar) ≤ 0 by rw [hstar]; exact hθneg)
  have hlmass := cone_mass_of_nonpositive a he hκ hL hL0 hL1 hneg.le
  have hweighted : (∫ y, (L y+J y)*‖a.density y‖) ≤ 2*(B/κ) := by
    have hiLn := real_weight_norm_integrable a.integrable hL hL0 hL1
    have hiJn := real_weight_norm_integrable a.integrable hJ hJ0 hJ1
    simp_rw [add_mul]
    rw [integral_add hiLn hiJn]
    have hs := hsmass.trans (div_le_div_of_nonneg_right hpstar hκ.le)
    have hl := hlmass.trans (div_le_div_of_nonneg_right hq hκ.le)
    linarith
  have hJdiff (y : ℂ) : L y-J y = θ*(L y-K y) := by dsimp [J]; ring
  have hJDs : ∀ y, L y-J y ≠ 0 → y ∈ D := by
    intro y hy
    apply hsupp y
    intro h
    exact hy (by rw [hJdiff,h,mul_zero])
  let G := ∫ y, correction x z y*((L y : ℂ)-J y)*a.density y
  have hG : ‖G‖ ≤ 4*ρ*(B/κ)+7*H := by
    have hh := cone_corrected_cap a.integrable hJ hL hJ0 hJ1 hL0 hL1 hD hJDs x z hρ hz hD3
    change ‖G‖ ≤ _ at hh
    have hg := mul_le_mul_of_nonneg_left hweighted (by positivity : 0 ≤ 2*ρ)
    have hc := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 7)
    nlinarith
  have hGid : G = θ • (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with y
    change correction x z y*((L y : ℂ)-(θ*K y+(1-θ)*L y : ℝ))*a.density y =
      θ • (correction x z y*((L y : ℂ)-K y)*a.density y)
    simp only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.real_smul]
    ring
  have hdiff : Q-(θ • P+(1-θ) • Q) = G+θ • R := by
    have hh : Q-P = (∫ y, correction x z y*((L y : ℂ)-K y)*a.density y)+R := hcor
    rw [hGid, ← smul_add, ← hh]
    simp only [sub_smul,one_smul,smul_sub]
    abel
  have hR : ‖θ • R‖ ≤ ‖R‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hθ0]
    exact mul_le_of_le_one_left (norm_nonneg _) hθ1
  have hn := negative_projection_change e (θ • P+(1-θ) • Q) Q he
  rw [hθeq,hdiff] at hn
  have hh := (norm_add_le G (θ • R)).trans (add_le_add hG hR)
  change max 0 (-inner ℝ e Q) ≤ max 0 (-inner ℝ e P)+4*ρ*(B/κ)+7*H+‖R‖
  linarith

end LocalCancellation

namespace LocalCancellation
open DiskKernels DiskGeometry DiskScales

lemma cone_negative_le_error {e : ℂ} {κ : ℝ} (a : ConeDensity e κ)
    (he : ‖e‖ = 1) (hκ : 0 ≤ κ) {K : ℂ → ℝ}
    (hK : AEStronglyMeasurable K) (hK0 : ∀ y, 0 ≤ K y) (hK1 : ∀ y, K y ≤ 1) (p : ℂ) :
    max 0 (-inner ℝ e ((∫ y, (K y : ℂ)*a.density y)+p)) ≤ ‖p‖ := by
  have hh := cone_pairing a hK hK0 hK1
  have hi : 0 ≤ ∫ y, K y*‖a.density y‖ := integral_nonneg (fun y => mul_nonneg (hK0 y) (norm_nonneg _))
  have hproj : 0 ≤ inner ℝ e (∫ y, (K y : ℂ)*a.density y) := (mul_nonneg hκ hi).trans hh
  rw [inner_add_right]
  exact max_le (norm_nonneg _) (by linarith [(abs_le.mp (inner_unit_bound (p := p) he)).1])

lemma general_moment_integrable {a : ℂ → ℂ} (ha : Integrable a)
    {r δ : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x : ℂ) (hr : r+δ ≤ 3) :
    Integrable (fun y => star (y-x)*(kernel k x y : ℂ)*a y) := by
  apply integrable_bounded_pairing ha
    ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
      (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply position_bound (complex_kernel_bound k x) x (by norm_num : (0 : ℝ) ≤ 3)
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh, Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball, dist_eq_norm] using hyb).le.trans hr

lemma correcting_pairing {a F : ℂ → ℂ} (ha : Integrable a)
    (hF : AEStronglyMeasurable F) (hFb : ∀ y, ‖F y‖ ≤ 1) (x z : ℂ)
    (hsupp : ∀ y, F y ≠ 0 → ‖y-x‖ ≤ 3) :
    (∫ y, correction x z y*F y*a y) = (∫ y, F y*a y) -
      (star (z-x))⁻¹*(∫ y, star (y-x)*F y*a y) := by
  have hi := integrable_bounded_pairing ha hF hFb
  have him : Integrable (fun y => star (y-x)*F y*a y) :=
    integrable_bounded_pairing ha
      ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).aestronglyMeasurable.mul hF)
      (position_bound hFb x (by norm_num : (0 : ℝ) ≤ 3) hsupp)
  have he : (fun y => correction x z y*F y*a y) =
      fun y => F y*a y-(star (z-x))⁻¹*(star (y-x)*F y*a y) := by
    ext y
    simp only [correction,div_eq_mul_inv]
    ring
  rw [he,integral_sub hi (him.const_mul _),integral_const_mul]

lemma general_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {u v u' v' : ℝ} {M N : ℝ≥0} (k : RadiusDensity u v M) (l : RadiusDensity u' v' N) (x : ℂ) :
    (∫ y, (kernel l x y : ℂ)*a y)-(∫ y, (kernel k x y : ℂ)*a y) =
      ∫ y, ((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub
    (integrable_bounded_pairing ha (complex_kernel_lipschitz l x).continuous.aestronglyMeasurable (complex_kernel_bound l x))
    (integrable_bounded_pairing ha (complex_kernel_lipschitz k x).continuous.aestronglyMeasurable (complex_kernel_bound k x))]
  congr 1
  ext y
  ring

lemma corrected_kernel_integrable {a : ℂ → ℂ} (ha : Integrable a)
    {r δ : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M) (x z : ℂ)
    (hr : r+δ ≤ 3) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) :
    Integrable (fun y => correction x z y*(kernel k x y : ℂ)*a y) := by
  apply integrable_bounded_pairing ha
    ((by unfold correction; fun_prop : Continuous (correction x z)).mul (complex_kernel_lipschitz k x).continuous).aestronglyMeasurable
  apply correction_kernel_bound (complex_kernel_bound k x) x z hz
  intro y hy
  have hyb : y ∈ Metric.ball x (r+δ) := by
    by_contra hh
    exact hy (by rw [kernel_zero k x hh,Complex.ofReal_zero])
  exact (show ‖y-x‖ < r+δ by simpa only [Metric.mem_ball,dist_eq_norm] using hyb).le.trans hr

lemma corrected_kernel_pairing_sub {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M N : ℝ≥0} (k : RadiusDensity (r-δ) (r+δ) M)
    (l : RadiusDensity (r-ε) (r+ε) N) (x z : ℂ)
    (hrδ : r+δ ≤ 3) (hrε : r+ε ≤ 3) (hz : (1 : ℝ)/2 ≤ ‖z-x‖) :
    (∫ y, correction x z y*(kernel l x y : ℂ)*a y)-
      (∫ y, correction x z y*(kernel k x y : ℂ)*a y) =
      ∫ y, correction x z y*((kernel l x y : ℂ)-kernel k x y)*a y := by
  rw [← integral_sub (corrected_kernel_integrable ha l x z hrε hz)
    (corrected_kernel_integrable ha k x z hrδ hz)]
  congr 1
  ext y
  ring

lemma interior_mass_le_kernel {a : ℂ → ℂ} (ha : Integrable a)
    {r δ ε : ℝ} {M : ℝ≥0} (k : RadiusDensity (r-ε) (r+ε) M) (x : ℂ) (hεδ : ε ≤ δ) :
    (∫ y in Metric.ball x (r-δ), ‖a y‖) ≤ ∫ y, kernel k x y*‖a y‖ := by
  rw [← integral_indicator measurableSet_ball]
  apply integral_mono_ae (ha.norm.indicator measurableSet_ball)
    (ha.norm.bdd_mul (kernel_lipschitz k x).continuous.aestronglyMeasurable
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (kernel_nonneg k x y)]; exact kernel_le_one k x y)))
  filter_upwards with y
  by_cases hy : y ∈ Metric.ball x (r-δ)
  · have hk : kernel k x y = 1 := kernel_one k x (by
      simp only [Metric.mem_ball] at hy ⊢
      linarith)
    simp only [indicator_of_mem hy,hk,one_mul,le_refl]
  · simp only [indicator_of_notMem hy]
    exact mul_nonneg (kernel_nonneg k x y) (norm_nonneg _)

end LocalCancellation

end

end OAI
