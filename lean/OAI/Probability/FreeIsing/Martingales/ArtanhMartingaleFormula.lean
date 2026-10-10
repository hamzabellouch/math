import OAI.Probability.FreeIsing.Cavity.BaseMoments
import OAI.Probability.FreeIsing.Estimates.ArtanhTaylor
import OAI.Probability.FreeIsing.Estimates.WeightedPrimitiveApproximation
import OAI.Probability.FreeIsing.Martingales.BoundedMartingaleVariation
import OAI.Probability.FreeIsing.Martingales.QuadraticVariation
import OAI.Probability.FreeIsing.Martingales.TaylorRemainder
import OAI.Probability.FreeIsing.Martingales.TransformL2
import OAI.Probability.FreeIsing.Stochastic.CompensatorVariation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.ArtanhMartingaleFormula

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def firstWeight (x : ℝ) : ℝ := 1 / (1 - x ^ 2)
def secondWeight (x : ℝ) : ℝ := x / (1 - x ^ 2) ^ 2

def linearSum {I : Type*} (M : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, firstWeight (M (t i) ω) * (M (t (i + 1)) ω - M (t i) ω)

def quadraticSum {I : Type*} (M : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, secondWeight (M (t i) ω) * (M (t (i + 1)) ω - M (t i) ω) ^ 2

def compensatorSum {I : Type*} (M A : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, secondWeight (M (t i) ω) * (A (t (i + 1)) ω - A (t i) ω)

lemma firstWeight_bound {r x : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hx : |x| ≤ r) :
    |firstWeight x| ≤ 1 / (1 - r ^ 2) := by
  have hsq : x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr0).2 hx
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  have hdx : 0 < 1 - x ^ 2 := by linarith
  rw [firstWeight, abs_of_pos (div_pos zero_lt_one hdx)]
  exact one_div_le_one_div_of_le hd (by linarith)

lemma secondWeight_bound {r x : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (hx : |x| ≤ r) :
    |secondWeight x| ≤ r / (1 - r ^ 2) ^ 2 := by
  have hsq : x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hr0).2 hx
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  simp only [secondWeight, abs_div, abs_pow, sq_abs]
  calc
    |x| / (1 - x ^ 2) ^ 2 ≤ r / (1 - x ^ 2) ^ 2 := by gcongr
    _ ≤ r / (1 - r ^ 2) ^ 2 := by gcongr

omit mΩ in
lemma stronglyMeasurable_firstWeight {m : MeasurableSpace Ω} {X : Ω → ℝ}
    (hX : StronglyMeasurable[m] X) :
    StronglyMeasurable[m] (fun ω => firstWeight (X ω)) :=
  stronglyMeasurable_const.div (stronglyMeasurable_const.sub (hX.pow 2))

omit mΩ in
lemma stronglyMeasurable_secondWeight {m : MeasurableSpace Ω} {X : Ω → ℝ}
    (hX : StronglyMeasurable[m] X) :
    StronglyMeasurable[m] (fun ω => secondWeight (X ω)) :=
  hX.div ((stronglyMeasurable_const.sub (hX.pow 2)).pow 2)

theorem tendsto_integral_abs_zero_of_sq [IsProbabilityMeasure μ]
    (E : ℕ → Ω → ℝ) (hE : ∀ n, MemLp (E n) 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, E n ω ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |E n ω| ∂μ) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
    (fun n => integral_abs_le_sqrt_integral_sq (hE n).aestronglyMeasurable.aemeasurable
      (hE n).integrable_sq) ?_
  simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hlim

omit mΩ in
theorem taylor_identity {I : Type*} (M : I → Ω → ℝ) (t : ℕ → I) (N : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range N, ArtanhTaylor.remainder (M (t i) ω) (M (t (i + 1)) ω)) =
      Real.artanh (M (t N) ω) - Real.artanh (M (t 0) ω) -
        linearSum M t N ω - quadraticSum M t N ω := by
  have hfirst : (∑ i ∈ Finset.range N,
      (M (t (i + 1)) ω - M (t i) ω) / (1 - M (t i) ω ^ 2)) = linearSum M t N ω := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [firstWeight, div_eq_mul_inv]
    ring
  have hsecond : (∑ i ∈ Finset.range N,
      M (t i) ω * (M (t (i + 1)) ω - M (t i) ω) ^ 2 / (1 - M (t i) ω ^ 2) ^ 2) =
      quadraticSum M t N ω := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [secondWeight, div_eq_mul_inv]
    ring
  rw [ArtanhTaylor.sum_remainder, hfirst, hsecond]

omit mΩ in
theorem quadratic_sub_compensator {I : Type*} (M A : I → Ω → ℝ)
    (t : ℕ → I) (N : ℕ) (ω : Ω) :
    quadraticSum M t N ω - compensatorSum M A t N ω =
      ∑ i ∈ Finset.range N, secondWeight (M (t i) ω) *
        MartingaleQuadraticVariation.squareError M A (t i) (t (i + 1)) ω := by
  rw [quadraticSum, compensatorSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [MartingaleQuadraticVariation.squareError, MartingaleQuadraticVariation.increment]
  ring

lemma tendsto_L1_of_intermediate {U V : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hU : ∀ n, Integrable (U n) μ) (hV : ∀ n, Integrable (V n) μ)
    (hY : Integrable Y μ)
    (huv : Tendsto (fun n => ∫ ω, |U n ω - V n ω| ∂μ) atTop (𝓝 0))
    (hvy : Tendsto (fun n => ∫ ω, |V n ω - Y ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |U n ω - Y ω| ∂μ) atTop (𝓝 0) := by
  have hlim := huv.add hvy
  simp only [zero_add] at hlim
  refine squeeze_zero (fun n => integral_nonneg (fun _ => abs_nonneg _)) (fun n => ?_) hlim
  have h1 : Integrable (fun ω => |U n ω - V n ω|) μ := ((hU n).sub (hV n)).abs
  have h2 : Integrable (fun ω => |V n ω - Y ω|) μ := ((hV n).sub hY).abs
  calc
    _ ≤ ∫ ω, |U n ω - V n ω| + |V n ω - Y ω| ∂μ := by
      apply integral_mono ((hU n).sub hY).abs (h1.add h2)
      intro ω
      simpa only [Pi.sub_apply, Pi.add_apply] using abs_sub_le (U n ω) (V n ω) (Y ω)
    _ = _ := integral_add h1 h2

theorem artanh_eq_of_cubic_and_compensated_limits [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    {s T : I} (hstart : ∀ n, t n 0 = s) (hend : ∀ n, t n (N n) = T)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ u, ∀ᵐ ω ∂μ, |M u ω| ≤ r)
    (hD4 : ∀ n i, MemLp (fun ω => (M (t n (i + 1)) ω - M (t n i) ω) ^ 2) 2 μ)
    (hA2 : ∀ n i, MemLp (fun ω => A (t n (i + 1)) ω - A (t n i) ω) 2 μ)
    (hsmall : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ)) atTop (𝓝 0))
    (hthird : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ) atTop (𝓝 0))
    {L V : Ω → ℝ} (hL : Integrable L μ) (hV : Integrable V μ)
    (hlinear : Tendsto (fun n => ∫ ω, |linearSum M (t n) (N n) ω - L ω| ∂μ)
      atTop (𝓝 0))
    (hcompensator : Tendsto (fun n => ∫ ω,
      |compensatorSum M A (t n) (N n) ω - V ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) =ᵐ[μ]
      fun ω => L ω + V ω := by
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  have hfirst (n i : ℕ) : StronglyMeasurable[F (t n i)]
      (fun ω => firstWeight (M (t n i) ω)) :=
    stronglyMeasurable_firstWeight (hM.stronglyMeasurable _)
  have hsecond (n i : ℕ) : StronglyMeasurable[F (t n i)]
      (fun ω => secondWeight (M (t n i) ω)) :=
    stronglyMeasurable_secondWeight (hM.stronglyMeasurable _)
  have hbfirst (n i : ℕ) : ∀ᵐ ω ∂μ,
      |firstWeight (M (t n i) ω)| ≤ 1 / (1 - r ^ 2) :=
    (hbound _).mono (fun ω hω => firstWeight_bound hr0 hr hω)
  have hbsecond (n i : ℕ) : ∀ᵐ ω ∂μ,
      |secondWeight (M (t n i) ω)| ≤ r / (1 - r ^ 2) ^ 2 :=
    (hbound _).mono (fun ω hω => secondWeight_bound hr0 hr hω)
  have hfirstTop (n i : ℕ) : MemLp (fun ω => firstWeight (M (t n i) ω)) ⊤ μ :=
    memLp_top_of_bound ((hfirst n i).mono (F.le _)).aestronglyMeasurable _
      (by simpa only [Real.norm_eq_abs] using hbfirst n i)
  have hsecondTop (n i : ℕ) : MemLp (fun ω => secondWeight (M (t n i) ω)) ⊤ μ :=
    memLp_top_of_bound ((hsecond n i).mono (F.le _)).aestronglyMeasurable _
      (by simpa only [Real.norm_eq_abs] using hbsecond n i)
  have hLin2 (n : ℕ) : MemLp (linearSum M (t n) (N n)) 2 μ :=
    memLp_finsetSum _ (fun i _ => (hfirstTop n i).fun_mul ((hM2 _).sub (hM2 _)))
  have hQuad2 (n : ℕ) : MemLp (quadraticSum M (t n) (N n)) 2 μ :=
    memLp_finsetSum _ (fun i _ => (hsecondTop n i).fun_mul (hD4 n i))
  have hComp2 (n : ℕ) : MemLp (compensatorSum M A (t n) (N n)) 2 μ :=
    memLp_finsetSum _ (fun i _ => (hsecondTop n i).fun_mul (hA2 n i))
  have hErrSq : Tendsto (fun n => ∫ ω,
      (quadraticSum M (t n) (N n) ω - compensatorSum M A (t n) (N n) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have hh := MartingaleQuadraticVariation.tendsto_integral_grid_weighted_error_sq
      hM hQ hM2 t ht (fun n i ω => secondWeight (M (t n i) ω)) hsecond hD4 hA2
      (by positivity : 0 ≤ r / (1 - r ^ 2) ^ 2) hbsecond
      (fun n => Finset.range (N n)) hsmall
    simpa only [quadratic_sub_compensator] using hh
  have hErr := tendsto_integral_abs_zero_of_sq
    (fun n ω => quadraticSum M (t n) (N n) ω - compensatorSum M A (t n) (N n) ω)
    (fun n => (hQuad2 n).sub (hComp2 n)) hErrSq
  have hQuadLimit := tendsto_L1_of_intermediate
    (fun n => (hQuad2 n).integrable (by norm_num))
    (fun n => (hComp2 n).integrable (by norm_num)) hV hErr hcompensator
  have hm (n i : ℕ) : Measurable (M (t n i)) :=
    ((hM.stronglyMeasurable _).mono (F.le _)).measurable
  have hloc (n : ℕ) : ∀ᵐ ω ∂μ, ∀ i ≤ N n, |M (t n i) ω| ≤ r := by
    filter_upwards [ae_all_iff.2 (fun i => hbound (t n i))] with ω hω
    exact fun i _ => hω i
  have hcube (n i : ℕ) : Integrable (fun ω => |M (t n (i + 1)) ω - M (t n i) ω| ^ 3) μ :=
    ArtanhTaylor.integrable_cube_of_localized (hm n i) (hm n (i + 1)) (hbound _) (hbound _)
  have hRint (n : ℕ) := (ArtanhTaylor.integrable_sum_remainder_and_bound hr
    (fun i => M (t n i)) (N n) (hm n) (hloc n) (fun i _ => hcube n i)).1
  have hRlim := ArtanhTaylor.tendsto_integral_abs_sum_remainder hr
    (fun n i => M (t n i)) N hm hloc hthird
  have hY : Integrable (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) μ := by
    have hi := ((hRint 0).add ((hLin2 0).integrable (by norm_num))).add
      ((hQuad2 0).integrable (by norm_num))
    apply hi.congr
    filter_upwards [] with ω
    have he := taylor_identity M (t 0) (N 0) ω
    rw [hstart 0, hend 0] at he
    simp only [Pi.add_apply]
    linarith
  apply MartingaleTaylorRemainder.ae_eq_add_of_taylor_L1_limits hY hL hV
    (fun n => (hLin2 n).integrable (by norm_num))
    (fun n => (hQuad2 n).integrable (by norm_num)) _ hlinear hQuadLimit
  simpa only [taylor_identity, hstart, hend] using hRlim

theorem integral_grid_square_sum_le [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M : I → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ u, MemLp (M u) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (N : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ᵐ ω ∂μ, |M (t N) ω| ≤ r) :
    (∫ ω, ∑ i ∈ Finset.range N, (M (t (i + 1)) ω - M (t i) ω) ^ 2 ∂μ) ≤ r ^ 2 := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨fun i => hM.stronglyMeasurable _, fun _ _ hij => hM.condExp_ae_eq (ht hij)⟩
  calc
    _ = ∑ i ∈ Finset.range N, ∫ ω, (M (t (i + 1)) ω - M (t i) ω) ^ 2 ∂μ :=
      integral_finsetSum _ (fun i _ => ((hM2 _).sub (hM2 _)).integrable_sq)
    _ = ∫ ω, (M (t N) ω - M (t 0) ω) ^ 2 ∂μ :=
      MartingaleTransformL2.sum_integral_sq_increment hMG (fun i => hM2 _) N
    _ ≤ ∫ ω, M (t N) ω ^ 2 ∂μ :=
      MartingaleTransformL2.integral_sq_increment_le hM (ht (Nat.zero_le N)) (hM2 _) (hM2 _)
    _ ≤ ∫ _ : Ω, r ^ 2 ∂μ := by
      apply integral_mono_ae (hM2 _).integrable_sq (integrable_const _)
      filter_upwards [hbound] with ω hω
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).2 hω
    _ = r ^ 2 := by simp

theorem artanh_eq_of_compensated_sum_limits [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    {s T : I} (hstart : ∀ n, t n 0 = s) (hend : ∀ n, t n (N n) = T)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ u, ∀ᵐ ω ∂μ, |M u ω| ≤ r)
    (hA2 : ∀ n i, MemLp (fun ω => A (t n (i + 1)) ω - A (t n i) ω) 2 μ)
    (hsmall : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ)) atTop (𝓝 0))
    {L V : Ω → ℝ} (hL : Integrable L μ) (hV : Integrable V μ)
    (hlinear : Tendsto (fun n => ∫ ω, |linearSum M (t n) (N n) ω - L ω| ∂μ)
      atTop (𝓝 0))
    (hcompensator : Tendsto (fun n => ∫ ω,
      |compensatorSum M A (t n) (N n) ω - V ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) =ᵐ[μ]
      fun ω => L ω + V ω := by
  have hm (u : I) : StronglyMeasurable (M u) := (hM.stronglyMeasurable u).mono (F.le u)
  have hM2 (u : I) : MemLp (M u) 2 μ :=
    MemLp.of_bound (hm u).aestronglyMeasurable r
      (by simpa only [Real.norm_eq_abs] using hbound u)
  have hD4 (n i : ℕ) : MemLp (fun ω => (M (t n (i + 1)) ω - M (t n i) ω) ^ 2) 2 μ := by
    apply MemLp.of_bound (((hm _).sub (hm _)).pow 2).aestronglyMeasurable ((2 * r) ^ 2)
    filter_upwards [hbound (t n i), hbound (t n (i + 1))] with ω hs ht
    have hd : |M (t n (i + 1)) ω - M (t n i) ω| ≤ 2 * r :=
      (abs_sub _ _).trans (by linarith)
    simpa only [Pi.pow_apply, Pi.sub_apply, Real.norm_eq_abs, abs_pow, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * r)).2 hd
  have h4 (n i : ℕ) : Integrable (fun ω => (M (t n (i + 1)) ω - M (t n i) ω) ^ 4) μ := by
    simpa only [← pow_mul] using (hD4 n i).integrable_sq
  have hfourth : Tendsto (fun n => ∫ ω, ∑ i ∈ Finset.range (N n),
      (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => integral_nonneg (fun ω => Finset.sum_nonneg
      (fun i _ => by positivity))) (fun n => ?_) hsmall
    rw [integral_finsetSum _ (fun i _ => h4 n i)]
    apply Finset.sum_le_sum
    intro i _
    exact le_add_of_nonneg_right (integral_nonneg (fun ω => sq_nonneg _))
  have hthirdInt := MartingaleTaylorRemainder.tendsto_integral_sum_abs_cube_zero
    (fun n => Finset.range (N n))
    (fun n i ω => M (t n (i + 1)) ω - M (t n i) ω)
    (fun n i _ => ((hm _).sub (hm _)).aestronglyMeasurable)
    (fun n i _ => ((hM2 _).sub (hM2 _)).integrable_sq)
    (fun n i _ => h4 n i) (sq_nonneg r)
    (fun n => integral_grid_square_sum_le hM hM2 (t n) (ht n) (N n) hr0 (hbound _)) hfourth
  have hthird : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫ ω, ∑ i ∈ Finset.range (N n),
        |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ) =
        ∑ i ∈ Finset.range (N n), ∫ ω, |M (t n (i + 1)) ω - M (t n i) ω| ^ 3 ∂μ :=
      integral_finsetSum _ (fun i _ => ArtanhTaylor.integrable_cube_of_localized
        (hm _).measurable (hm _).measurable (hbound _) (hbound _))
    simpa only [he] using hthirdInt
  exact artanh_eq_of_cubic_and_compensated_limits hM hQ hM2 t ht N hstart hend
    hr0 hr hbound hD4 hA2 hsmall hthird hL hV hlinear hcompensator

theorem artanh_eq_of_continuous_compensated_limits [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    {s T : I} (hstart : ∀ n, t n 0 = s) (hend : ∀ n, t n (N n) = T)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ u, ∀ᵐ ω ∂μ, |M u ω| ≤ r)
    {K : Set I} (hK : IsCompact K)
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun u => M u ω) K)
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun u => A u ω) K)
    (hmem : ∀ n i, i ≤ N n → t n i ∈ K)
    (mesh : ℕ → ℝ) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hdist : ∀ n i, i < N n → dist (t n i) (t n (i + 1)) ≤ mesh n)
    (hpos : ∀ᵐ ω ∂μ, ∀ n i, i < N n → 0 ≤ A (t n (i + 1)) ω - A (t n i) ω)
    {C : ℝ} (hC : 0 ≤ C)
    (htotal : ∀ᵐ ω ∂μ, ∀ n, A (t n (N n)) ω - A (t n 0) ω ≤ C)
    {L V : Ω → ℝ} (hL : Integrable L μ) (hV : Integrable V μ)
    (hlinear : Tendsto (fun n => ∫ ω, |linearSum M (t n) (N n) ω - L ω| ∂μ)
      atTop (𝓝 0))
    (hcompensator : Tendsto (fun n => ∫ ω,
      |compensatorSum M A (t n) (N n) ω - V ω| ∂μ) atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M s ω)) =ᵐ[μ]
      fun ω => L ω + V ω := by
  have hfour := BoundedMartingaleVariation.tendsto_sum_integral_fourth_of_continuous
    hM hr0 hbound hK hcM t ht N hmem mesh hmesh
    (fun n i hi => by simpa only [dist_comm] using hdist n i hi)
  have hAm (u : I) : AEStronglyMeasurable (A u) μ :=
    ((MartingaleQuadraticVariation.stronglyAdapted_compensator hM hQ u).mono
      (F.le u)).aestronglyMeasurable
  have hcomp := CompensatorVariation.tendsto_sum_integral_sq_increments hK hAm hcA
    t N mesh hmem hdist hmesh hpos hC htotal
  have hsmall : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa only [Finset.sum_add_distrib, zero_add] using hfour.add hcomp
  let u : ℕ → ℕ → I := fun n i => t n (min i (N n))
  have hu (n i : ℕ) (hi : i ≤ N n) : u n i = t n i := by simp only [u, min_eq_left hi]
  have huend (n i : ℕ) (hi : N n ≤ i) : u n i = t n (N n) := by simp only [u, min_eq_right hi]
  have humo (n : ℕ) : Monotone (u n) :=
    fun i j hij => ht n (min_le_min_right (N n) hij)
  have hustart (n : ℕ) : u n 0 = s := by rw [hu n 0 (Nat.zero_le _), hstart]
  have huendT (n : ℕ) : u n (N n) = T := by rw [hu n (N n) le_rfl, hend]
  have hA2 (n i : ℕ) : MemLp (fun ω => A (u n (i + 1)) ω - A (u n i) ω) 2 μ := by
    by_cases hi : i < N n
    · rw [hu n i hi.le, hu n (i + 1) hi]
      exact CompensatorVariation.memLp_increment_of_total_bound (fun j => hAm (t n j))
        (hpos.mono (fun ω hω => hω n)) (htotal.mono (fun ω hω => hω n)) hi 2
    · have hNi := Nat.le_of_not_gt hi
      simp only [huend n i hNi, huend n (i + 1) (hNi.trans (Nat.le_succ i)), sub_self]
      exact MemLp.zero
  have henergy (n : ℕ) : (∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (u n (i + 1)) ω - M (u n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (u n (i + 1)) ω - A (u n i) ω) ^ 2 ∂μ)) =
      ∑ i ∈ Finset.range (N n),
      ((∫ ω, (M (t n (i + 1)) ω - M (t n i) ω) ^ 4 ∂μ) +
        ∫ ω, (A (t n (i + 1)) ω - A (t n i) ω) ^ 2 ∂μ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hu n i hi'.le, hu n (i + 1) hi']
  have hlinEq (n : ℕ) (ω : Ω) : linearSum M (u n) (N n) ω = linearSum M (t n) (N n) ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hu n i hi'.le, hu n (i + 1) hi']
  have hcompEq (n : ℕ) (ω : Ω) :
      compensatorSum M A (u n) (N n) ω = compensatorSum M A (t n) (N n) ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hu n i hi'.le, hu n (i + 1) hi']
  exact artanh_eq_of_compensated_sum_limits hM hQ u humo N hustart huendT hr0 hr hbound hA2
    (by simpa only [henergy] using hsmall) hL hV
    (by simpa only [hlinEq] using hlinear) (by simpa only [hcompEq] using hcompensator)

theorem artanh_eq_stochasticLimit_add_integral [IsProbabilityMeasure μ]
    {F : Filtration ℝ mΩ} {M A a : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hMm : Measurable (fun p : ℝ × Ω => M p.1 p.2))
    (hcM : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) (Set.Icc 0 T))
    (hcA : ∀ᵐ ω ∂μ, ContinuousOn (fun t => A t ω) (Set.Icc 0 T))
    (hmonoA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Set.Icc 0 T))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ r)
    {C : ℝ} (hC : 0 ≤ C) (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (ha : Integrable (fun p : ℝ × Ω => a p.1 p.2)
      ((volume.restrict (Set.Ioc 0 T)).prod μ))
    (hprimitive : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T,
      A t ω = A 0 ω + ∫ s in (0 : ℝ)..t, a s ω)
    {L : Ω → ℝ} (hL : Integrable L μ)
    (hlinear : Tendsto (fun n => ∫ ω,
      |linearSum M (EnergyRiemann.point T (n + 1)) (n + 1) ω - L ω| ∂μ)
      atTop (𝓝 0)) :
    (fun ω => Real.artanh (M T ω) - Real.artanh (M 0 ω)) =ᵐ[μ]
      fun ω => L ω + ∫ t in (0 : ℝ)..T, secondWeight (M t ω) * a t ω := by
  let f : ℝ → Ω → ℝ := fun t ω => secondWeight (M t ω)
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  have hfm : Measurable (fun p : ℝ × Ω => f p.1 p.2) := by
    unfold f secondWeight
    exact hMm.div ((measurable_const.sub (hMm.pow_const 2)).pow_const 2)
  have hfc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Set.Icc 0 T) := by
    filter_upwards [hcM, hbound] with ω hc hb
    apply hc.div ((continuousOn_const.sub (hc.pow 2)).pow 2)
    intro t ht
    have hs : M t ω ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr0).2 (hb t)
    exact pow_ne_zero 2 (by linarith : 1 - M t ω ^ 2 ≠ 0)
  have hfb : ∀ᵐ ω ∂μ, ∀ t ∈ Set.Icc 0 T, |f t ω| ≤ r / (1 - r ^ 2) ^ 2 :=
    hbound.mono (fun ω hω t _ => secondWeight_bound hr0 hr (hω t))
  have hcompLimit := WeightedPrimitiveApproximation.tendsto_integral_abs_compensator_error
    hT (by positivity : 0 ≤ r / (1 - r ^ 2) ^ 2) hfm hfc ha hfb hprimitive
  have hshift := hcompLimit.comp (tendsto_add_atTop_nat 1)
  have hV : Integrable (fun ω => ∫ t in (0 : ℝ)..T, f t ω * a t ω) μ := by
    simpa only [intervalIntegral.integral_of_le hT] using
      (WeightedPrimitiveApproximation.integrable_weightedDensity hfm ha hfb).integral_prod_right
  have hmesh : Tendsto (fun n : ℕ => T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hmem (n i : ℕ) (hi : i ≤ n + 1) : EnergyRiemann.point T (n + 1) i ∈ Set.Icc 0 T :=
    EnergyRiemann.point_mem hT (Nat.succ_pos n) hi
  have hdist (n i : ℕ) (_hi : i < n + 1) :
      dist (EnergyRiemann.point T (n + 1) i) (EnergyRiemann.point T (n + 1) (i + 1)) ≤
        T / ((n + 1 : ℕ) : ℝ) := by
    rw [dist_comm, Real.dist_eq, EnergyRiemann.point_step, abs_of_nonneg (by positivity)]
  have hpos : ∀ᵐ ω ∂μ, ∀ n i, i < n + 1 →
      0 ≤ A (EnergyRiemann.point T (n + 1) (i + 1)) ω - A (EnergyRiemann.point T (n + 1) i) ω := by
    filter_upwards [hmonoA] with ω hω
    intro n i hi
    exact sub_nonneg.mpr (hω (hmem n i hi.le) (hmem n (i + 1) hi)
      (EnergyRiemann.point_mono hT (n + 1) (Nat.le_succ i)))
  have htotal' : ∀ᵐ ω ∂μ, ∀ n,
      A (EnergyRiemann.point T (n + 1) (n + 1)) ω - A (EnergyRiemann.point T (n + 1) 0) ω ≤ C := by
    filter_upwards [htotal] with ω hω
    intro n
    simpa only [EnergyRiemann.point_zero, EnergyRiemann.point_end T (Nat.succ_pos n)] using hω
  apply artanh_eq_of_continuous_compensated_limits hM hQ
    (fun n => EnergyRiemann.point T (n + 1)) (fun n => EnergyRiemann.point_mono hT (n + 1))
    (fun n => n + 1) (fun n => EnergyRiemann.point_zero T (n + 1))
    (fun n => EnergyRiemann.point_end T (Nat.succ_pos n)) hr0 hr
    (fun t => hbound.mono (fun ω hω => hω t)) isCompact_Icc hcM hcA hmem
    (fun n => T / ((n + 1 : ℕ) : ℝ)) hmesh hdist hpos hC htotal' hL hV hlinear
  simpa only [Function.comp_def, compensatorSum, f] using hshift

end Problem367.ArtanhMartingaleFormula

end

end OAI
