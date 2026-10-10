import OAI.Probability.FreeIsing.Martingales.PredictableL2Completion
import OAI.Probability.FreeIsing.Martingales.TransformL2
import OAI.Probability.FreeIsing.Stochastic.SimpleIntegralAssociativity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367.SimpleIntegral

section Multiplier

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {K : Ω → ℝ} {C : ℝ}

abbrev bounded_mul_memLp (hK : AEStronglyMeasurable K μ)
    (hbound : ∀ᵐ ω ∂μ, |K ω| ≤ C) {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    MemLp (fun ω => K ω * X ω) 2 μ :=
  BrownianGrid.memLp_compose_of_bounded hX hK hbound

def boundedMulLinear (hK : AEStronglyMeasurable K μ)
    (hbound : ∀ᵐ ω ∂μ, |K ω| ≤ C) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun X := (bounded_mul_memLp hK hbound (Lp.memLp X)).toLp (fun ω => K ω * X ω)
  map_add' X Y := by
    apply Lp.ext
    filter_upwards
      [(bounded_mul_memLp hK hbound (Lp.memLp (X + Y))).coeFn_toLp,
       Lp.coeFn_add X Y,
       Lp.coeFn_add
         ((bounded_mul_memLp hK hbound (Lp.memLp X)).toLp (fun ω => K ω * X ω))
         ((bounded_mul_memLp hK hbound (Lp.memLp Y)).toLp (fun ω => K ω * Y ω)),
       (bounded_mul_memLp hK hbound (Lp.memLp X)).coeFn_toLp,
       (bounded_mul_memLp hK hbound (Lp.memLp Y)).coeFn_toLp] with ω hxy hsum hout hx hy
    simp only [Pi.add_apply] at *
    rw [hxy, hsum, hout, hx, hy, mul_add]
  map_smul' r X := by
    apply Lp.ext
    filter_upwards
      [(bounded_mul_memLp hK hbound (Lp.memLp (r • X))).coeFn_toLp,
       Lp.coeFn_smul r X,
       Lp.coeFn_smul r
         ((bounded_mul_memLp hK hbound (Lp.memLp X)).toLp (fun ω => K ω * X ω)),
       (bounded_mul_memLp hK hbound (Lp.memLp X)).coeFn_toLp] with ω hrx hsm hout hx
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at *
    rw [hrx, hsm, hout, hx]
    ring

theorem norm_boundedMulLinear_le (hK : AEStronglyMeasurable K μ)
    (hbound : ∀ᵐ ω ∂μ, |K ω| ≤ C) (X : Lp ℝ 2 μ) :
    ‖boundedMulLinear hK hbound X‖ ≤ C * ‖X‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hbound,
    (bounded_mul_memLp hK hbound (Lp.memLp X)).coeFn_toLp] with ω hb he
  change ‖(bounded_mul_memLp hK hbound (Lp.memLp X)).toLp
    (fun ω => K ω * X ω) ω‖ ≤ C * ‖X ω‖
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

def boundedMulL2 (hK : AEStronglyMeasurable K μ)
    (hbound : ∀ᵐ ω ∂μ, |K ω| ≤ C) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (boundedMulLinear hK hbound).mkContinuous C (norm_boundedMulLinear_le hK hbound)

theorem boundedMulL2_toLp (hK : AEStronglyMeasurable K μ)
    (hbound : ∀ᵐ ω ∂μ, |K ω| ≤ C) {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    boundedMulL2 hK hbound (hX.toLp X) =
      (bounded_mul_memLp hK hbound hX).toLp (fun ω => K ω * X ω) := by
  apply Lp.ext
  filter_upwards
    [(bounded_mul_memLp hK hbound (Lp.memLp (hX.toLp X))).coeFn_toLp,
     hX.coeFn_toLp, (bounded_mul_memLp hK hbound hX).coeFn_toLp] with ω hleft hx hright
  change (bounded_mul_memLp hK hbound (Lp.memLp (hX.toLp X))).toLp
    (fun ω => K ω * hX.toLp X ω) ω = _
  rw [hleft, hx, hright]

theorem hasSum_bounded_mul {ι : Type*}
    (hK : AEStronglyMeasurable K μ) (hbound : ∀ᵐ ω ∂μ, |K ω| ≤ C)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ)
    (hsum : HasSum (fun i => (hX i).toLp (X i)) (hY.toLp Y)) :
    HasSum (fun i => (bounded_mul_memLp hK hbound (hX i)).toLp
      (fun ω => K ω * X i ω))
      ((bounded_mul_memLp hK hbound hY).toLp (fun ω => K ω * Y ω)) := by
  simpa only [boundedMulL2_toLp] using hsum.mapL (boundedMulL2 hK hbound)

end Multiplier

section Limits

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem tendsto_toLp_iff_meanSquare {α : Type*} {l : Filter α}
    {X : α → Ω → ℝ} (hX : ∀ a, MemLp (X a) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    Tendsto (fun a => (hX a).toLp (X a)) l (𝓝 (hY.toLp Y)) ↔
      Tendsto (fun a => ∫ ω, (X a ω - Y ω) ^ 2 ∂μ) l (𝓝 0) := by
  have heq (a : α) :
      ‖(hX a).toLp (X a) - hY.toLp Y‖ ^ 2 =
        ∫ ω, (X a ω - Y ω) ^ 2 ∂μ := by
    rw [← MemLp.toLp_sub (hX a) hY]
    exact PredictableL2.norm_toLp_sq ((hX a).sub hY)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  constructor
  · intro h
    simpa only [heq, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h.pow 2
  · intro h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa only [Function.comp_def, ← heq, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hs

theorem meanSquare_limit_of_close {α : Type*} {l : Filter α}
    {X Y : α → Ω → ℝ} (hX : ∀ a, MemLp (X a) 2 μ)
    (hY : ∀ a, MemLp (Y a) 2 μ) {Z : Ω → ℝ} (hZ : MemLp Z 2 μ)
    (hclose : Tendsto (fun a => ∫ ω, (X a ω - Y a ω) ^ 2 ∂μ) l (𝓝 0))
    (hlim : Tendsto (fun a => ∫ ω, (X a ω - Z ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun a => ∫ ω, (Y a ω - Z ω) ^ 2 ∂μ) l (𝓝 0) := by
  apply (tendsto_toLp_iff_meanSquare hY hZ).mp
  apply ((tendsto_toLp_iff_meanSquare hX hZ).mpr hlim).congr_dist
  have heq (a : α) :
      dist ((hX a).toLp (X a)) ((hY a).toLp (Y a)) ^ 2 =
        ∫ ω, (X a ω - Y a ω) ^ 2 ∂μ := by
    rw [dist_eq_norm, ← MemLp.toLp_sub (hX a) (hY a)]
    exact PredictableL2.norm_toLp_sq ((hX a).sub (hY a))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hclose
  simpa only [Function.comp_def, ← heq, Real.sqrt_sq dist_nonneg,
    Real.sqrt_zero] using hs

theorem tendsto_bounded_multiplier_energy
    {K : ℕ → Ω → ℝ} {L X : Ω → ℝ}
    (hK : ∀ n, AEStronglyMeasurable (K n) μ)
    (hL : AEStronglyMeasurable L μ) (hX : MemLp X 2 μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hboundK : ∀ n, ∀ᵐ ω ∂μ, |K n ω| ≤ C)
    (hboundL : ∀ᵐ ω ∂μ, |L ω| ≤ C)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => K n ω) atTop (𝓝 (L ω))) :
    Tendsto (fun n => ∫ ω, ((K n ω - L ω) * X ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hb (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖((K n ω - L ω) * X ω) ^ 2‖ ≤ (2 * C) ^ 2 * X ω ^ 2 := by
    filter_upwards [hboundK n, hboundL] with ω hn hl
    have hd : |K n ω - L ω| ≤ 2 * C :=
      (abs_sub _ _).trans (by linarith)
    have hs : (K n ω - L ω) ^ 2 ≤ (2 * C) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * C)).2 hd
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg (X ω))
  have hi := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun ω => (2 * C) ^ 2 * X ω ^ 2)
    (fun n => (((hK n).sub hL).mul hX.aestronglyMeasurable).pow 2)
    (hX.integrable_sq.const_mul ((2 * C) ^ 2)) hb
    (hlim.mono (fun ω hω => by
      simpa using ((hω.sub tendsto_const_nhds).mul_const (X ω)).pow 2))
  simpa using hi

def coarseTransform (K M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, K j ω * (M (j + 1) ω - M j ω)

theorem coarseTransform_memLp (K : ℕ → Ω → ℝ)
    (hK : ∀ j, AEStronglyMeasurable (K j) μ) (C : ℕ → ℝ)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, |K j ω| ≤ C j)
    {M : ℕ → Ω → ℝ} (hM : ∀ j, MemLp (M j) 2 μ) (n : ℕ) :
    MemLp (coarseTransform K M n) 2 μ := by
  exact memLp_finsetSum _ fun j _ =>
    bounded_mul_memLp (hK j) (hbound j) ((hM (j + 1)).sub (hM j))

theorem toLp_coarseTransform (K : ℕ → Ω → ℝ)
    (hK : ∀ j, AEStronglyMeasurable (K j) μ) (C : ℕ → ℝ)
    (hbound : ∀ j, ∀ᵐ ω ∂μ, |K j ω| ≤ C j)
    {M : ℕ → Ω → ℝ} (hM : ∀ j, MemLp (M j) 2 μ) (n : ℕ) :
    (coarseTransform_memLp K hK C hbound hM n).toLp (coarseTransform K M n) =
      ∑ j ∈ Finset.range n, boundedMulL2 (hK j) (hbound j)
        ((hM (j + 1)).toLp (M (j + 1)) - (hM j).toLp (M j)) := by
  have hterm (j : ℕ) : MemLp (fun ω => K j ω * (M (j + 1) ω - M j ω)) 2 μ :=
    bounded_mul_memLp (hK j) (hbound j) ((hM (j + 1)).sub (hM j))
  calc
    _ = ∑ j ∈ Finset.range n, (hterm j).toLp
        (fun ω => K j ω * (M (j + 1) ω - M j ω)) :=
      PredictableL2.toLp_finsetSum _ hterm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← MemLp.toLp_sub (hM (j + 1)) (hM j), boundedMulL2_toLp]
      rfl

theorem tendsto_coarseTransform {α : Type*} {l : Filter α}
    (K : ℕ → Ω → ℝ) (hK : ∀ j, AEStronglyMeasurable (K j) μ)
    (C : ℕ → ℝ) (hbound : ∀ j, ∀ᵐ ω ∂μ, |K j ω| ≤ C j)
    {X : α → ℕ → Ω → ℝ} (hX : ∀ a j, MemLp (X a j) 2 μ)
    {M : ℕ → Ω → ℝ} (hM : ∀ j, MemLp (M j) 2 μ) (n : ℕ)
    (hlim : ∀ j ≤ n, Tendsto (fun a => (hX a j).toLp (X a j)) l
      (𝓝 ((hM j).toLp (M j)))) :
    Tendsto (fun a => (coarseTransform_memLp K hK C hbound (hX a) n).toLp
      (coarseTransform K (X a) n)) l
      (𝓝 ((coarseTransform_memLp K hK C hbound hM n).toLp
        (coarseTransform K M n))) := by
  rw [toLp_coarseTransform K hK C hbound hM n]
  have ht : Tendsto (fun a => ∑ j ∈ Finset.range n,
      boundedMulL2 (hK j) (hbound j)
        ((hX a (j + 1)).toLp (X a (j + 1)) - (hX a j).toLp (X a j))) l
      (𝓝 (∑ j ∈ Finset.range n, boundedMulL2 (hK j) (hbound j)
        ((hM (j + 1)).toLp (M (j + 1)) - (hM j).toLp (M j)))) := by
    apply tendsto_finsetSum
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    exact ((boundedMulL2 (hK j) (hbound j)).continuous.tendsto _).comp
      ((hlim (j + 1) hjn).sub (hlim j hjn.le))
  exact ht.congr (fun a => (toLp_coarseTransform K hK C hbound (hX a) n).symm)

theorem integralSum_compose_refined_tendsto {α : Type*} {l : Filter α}
    (B : ℝ≥0 → Ω → ℝ) (t : α → ℕ → ℝ≥0) (H : α → ℕ → Ω → ℝ)
    (k : α → ℕ) (hk : ∀ a, 0 < k a)
    (K : ℕ → Ω → ℝ) (hK : ∀ j, AEStronglyMeasurable (K j) μ)
    (C : ℕ → ℝ) (hbound : ∀ j, ∀ᵐ ω ∂μ, |K j ω| ≤ C j)
    (hI : ∀ a j, MemLp (BrownianGrid.integralSum B (t a) (H a) (j * k a)) 2 μ)
    {M : ℕ → Ω → ℝ} (hM : ∀ j, MemLp (M j) 2 μ) (n : ℕ)
    (hlim : ∀ j ≤ n, Tendsto (fun a => (hI a j).toLp
      (BrownianGrid.integralSum B (t a) (H a) (j * k a))) l
        (𝓝 ((hM j).toLp (M j)))) :
    Tendsto (fun a => ∫ ω,
      (BrownianGrid.integralSum B (t a)
        (fun i ω => K (i / k a) ω * H a i ω) (n * k a) ω -
          coarseTransform K M n ω) ^ 2 ∂μ) l (𝓝 0) := by
  have h := (tendsto_toLp_iff_meanSquare
    (fun a => coarseTransform_memLp K hK C hbound (hI a) n)
    (coarseTransform_memLp K hK C hbound hM n)).mp
      (tendsto_coarseTransform K hK C hbound hI hM n hlim)
  refine h.congr (fun a => ?_)
  congr 1
  funext ω
  rw [coarseTransform, BrownianGrid.integralSum_compose_refined B (t a) (H a) K n (hk a)]

theorem integralSum_ae_coarseTransform
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (H K : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k) (I : ℕ → Ω → ℝ)
    (hrep : ∀ j, I j =ᵐ[μ] BrownianGrid.integralSum B t H (j * k)) (n : ℕ) :
    BrownianGrid.integralSum B t (fun i ω => K (i / k) ω * H i ω) (n * k) =ᵐ[μ]
      coarseTransform K I n := by
  filter_upwards [ae_all_iff.mpr hrep] with ω hω
  rw [← BrownianGrid.integralSum_compose_refined B t H K n hk]
  simp only [coarseTransform]
  simp_rw [hω]

theorem integralSum_compose_varying_grid_tendsto [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} {I : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hI : ∀ n, Martingale (I n) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hI2 : ∀ n t, MemLp (I n t) 2 μ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℕ → ℝ≥0) (ht : ∀ n, Monotone (t n))
    (H K : ℕ → ℕ → Ω → ℝ) (k N : ℕ → ℕ) (hk : ∀ n, 0 < k n)
    (hK : ∀ n j, StronglyMeasurable[F (t n (j * k n))] (K n j))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n j, ∀ᵐ ω ∂μ, |K n j ω| ≤ C)
    {T : ℝ≥0} (hterminal : ∀ n, t n (N n * k n) = T)
    (hrep : ∀ n j, I n (t n (j * k n)) =ᵐ[μ]
      BrownianGrid.integralSum B (t n) (H n) (j * k n))
    (hlim : Tendsto (fun n => ∫ ω, (I n T ω - M T ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (BrownianGrid.integralSum B (t n)
        (fun i ω => K n (i / k n) ω * H n i ω) (N n * k n) ω -
          coarseTransform (K n) (fun j => M (t n (j * k n))) (N n) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have herr := MartingaleTransformL2.tendsto_integral_sq_grid_transform
    (fun n => (hI n).sub hM) (fun n s => (hI2 n s).sub (hM2 s))
    (fun n j => t n (j * k n))
    (fun n i j hij => ht n (Nat.mul_le_mul_right (k n) hij)) N hterminal K hK hC hbound hlim
  refine herr.congr (fun n => ?_)
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (hrep n)] with ω hω
  rw [← BrownianGrid.integralSum_compose_refined B (t n) (H n) (K n) (N n) (hk n)]
  congr 1
  simp only [Pi.sub_apply, coarseTransform]
  simp_rw [hω]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem integralSum_compose_limit [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} {I : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (hI : ∀ n, Martingale (I n) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hI2 : ∀ n t, MemLp (I n t) 2 μ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℕ → ℝ≥0) (ht : ∀ n, Monotone (t n))
    (H K : ℕ → ℕ → Ω → ℝ) (k N : ℕ → ℕ) (hk : ∀ n, 0 < k n)
    (hK : ∀ n j, StronglyMeasurable[F (t n (j * k n))] (K n j))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n j, ∀ᵐ ω ∂μ, |K n j ω| ≤ C)
    {T : ℝ≥0} (hterminal : ∀ n, t n (N n * k n) = T)
    (hrep : ∀ n j, I n (t n (j * k n)) =ᵐ[μ]
      BrownianGrid.integralSum B (t n) (H n) (j * k n))
    (hlim : Tendsto (fun n => ∫ ω, (I n T ω - M T ω) ^ 2 ∂μ) atTop (𝓝 0))
    {Z : Ω → ℝ} (hZ : MemLp Z 2 μ)
    (hproduct : Tendsto (fun n => ∫ ω,
      (BrownianGrid.integralSum B (t n)
        (fun i ω => K n (i / k n) ω * H n i ω) (N n * k n) ω - Z ω) ^ 2 ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (coarseTransform (K n) (fun j => M (t n (j * k n))) (N n) ω - Z ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hKm (n j : ℕ) : AEStronglyMeasurable (K n j) μ :=
    ((hK n j).mono (F.le _)).aestronglyMeasurable
  have houter (n : ℕ) := coarseTransform_memLp (K n) (hKm n) (fun _ => C)
    (hbound n) (fun j => hM2 (t n (j * k n))) (N n)
  have hfine (n : ℕ) : MemLp (BrownianGrid.integralSum B (t n)
      (fun i ω => K n (i / k n) ω * H n i ω) (N n * k n)) 2 μ := by
    apply MemLp.ae_eq
      (integralSum_ae_coarseTransform B (t n) (H n) (K n) (hk n)
        (fun j => I n (t n (j * k n))) (hrep n) (N n)).symm
    exact coarseTransform_memLp (K n) (hKm n) (fun _ => C) (hbound n)
      (fun j => hI2 n (t n (j * k n))) (N n)
  exact meanSquare_limit_of_close hfine houter hZ
    (integralSum_compose_varying_grid_tendsto hM hI hM2 hI2 B t ht H K k N hk
      hK hC hbound hterminal hrep hlim) hproduct

end Limits
end Problem367.SimpleIntegral

end

end OAI
