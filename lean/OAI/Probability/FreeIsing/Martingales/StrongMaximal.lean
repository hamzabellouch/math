import OAI.Probability.FreeIsing.Martingales.PredictableMeshApproximation
import OAI.Probability.FreeIsing.Martingales.SquareMaximal

namespace OAI

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal Topology

namespace Problem367.MartingaleStrongMaximal

def runningMax (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | n + 1 => max (runningMax x n) (x (n + 1))

@[simp] theorem runningMax_zero (x : ℕ → ℝ) : runningMax x 0 = x 0 := rfl

@[simp] theorem runningMax_succ (x : ℕ → ℝ) (n : ℕ) :
    runningMax x (n + 1) = max (runningMax x n) (x (n + 1)) := rfl

theorem self_le_runningMax (x : ℕ → ℝ) (n : ℕ) : x n ≤ runningMax x n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_right _ _

theorem runningMax_mono (x : ℕ → ℝ) : Monotone (runningMax x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem le_runningMax (x : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) : x i ≤ runningMax x n :=
  (self_le_runningMax x i).trans (runningMax_mono x h)

theorem runningMax_sq_le_twice (x : ℕ → ℝ) (n : ℕ) :
    runningMax x n ^ 2 ≤ 2 * runningMax x n * x n -
      2 * ∑ k ∈ range n, runningMax x k * (x (k + 1) - x k) := by
  induction n with
  | zero =>
    simp only [sum_range_zero, mul_zero, sub_zero, runningMax_zero]
    nlinarith [sq_nonneg (x 0)]
  | succ n ih =>
    rw [sum_range_succ, runningMax_succ]
    rcases le_total (x (n + 1)) (runningMax x n) with h | h
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (x (n + 1) - runningMax x n)]

theorem runningMax_sq_le_four (x : ℕ → ℝ) (n : ℕ) :
    runningMax x n ^ 2 ≤ 4 * x n ^ 2 -
      4 * ∑ k ∈ range n, runningMax x k * (x (k + 1) - x k) := by
  have h := runningMax_sq_le_twice x n
  nlinarith [sq_nonneg (runningMax x n - 2 * x n)]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem runningMax_memLp {X : ℕ → Ω → ℝ} (h2 : ∀ n, MemLp (X n) 2 μ) (n : ℕ) :
    MemLp (fun ω => runningMax (fun k => X k ω) n) 2 μ := by
  induction n with
  | zero => exact h2 0
  | succ n ih => exact ih.sup (h2 (n + 1))

theorem runningMax_stronglyAdapted {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : StronglyAdapted F X) :
    StronglyAdapted F (fun n ω => runningMax (fun k => X k ω) n) := by
  intro n
  induction n with
  | zero => exact hX 0
  | succ n ih =>
    let : MeasurableSpace Ω := F (n + 1)
    have hi : StronglyMeasurable[F (n + 1)]
        (fun ω => runningMax (fun k => X k ω) n) := ih.mono (F.mono (Nat.le_succ n))
    exact hi.sup (hX (n + 1))

theorem integral_mul_sub_nonneg [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ} (hX : Submartingale X F μ)
    (n : ℕ) {H : Ω → ℝ} (hH : StronglyMeasurable[F n] H)
    (hHnonneg : ∀ ω, 0 ≤ H ω)
    (hprod : Integrable (fun ω => H ω * (X (n + 1) ω - X n ω)) μ) :
    0 ≤ ∫ ω, H ω * (X (n + 1) ω - X n ω) ∂μ := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hprod
    ((hX.integrable (n + 1)).sub (hX.integrable n))
  rw [← integral_condExp (F.le n)]
  apply integral_nonneg_of_ae
  filter_upwards [hpull, hX.condExp_sub_nonneg (Nat.le_succ n)] with ω hp hn
  change 0 ≤ μ[H * (fun ω => X (n + 1) ω - X n ω) | F n] ω
  rw [hp]
  exact mul_nonneg (hHnonneg ω) hn

theorem finite_submartingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {X : ℕ → Ω → ℝ}
    (hX : Submartingale X F μ) (h2 : ∀ n, MemLp (X n) 2 μ)
    (hnonneg : ∀ n ω, 0 ≤ X n ω) (n : ℕ) :
    (∫ ω, runningMax (fun k => X k ω) n ^ 2 ∂μ) ≤
      4 * ∫ ω, X n ω ^ 2 ∂μ := by
  have hmax2 := runningMax_memLp h2
  have hmaxA := runningMax_stronglyAdapted hX.stronglyAdapted
  have hprod (k : ℕ) : Integrable (fun ω =>
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω)) μ :=
    (hmax2 k).integrable_mul ((h2 (k + 1)).sub (h2 k))
  have hsum : Integrable (fun ω => ∑ k ∈ range n,
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω)) μ :=
    integrable_finsetSum _ (fun k _ => hprod k)
  have hbound := integral_mono (hmax2 n).integrable_sq
    (((h2 n).integrable_sq.const_mul 4).sub (hsum.const_mul 4))
    (fun ω => runningMax_sq_le_four (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub ((h2 n).integrable_sq.const_mul 4) (hsum.const_mul 4),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun k _ => hprod k)] at hbound
  have hsum_nonneg : 0 ≤ ∑ k ∈ range n, ∫ ω,
      runningMax (fun j => X j ω) k * (X (k + 1) ω - X k ω) ∂μ := by
    apply sum_nonneg
    intro k hk
    exact integral_mul_sub_nonneg hX k (hmaxA k)
      (fun ω => (hnonneg k ω).trans (self_le_runningMax (fun j => X j ω) k)) (hprod k)
  linarith

theorem submartingale_abs {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) : Submartingale (fun n ω => |M n ω|) F μ := by
  refine ⟨fun n => ?_, ?_, fun n => (hM.integrable n).abs⟩
  · simpa only [Real.norm_eq_abs] using (hM.stronglyMeasurable n).norm
  · intro i j hij
    have hj := norm_condExp_le (m := F i) (μ := μ) (M j)
    filter_upwards [hj, hM.condExp_ae_eq hij] with ω hω heq
    simpa only [Real.norm_eq_abs, heq] using hω

theorem finite_martingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    (∫ ω, runningMax (fun k => |M k ω|) n ^ 2 ∂μ) ≤
      4 * ∫ ω, M n ω ^ 2 ∂μ := by
  simpa only [sq_abs] using finite_submartingale_maximal_sq (submartingale_abs hM)
    (fun n => (h2 n).norm) (fun n ω => abs_nonneg (M n ω)) n

theorem runningMax_le {x : ℕ → ℝ} {n : ℕ} {a : ℝ}
    (h : ∀ k ≤ n, x k ≤ a) : runningMax x n ≤ a := by
  induction n with
  | zero => exact h 0 le_rfl
  | succ n ih =>
    exact max_le (ih (fun k hk => h k (hk.trans (Nat.le_succ n)))) (h (n + 1) le_rfl)

theorem sampled_martingale_maximal_sq [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (q : ℕ → ι) (hq : Monotone q) (n : ℕ) {T : ι} (hT : q n ≤ T) :
    (∫ ω, runningMax (fun k => |M (q k) ω|) n ^ 2 ∂μ) ≤
      4 * ∫ ω, M T ω ^ 2 ∂μ := by
  let G : Filtration ℕ mΩ := ⟨fun k => F (q k),
    fun _ _ h => F.mono (hq h), fun k => F.le (q k)⟩
  have hMq : Martingale (fun k => M (q k)) G μ :=
    ⟨fun k => hM.stronglyMeasurable (q k), fun i j hij => hM.condExp_ae_eq (hq hij)⟩
  exact (finite_martingale_maximal_sq hMq (fun k => h2 (q k)) n).trans
    (mul_le_mul_of_nonneg_left (MartingaleSquareMaximal.integral_sq_le hM h2 hT)
      (by norm_num))

def dyadicPoint (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 ^ n : ℕ)

def dyadicCount (n : ℕ) (T : ℝ≥0) : ℕ := ⌊(2 ^ n : ℕ) * T⌋₊

theorem dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro i j hij
  dsimp [dyadicPoint]
  gcongr

theorem dyadicPoint_double (n k : ℕ) :
    dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  simp only [dyadicPoint, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem dyadicPoint_le_iff {n k : ℕ} {T : ℝ≥0} :
    dyadicPoint n k ≤ T ↔ k ≤ dyadicCount n T := by
  have hp : (0 : ℝ≥0) < (2 ^ n : ℕ) := by positivity
  rw [dyadicPoint, div_le_iff₀ hp, dyadicCount, Nat.le_floor_iff (by positivity)]
  rw [mul_comm]

theorem dyadicPoint_eq_mesh (n k : ℕ) :
    dyadicPoint n k = PredictableMesh.point (2 ^ n - 1) k := by
  have hn : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  simp only [dyadicPoint, PredictableMesh.point, Nat.sub_add_cancel hn]

def gridMax (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  runningMax (fun k => |M (dyadicPoint n k) ω|) (dyadicCount n T)

omit mΩ in
theorem gridMax_nonneg (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ gridMax M T n ω :=
  (abs_nonneg _).trans (self_le_runningMax
    (fun k => |M (dyadicPoint n k) ω|) (dyadicCount n T))

omit mΩ in
theorem gridMax_mono (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    Monotone (fun n => gridMax M T n ω) := by
  apply monotone_nat_of_le_succ
  intro n
  apply runningMax_le
  intro k hk
  have ht : dyadicPoint (n + 1) (2 * k) ≤ T := by
    rw [dyadicPoint_double]
    exact dyadicPoint_le_iff.mpr hk
  have hb := le_runningMax (fun j => |M (dyadicPoint (n + 1) j) ω|)
    (dyadicPoint_le_iff.mp ht)
  simpa only [dyadicPoint_double, gridMax] using hb

theorem gridMax_memLp {M : ℝ≥0 → Ω → ℝ} (h2 : ∀ t, MemLp (M t) 2 μ)
    (T : ℝ≥0) (n : ℕ) : MemLp (gridMax M T n) 2 μ :=
  runningMax_memLp (fun k => (h2 (dyadicPoint n k)).norm) _

theorem gridMax_integral_sq_le [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, gridMax M T n ω ^ 2 ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ :=
  sampled_martingale_maximal_sq hM h2 (dyadicPoint n) (dyadicPoint_mono n) _
    (dyadicPoint_le_iff.mpr le_rfl)

def supremumSq (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t : Set.Iic T, ENNReal.ofReal (M t ω ^ 2)

omit mΩ in

theorem supremumSq_eq_iSup_gridMax {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (T : ℝ≥0) :
    supremumSq M T ω = ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hp : Tendsto (fun n : ℕ => 2 ^ n - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (M (PredictableMesh.left (2 ^ n - 1) t) ω ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (M t ω ^ 2))) :=
      ENNReal.tendsto_ofReal (((hc.tendsto t).comp
        ((PredictableMesh.tendsto_left t).comp hp)).pow 2)
    apply le_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro n
    apply le_iSup_of_le n
    apply ENNReal.ofReal_le_ofReal
    rw [← sq_abs (M (PredictableMesh.left (2 ^ n - 1) t) ω)]
    apply (sq_le_sq₀ (abs_nonneg _) (gridMax_nonneg M T n ω)).mpr
    let k := ⌈((2 ^ n - 1 + 1 : ℕ) : ℝ≥0) * t⌉₊ - 1
    have heq : dyadicPoint n k = PredictableMesh.left (2 ^ n - 1) t :=
      dyadicPoint_eq_mesh n k
    have ht : dyadicPoint n k ≤ T := by
      rw [heq]
      exact (PredictableMesh.left_le _ t).trans t.property
    have hb := le_runningMax (fun j => |M (dyadicPoint n j) ω|)
      (dyadicPoint_le_iff.mp ht)
    simpa only [heq, gridMax] using hb
  · apply iSup_le
    intro n
    have hmax : ∃ k ≤ dyadicCount n T,
        gridMax M T n ω = |M (dyadicPoint n k) ω| := by
      dsimp only [gridMax]
      generalize dyadicCount n T = N
      induction N with
      | zero => exact ⟨0, le_rfl, rfl⟩
      | succ N ih =>
        obtain ⟨k, hk, heq⟩ := ih
        rcases le_total |M (dyadicPoint n (N + 1)) ω|
          (runningMax (fun k => |M (dyadicPoint n k) ω|) N) with h | h
        · exact ⟨k, hk.trans (Nat.le_succ N), (max_eq_left h).trans heq⟩
        · exact ⟨N + 1, le_rfl, max_eq_right h⟩
    obtain ⟨k, hk, heq⟩ := hmax
    rw [heq, sq_abs]
    exact le_iSup_of_le ⟨dyadicPoint n k, dyadicPoint_le_iff.mpr hk⟩ le_rfl

theorem continuous_martingale_maximal_sq [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    (∫⁻ ω, supremumSq M T ω ∂μ) ≤
      ENNReal.ofReal (4 * ∫ ω, M T ω ^ 2 ∂μ) := by
  have heq : supremumSq M T =ᵐ[μ]
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2)) := by
    filter_upwards [hc] with ω hω
    exact supremumSq_eq_iSup_gridMax hω T
  rw [lintegral_congr_ae heq, lintegral_iSup']
  · apply iSup_le
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (gridMax_memLp h2 T n).integrable_sq
      (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (gridMax_integral_sq_le hM h2 T n)
  · intro n
    exact ((gridMax_memLp h2 T n).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun ω n m hnm =>
      ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (gridMax_nonneg M T n ω)
        (gridMax_nonneg M T m ω)).mpr (gridMax_mono M T ω hnm))

theorem supremumSq_aemeasurable {M : ℝ≥0 → Ω → ℝ}
    (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    AEMeasurable (supremumSq M T) μ := by
  have hg : AEMeasurable
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (gridMax M T n ω ^ 2)) μ :=
    AEMeasurable.iSup (fun n =>
      ((gridMax_memLp h2 T n).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal)
  apply hg.congr
  filter_upwards [hc] with ω hω
  exact (supremumSq_eq_iSup_gridMax hω T).symm

theorem ae_supremumSq_lt_top [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, supremumSq M T ω < ∞ :=
  ae_lt_top' (supremumSq_aemeasurable h2 hc T)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (continuous_martingale_maximal_sq hM h2 hc T))

def maximalSquare (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  (supremumSq M T ω).toReal

theorem integrable_maximalSquare [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    Integrable (maximalSquare M T) μ :=
  integrable_toReal_of_lintegral_ne_top (supremumSq_aemeasurable h2 hc T)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (continuous_martingale_maximal_sq hM h2 hc T))

theorem integral_maximalSquare_le [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    (∫ ω, maximalSquare M T ω ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ := by
  change (∫ ω, (supremumSq M T ω).toReal ∂μ) ≤ _
  rw [integral_toReal (supremumSq_aemeasurable h2 hc T) (ae_supremumSq_lt_top hM h2 hc T)]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (continuous_martingale_maximal_sq hM h2 hc T)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (integral_nonneg (fun ω => sq_nonneg (M T ω))))] using h

theorem tendsto_integral_maximalSquare_sub [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ} {L : ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ) (hL : Martingale L F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ) (hL2 : ∀ t, MemLp (L t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω))
    (hLc : ∀ᵐ ω ∂μ, Continuous (fun t => L t ω)) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω, (M n T ω - L T ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, maximalSquare (M n - L) T ω ∂μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) := integral_maximalSquare_le ((hM n).sub hL)
    (fun t => (h2 n t).sub (hL2 t)) (show ∀ᵐ ω ∂μ,
      Continuous (fun t => (M n - L) t ω) from by
        filter_upwards [hc n, hLc] with ω hm hl
        exact hm.sub hl) T
  apply squeeze_zero
    (fun n => integral_nonneg (fun ω => ENNReal.toReal_nonneg))
    (fun n => by simpa only [Pi.sub_apply, maximalSquare] using hbound n)
  simpa only [mul_zero] using hlim.const_mul 4

theorem ae_all_sq_le_maximalSquare [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) (h2 : ∀ t, MemLp (M t) 2 μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, M t ω ^ 2 ≤ maximalSquare M T ω := by
  filter_upwards [ae_supremumSq_lt_top hM h2 hc T] with ω hω
  intro t ht
  have hle : ENNReal.ofReal (M t ω ^ 2) ≤ supremumSq M T ω :=
    le_iSup_of_le ⟨t, ht⟩ le_rfl
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), maximalSquare] using
    ENNReal.toReal_mono hω.ne hle

end Problem367.MartingaleStrongMaximal

end

end OAI
