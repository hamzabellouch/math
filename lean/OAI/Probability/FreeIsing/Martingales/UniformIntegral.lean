import OAI.Probability.FreeIsing.Brownian.UniformIntegral
import OAI.Probability.FreeIsing.Estimates.ContinuousCoefficientModulus
import OAI.Probability.FreeIsing.Martingales.BracketIsometry

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.MartingaleUniformIntegral

open BrownianGrid ContinuousCoefficientModulus

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem uniformSum_memLp {F : Filtration ℝ≥0 mΩ} {M H : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    {K : ℝ} (hb : ∀ t, ∀ᵐ ω ∂μ, |H t ω| ≤ K) (T : ℝ≥0) (n : ℕ) :
    MemLp (uniformSum M H T n) 2 μ := by
  unfold uniformSum integralSum
  apply memLp_finsetSum
  intro i hi
  exact MartingaleTransformL2.bounded_mul_memLp_two
    ((hH _).mono (F.le _)).aestronglyMeasurable
    ((hM2 _).sub (hM2 _)) (hb _)

theorem tendsto_integral_sq_refinement [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A H : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ∀ᵐ ω ∂μ, |H t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C)
    (n k : ℕ → ℕ) (hn : ∀ j, 0 < n j) (hk : ∀ j, 0 < k j)
    (hnlim : Tendsto n atTop atTop) :
    Tendsto (fun j => ∫ ω,
      (uniformSum M H T (n j) ω - uniformSum M H T (n j * k j) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  let s : ℕ → ℕ → ℝ≥0 := fun j i => uniformGrid T (n j) (i / k j)
  let t : ℕ → ℕ → ℝ≥0 := fun j i => uniformGrid T (n j * k j) i
  let N : ℕ → ℕ := fun j => n j * k j
  let D : ℕ → ℕ → Ω → ℝ := fun j i ω => H (s j i) ω - H (t j i) ω
  let R : ℕ → Ω → ℝ := fun j ω =>
    pairModulus (fun i => H (s j i) ω) (fun i => H (t j i) ω) (N j)
  have hHm (u : ℝ≥0) : StronglyMeasurable (H u) := (hH u).mono (F.le u)
  have hle (j i : ℕ) : s j i ≤ t j i := uniformGrid_floor_le T (hn j) (hk j) i
  have htmem (j i : ℕ) (hi : i < N j) : t j i ∈ Icc 0 T :=
    ⟨zero_le, uniformGrid_le_horizon T (Nat.mul_pos (hn j) (hk j)) hi.le⟩
  have hsmem (j i : ℕ) (hi : i < N j) : s j i ∈ Icc 0 T :=
    ⟨zero_le, (hle j i).trans (htmem j i hi).2⟩
  have hDb (j i : ℕ) : ∀ᵐ ω ∂μ, |D j i ω| ≤ 2 * K := by
    filter_upwards [hb (s j i), hb (t j i)] with ω hsω htω
    exact (abs_sub _ _).trans (by linarith)
  have hR2 (j : ℕ) : MemLp (R j) 2 μ :=
    memLp_pairModulus _ _ (fun i => hHm (s j i)) (fun i => hHm (t j i)) (N j)
      (show 0 ≤ 2 * K by positivity) (fun i _ => hDb j i) 2
  have hδ : Tendsto (fun j => (T : ℝ) / (n j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hnlim)
  have hd (j i : ℕ) (_hi : i < N j) :
      dist (s j i) (t j i) ≤ (T : ℝ) / (n j : ℝ) := by
    change |(s j i : ℝ) - (t j i : ℝ)| ≤ _
    rw [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr (hle j i)))]
    have hh := uniformGrid_floor_sub_le T (hn j) (hk j) i
    change (t j i : ℝ) - (s j i : ℝ) ≤ _ at hh
    linarith
  have hRlim : Tendsto (fun j => ∫ ω, R j ω ^ 2 ∂μ) atTop (𝓝 0) :=
    tendsto_integral_pairModulus_pow isCompact_Icc hHm hc hK (fun u _ => hb u)
      s t N hsmem htmem _ hδ hd 2 (by decide)
  have hlim := MartingaleBracketIsometry.tendsto_integral_sq_grid_transform hM hQ hM2
    t (fun j => uniformGrid_mono T (N j)) D
    (fun j i => ((hH (s j i)).mono (F.mono (hle j i))).sub (hH (t j i)))
    (show 0 ≤ 2 * K by positivity) hDb N
    (R := fun j ω => R j ω ^ 2) (fun j => (hR2 j).integrable_sq)
    (fun _ => Filter.Eventually.of_forall (fun ω => sq_nonneg _))
    (fun j => Filter.Eventually.of_forall (fun ω i hi => by
      have hh := abs_sub_le_pairModulus (fun i => H (s j i) ω) (fun i => H (t j i) ω) hi
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (pairModulus_nonneg _ _ _)).2 hh)) hA
    (C := C) (fun j => by
      simpa only [t, N, uniformGrid_end T (Nat.mul_pos (hn j) (hk j)), uniformGrid_zero] using htotal)
    hRlim
  have href (j : ℕ) : uniformSum M H T (n j) =
      integralSum M (t j) (fun i => H (s j i)) (N j) := by
    have hh := integralSum_refinement M (t j)
      (fun i => H (uniformGrid T (n j) i)) (n j) (hk j)
    simpa only [t, s, N, uniformGrid_refine T (hn j) (hk j), uniformSum] using hh
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro j
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  rw [href j]
  simp only [uniformSum, integralSum, D, t, N, sub_mul, Finset.sum_sub_distrib]

theorem exists_uniform_integral [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A H : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ∀ᵐ ω ∂μ, |H t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C) :
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun n => ∫ ω, (uniformSum M H T n ω - L ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hS (n : ℕ) : MemLp (uniformSum M H T n) 2 μ := uniformSum_memLp hM2 hH hb T n
  let f : ℕ → Lp ℝ 2 μ := fun n => (hS n).toLp (uniformSum M H T n)
  have hf : CauchySeq f := by
    by_contra hnot
    rw [Metric.cauchySeq_iff] at hnot
    push Not at hnot
    obtain ⟨ε, hε, hbad⟩ := hnot
    choose n hn m hm hsep using hbad
    let u : ℕ → ℕ := fun j => n (j + 1)
    let v : ℕ → ℕ := fun j => m (j + 1)
    have hu (j : ℕ) : 0 < u j := (Nat.succ_pos j).trans_le (hn (j + 1))
    have hv (j : ℕ) : 0 < v j := (Nat.succ_pos j).trans_le (hm (j + 1))
    have hulim : Tendsto u atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with j hj
      exact hj.trans ((Nat.le_succ j).trans (hn (j + 1)))
    have hvlim : Tendsto v atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop b] with j hj
      exact hj.trans ((Nat.le_succ j).trans (hm (j + 1)))
    have hleft := tendsto_integral_sq_refinement hM hQ hM2 hH T hc hK hb hA htotal
      u v hu hv hulim
    have hright := tendsto_integral_sq_refinement hM hQ hM2 hH T hc hK hb hA htotal
      v u hv hu hvlim
    have hright' : Tendsto (fun j => ∫ ω,
        (uniformSum M H T (v j) ω - uniformSum M H T (u j * v j) ω) ^ 2 ∂μ)
        atTop (𝓝 0) := by simpa only [Nat.mul_comm] using hright
    have hbound (j : ℕ) : ε ^ 2 ≤
        2 * (∫ ω, (uniformSum M H T (u j) ω - uniformSum M H T (u j * v j) ω) ^ 2 ∂μ) +
        2 * (∫ ω, (uniformSum M H T (v j) ω - uniformSum M H T (u j * v j) ω) ^ 2 ∂μ) := by
      have hs : ε ≤ ‖f (u j) - f (v j)‖ := by
        simpa only [dist_eq_norm] using hsep (j + 1)
      have hsq := (sq_le_sq₀ hε.le (norm_nonneg _)).2 hs
      have hnorm : ‖f (u j) - f (v j)‖ ^ 2 =
          ∫ ω, (uniformSum M H T (u j) ω - uniformSum M H T (v j) ω) ^ 2 ∂μ :=
        BrownianGrid.norm_sq_toLp_sub (hS _) (hS _)
      rw [hnorm] at hsq
      exact hsq.trans (integral_sq_sub_le_two (hS _) (hS _) (hS _))
    have hzero := (hleft.const_mul 2).add (hright'.const_mul 2)
    have hcontra := ge_of_tendsto hzero (Filter.Eventually.of_forall hbound)
    nlinarith [sq_pos_of_pos hε]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hf
  refine ⟨L, Lp.stronglyMeasurable L, Lp.memLp L, ?_⟩
  have hnorm := (hL.sub (tendsto_const_nhds (x := L))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
  apply hnorm.congr'
  apply Filter.Eventually.of_forall
  intro n
  have hh := BrownianGrid.norm_sq_toLp_sub (hS n) (Lp.memLp L)
  simpa only [Lp.toLp_coeFn, f] using hh

theorem exists_uniform_integral_on [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M A H : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ)
    (hQ : Martingale (fun t ω => M t ω ^ 2 - A t ω) F μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (hH : StronglyAdapted F H)
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) (Icc 0 T))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t ∈ Icc 0 T, ∀ᵐ ω ∂μ, |H t ω| ≤ K)
    (hA : ∀ᵐ ω ∂μ, MonotoneOn (fun t => A t ω) (Icc 0 T))
    {C : ℝ} (htotal : ∀ᵐ ω ∂μ, A T ω - A 0 ω ≤ C) :
    ∃ L : Ω → ℝ, StronglyMeasurable L ∧ MemLp L 2 μ ∧
      Tendsto (fun n => ∫ ω, (uniformSum M H T n ω - L ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  let q : ℝ≥0 → ℝ≥0 := fun u => min u T
  have hqm : Monotone q := monotone_id.min monotone_const
  have hqmem (u : ℝ≥0) : q u ∈ Icc 0 T := ⟨zero_le, min_le_right _ _⟩
  let G : Filtration ℝ≥0 mΩ :=
    ⟨fun u => F (q u), fun _ _ h => F.mono (hqm h), fun u => F.le (q u)⟩
  have hMG : Martingale (fun u => M (q u)) G μ :=
    ⟨fun u => hM.stronglyMeasurable _, fun _ _ h => hM.condExp_ae_eq (hqm h)⟩
  have hQG : Martingale (fun u ω => M (q u) ω ^ 2 - A (q u) ω) G μ :=
    ⟨fun u => hQ.stronglyMeasurable _, fun _ _ h => hQ.condExp_ae_eq (hqm h)⟩
  have hHc : ∀ᵐ ω ∂μ, ContinuousOn (fun u => H (q u) ω) (Icc 0 T) := by
    filter_upwards [hc] with ω hω
    apply hω.congr
    intro u hu
    simp only [q, min_eq_left hu.2]
  have hAm : ∀ᵐ ω ∂μ, Monotone (fun u => A (q u) ω) := by
    filter_upwards [hA] with ω hω
    exact fun u v huv => hω (hqmem u) (hqmem v) (hqm huv)
  obtain ⟨L, hLm, hL2, hlim⟩ := exists_uniform_integral hMG hQG
    (fun u => hM2 (q u)) (fun u => hH (q u)) T hHc hK
    (fun u => hb (q u) (hqmem u)) hAm
    (C := C) (by simpa only [q, min_self, min_eq_left (show (0 : ℝ≥0) ≤ T from zero_le)] using htotal)
  have hsum (n : ℕ) : uniformSum (fun u => M (q u)) (fun u => H (q u)) T n =
      uniformSum M H T n := by
    funext ω
    unfold uniformSum integralSum
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hn : 0 < n := (Nat.zero_le i).trans_lt hin
    have hleft := uniformGrid_le_horizon T hn hin.le
    have hright := uniformGrid_le_horizon T hn (Nat.succ_le_of_lt hin)
    simp only [q, min_eq_left hleft, min_eq_left hright]
  exact ⟨L, hLm, hL2, by simpa only [hsum] using hlim⟩

end Problem367.MartingaleUniformIntegral

end

end OAI
