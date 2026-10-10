import OAI.Probability.FreeIsing.Stochastic.SimpleIntegralIsometry

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.MartingaleQuadraticVariation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def increment {I : Type*} (M : I → Ω → ℝ) (s t : I) : Ω → ℝ :=
  fun ω => M t ω - M s ω

def squareError {I : Type*} (M A : I → Ω → ℝ) (s t : I) : Ω → ℝ :=
  fun ω => (increment M s t ω) ^ 2 - increment A s t ω

theorem condExp_increment_eq_zero [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M : I → Ω → ℝ} (hM : Martingale M ℱ μ) {s t : I} (hst : s ≤ t) :
    μ[increment M s t | ℱ s] =ᵐ[μ] 0 := by
  have hsub := condExp_sub (hM.integrable t) (hM.integrable s) (ℱ s)
  filter_upwards [hsub, hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)]
    with ω hs ht hself
  simp only [Pi.sub_apply] at hs
  change μ[M t - M s | ℱ s] ω = 0
  rw [hs, ht, hself, sub_self]

theorem integrable_compensator [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ}
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (t : I) : Integrable (A t) μ := by
  simpa only [Pi.sub_def, sub_sub_cancel] using
    (hM2 t).integrable_sq.sub (hQ.integrable t)

theorem stronglyAdapted_compensator
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ) :
    StronglyAdapted ℱ A := by
  intro t
  simpa only [Pi.sub_def, Pi.pow_apply, sub_sub_cancel] using
    ((hM.stronglyMeasurable t).pow 2).sub (hQ.stronglyMeasurable t)

theorem condExp_squareError_eq_zero [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) {s t : I} (hst : s ≤ t) :
    μ[squareError M A s t | ℱ s] =ᵐ[μ] 0 := by
  let Q : I → Ω → ℝ := fun r ω => (M r ω) ^ 2 - A r ω
  have hd : Integrable (increment M s t) μ := (hM.integrable t).sub (hM.integrable s)
  have hprod : Integrable (M s * increment M s t) μ :=
    (hM2 s).integrable_mul ((hM2 t).sub (hM2 s))
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (hM.stronglyMeasurable s) hprod hd
  have hpzero : μ[M s * increment M s t | ℱ s] =ᵐ[μ] 0 := by
    filter_upwards [hpull, condExp_increment_eq_zero hM hst] with ω hp hz
    simp only [Pi.mul_apply, Pi.zero_apply] at hp hz ⊢
    rw [hp, hz, mul_zero]
  have hident : squareError M A s t =
      increment Q s t - (2 : ℝ) • (M s * increment M s t) := by
    funext ω
    simp only [squareError, increment, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.mul_apply, Q]
    ring
  rw [hident]
  have hsub : μ[increment Q s t - (2 : ℝ) • (M s * increment M s t) | ℱ s] =ᵐ[μ]
      μ[increment Q s t | ℱ s] - μ[(2 : ℝ) • (M s * increment M s t) | ℱ s] :=
    condExp_sub ((hQ.integrable t).sub (hQ.integrable s))
      (hprod.smul (2 : ℝ)) (ℱ s)
  have hscale := condExp_smul (μ := μ) (m := ℱ s) (2 : ℝ)
    (M s * increment M s t)
  filter_upwards [hsub, condExp_increment_eq_zero hQ hst, hpzero, hscale]
    with ω hs hq hp hc
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hs hq hp hc ⊢
  change μ[increment Q s t | ℱ s] ω = 0 at hq
  rw [hs, hq, hc, hp]
  ring

theorem stronglyMeasurable_squareError
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    {s t : I} (hst : s ≤ t) : StronglyMeasurable[ℱ t] (squareError M A s t) := by
  have hA := stronglyAdapted_compensator hM hQ
  exact (((hM.stronglyMeasurable t).sub
    ((hM.stronglyMeasurable s).mono (ℱ.mono hst))).pow 2).sub
      ((hA t).sub ((hA s).mono (ℱ.mono hst)))

theorem integrable_squareError [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ}
    {M A : I → Ω → ℝ}
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (s t : I) :
    Integrable (squareError M A s t) μ :=
  ((hM2 t).sub (hM2 s)).integrable_sq.sub
    ((integrable_compensator hQ hM2 t).sub (integrable_compensator hQ hM2 s))

theorem weighted_error_isometry [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hY2 : ∀ i, MemLp (fun ω => H i ω * squareError M A i (i + 1) ω) 2 μ)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, (H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ := by
  let D : ℕ → Ω → ℝ := fun i => squareError M A i (i + 1)
  have hD (i : ℕ) : StronglyMeasurable[ℱ (i + 1)] (D i) :=
    stronglyMeasurable_squareError hM hQ (Nat.le_succ i)
  have hDint (i : ℕ) : Integrable (D i) μ := integrable_squareError hQ hM2 _ _
  have hzero (i : ℕ) : μ[D i | ℱ i] =ᵐ[μ] 0 :=
    condExp_squareError_eq_zero hM hQ hM2 (Nat.le_succ i)
  apply SimpleIntegral.integral_sq_sum_of_orthogonal
  · intro i _ j _
    exact (hY2 i).integrable_mul (hY2 j)
  · intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact SimpleIntegral.predictable_increments_orthogonal
        ℱ H D hH hD hDint hY2 hzero hij
    · simpa only [mul_comm] using
        SimpleIntegral.predictable_increments_orthogonal ℱ H D hH hD hDint hY2 hzero hji

theorem weighted_error_sq_le {h x a K : ℝ} (hK : 0 ≤ K) (hh : |h| ≤ K) :
    (h * (x ^ 2 - a)) ^ 2 ≤ 2 * K ^ 2 * (x ^ 4 + a ^ 2) := by
  have hh2 : h ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg h) hK).2 hh
  have he : (x ^ 2 - a) ^ 2 ≤ 2 * (x ^ 4 + a ^ 2) := by
    nlinarith [sq_nonneg (x ^ 2 + a)]
  calc
    (h * (x ^ 2 - a)) ^ 2 = h ^ 2 * (x ^ 2 - a) ^ 2 := mul_pow _ _ _
    _ ≤ K ^ 2 * (x ^ 2 - a) ^ 2 := mul_le_mul_of_nonneg_right hh2 (sq_nonneg _)
    _ ≤ K ^ 2 * (2 * (x ^ 4 + a ^ 2)) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = 2 * K ^ 2 * (x ^ 4 + a ^ 2) := by ring

theorem integral_weighted_error_sq_le [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {M A H : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hD4 : ∀ i, MemLp (fun ω => (increment M i (i + 1) ω) ^ 2) 2 μ)
    (hA2 : ∀ i, MemLp (increment A i (i + 1)) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ) ≤
      2 * K ^ 2 * ∑ i ∈ s,
        ((∫ ω, (increment M i (i + 1) ω) ^ 4 ∂μ) +
          ∫ ω, (increment A i (i + 1) ω) ^ 2 ∂μ) := by
  have hY2 (i : ℕ) : MemLp (fun ω => H i ω * squareError M A i (i + 1) ω) 2 μ := by
    have hHtop : MemLp (H i) ⊤ μ := memLp_top_of_bound
      ((hH i).mono (ℱ.le i)).aestronglyMeasurable K (by simpa only [Real.norm_eq_abs] using hbound i)
    exact hHtop.fun_mul ((hD4 i).sub (hA2 i))
  rw [weighted_error_isometry hM hQ hM2 hH hY2 s, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hfour : Integrable (fun ω => (increment M i (i + 1) ω) ^ 4) μ := by
    simpa only [← pow_mul] using (hD4 i).integrable_sq
  calc
    (∫ ω, (H i ω * squareError M A i (i + 1) ω) ^ 2 ∂μ) ≤
        ∫ ω, 2 * K ^ 2 * ((increment M i (i + 1) ω) ^ 4 +
          (increment A i (i + 1) ω) ^ 2) ∂μ := by
      apply integral_mono_ae (hY2 i).integrable_sq
        ((hfour.add (hA2 i).integrable_sq).const_mul _)
      filter_upwards [hbound i] with ω hω
      exact weighted_error_sq_le hK hω
    _ = _ := by rw [integral_const_mul, integral_add hfour (hA2 i).integrable_sq]

theorem integral_grid_weighted_error_sq_le [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[ℱ (t i)] (H i))
    (hD4 : ∀ i, MemLp (fun ω => (increment M (t i) (t (i + 1)) ω) ^ 2) 2 μ)
    (hA2 : ∀ i, MemLp (increment A (t i) (t (i + 1))) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K)
    (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * squareError M A (t i) (t (i + 1)) ω) ^ 2 ∂μ) ≤
      2 * K ^ 2 * ∑ i ∈ s,
        ((∫ ω, (increment M (t i) (t (i + 1)) ω) ^ 4 ∂μ) +
          ∫ ω, (increment A (t i) (t (i + 1)) ω) ^ 2 ∂μ) := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => ℱ (t i), fun _ _ hij => ℱ.mono (ht hij), fun i => ℱ.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨fun i => hM.stronglyMeasurable (t i), fun _ _ hij => hM.condExp_ae_eq (ht hij)⟩
  have hQG : Martingale (fun i ω => (M (t i) ω) ^ 2 - A (t i) ω) G μ :=
    ⟨fun i => hQ.stronglyMeasurable (t i), fun _ _ hij => hQ.condExp_ae_eq (ht hij)⟩
  exact integral_weighted_error_sq_le hMG hQG (fun i => hM2 (t i))
    hH hD4 hA2 hK hbound s

theorem memLp_finite_grid_weighted_error
    {I : Type*} {M A : I → Ω → ℝ} (t : ℕ → I) (H : ℕ → Ω → ℝ) (N : ℕ)
    (hH : ∀ i < N, AEStronglyMeasurable (H i) μ)
    (hD4 : ∀ i < N,
      MemLp (fun ω => (increment M (t i) (t (i + 1)) ω) ^ 2) 2 μ)
    (hA2 : ∀ i < N, MemLp (increment A (t i) (t (i + 1))) 2 μ)
    {K : ℝ} (hbound : ∀ i < N, ∀ᵐ ω ∂μ, |H i ω| ≤ K) :
    MemLp (fun ω => ∑ i ∈ Finset.range N,
      H i ω * squareError M A (t i) (t (i + 1)) ω) 2 μ := by
  apply memLp_finsetSum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hHtop : MemLp (H i) ⊤ μ := memLp_top_of_bound (hH i hi') K
    (by simpa only [Real.norm_eq_abs] using hbound i hi')
  exact hHtop.fun_mul ((hD4 i hi').sub (hA2 i hi'))

theorem integral_finite_grid_weighted_error_sq_le [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → I) (ht : Monotone t) (H : ℕ → Ω → ℝ) (N : ℕ)
    (hH : ∀ i < N, StronglyMeasurable[ℱ (t i)] (H i))
    (hD4 : ∀ i < N,
      MemLp (fun ω => (increment M (t i) (t (i + 1)) ω) ^ 2) 2 μ)
    (hA2 : ∀ i < N, MemLp (increment A (t i) (t (i + 1))) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ i < N, ∀ᵐ ω ∂μ, |H i ω| ≤ K) :
    (∫ ω, (∑ i ∈ Finset.range N,
      H i ω * squareError M A (t i) (t (i + 1)) ω) ^ 2 ∂μ) ≤
      2 * K ^ 2 * ∑ i ∈ Finset.range N,
        ((∫ ω, (increment M (t i) (t (i + 1)) ω) ^ 4 ∂μ) +
          ∫ ω, (increment A (t i) (t (i + 1)) ω) ^ 2 ∂μ) := by
  let u : ℕ → I := fun i => t (min i N)
  let G : ℕ → Ω → ℝ := fun i => if i < N then H i else 0
  have hu (i : ℕ) (hi : i ≤ N) : u i = t i := by simp only [u, min_eq_left hi]
  have huend (i : ℕ) (hi : N ≤ i) : u i = t N := by simp only [u, min_eq_right hi]
  have hmono : Monotone u := fun i j hij => ht (min_le_min_right N hij)
  have hG (i : ℕ) : StronglyMeasurable[ℱ (u i)] (G i) := by
    by_cases hi : i < N
    · rw [hu i hi.le]
      simpa only [G, ite_eq_left hi] using hH i hi
    · simp only [G, ite_eq_right hi]
      exact stronglyMeasurable_zero
  have hD (i : ℕ) : MemLp (fun ω => (increment M (u i) (u (i + 1)) ω) ^ 2) 2 μ := by
    by_cases hi : i < N
    · simpa only [hu i hi.le, hu (i + 1) (Nat.succ_le_of_lt hi)] using hD4 i hi
    · have hNi := Nat.le_of_not_gt hi
      simp only [huend i hNi, huend (i + 1) (hNi.trans (Nat.le_succ i)), increment,
        sub_self, zero_pow (by norm_num : 2 ≠ 0)]
      exact MemLp.zero
  have hA (i : ℕ) : MemLp (increment A (u i) (u (i + 1))) 2 μ := by
    by_cases hi : i < N
    · simpa only [hu i hi.le, hu (i + 1) (Nat.succ_le_of_lt hi)] using hA2 i hi
    · have hNi := Nat.le_of_not_gt hi
      rw [huend i hNi, huend (i + 1) (hNi.trans (Nat.le_succ i))]
      have hz : increment A (t N) (t N) = 0 := by
        funext ω
        exact sub_self _
      rw [hz]
      exact MemLp.zero
  have hB (i : ℕ) : ∀ᵐ ω ∂μ, |G i ω| ≤ K := by
    by_cases hi : i < N
    · simpa only [G, ite_eq_left hi] using hbound i hi
    · exact Filter.Eventually.of_forall (fun _ => by simpa only [G, ite_eq_right hi,
        Pi.zero_apply, abs_zero] using hK)
  have he := integral_grid_weighted_error_sq_le hM hQ hM2 u hmono G hG hD hA hK hB
    (Finset.range N)
  have hsum (ω : Ω) : (∑ i ∈ Finset.range N,
      G i ω * squareError M A (u i) (u (i + 1)) ω) =
      ∑ i ∈ Finset.range N, H i ω * squareError M A (t i) (t (i + 1)) ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [G, ite_eq_left hi', hu i hi'.le, hu (i + 1) (Nat.succ_le_of_lt hi')]
  have henergy : (∑ i ∈ Finset.range N,
      ((∫ ω, (increment M (u i) (u (i + 1)) ω) ^ 4 ∂μ) +
        ∫ ω, (increment A (u i) (u (i + 1)) ω) ^ 2 ∂μ)) =
      ∑ i ∈ Finset.range N,
        ((∫ ω, (increment M (t i) (t (i + 1)) ω) ^ 4 ∂μ) +
          ∫ ω, (increment A (t i) (t (i + 1)) ω) ^ 2 ∂μ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [hu i hi'.le, hu (i + 1) (Nat.succ_le_of_lt hi')]
  simpa only [hsum, henergy] using he

theorem tendsto_integral_grid_weighted_error_sq [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ n i, StronglyMeasurable[ℱ (t n i)] (H n i))
    (hD4 : ∀ n i,
      MemLp (fun ω => (increment M (t n i) (t n (i + 1)) ω) ^ 2) 2 μ)
    (hA2 : ∀ n i, MemLp (increment A (t n i) (t n (i + 1))) 2 μ)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ n i, ∀ᵐ ω ∂μ, |H n i ω| ≤ K)
    (s : ℕ → Finset ℕ)
    (hsmall : Tendsto (fun n => ∑ i ∈ s n,
      ((∫ ω, (increment M (t n i) (t n (i + 1)) ω) ^ 4 ∂μ) +
        ∫ ω, (increment A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω,
      (∑ i ∈ s n, H n i ω * squareError M A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => integral_grid_weighted_error_sq_le hM hQ hM2 (t n) (ht n) (H n)
      (hH n) (hD4 n) (hA2 n) hK (hbound n) (s n))
  simpa only [mul_zero] using hsmall.const_mul (2 * K ^ 2)

theorem tendsto_integral_finite_grid_weighted_error_sq [IsFiniteMeasure μ]
    {I : Type*} [Preorder I] {ℱ : Filtration I mΩ} {M A : I → Ω → ℝ}
    (hM : Martingale M ℱ μ)
    (hQ : Martingale (fun t ω => (M t ω) ^ 2 - A t ω) ℱ μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ℕ → I) (ht : ∀ n, Monotone (t n)) (N : ℕ → ℕ)
    (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ n i, i < N n → StronglyMeasurable[ℱ (t n i)] (H n i))
    (hD4 : ∀ n i, i < N n →
      MemLp (fun ω => (increment M (t n i) (t n (i + 1)) ω) ^ 2) 2 μ)
    (hA2 : ∀ n i, i < N n → MemLp (increment A (t n i) (t n (i + 1))) 2 μ)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ n i, i < N n → ∀ᵐ ω ∂μ, |H n i ω| ≤ K)
    (hfour : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, (increment M (t n i) (t n (i + 1)) ω) ^ 4 ∂μ) atTop (𝓝 0))
    (hcomp : Tendsto (fun n => ∑ i ∈ Finset.range (N n),
      ∫ ω, (increment A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (∑ i ∈ Finset.range (N n),
      H n i ω * squareError M A (t n i) (t n (i + 1)) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => integral_finite_grid_weighted_error_sq_le hM hQ hM2 (t n) (ht n)
      (H n) (N n) (hH n) (hD4 n) (hA2 n) hK (hbound n))
  simpa only [Finset.sum_add_distrib, add_zero, mul_zero] using
    (hfour.add hcomp).const_mul (2 * K ^ 2)

end Problem367.MartingaleQuadraticVariation

end

end OAI
