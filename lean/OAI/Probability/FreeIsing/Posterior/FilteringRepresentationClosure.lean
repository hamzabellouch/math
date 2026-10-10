import OAI.Probability.FreeIsing.Martingales.PredictableL2Completion

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Problem367.FilteringRepresentationClosure

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eq_of_cross_energy {x y : E}
    (hcross : inner ℝ x y = ‖y‖ ^ 2) (henergy : ‖x‖ ^ 2 = ‖y‖ ^ 2) :
    x = y := by
  have hz : ‖x - y‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hcross, henergy]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem cross_energy_of_approximations
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {α : Type*} {l : Filter α} [NeBot l]
    (x y : E) (c : K) (I : α → E) (G : α → K)
    (hI : Tendsto I l (𝓝 y)) (hG : Tendsto G l (𝓝 c))
    (htest : ∀ᶠ n in l, inner ℝ x (I n) = inner ℝ c (G n)) :
    inner ℝ x y = ‖c‖ ^ 2 := by
  have hleft := (tendsto_const_nhds (x := x)).inner (𝕜 := ℝ) hI
  have hright := (tendsto_const_nhds (x := c)).inner (𝕜 := ℝ) hG
  rw [real_inner_self_eq_norm_sq] at hright
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright htest

theorem eq_of_approximations_and_energy
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {α : Type*} {l : Filter α} [NeBot l]
    (x y : E) (c : K) (I : α → E) (G : α → K)
    (hI : Tendsto I l (𝓝 y)) (hG : Tendsto G l (𝓝 c))
    (htest : ∀ᶠ n in l, inner ℝ x (I n) = inner ℝ c (G n))
    (hisometry : ‖y‖ ^ 2 = ‖c‖ ^ 2)
    (henergy : ‖x‖ ^ 2 = ‖c‖ ^ 2) : x = y := by
  apply eq_of_cross_energy
  · exact (cross_energy_of_approximations x y c I G hI hG htest).trans
      hisometry.symm
  · exact henergy.trans hisometry.symm

theorem norm_finset_sum_sq
    {ι : Type*} (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0) (s : Finset ι) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq (f i)
  · intro j hj hji
    exact horth hji
  · exact fun h => (h hi).elim

theorem norm_residual_sq_eq_sub_sum
    {ι : Type*} (x : E) (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hcross : ∀ i, inner ℝ x (f i) = ‖f i‖ ^ 2) (s : Finset ι) :
    ‖x - ∑ i ∈ s, f i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i ∈ s, ‖f i‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_finset_sum_sq f horth, inner_sum]
  simp only [hcross]
  ring

theorem norm_residual_sq_eq_tsum_compl
    {ι : Type*} (x : E) (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hsum : Summable fun i => ‖f i‖ ^ 2)
    (hcross : ∀ i, inner ℝ x (f i) = ‖f i‖ ^ 2)
    (henergy : ‖x‖ ^ 2 = ∑' i, ‖f i‖ ^ 2) (s : Finset ι) :
    ‖x - ∑ i ∈ s, f i‖ ^ 2 = ∑' i : {i // i ∉ s}, ‖f i‖ ^ 2 := by
  rw [norm_residual_sq_eq_sub_sum x f horth hcross, henergy]
  have hsplit := hsum.sum_add_tsum_compl (s := s)
  change (∑ i ∈ s, ‖f i‖ ^ 2) +
    (∑' i : {i // i ∉ s}, ‖f i‖ ^ 2) = ∑' i, ‖f i‖ ^ 2 at hsplit
  linarith

variable [CompleteSpace E]

theorem hasSum_of_orthogonal_cross_energy
    {ι : Type*} (x : E) (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hsum : Summable fun i => ‖f i‖ ^ 2)
    (hcross : ∀ i, inner ℝ x (f i) = ‖f i‖ ^ 2)
    (henergy : ‖x‖ ^ 2 = ∑' i, ‖f i‖ ^ 2) : HasSum f x := by
  have hf := PredictableL2.summable_of_orthogonal_sq f horth hsum
  have hinner := hf.hasSum.mapL (innerSL ℝ x)
  change HasSum (fun i => inner ℝ x (f i)) (inner ℝ x (∑' i, f i)) at hinner
  simp only [hcross] at hinner
  have hcross' : inner ℝ x (∑' i, f i) = ‖∑' i, f i‖ ^ 2 := by
    rw [PredictableL2.norm_tsum_sq_of_orthogonal f horth hsum]
    exact hinner.unique hsum.hasSum
  have henergy' : ‖x‖ ^ 2 = ‖∑' i, f i‖ ^ 2 := by
    rw [PredictableL2.norm_tsum_sq_of_orthogonal f horth hsum]
    exact henergy
  rw [eq_of_cross_energy hcross' henergy']
  exact hf.hasSum

end Hilbert

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ae_eq_of_cross_second_moment
    {M I : Ω → ℝ} (hM : MemLp M 2 μ) (hI : MemLp I 2 μ)
    (hcross : (∫ ω, M ω * I ω ∂μ) = ∫ ω, I ω ^ 2 ∂μ)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∫ ω, I ω ^ 2 ∂μ) : M =ᵐ[μ] I := by
  apply (hM.toLp_eq_toLp_iff hI).mp
  apply eq_of_cross_energy
  · simpa only [PredictableL2.inner_toLp, PredictableL2.norm_toLp_sq] using hcross
  · simpa only [PredictableL2.norm_toLp_sq] using henergy

theorem tendsto_toLp_of_integral_sq_error
    {α : Type*} {l : Filter α} {F : α → Ω → ℝ} {Y : Ω → ℝ}
    (hF : ∀ n, MemLp (F n) 2 μ) (hY : MemLp Y 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, (F n ω - Y ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => (hF n).toLp (F n)) l (𝓝 (hY.toLp Y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heq (n : α) : (∫ ω, (F n ω - Y ω) ^ 2 ∂μ) =
      ‖(hF n).toLp (F n) - hY.toLp Y‖ ^ 2 := by
    exact (PredictableL2.norm_toLp_sq ((hF n).sub hY)).symm
  have h := hlim.sqrt
  simpa only [heq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

theorem integral_mul_eq_of_meanSquare_limit
    {α : Type*} {l : Filter α} [NeBot l]
    {M I : Ω → ℝ} {S : α → Ω → ℝ} {a : ℝ}
    (hM : MemLp M 2 μ) (hI : MemLp I 2 μ)
    (hS : ∀ n, MemLp (S n) 2 μ)
    (hSlim : Tendsto (fun n => ∫ ω, (S n ω - I ω) ^ 2 ∂μ) l (𝓝 0))
    (hcross : Tendsto (fun n => ∫ ω, M ω * S n ω ∂μ) l (𝓝 a)) :
    (∫ ω, M ω * I ω ∂μ) = a := by
  have h := (tendsto_const_nhds (x := hM.toLp M)).inner (𝕜 := ℝ)
    (tendsto_toLp_of_integral_sq_error hS hI hSlim)
  simp only [PredictableL2.inner_toLp] at h
  exact tendsto_nhds_unique h hcross

theorem tendsto_integral_sq_fintype_sum_error
    {ι α : Type*} [Fintype ι] {l : Filter α}
    {I : ι → Ω → ℝ} {S : ι → α → Ω → ℝ}
    (hI : ∀ i, MemLp (I i) 2 μ) (hS : ∀ i n, MemLp (S i n) 2 μ)
    (hlim : ∀ i, Tendsto (fun n => ∫ ω, (S i n ω - I i ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ ω, ((∑ i, S i n ω) - ∑ i, I i ω) ^ 2 ∂μ) l (𝓝 0) := by
  classical
  have h := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_toLp_of_integral_sq_error (hS i) (hI i) (hlim i))
  have hn := (h.sub (tendsto_const_nhds (x := ∑ i, (hI i).toLp (I i)))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
  apply hn.congr'
  apply Eventually.of_forall
  intro n
  have he := PredictableL2.norm_toLp_sq
    ((memLp_finsetSum Finset.univ (fun i _ => hS i n)).sub
      (memLp_finsetSum Finset.univ (fun i _ => hI i)))
  change ‖(memLp_finsetSum Finset.univ (fun i _ => hS i n)).toLp
    (fun ω => ∑ i, S i n ω) - (memLp_finsetSum Finset.univ (fun i _ => hI i)).toLp
    (fun ω => ∑ i, I i ω)‖ ^ 2 = _ at he
  rw [PredictableL2.toLp_finsetSum, PredictableL2.toLp_finsetSum] at he
  exact he

theorem ae_eq_of_approximations_and_energy
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ}
    {α : Type*} {l : Filter α} [NeBot l]
    {M I : Ω → ℝ} {C : Ξ → ℝ} {S : α → Ω → ℝ} {G : α → Ξ → ℝ}
    (hM : MemLp M 2 μ) (hI : MemLp I 2 μ) (hC : MemLp C 2 ν)
    (hS : ∀ n, MemLp (S n) 2 μ) (hG : ∀ n, MemLp (G n) 2 ν)
    (hSlim : Tendsto (fun n => ∫ ω, (S n ω - I ω) ^ 2 ∂μ) l (𝓝 0))
    (hGlim : Tendsto (fun n => ∫ ξ, (G n ξ - C ξ) ^ 2 ∂ν) l (𝓝 0))
    (htest : ∀ᶠ n in l,
      (∫ ω, M ω * S n ω ∂μ) = ∫ ξ, C ξ * G n ξ ∂ν)
    (hisometry : (∫ ω, I ω ^ 2 ∂μ) = ∫ ξ, C ξ ^ 2 ∂ν)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∫ ξ, C ξ ^ 2 ∂ν) : M =ᵐ[μ] I := by
  apply (hM.toLp_eq_toLp_iff hI).mp
  apply eq_of_approximations_and_energy (hM.toLp M) (hI.toLp I) (hC.toLp C)
    (fun n => (hS n).toLp (S n)) (fun n => (hG n).toLp (G n))
    (tendsto_toLp_of_integral_sq_error hS hI hSlim)
    (tendsto_toLp_of_integral_sq_error hG hC hGlim)
  · simpa only [PredictableL2.inner_toLp] using htest
  · simpa only [PredictableL2.norm_toLp_sq] using hisometry
  · simpa only [PredictableL2.norm_toLp_sq] using henergy

theorem integral_sq_residual_eq_tsum_compl
    {ι : Type*} {M : Ω → ℝ} (hM : MemLp M 2 μ)
    (I : ι → Ω → ℝ) (hI : ∀ i, MemLp (I i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, I i ω * I j ω ∂μ = 0)
    (hsum : Summable fun i => ∫ ω, I i ω ^ 2 ∂μ)
    (hcross : ∀ i, (∫ ω, M ω * I i ω ∂μ) = ∫ ω, I i ω ^ 2 ∂μ)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∑' i, ∫ ω, I i ω ^ 2 ∂μ)
    (s : Finset ι) :
    (∫ ω, (M ω - ∑ i ∈ s, I i ω) ^ 2 ∂μ) =
      ∑' i : {i // i ∉ s}, ∫ ω, I i ω ^ 2 ∂μ := by
  have hnorm := PredictableL2.norm_toLp_sq
    (hM.sub (memLp_finsetSum s (fun i _ => hI i)))
  change ‖hM.toLp M - (memLp_finsetSum s (fun i _ => hI i)).toLp
    (fun ω => ∑ i ∈ s, I i ω)‖ ^ 2 = _ at hnorm
  rw [PredictableL2.toLp_finsetSum] at hnorm
  simp only [Pi.sub_apply] at hnorm
  rw [← hnorm]
  have h := norm_residual_sq_eq_tsum_compl (hM.toLp M)
    (fun i => (hI i).toLp (I i))
    (by simpa only [PredictableL2.inner_toLp] using horth)
    (by simpa only [PredictableL2.norm_toLp_sq] using hsum)
    (by simpa only [PredictableL2.inner_toLp, PredictableL2.norm_toLp_sq] using hcross)
    (by simpa only [PredictableL2.norm_toLp_sq] using henergy) s
  simpa only [PredictableL2.norm_toLp_sq] using h

theorem hasSum_toLp_of_cross_energy
    {ι : Type*} {M : Ω → ℝ} (hM : MemLp M 2 μ)
    (I : ι → Ω → ℝ) (hI : ∀ i, MemLp (I i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, I i ω * I j ω ∂μ = 0)
    (hsum : Summable fun i => ∫ ω, I i ω ^ 2 ∂μ)
    (hcross : ∀ i, (∫ ω, M ω * I i ω ∂μ) = ∫ ω, I i ω ^ 2 ∂μ)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∑' i, ∫ ω, I i ω ^ 2 ∂μ) :
    HasSum (fun i => (hI i).toLp (I i)) (hM.toLp M) := by
  apply hasSum_of_orthogonal_cross_energy
  · intro i j hij
    simpa only [PredictableL2.inner_toLp] using horth hij
  · simpa only [PredictableL2.norm_toLp_sq] using hsum
  · intro i
    simpa only [PredictableL2.inner_toLp, PredictableL2.norm_toLp_sq] using hcross i
  · simpa only [PredictableL2.norm_toLp_sq] using henergy

theorem ae_eq_fintype_sum_of_cross_energy
    {ι : Type*} [Fintype ι] {M : Ω → ℝ} (hM : MemLp M 2 μ)
    (I : ι → Ω → ℝ) (hI : ∀ i, MemLp (I i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, I i ω * I j ω ∂μ = 0)
    (hcross : ∀ i, (∫ ω, M ω * I i ω ∂μ) = ∫ ω, I i ω ^ 2 ∂μ)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∑ i, ∫ ω, I i ω ^ 2 ∂μ) :
    M =ᵐ[μ] fun ω => ∑ i, I i ω := by
  classical
  have hs := hasSum_toLp_of_cross_energy hM I hI horth (hasSum_fintype _).summable
    hcross (by simpa only [tsum_fintype] using henergy)
  have heq := hs.unique (hasSum_fintype (fun i => (hI i).toLp (I i)))
  apply (hM.toLp_eq_toLp_iff (memLp_finsetSum Finset.univ (fun i _ => hI i))).mp
  rw [PredictableL2.toLp_finsetSum]
  exact heq

theorem tendsto_integral_sq_residual
    {ι : Type*} {M : Ω → ℝ} (hM : MemLp M 2 μ)
    (I : ι → Ω → ℝ) (hI : ∀ i, MemLp (I i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, I i ω * I j ω ∂μ = 0)
    (hsum : Summable fun i => ∫ ω, I i ω ^ 2 ∂μ)
    (hcross : ∀ i, (∫ ω, M ω * I i ω ∂μ) = ∫ ω, I i ω ^ 2 ∂μ)
    (henergy : (∫ ω, M ω ^ 2 ∂μ) = ∑' i, ∫ ω, I i ω ^ 2 ∂μ) :
    Tendsto (fun s : Finset ι => ∫ ω, ((∑ i ∈ s, I i ω) - M ω) ^ 2 ∂μ)
      atTop (𝓝 0) :=
  PredictableL2.tendsto_integral_sq_error_of_hasSum I hI hM
    (hasSum_toLp_of_cross_energy hM I hI horth hsum hcross henergy)

end RandomVariables

end Problem367.FilteringRepresentationClosure

end

end OAI
