import OAI.NumberTheory.TwoPoint.Halasz.HalaszOriginalKernel
import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortMean
import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandDensity
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogShortQuarter

namespace OAI

/-! Literal short-interval L1 means with one original distance cutoff
and exactly its published frequency range. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_original_short_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 →
      ∀ H : ℕ, 4 ≤ H → H ≤ N → 2*Q ≤ (N:ℝ) →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u:ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum F H 0 x‖)/((N:ℝ)*H) ≤
        Real.sqrt ((139968/(2*Real.pi)) *
          (12*(C₁*((Real.log P/Real.log Q)^2+Real.exp (-M)+
              Real.log (Real.log N)/(Real.log N)^(1/100:ℝ)) +
            33792*Real.exp 1*(mrtBaseResolution P Q (1/100))⁻¹ + 2*P⁻¹ +
            1024*Real.exp 2*(mrtBaseResolution P Q (1/100))⁻¹*(1+Q/H)) +
            2048*Real.exp 1/(H:ℝ)^2)) + C₂*(Real.log P/Real.log Q) := by
  obtain ⟨C₁,hC₁,hkernel⟩ := halasz_original_kernel_bound hprime hhigh
  obtain ⟨C₂,hC₂,hdensity⟩ := mrt_typical_density
  refine ⟨C₁,2*C₂,hC₁,by positivity,?_⟩
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hkernel,hlog.eventually hdensity,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop 2]
    with N hkernel hdensity hL hN2
  intro P Q hP hPQ hlP hlQ hbudget hres J hJ hbands X hNX hXN H hH2 hHN hsize F hF1 hFm hFb M hM hd
  have hH : 0 < H := by omega
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let δ := C₁*((Real.log P/Real.log Q)^2+Real.exp (-M)+
    Real.log (Real.log N)/(Real.log N)^(1/100:ℝ))
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hR : 0 ≤ Real.log P/Real.log Q :=
    div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  have hLL : 0 ≤ Real.log (Real.log (N:ℝ)) := Real.log_nonneg hL
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hmax := (hbands N (by simp)).2
  have hk := hkernel F hF1 hFm hFb P Q hP hPQ hlQ hres J hJ
    (fun k hk => ⟨(hbands k hk).1,(hbands k hk).2 J (mem_Icc.mpr ⟨hJ,le_rfl⟩)⟩)
    X hNX hXN M hM hd
  have hprimeV : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, p.Prime :=
    fun _ _ _ hp => mrtPrimeBand_prime hp
  have hdis : Set.PairwiseDisjoint (Icc 1 J : Set ℕ) V :=
    halasz_actual_bands_disjoint P Q J hP hPQ (by linarith)
  have hrange : ∀ j ∈ Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j := by
    intro j _ p hp
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp
    exact ⟨hh.1.le,hh.2⟩
  have henergy := mrt_log_short_energy_quarter V J hprimeV hdis (by linarith) (by linarith)
    hlP hlQ (Real.log_le_log (by linarith) hPQ) (by norm_num : (0:ℝ)<1/100)
    (by norm_num : (1/100:ℝ)≤1/12) hbudget hres hrange hH2 hHN hsize F hFm hFb hδ
    (fun k hk' v hv hvk => hk k hk' v
      ((div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg H)).trans hv) hvk)
  have : NeZero (N+H) := ⟨by omega⟩
  have hscale : (1/2:ℝ)*Real.exp ((Real.log N)^(199/200:ℝ)) ≤ (N+H:ℕ) := by
    have hp := Real.rpow_le_self_of_one_le hL (show (199/200:ℝ)≤1 by norm_num)
    have he := Real.exp_le_exp.mpr hp
    rw [Real.exp_log hN0] at he
    have hn : (N:ℝ) ≤ (N+H:ℕ) := by exact_mod_cast (Nat.le_add_right N H)
    nlinarith [Real.exp_pos ((Real.log N)^(199/200:ℝ))]
  have hcut : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp ((Real.log N)^(99/100:ℝ)) :=
    mrt_common_density_cutoff hL J hmax
  have heq (n:ℕ) :
      mrtTypical univ (fun j:{j:ℕ // j∈(Icc 1 J:Finset ℕ)} => V j) n ↔
        mrtTypical (Icc 1 J) V n := by simp [mrtTypical]
  have hp := hdensity P Q J hP hPQ hlQ hcut (N+1) (N+H) hscale
  change (uniformFiniteLaw (Fin (N+H))).probability
    (fun n => ¬mrtTypical univ
      (fun j:{j:ℕ // j∈(Icc 1 J:Finset ℕ)} => V j) (N+1+n.val)) ≤ _ at hp
  have hp' : (uniformFiniteLaw (Fin (N+H))).probability
      (fun n => ¬mrtTypical (Icc 1 J) V (N+1+n.val)) ≤ C₂*(Real.log P/Real.log Q) := by
    simpa only [heq,mul_div_assoc] using hp
  have hmean := halasz_short_mean_transfer (Icc 1 J) V F hFb hH hHN
    (mul_nonneg hC₂.le hR) hp' henergy
  simpa only [δ,mul_assoc] using hmean

end TwoPointCorrelations

end OAI
