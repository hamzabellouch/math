import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalKernelSharp
import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortMean
import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandDensity
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogShortQuarter

namespace OAI

/-! The short-window energy of the literal typical coefficient, before
any exceptional integers are removed. The original distance scale and
frequency height are unchanged. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_typical_short_energy_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 → ∀ H : ℕ, 4 ≤ H → H ≤ N → 2*Q ≤ (N:ℝ) →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) H 0 x‖^2)/
        ((N:ℝ)*(H:ℝ)^2)  ≤
      (139968/(2*Real.pi))*(12*(C*(Real.exp (-4*M/5)+
        Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))+
        33792*Real.exp 1*(mrtBaseResolution P Q (1/100))⁻¹+2*P⁻¹+
        1024*Real.exp 2*(mrtBaseResolution P Q (1/100))⁻¹*(1+Q/H))+
        2048*Real.exp 1/(H:ℝ)^2) := by
  obtain ⟨C,hC,hkernel⟩ := halasz_typical_kernel_bound_sharp hprime hhigh
  refine ⟨C,hC,?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hkernel,hl] with N hkernel hL
  intro P Q hP hPQ hlP hlQ hbudget hres J hJ hbands X hNX hXN H hH hHN hsize F hF1 hFc hFb M hM hd
  have hFm : Multiplicative F := fun a b ha hb _ => hFc a b ha hb
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let δ := C*(Real.exp (-4*M/5)+Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))
  have hδ : 0 ≤ δ := by
    have hLL : 0 ≤ Real.log (Real.log (N:ℝ)) := Real.log_nonneg hL
    dsimp [δ]
    positivity
  have hk := hkernel F hF1 hFc hFb P Q hP hPQ (by linarith) hlQ hres J hJ
    (fun k hk => ⟨(hbands k hk).1,(hbands k hk).2 J (mem_Icc.mpr ⟨hJ,le_rfl⟩)⟩)
    X hNX hXN M hM hd
  have hprimeV : ∀ j ∈ Icc 1 J, ∀ p ∈ V j, p.Prime := fun _ _ _ hp => mrtPrimeBand_prime hp
  have hdis : Set.PairwiseDisjoint (Icc 1 J : Set ℕ) V :=
    halasz_actual_bands_disjoint P Q J hP hPQ (by linarith)
  have hrange : ∀ j ∈ Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j := by
    intro j _ p hp
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp
    exact ⟨hh.1.le,hh.2⟩
  exact mrt_log_short_energy_quarter V J hprimeV hdis (by linarith) (by linarith)
    hlP hlQ (Real.log_le_log (by linarith) hPQ) (by norm_num : (0:ℝ) < 1/100)
    (by norm_num : (1/100:ℝ) ≤ 1/12) hbudget hres hrange hH hHN hsize F hFm hFb hδ
    (fun k hk' v hv hvk => hk k hk' v
      ((div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg H)).trans hv) hvk)

end TwoPointCorrelations

end OAI
