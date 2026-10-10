import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmallClassSum
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLinearKernel

namespace OAI

/-! Actual logarithmic frequency classes enter the short-window kernel.
The resulting bound separates the no-small-band energy. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

theorem mrt_log_kernel_bound (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hH : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N : ℕ} (hN : 0 < N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {T δ : ℝ} (hT : 0 < T) (hTN : T ≤ N) (hδ : 0 ≤ δ)
    (hnone : ∀ v : ℝ, T ≤ v → v ≤ N →
      (∫ t in Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
          δ*(v/N+1)) :
    (∫ t : ℝ, mrtShortKernel T t *
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      6*(δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
        1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+T*Q/N)) +
        64*Real.exp 1*(T/N)^2 := by
  let A := δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹
  let B := 1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hε : 0 ≤ A+B*(1+T*Q/N) := by positivity
  have hs (v : ℝ) (hv : T ≤ v) (hvN : v ≤ N) :
      (∫ t in -v..v,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
        (A+B*(1+T*Q/N))*(v/T+1) := by
    have hv0 : 0 < v := hT.trans_le hv
    have he := mrt_log_energy_partition_bound V J hprime hdis hP0 hQ0 hP hQ hPQ
      hη hη' hbudget hH hrange hN hsize F hF hFb hv0
    calc
      _ ≤ δ*(v/N+1) +
          (33792*Real.exp 1*(v/N+1)*(mrtBaseResolution P Q η)⁻¹ +
          1024*Real.exp 2*(v*Q/N+1)*(mrtBaseResolution P Q η)⁻¹ +
          2*(v/N+1)*P⁻¹) := he.trans (add_le_add (hnone v hv hvN) le_rfl)
      _ = A*(v/N+1)+B*(v*Q/N+1) := by dsimp [A, B]; ring
      _ ≤ _ := mrt_linear_prefix_two_slopes (by exact_mod_cast hN) hT hTN hQ0.le
        hv0.le hA hB
  exact mrt_dyadic_kernel_linear_height _ hN
    (fun n hn => mrtTypicalCoefficient_oneBounded _ _ _ hFb n
      (hN.trans (Finset.mem_Ioc.mp hn).1)) hT hTN hε hs

end TwoPointCorrelations

end OAI
