import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogShortEnergy

namespace OAI

/-! The short-window kernel needs spectral information only below one quarter
of the polynomial length. The rest uses the unconditional mean square. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

theorem mrt_dyadic_kernel_quarter_height (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1)
    {T ε : ℝ} (hT : 0 < T) (hTN : T ≤ (N:ℝ)/4) (hε : 0 ≤ ε)
    (hsmall : ∀ v, T ≤ v → v ≤ (N:ℝ)/4 →
      (∫ t in -v..v, ‖mrtDyadicPolynomial b N t‖^2) ≤ ε*(v/T+1)) :
    (∫ t : ℝ, mrtShortKernel T t * ‖mrtDyadicPolynomial b N t‖^2) ≤
      6*ε+1024*Real.exp 1*(T/N)^2 := by
  let C : ℝ := (∑ n ∈ Finset.Ioc N (2*N), ‖b n‖*Real.exp (-Real.log (n:ℝ)))^2
  have he (t : ℝ) : mrtLogDirichlet (Finset.Ioc N (2*N)) b t =
      mrtDyadicPolynomial b N t :=
    mrt_log_dirichlet_polynomial _ (fun n hn =>
      lt_trans hN (Finset.mem_Ioc.mp hn).1) b t
  have hFc : Continuous (fun t => ‖mrtDyadicPolynomial b N t‖^2) :=
    (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hbound (t : ℝ) : ‖mrtDyadicPolynomial b N t‖^2 ≤ C := by
    rw [← he]
    exact pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm _ _ t) 2
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hquarter : 0 < (N:ℝ)/4 := by positivity
  have hglobal (v : ℝ) (hv : (N:ℝ)/4 ≤ v) :
      (∫ t in -v..v, ‖mrtDyadicPolynomial b N t‖^2) ≤
        (16*Real.exp 1)*(v/((N:ℝ)/4)+1) := by
    have hh := mrt_dyadic_mean_square b hN hb (hquarter.trans_le hv)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (div_le_div_of_nonneg_left (hquarter.trans_le hv).le hquarter
      (by linarith)) le_rfl
  have hm := mrt_short_kernel_linear_height _ hFc (fun _ => sq_nonneg _)
    hbound hquarter hT hTN hε (by positivity : 0 ≤ 16*Real.exp 1) hsmall hglobal
  apply hm.trans_eq
  field_simp [hNr.ne']
  ring

theorem mrt_log_kernel_quarter_bound (V : ℕ → Finset ℕ) (J : ℕ)
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
    {T δ : ℝ} (hT : 0 < T) (hTN : T ≤ (N:ℝ)/4) (hδ : 0 ≤ δ)
    (hnone : ∀ v : ℝ, T ≤ v → v ≤ (N:ℝ)/4 →
      (∫ t in Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
          δ*(v/N+1)) :
    (∫ t : ℝ, mrtShortKernel T t *
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) N t‖^2) ≤
      6*(δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
        1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+T*Q/N)) +
        1024*Real.exp 1*(T/N)^2 := by
  let A := δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹
  let B := 1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hε : 0 ≤ A+B*(1+T*Q/N) := by positivity
  have hs (v : ℝ) (hv : T ≤ v) (hvN : v ≤ (N:ℝ)/4) :
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
      _ ≤ _ := mrt_linear_prefix_two_slopes (by exact_mod_cast hN) hT (by linarith : T ≤ (N:ℝ)) hQ0.le
        hv0.le hA hB
  exact mrt_dyadic_kernel_quarter_height _ hN
    (fun n hn => mrtTypicalCoefficient_oneBounded _ _ _ hFb n
      (hN.trans (Finset.mem_Ioc.mp hn).1)) hT hTN hε hs

end TwoPointCorrelations

end OAI
