import OAI.NumberTheory.TwoPoint.Halasz.HalaszCofactorScale

namespace OAI

/-! The actual extra-prime cofactor has uniform decay off the original
minimizing twist. All floor and band-count losses have been absorbed. -/
namespace TwoPointCorrelations

open Filter Finset

theorem HalaszHighPrimeInput.extra_cofactor (hhigh : HalaszHighPrimeInput) :
    ∀ᶠ N : ℕ in atTop, ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
      ∀ (A : Finset ℕ), (∀ p ∈ A, p.Prime) →
      ∀ a : ℝ, 1 ≤ a → a ≤ Real.exp (Real.log N/Real.log (Real.log N)) →
      ∀ t τ : ℝ, |t| ≤ N → |τ| ≤ 2*N →
      (∀ v : ℝ, |v| ≤ 2*N → squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
      (Real.log N)^(1/16:ℝ) ≤ |t-τ| →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        2*(Real.log N)^(-1/40:ℝ) := by
  obtain ⟨X₀,hcofactor⟩ := hhigh.actual_cofactor
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hcofactor
  filter_upwards [halasz_cofactor_floor_scale X₀ n₀,eventually_ge_atTop 2]
    with N hscale hN
  intro F hF1 hFm hFb P Q J hQ hband A hA a ha haU t τ ht hτ hmin haway
  let n := ⌊(2*N:ℝ)/a⌋₊
  obtain ⟨hbase,hnlarge,hnupper,hncube,hloglow,hlogupper,hwidth⟩ := hscale a ha haU
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hLN : 0 < Real.log (N:ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hdec := halasz_cofactor_scale_decay hLN hloglow hlogupper
  have hband' : mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log (2*N:ℕ))) := by
    apply hband.trans
    apply Real.exp_le_exp.mpr
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log hN0
    exact_mod_cast (show N≤2*N by omega)
  have ht' : |t|+Real.log (n:ℝ)^8 ≤ (2*N:ℕ) := by
    push_cast
    linarith
  have hτ' : |τ| ≤ (2*N:ℕ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hτ
  have hmin' : ∀ v:ℝ, |v| ≤ (2*N:ℕ) →
      squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmin
  have hh := hn₀ n hnlarge N a ha hbase rfl (2*N) hnupper hncube
    F hF1 hFm hFb P Q J hQ hband' A hA t τ hτ' hmin' ht' (hdec.1.trans haway)
  exact hh.trans hdec.2

end TwoPointCorrelations

end OAI
