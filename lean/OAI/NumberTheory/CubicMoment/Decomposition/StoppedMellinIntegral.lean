import OAI.NumberTheory.CubicMoment.Decomposition.StoppedEarlyDivisorMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorMellinTail
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinScale
import OAI.NumberTheory.CubicMoment.Estimates.LowCoreMellinIntegral

namespace OAI

/-! The full arithmetic Mellin integral for the actual early-stopped
coefficient. Pointwise Kummer cancellation controls the central interval;
the proved divisor-weighted mean controls its two infinite tails. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_arithmetic_mellin_integral
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S U : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ p ∈ U, primaryPrime p) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
        stoppedDivisorMass X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) e S U) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨Kt,Ct,hKt,htail⟩ := bounded_divisor_arithmetic_mellin_tail
    hpnt hMV hC hHuxley m hm Φ hΦ hΦ' k q
  obtain ⟨Kn,hKn,hnear⟩ := stopped_early_divisor_noncube_mass (ι := ι)
    hpnt hSW hHuxley hξ hξz hκ
    (show (0:ℝ) ≤ ((max (Ct+1) H+1:ℕ):ℝ) by positivity) hF hJ k
  obtain ⟨A,hA,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  obtain ⟨D,hD,hmoment⟩ := arithmeticMellinCoefficient_moment_decay m hm Φ hΦ hΦ' q 0
  refine ⟨Kn*D+Kt*A^2*(4/κ^k),by positivity,?_⟩
  filter_upwards [hnear,hcoeff,stopped_divisor_cutoff_geometry hκ,
    eventually_ge_atTop (Real.exp 1),Real.tendsto_log_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop ((3:ℝ)^Ct)]
    with X hnear hcoeff hgeometry hX hL2 hLC
  intro δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb W hW hWi hWd
    S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  obtain ⟨hb1,hbceil,hceil,hloglo,hloghi⟩ := stopped_mellin_ceil_scale hX hκ hb hbX
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hLp : 0 < Real.log X := by linarith
  obtain ⟨_,hN,hsize⟩ := hgeometry b B hb hBb
  have hqb : b/b^(1/8:ℝ) ≤ b := div_le_self hbp.le (Real.one_le_rpow hb1 (by norm_num))
  have hbmin : 65536 ≤ b := hN.trans hqb
  let N := ⌈b⌉₊
  let T := (1+Real.log (N:ℝ))^Ct
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let P := stoppedIntervalSupport ι X l b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  let G := fun t => divisorCharacterMass P S U β (t+u)
  let f := fun t => (1+ρ)^q*‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖
  let B₀ := Kn*b^2*B^(1/3:ℝ)/(Real.log X)^k
  have hNmin : 65536 ≤ (N:ℝ) := hbmin.trans hbceil
  have hN1 : 1 ≤ (N:ℝ) := hb1.trans hbceil
  have hNp : 0 < (N:ℝ) := zero_lt_one.trans_le hN1
  have hT1 : 1 ≤ T := one_le_pow₀ (by linarith [Real.log_nonneg hN1])
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have hTlog : T ≤ (Real.log X)^(Ct+1) :=
    stopped_mellin_cutoff_scale (by linarith) Ct
      (by linarith [Real.log_nonneg hN1]) hloghi hLC
  have hP : ∀ n ∈ P, primary n ∧ Squarefree n ∧ norm n ≤ (N:ℝ) := by
    intro n hn
    have hs := stoppedIntervalSupport_spec X l b e hn
    exact ⟨hs.1,hs.2.1,hs.2.2.trans hbceil⟩
  have hβ : ∀ n ∈ P, ‖β n‖ ≤ A :=
    (hcoeff W hW selected 0 l b e hbp.le hbX).1
  have hsizeN : 8*B ≤ (N:ℝ)^(3/4:ℝ) := hsize.trans
    (Real.rpow_le_rpow (by positivity) (hqb.trans hbceil) (by norm_num))
  have hG : Continuous G :=
    (divisorCharacterMass_continuous P S U β).comp (continuous_id.add continuous_const)
  have hGbound := divisorCharacterMass_bound P S U β (fun n hn => (hP n hn).1)
  have hfi : Integrable f :=
    (arithmeticMellinCoefficient_integrable m hm Φ hΦ hΦ' ρ).norm.const_mul _
  have hfg : Integrable (fun t => f t*G t) := hfi.mul_bdd hG.aestronglyMeasurable
    (Eventually.of_forall (fun t => hGbound (t+u)))
  have hGmass (t : ℝ) : G t = stoppedDivisorMass X (X^ξ) (X^(2/5:ℝ)) l b
      (t+u) W selected e S U := (stoppedDivisorMass_eq _ _ _ _ _ _ _ _ _ _ _).symm
  have hlocal (t : ℝ) (ht : |t| < T) : G t ≤ B₀ := by
    rw [hGmass]
    have ht' := log_height_translate hL2 (Ct+1) H (ht.le.trans hTlog) hu
    exact hnear δ l b (t+u) V B hδ hδone hwidth hl hb hbX hV
      (by simpa only [Real.rpow_natCast] using ht') hVF hB hBb W hW hWi hWd
      S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL
  have ht := htail P S U β N B A u T ρ hNmin hB hA.le le_rfl hρ hU hP hβ hsizeN
    (fun v hv => ⟨(hS v hv).1,(hS v hv).2.1⟩)
  have hscale := stopped_mellin_mass_scale hbp.le hLp hκ hNp.le hceil hloglo k
  have htail' : (∫ t in Ici T, f t*G t)+(∫ t in Ici T, f (-t)*G (-t)) ≤
      (Kt*A^2*(4/κ^k))*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
    simp only [f,mul_assoc,integral_const_mul]
    rw [←mul_add]
    apply ht.trans
    calc
      _ = (Kt*A^2*B^(1/3:ℝ))*((N:ℝ)^2/(1+Real.log (N:ℝ))^k)/T := by ring
      _ ≤ (Kt*A^2*B^(1/3:ℝ))*((4/κ^k)*b^2/(Real.log X)^k)/T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) hTp.le
      _ ≤ (Kt*A^2*B^(1/3:ℝ))*((4/κ^k)*b^2/(Real.log X)^k) :=
        div_le_self (by positivity) hT1
      _ = _ := by ring
  have hi := integral_local_and_signed_tail hfi (fun t => by dsimp [f]; positivity)
    hfg hTp (show 0 ≤ B₀ by dsimp [B₀]; positivity) hlocal htail'
  have hf : (∫ t : ℝ, f t) ≤ D := by
    rw [show f = fun t => (1+ρ)^q*‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖ from rfl,
      integral_const_mul]
    simpa only [pow_zero,one_mul] using hmoment ρ hρ
  have hi' := hi.trans (add_le_add (mul_le_mul_of_nonneg_left hf
    (show 0 ≤ B₀ by dsimp [B₀]; positivity)) le_rfl)
  simp_rw [hGmass] at hi'
  simp only [f,mul_assoc,integral_const_mul] at hi'
  convert hi' using 1; simp only [B₀]; ring

end CubicFirstMoment

end

end OAI
