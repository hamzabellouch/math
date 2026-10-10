import OAI.NumberTheory.CubicMoment.Decomposition.StoppedNormMellin
import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellin
import OAI.NumberTheory.CubicMoment.Estimates.NormCoprimeMellin

namespace OAI

/-! A noncube Poisson annulus for literal early-stopped coefficients.
The coefficient interval is an actual dyad; its normalized log range and
ambient prime support are constructed here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedIntervalSupport_scaled_norm {X b : ℝ} (hb : 0 < b) (e : Eisenstein)
    {n : Eisenstein} (hn : n ∈ stoppedIntervalSupport ι X (b/2) b e) :
    norm n/(b/2) ∈ Icc (1:ℝ) 2 := by
  have hn' := (Finset.mem_filter.mp hn).2
  have hp : 0 < b/2 := by positivity
  exact ⟨(le_div_iff₀ hp).mpr (by simpa using hn'.2.2.1.le),
    (div_le_iff₀ hp).mpr (by linarith [hn'.2.2.2])⟩

theorem stopped_noncube_radial_form
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V B Y : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      0 < Y → ∀ (S : Finset Eisenstein) (phase : Eisenstein → ℂ),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ v ∈ S, Y ≤ norm v ∧ norm v ≤ 2*Y) → (∀ v ∈ S, ‖phase v‖ ≤ 1) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*‖normCoprimeRadialForm (stoppedIntervalSupport ι X (b/2) b e) S
        (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) n))
        (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) n))
        phase (fun v => norm v/Y) (fun n => norm n/(b/2)) Φ ρ‖ ≤
      K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  let m := 1+2*Real.log 2
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨K,hK,hmass⟩ := stopped_norm_mellin_integral (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ m hm Φ hΦ hΦ' k q H
  refine ⟨K,hK,?_⟩
  filter_upwards [hmass] with X hmass
  intro δ b u V B Y hδ hδone hwidth hb2 hb hbX hV hu hVF hB hBb
    W hW hWi hWd hY S phase hS hSY hphase e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  let P := stoppedIntervalSupport ι X (b/2) b e
  let U := P.biUnion primaryPrimeFactors
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let v := fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n)
  have hbpos : 0 < b := by linarith
  have hN : 0 < b/2 := by positivity
  have hP : ∀ n ∈ P, primary n ∧ Squarefree n :=
    fun n hn => ⟨(stoppedIntervalSupport_spec X (b/2) b e hn).1,
      (stoppedIntervalSupport_spec X (b/2) b e hn).2.1⟩
  have hU : ∀ p ∈ U, primaryPrime p := by
    intro p hp
    obtain ⟨n,hn,hpn⟩ := Finset.mem_biUnion.mp hp
    exact (primaryPrimeFactor_spec (hP n hn).1 hpn).1
  have hPU : ∀ n ∈ P, primaryPrimeFactors n ⊆ U := by
    intro n hn p hp
    exact Finset.mem_biUnion.mpr ⟨n,hn,hp⟩
  have hlog : ∀ v ∈ S, ∀ a ∈ P, ∀ c ∈ P,
      |Real.log (norm v/Y)-Real.log ((norm a/(b/2))*(norm c/(b/2)))| ≤ m := by
    intro v hv a ha c hc
    exact compact_norm_log_ratio (by norm_num : (1:ℝ) ≤ 2)
      ⟨(le_div_iff₀ hY).mpr (by simpa using (hSY v hv).1),
        (div_le_iff₀ hY).mpr (hSY v hv).2⟩
      (stoppedIntervalSupport_scaled_norm hbpos e ha)
      (stoppedIntervalSupport_scaled_norm hbpos e hc)
  have hn := normCoprimeRadialForm_norm_le_mass m hm P S U hP hU hPU v v phase hphase
    (fun v => norm v/Y) (fun n => norm n/(b/2))
    (fun v hv => (le_div_iff₀ hY).mpr (by simpa using (hSY v hv).1))
    (fun n hn => zero_lt_one.trans_le (stoppedIntervalSupport_scaled_norm hbpos e hn).1)
    hlog Φ hΦ hΦ' hρ
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans
    (hmass δ (b/2) b u V B hδ hδone hwidth (by linarith) hb hbX hV hu hVF hB hBb
      W hW hWi hWd S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL hN ρ hρ)

end CubicFirstMoment

end

end OAI
