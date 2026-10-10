import OAI.NumberTheory.JointDickman.Counting.CountingErrorBound
import OAI.NumberTheory.JointDickman.Probability.SingularSeriesMoments

namespace OAI

/-! # A summable vanishing error for the actual finite-feature comparison -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_candidate_approximation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {L : ℕ} {τ η w δ : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hη : 0 < η) (hw : 0 < w) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ P : MvPolynomial (Fin 4) ℝ,
      ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V Q : ℕ),
        0 ≤ C → 0 < T → T ≤ amplificationMultiplier B → Real.log T ≤ (B : ℝ)/10 →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q →
        ∀ i t : Fin M, i < t → H < t.val-i.val → t.val-i.val < T →
        (t.val-i.val)*Q ≤ B → η*T ≤ ((t.val-i.val : ℕ) : ℝ) →
        ∀ σ : ℝ, |σ| ≤ 3 →
        ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
        (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
        (T : ℝ)*|subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
            (subsetSiteTest (auxiliaryPrimes B) h)
            (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i t)-
          subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
            (subsetSiteTest (auxiliaryPrimes B) h)
            (countingCandidateModel P m B L (t.val-i.val) τ C c D T σ)| ≤
          (ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*singularFactor 24 (t.val-i.val) ∧
        ∀ x y, |countingPrimeKernel P m B (t.val-i.val) c D T σ x y| ≤ C₀ := by
  obtain ⟨Kr,Kc,hKr,hKc,hcompare⟩ := counting_candidate_feature_comparison hFord hSD hSW hM hMP
  obtain ⟨er,ec,her0,hec0,her,hec,hcompare⟩ := hcompare L τ hL hτ
  obtain ⟨R,hR,hroot⟩ := independentRootMean_bounded hM
  obtain ⟨Kp,hKp,ep,hep,hpositive⟩ := amplification_positive_mass_bound hSD hSW hM hMP hη
  let δ₀ := δ*η/R
  have hδ₀ : 0 < δ₀ := div_pos (mul_pos hδ hη) hR
  obtain ⟨P,c,hc,D,m,hm,C₀,hC₀,ef,hef,hcompare⟩ := hcompare η w δ₀ hη hw hδ₀
  let K := R*(Kr*Kp/η+Kc)
  let ε := countingErrorRate R Kr Kc Kp η er ec ep ef
  refine ⟨K,by dsimp [K]; positivity,P,c,hc,D,m,hm,C₀,hC₀,ε,
    countingErrorRate_nonneg hR.le hKr.le hKc.le hKp hη.le her0 hec0,
    countingErrorRate_tendsto R Kr Kc Kp η her hec hep hef,?_⟩
  filter_upwards [hcompare,hpositive,hroot] with B hb hp hr
  intro C T H M U V Q hC hT hTcap hlog hU hV hdyU hdyV hQ hcut i t hit hH hjT hscale hlag σ hσ g h hg hh
  let j := t.val-i.val
  have hj : 0 < j := Nat.sub_pos_of_lt hit
  have : NeZero j := ⟨hj.ne'⟩
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨he,hbound⟩ := hb C T H M U V Q hC hT hlog hU hV hdyU hdyV hQ hcut
    i t hit hH hjT hscale hlag σ hσ g h hg hh
  have hpa := hp j Q hQ hscale hcut T hT1 hlog hlag U V hdyU hdyV
  refine ⟨?_,hbound⟩
  have hG : 0 ≤ (amplificationMultiplier B : ℝ)*
      (((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _)) (by positivity))
  have hgcd : (T : ℝ)*(((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) ≤
      (amplificationMultiplier B : ℝ)*(((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hTcap)
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _)) (by positivity))
  have hq : Real.exp (-(1/10 : ℝ)*C) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he' := countingError_bound hTr hη hlag (independentRootMean_nonneg B L τ C)
    (hr L τ C) hKr.le hKc.le hKp (her0 B) (hec0 B) hG (Real.exp_pos _).le hq hδ₀.le
    (singularFactor_one_le (by norm_num) j) (singularSeries_bounds hMP j).1
    (singularSeries_le_singularFactor hMP hj) hgcd hpa he
  have hd : R*δ₀/η = δ := by dsimp [δ₀]; field_simp
  simpa only [hd,ε,countingErrorRate,K,j] using he'

end JointDickman

end OAI
