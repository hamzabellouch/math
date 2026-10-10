import OAI.NumberTheory.JointDickman.Counting.CountingCandidateModel

namespace OAI

/-! # The actual latent counting-ramp entry has a finite prime-feature model -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem counting_candidate_feature_comparison
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    :
    ∃ Kr Kc : ℝ, 0 < Kr ∧ 0 < Kc ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ er ec : ℕ → ℝ, (∀ B, 0 ≤ er B) ∧ (∀ B, 0 ≤ ec B) ∧
        Tendsto er atTop (𝓝 0) ∧ Tendsto ec atTop (𝓝 0) ∧
        ∀ η w δ : ℝ, 0 < η → 0 < w → 0 < δ →
        ∃ P : MvPolynomial (Fin 4) ℝ,
        ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
        (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
        ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
        ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M U V Q : ℕ),
          0 ≤ C → 0 < T → Real.log T ≤ (B : ℝ)/10 →
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
          independentRootMean B L τ C*
            ((T : ℝ)*(Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B (t.val-i.val) T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 (t.val-i.val)*(ec B+Real.exp (-(1/10 : ℝ)*C)))+
              ε B+δ*((T : ℝ)/((t.val-i.val : ℕ) : ℝ))*singularSeries (t.val-i.val)) ∧
          ∀ x y, |countingPrimeKernel P m B (t.val-i.val) c D T σ x y| ≤ C₀ := by
  obtain ⟨Kr,Kc,hKr,hKc,hcandidate⟩ := ramped_candidate_arithmetic_comparison hFord hM
  refine ⟨Kr,Kc,hKr,hKc,?_⟩
  intro L τ hL hτ
  obtain ⟨er,ec,her0,hec0,her,hec,hcandidate⟩ := hcandidate L τ hL hτ
  refine ⟨er,ec,her0,hec0,her,hec,?_⟩
  intro η w δ hη hw hδ
  obtain ⟨P,c,hc,D,m,hm,C₀,hC₀,ε,hε,hfeature⟩ :=
    counting_arithmetic_feature_comparison hSD hSW hM hMP hη hw δ hδ
  refine ⟨P,c,hc,D,m,hm,C₀,hC₀,ε,hε,?_⟩
  filter_upwards [hcandidate,hfeature] with B hb hf
  intro C T H M U V Q hC hT hlog hU hV hdyU hdyV hQ hcut i t hit hH hjT hscale hlag σ hσ g h hg hh
  let j := t.val-i.val
  have : NeZero j := ⟨Nat.ne_of_gt (Nat.sub_pos_of_lt hit)⟩
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have ha := hb C T H M U V hC hT hlog hU hV hdyU hdyV i t hit hH hjT w σ hw g h hg hh
  obtain ⟨hf,hbound⟩ := hf j Q hQ hscale hcut T hT1 hlog hlag σ hσ U V hdyU hdyV h g hh hg
  refine ⟨?_,hbound⟩
  rw [countingCandidateModel_mean]
  let A := subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
    (subsetSiteTest (auxiliaryPrimes B) h)
    (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i t)
  let R := independentRootMean B L τ C
  let S := (singularSeries j/(j : ℝ))*(∑ x, ∑ y,
    fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*h x*g y*
      countingPrimeKernel P m B j c D T σ x y)
  let a := rampedAmplificationArithmeticSum B j T U V w σ h g
  have hR : 0 ≤ R := independentRootMean_nonneg ..
  have ht : |A-R*S| ≤ |A-R*a|+R*|a-S| := by
    have h := abs_sub_le A (R*a) (R*S)
    have he : |R*a-R*S| = R*|a-S| := by rw [← mul_sub,abs_mul,abs_of_nonneg hR]
    exact h.trans_eq (congrArg (fun z => |A-R*a|+z) he)
  calc
    _ = (T : ℝ)*|A-R*S| := rfl
    _ ≤ (T : ℝ)*|A-R*a|+R*((T : ℝ)*|a-S|) :=
      (mul_le_mul_of_nonneg_left ht hTr.le).trans_eq (by ring)
    _ ≤ (T : ℝ)*(R*(Kr*(er B+Real.exp (-(1/10 : ℝ)*C))*
                amplificationArithmeticSum B j T U V (fun _ => 1) (fun _ => 1)+
              ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              Kc/T*singularFactor 24 j*(ec B+Real.exp (-(1/10 : ℝ)*C))))+
        R*(ε B+δ*((T : ℝ)/j)*singularSeries j) :=
      add_le_add (mul_le_mul_of_nonneg_left ha hTr.le) (mul_le_mul_of_nonneg_left hf hR)
    _ = _ := by dsimp only [R,j]; ring

end JointDickman

end OAI
