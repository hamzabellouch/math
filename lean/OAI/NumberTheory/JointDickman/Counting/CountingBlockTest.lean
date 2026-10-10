import OAI.NumberTheory.JointDickman.Counting.CountingCandidateApproximation
import OAI.NumberTheory.JointDickman.Counting.CountingSiteTestBound
import OAI.NumberTheory.JointDickman.Counting.LagEnvelopeTests

namespace OAI

/-! # The fixed-test estimate for the actual latent counting graph -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_block_test
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {τ η w δ : ℝ} (hL : 0 < L) (hτ : 0 < τ)
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
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → T*Q ≤ B → η*T ≤ H → T ≤ M →
        ∀ σ : ℝ, |σ| ≤ 3 →
        (∀ j : ℕ, H < j → j < T →
          ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀) ∧
        (∀ g h : Fin M → (auxiliaryPrimes B).powerset → ℝ,
          (∀ i a, |g i a| ≤ 1) → (∀ i a, |h i a| ≤ 1) →
          siteTestMean (fun _ : Fin M => independentPrimeSetMass B)
            (countingSiteError P m B L T H M τ C w c D σ) g h ≤
            (M : ℝ)*(2*(ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ)*Real.exp 24)) := by
  obtain ⟨K,hK,P,c,hc,D,m,hm,C₀,hC₀,ε,hε0,hε,hcomp⟩ :=
    counting_candidate_approximation hFord hSD hSW hM hMP hL hτ hη hw hδ
  refine ⟨K,hK,P,c,hc,D,m,hm,C₀,hC₀,ε,hε0,hε,?_⟩
  filter_upwards [hcomp] with B hb
  intro C T H M U V Q hC hT hTcap hlog hU hV hdyU hdyV hQ hcut hscale hH hTM σ hσ
  have hMpos : 0 < M := hT.trans_le hTM
  have hepsB : 0 ≤ ε B := hε0 B
  have hpair (i k : Fin M) (hik : i < k) (hiH : H < k.val-i.val) (hkT : k.val-i.val < T) :=
    hb C T H M U V Q hC hT hTcap hlog hU hV hdyU hdyV hQ hcut i k hik hiH hkT
      ((Nat.mul_le_mul_right Q hkT.le).trans hscale)
      (hH.trans (by exact_mod_cast hiH.le)) σ hσ
  constructor
  · intro j hjH hjT x y
    let i : Fin M := ⟨0,hMpos⟩
    let k : Fin M := ⟨j,hjT.trans_le hTM⟩
    have hik : i < k := by change (0 : ℕ) < j; omega
    have he := (hpair i k hik (by simpa only [i,k,Nat.sub_zero] using hjH)
      (by simpa only [i,k,Nat.sub_zero] using hjT) (fun _ => 0) (fun _ => 0)
      (by simp) (by simp)).2 x y
    simpa only [i,k,Nat.sub_zero] using he
  · intro g h hg hh
    apply siteTestMean_le_lag_envelope hT
      (show 0 ≤ ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ by positivity)
      (fun _ : Fin M => independentPrimeSetMass B) (fun _ => independentPrimeSetMass_sum B)
      (countingSiteError P m B L T H M τ C w c D σ)
    · intro i a
      simp only [countingSiteError,latentPrimeSiteKernel,candidateSiteKernel_diag,countingSiteModel_diag,sub_self]
    · intro i k _ f h hf hh
      exact countingSiteError_pair_bound P m B L T H M τ C w c D σ
        (ε B+K*Real.exp (-(1/10 : ℝ)*C)+δ) hT (by positivity)
        (fun i k hik hiH hkT f h hf hh => (hpair i k hik hiH hkT f h hf hh).1)
        i k f h hf hh
    · exact hg
    · exact hh

end JointDickman

end OAI
