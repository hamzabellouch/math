import OAI.NumberTheory.TotientAsymptotic.PPTNormalWitness
import OAI.NumberTheory.TotientAsymptotic.UniformNonNormalCount

namespace OAI

/-!
The nonnormal-target discard in the PPT construction, at the existing
dyadic counting-envelope scale.  The finite singleton-fiber argument
allows the unconditional exceptional-totient estimate to count the
original candidate integers without any multiplicity loss.
-/

noncomputable section

namespace TotientAsymptotic

theorem ppt_nonnormal_witness_count_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (W x : ℝ) (J d q : ℕ),
      2 < W → 0 ≤ B W → 256 ≤ x → 1 ≤ J → x ≤ (2 : ℝ)^J → 0 < d →
      ∀ (A Q : Finset ℕ) (F : ℕ → ℕ), Q ⊆ A →
      (∀ n ∈ A, ∀ p : ℕ, p.Prime → p ∣ n → IsNormalPrime W p) →
      (∀ p : ℕ, p.Prime → p ∣ q → IsNormalPrime W p) →
      (∀ n ∈ A, (∃ m ∈ A, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ A, F n = c*q) →
      (∀ n ∈ Q, ∃ p : ℕ, p.Prime ∧ p ∣ F n ∧ ¬IsNormalPrime W p) →
      (∀ n ∈ Q, 0 < F n ∧ (F n).totient = d*n.totient ∧
        ((d*n.totient : ℕ) : ℝ) ≤ x) →
      (Q.card : ℝ) ≤ C*dyadicTotientEnvelope J*x/Real.log x*
        (B (2*x))^5*(1+Real.log J)*(Real.log W)^(-1/6 : ℝ) := by
  classical
  obtain ⟨C, hC, hcount⟩ := uniform_non_normal_value_count
  refine ⟨C, hC, ?_⟩
  intro W x J d q hW hBW hx hJ hxJ hd A Q F hQA hA hq hbranch hbad hF
  have hinj := ppt_nonnormal_witness_target_injective hd hQA hA hq hbranch hbad
  have hb := hcount W x J hW hBW hx hJ hxJ
    (Q.image (fun n : ℕ => d*n.totient)) (by
      intro v hv
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨p, hp, hpd, hpn⟩ := hbad n hn
      have hnF := hF n hn
      exact ⟨F n, p, hnF.1, hnF.2.1, hp, hpd, hnF.2.2, hpn⟩)
  rwa [Finset.card_image_of_injOn hinj] at hb

end TotientAsymptotic

end

end OAI
