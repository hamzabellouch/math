import OAI.MeasureTheory.Falconer.Angular.OuterAngularBound
import OAI.MeasureTheory.Falconer.Recursion.ProfileEntry

namespace OAI

/-! # The common entry depth for the two actual outer policy states -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (sourcePolicyBlock)

 theorem exists_policy_profile_entry {m : ℕ} (P Q : PolicyJetData m)
    {χ β lam κ : ℝ} (hχ : 0 < χ) (hβ : 0 < β) (hlam : 0 ≤ lam)
    (hsmall : β+((m+3:ℕ)+4)*lam < χ/4)
    (hN : P.N = Q.N) (hLamP : P.lam = lam) (hLamQ : Q.lam = lam)
    (hsP : P.s = (m+3:ℕ)/2+χ) (hsQ : Q.s = (m+3:ℕ)/2+χ)
    (htP : P.t = P.N) (htQ : Q.t = Q.N)
    (hprofileP : P.policy = profileExcess (d := m+3) P.profile P.N)
    (hprofileQ : Q.policy = profileExcess (d := m+3) Q.profile Q.N)
    (hqP : P.q = sourcePolicyBlock P.N κ)
    (hlarge : 2*(m+3:ℕ) ≤ β*P.N)
    (hqsmall : 400*P.q ≤ P.N) :
    ∃ c : ℕ, 4*c ≤ P.N ∧ c+100*P.q < P.N ∧
      β*P.N/(2*(m+3:ℕ)) ≤ (c:ℝ) ∧
      (∀ n, c ≤ n → n ≤ P.N → β-(m+3:ℕ)/P.N ≤ P.policy n) ∧
      (∀ n, c ≤ n → n ≤ Q.N → β-(m+3:ℕ)/Q.N ≤ Q.policy n) ∧
      outerEntryExponent P Q c κ ≤ -β+((m+3:ℕ)+4)*lam+2*(m+3:ℕ)/P.N := by
  let cubes : Fin 2 → DyadicCube (m+3) := ![P.Q,Q.Q]
  let laws : Fin 2 → Measure (Space (m+3)) := ![P.ρ,Q.ρ]
  let profiles : Fin 2 → ℝ → ℝ := ![P.profile,Q.profile]
  have hp := P.regular
  have hq := Q.regular
  rw [hsP,hLamP] at hp
  rw [hsQ,hLamQ,← hN] at hq
  have hreg : ∀ i, Regularization.RegularizedProfileData (cubes i) (laws i) P.N
      ((m+3:ℕ)/2+χ) lam (profiles i) := by
    intro i
    fin_cases i
    · exact hp
    · exact hq
  obtain ⟨c,hcN,hclo,hchi,hcq,htail,hheight,hpot,hentry⟩ :=
    regularized_profiles_entry (by omega : 0 < m+3) cubes laws profiles P.N (10*P.q)
      hreg hχ hβ hlam hsmall P.N_pos hlarge (by have := P.q_pos; omega) (by omega)
  have hc4 : 4*c < P.N := by exact_mod_cast (show 4*(c:ℝ) < P.N by linarith)
  refine ⟨c,by omega,by have := P.q_pos; omega,hclo,?_,?_,?_⟩
  · intro n hcn hn
    simpa only [profiles,Matrix.cons_val_zero,← hprofileP] using htail 0 n hcn hn
  · intro n hcn hn
    have hh := htail 1 n hcn (by omega : n ≤ P.N)
    rw [hprofileQ,← hN]
    simpa only [profiles,Matrix.cons_val_one,Matrix.cons_val_zero] using hh
  · change -profileExcess (d := m+3) P.profile P.N c-
      profileExcess (d := m+3) Q.profile P.N c+
      min (PlanarFalconer.height (profileExcess (d := m+3) P.profile P.N) 0 c)
        (PlanarFalconer.height (profileExcess (d := m+3) Q.profile P.N) 0 c)+
      ((2*profileExcess (d := m+3) P.profile P.N c-
        PlanarFalconer.potential (profileExcess (d := m+3) P.profile P.N) c P.N (10*P.q))+
        (2*profileExcess (d := m+3) Q.profile P.N c-
        PlanarFalconer.potential (profileExcess (d := m+3) Q.profile P.N) c P.N (10*P.q)))/2 ≤ _ at hentry
    unfold outerEntryExponent
    rw [hprofileP,hprofileQ,htP,htQ,← hN,← hqP]
    convert hentry using 1
    ring

end Falconer

end OAI
