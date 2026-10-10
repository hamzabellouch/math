import OAI.Probability.InvariantIsing.Cavity.CavityResidueConvergence

namespace OAI

/-! Selecting a bad residue for each candidate block is enough to test the
full-sequence pressure lower bound. -/
noncomputable section
open Filter
namespace InvariantIsing

lemma cavity_residue_eventually_lower {n : ℕ} (hn : 0 < n) (q : ℕ)
    (P : ℕ → ℝ) (L : ℝ)
    (h : ∀ t : Fin n, ∀ ε > 0, ∀ᶠ j in atTop, L-ε ≤ P (t+(q+j)*n)) :
    ∀ ε > 0, ∀ᶠ N in atTop, L-ε ≤ P N := by
  intro ε hε
  have he : ∀ᶠ j in atTop, ∀ t : Fin n, L-ε ≤ P (t+(q+j)*n) :=
    Filter.eventually_all.mpr (fun t => h t ε hε)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp he
  apply eventually_atTop.mpr
  refine ⟨(q+J)*n, fun N hN => ?_⟩
  have hdiv : q+J ≤ N/n := (Nat.le_div_iff_mul_le hn).mpr hN
  let t : Fin n := ⟨N%n,Nat.mod_lt _ hn⟩
  have hj : J ≤ N/n-q := by omega
  have heq : (t : ℕ)+(q+(N/n-q))*n=N := by
    have hq : q+(N/n-q)=N/n := by omega
    rw [hq]
    simpa only [t, Nat.mul_comm] using Nat.mod_add_div N n
  simpa only [heq] using hJ (N/n-q) hj t

theorem magnetic_full_lower_of_residue_selection
    (n q : ℕ → ℕ) (hn : ∀ r, 0 < n r) (P : ℕ → ℝ) (L : ℝ)
    (h : ∀ t : (r : ℕ) → Fin (n r), ∃ r,
      ∀ ε > 0, ∀ᶠ j in atTop, L-ε ≤ P (t r+(q r+j)*n r)) :
    ∀ ε > 0, ∀ᶠ N in atTop, L-ε ≤ P N := by
  have hex : ∃ r, ∀ t : Fin (n r), ∀ ε > 0,
      ∀ᶠ j in atTop, L-ε ≤ P (t+(q r+j)*n r) := by
    by_contra hnone
    have hbad : ∀ r, ∃ t : Fin (n r), ¬(∀ ε > 0,
        ∀ᶠ j in atTop, L-ε ≤ P (t+(q r+j)*n r)) := by
      intro r
      by_contra hnr
      push Not at hnr
      exact hnone ⟨r,hnr⟩
    choose t ht using hbad
    obtain ⟨r,hr⟩ := h t
    exact ht r hr
  obtain ⟨r,hr⟩ := hex
  exact cavity_residue_eventually_lower (hn r) (q r) P L hr

end InvariantIsing

end

end OAI
