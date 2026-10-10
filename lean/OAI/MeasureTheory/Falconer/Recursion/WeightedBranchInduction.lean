import OAI.MeasureTheory.Falconer.Recursion.ReachedBranchWeights

namespace OAI

namespace PlanarFalconer

theorem weighted_branch_energy_induction (A : ℕ → ℝ) (N q D : ℕ)
    (sig lam eps C terminal floor error L E : ℝ) (root : BranchState)
    (energies : BranchState → ℝ → Prop)
    (hN : 0 < N) (hq : 0 < q) (hsig : 0 < sig)
    (hC : 1 ≤ C) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hvalid : ∀ s u l, s.Valid N sig → BranchStep A N q sig s l u → u.Valid N sig)
    (hdepth : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root → n ≤ D)
    (hterminal : ∀ s, s.Valid N sig → s.finish ≤ s.start+100*q →
      ∀ x, energies s x → x ≤ terminal)
    (hreduction : ∀ s, s.Valid N sig →
      (∃ n, ∃ b : PolicyBranch A N q sig n, b.state 0 = root ∧ b.state n = s) →
      s.start+100*q < s.finish →
      ∀ M : ℝ, 0 ≤ M → floor ≤ M →
      (∀ u l, BranchStep A N q sig s l u → ∀ x, energies u x →
        ((2:ℝ)^N)^(branchExponent A lam sig eps s l u)*x ≤ M) →
      ∀ x, energies s x → x ≤ C*M+error)
    (htermWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*terminal ≤ L)
    (hfloorWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*floor ≤ L)
    (herrorWeight : ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      b.weight lam eps*error ≤ E) :
    ∀ n, ∀ b : PolicyBranch A N q sig n, b.state 0 = root →
      ∀ x, energies (b.state n) x →
      b.weight lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
  have haux : ∀ s : BranchState, ∀ n, ∀ b : PolicyBranch A N q sig n,
      b.state 0 = root → b.state n = s → ∀ x, energies s x →
      b.weight lam eps*x ≤ (C+1)^(D-n+1)*(L+E) := by
    intro s
    induction s using (measure (fun s : BranchState => s.finish-s.start)).wf.induction with
    | h s ih =>
      intro n b hroot hlast x hx
      have hs : s.Valid N sig := hlast ▸ b.valid n le_rfl
      have hW := b.weight_pos lam eps
      have hsum : 0 ≤ L+E := add_nonneg hL hE
      have hpow : 1 ≤ (C+1)^(D-n) := one_le_pow₀ (by linarith)
      let H := (C+1)^(D-n)*(L+E)
      have hLH : L ≤ H := by dsimp only [H]; nlinarith
      have hEH : E ≤ H := by dsimp only [H]; nlinarith
      have hH : 0 ≤ H := hL.trans hLH
      have hHlast : H ≤ (C+1)^(D-n+1)*(L+E) := by
        rw [pow_succ]
        change H ≤ (C+1)^(D-n)*(C+1)*(L+E)
        nlinarith
      by_cases hw : s.finish ≤ s.start+100*q
      · have ht := hterminal s hs hw x hx
        exact ((mul_le_mul_of_nonneg_left ht hW.le).trans (htermWeight n b hroot)).trans
          (hLH.trans hHlast)
      · have hfloor : floor ≤ H/b.weight lam eps := by
          apply (le_div_iff₀ hW).mpr
          simpa only [mul_comm] using (hfloorWeight n b hroot).trans hLH
        have hchildren : ∀ u l, BranchStep A N q sig s l u → ∀ y, energies u y →
            ((2:ℝ)^N)^(branchExponent A lam sig eps s l u)*y ≤ H/b.weight lam eps := by
          intro u l hstep y hy
          have hu := hvalid s u l hs hstep
          have hstep' : BranchStep A N q sig (b.state n) l u := hlast ▸ hstep
          let b' := b.extend hu hstep'
          have hroot' : b'.state 0 = root := by
            change (b.extend hu hstep').state 0 = root
            rw [b.extend_state_le hu hstep' (Nat.zero_le n),hroot]
          have hlast' : b'.state (n+1) = u := b.extend_last_state hu hstep'
          have hnd := hdepth (n+1) b' hroot'
          have hi := ih u (hstep.width_decreases hN hq hsig hs hu) (n+1) b' hroot' hlast' y hy
          have harith : D-(n+1)+1 = D-n := by omega
          rw [harith] at hi
          change b'.weight lam eps*y ≤ H at hi
          dsimp only [b'] at hi
          rw [b.weight_extend,hlast] at hi
          apply (le_div_iff₀ hW).mpr
          nlinarith only [hi]
        have hred := hreduction s hs ⟨n,b,hroot,hlast⟩ (by omega) (H/b.weight lam eps)
          (div_nonneg hH hW.le) hfloor hchildren x hx
        have hh := mul_le_mul_of_nonneg_left hred hW.le
        have herr := herrorWeight n b hroot
        have hid : b.weight lam eps*(C*(H/b.weight lam eps)+error) =
            C*H+b.weight lam eps*error := by field_simp
        rw [hid] at hh
        calc
          b.weight lam eps*x ≤ C*H+E := by linarith
          _ ≤ (C+1)*H := by linarith
          _ = (C+1)^(D-n+1)*(L+E) := by dsimp only [H]; rw [pow_succ]; ring
  intro n b hr x hx
  exact haux (b.state n) n b hr rfl x hx

end PlanarFalconer

end OAI
