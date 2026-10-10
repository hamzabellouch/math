import OAI.Combinatorics.Progressions.Dynamics.ScheduledPhysicalEpochStack

namespace OAI

section

namespace Erdos3

open Module PhysicalEpochStack

universe u v

theorem exists_uniform_physical_epoch_stack (A s : ℕ) (hA : 1 ≤ A) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {bound : ℕ}
      (base : PhysicalEpochSource.{u, v} σ s bound) (state : PhysicalEpochRecords base)
      (M : ℕ), 0 < M → ∀ anchor : σ → ℤ,
      (∀ i, base.lower i ≤ anchor i ∧ anchor i < base.lower i + base.sides i) →
      (∀ r ∈ state.records, r.modulus ∣ M) →
      (∀ i, Real.exp ((base.recordBudget + 2) ^ K) ≤ (base.sides i : ℝ) / M) →
      ∃ stack : PhysicalEpochStack base,
        RootState state stack ∧ UniformAt A M anchor ((base.recordBudget + 2) ^ K) K stack := by
  induction s with
  | zero =>
    refine ⟨2, by omega, ?_⟩
    intro σ _ _ bound base state M hM anchor hanchor hdiv hlarge
    have hp : 0 ≤ base.recordBudget := base.incoming_nonneg.trans base.incoming_le_record
    have hbound : base.recordBudget ≤ (base.recordBudget + 2) ^ 2 := by nlinarith
    exact ⟨.zero base, trivial, base.incoming_le_record.trans hbound, hbound⟩
  | succ s ih =>
    obtain ⟨Kt, hKt, htail⟩ := ih
    obtain ⟨Kf, hKf, hframe⟩ := exists_physical_epoch_frame s
    let F : Polynomial ℕ := (Polynomial.X + 2) ^ Kf
    let G : Polynomial ℕ := (F + 2) ^ A
    let P : Polynomial ℕ := F + G + (G + 2) ^ Kt + Polynomial.X
    obtain ⟨K₀, hK₀, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
    let K := max K₀ (max Kf Kt)
    refine ⟨K, hK₀.trans (le_max_left _ _), ?_⟩
    intro σ _ _ bound base state M hM anchor hanchor hdiv hlarge
    let p := base.recordBudget
    let f : ℝ := (p + 2) ^ Kf
    let g : ℝ := (f + 2) ^ A
    have hp : 0 ≤ p := base.incoming_nonneg.trans base.incoming_le_record
    have hf : 0 ≤ f := by dsimp only [f]; positivity
    have hg : 0 ≤ g := by dsimp only [g]; positivity
    have ht : 0 ≤ (g + 2) ^ Kt := by positivity
    have hK₀K : (p + 2) ^ K₀ ≤ (p + 2) ^ K :=
      pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (le_max_left _ _)
    have hpoly : f + g + (g + 2) ^ Kt + p ≤ (p + 2) ^ K := by
      have h := hbudget p hp
      have h' : f + g + (g + 2) ^ Kt + p ≤ (p + 2) ^ K₀ := by
        simpa [P, G, F, f, g, Polynomial.eval₂_pow] using h
      exact h'.trans hK₀K
    have hfBound : f ≤ (p + 2) ^ K := by linarith
    have htBound : (g + 2) ^ Kt ≤ (p + 2) ^ K := by linarith
    have hpBound : p ≤ (p + 2) ^ K := by linarith
    have hinflate : ∀ x : ℝ, 0 ≤ x → x ≤ (x + 2) ^ A := by
      intro x hx
      calc
        x ≤ x + 2 := by linarith
        _ = (x + 2) ^ 1 := (pow_one _).symm
        _ ≤ (x + 2) ^ A := pow_le_pow_right₀ (by linarith) hA
    obtain ⟨frame, hstate, hmod, hanchorFrame, hwork, hchildIncoming, hchildRecord, hperiod, hfreeze, hevent⟩ :=
      hframe base state M hM anchor hanchor hdiv (fun x => (x + 2) ^ A) hinflate
        (fun i => (Real.exp_le_exp.mpr hfBound).trans (hlarge i))
    have hchild0 := frame.child.incoming_nonneg
    have hchildRecord0 := hchild0.trans frame.child.incoming_le_record
    have hchildG : frame.child.recordBudget ≤ g := by
      rw [hchildRecord]
      dsimp only [g]
      gcongr
    have hchildPower : (frame.child.recordBudget + 2) ^ Kt ≤ (g + 2) ^ Kt := by gcongr
    have hchildBound : (frame.child.recordBudget + 2) ^ Kt ≤ (p + 2) ^ K := hchildPower.trans htBound
    have hanchorChild : ∀ i, frame.child.lower i ≤ anchor i ∧
        anchor i < frame.child.lower i + frame.child.sides i := by
      intro i
      simpa only [frame.child_lower, frame.child_sides] using hanchor i
    have hlargeChild : ∀ i, Real.exp ((frame.child.recordBudget + 2) ^ Kt) ≤
        (frame.child.sides i : ℝ) / M := by
      intro i
      rw [frame.child_sides]
      exact (Real.exp_le_exp.mpr hchildBound).trans (hlarge i)
    obtain ⟨tail, _, htailUniform⟩ := htail frame.child (PhysicalEpochRecords.empty frame.child)
      M hM anchor hanchorChild (by simp [PhysicalEpochRecords.empty]) hlargeChild
    refine ⟨.succ frame tail, hstate, ?_⟩
    exact ⟨base.incoming_le_record.trans hpBound, hpBound, hmod, hanchorFrame,
      hwork.trans hfBound, hperiod.trans (Real.exp_le_exp.mpr hfBound),
      hfreeze.trans ((le_max_left Kf Kt).trans (le_max_right K₀ (max Kf Kt))),
      hevent.trans ((le_max_left Kf Kt).trans (le_max_right K₀ (max Kf Kt))), hchildRecord,
      htailUniform.mono hchildBound ((le_max_right Kf Kt).trans (le_max_right K₀ (max Kf Kt)))⟩

end Erdos3

end

end OAI
