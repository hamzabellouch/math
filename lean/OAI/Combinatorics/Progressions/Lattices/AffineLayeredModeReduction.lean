import OAI.Combinatorics.Progressions.Estimates.SubspaceLayeredModeSmoothRemoval

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def liftedIntegerSite {K : Type*} (site : K → ℤ) : Option K → ℤ :=
  fun k => k.elim 1 site

theorem liftedIntegerSite_cast {K : Type*} (site : K → ℤ) :
    (fun k => (liftedIntegerSite site k : ℝ)) =
      (fun k : Option K => k.elim 1 (fun k => (site k : ℝ))) := by
  funext k
  cases k <;> simp [liftedIntegerSite]

theorem exists_affine_layered_mode_reduction {I K S : Type*}
    [Fintype K] [Fintype S] [DecidableEq S] {m : ℕ}
    {W : Fin m → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℝ (W j)]
    (site : S → K → ℤ) (L : ∀ j, VectorPolynomial K ℝ (W j) →ₗ[ℝ] ℝ)
    (p : ∀ j, VectorPolynomial I ℝ (W j))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hbad : ∃ i, ¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (fun k => (site s k : ℝ))) q))
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ i, (¬∃ M : (S → W i) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (i.val + 1) q → affineModeLift (L i) q =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (fun k => (site s k : ℝ))) q)) ∧
      ∃ Q' : MvPolynomial (Option K × I) ℝ, Q'.totalDegree < i.val + 1 ∧
        ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ b,
          layeredModeTestedPhase (fun j => affineModeLift (L j)) p Q
            (fun s => liftedIntegerSite (site s)) test b =
          coefficientModeTestedPhase (affineModeLift (L i)) (p i) Q'
            (fun s => liftedIntegerSite (site s)) test' b := by
  obtain ⟨i, hi, hh⟩ := exists_highest_affine_nonfactor (fun s k => (site s k : ℝ)) L hbad
  refine ⟨i, hi, ?_⟩
  apply exists_layered_mode_reduction i (fun j => affineModeLift (L j)) p hp
    (fun s => liftedIntegerSite (site s)) _ Q (hQ.trans_lt (Nat.zero_lt_succ _)) test htest
  have hs : (fun s k => (liftedIntegerSite (site s) k : ℝ)) =
      (fun s (k : Option K) => k.elim 1 (fun k => (site s k : ℝ))) := by
    funext s k
    exact congrFun (liftedIntegerSite_cast (site s)) k
  rw [hs]
  exact hh

end Erdos3.VectorPolynomial

end

end OAI
