import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootReduction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIndividualSymbol

namespace OAI

/-! Restricting the finite reduction to one parameter preserves its exact
formula. Individual tail bounds can therefore be used without exchanging
the parameter and derivative quantifiers of the uniform estimates. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemoteReductionData_restrict
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator) (P : SpectralRemoteSuperOperator)
    (K : ℕ → ℝ → SpectralRemoteSuperOperator) (m n : ℕ) :
    spectralRemoteReductionData (fun _ => Lambda n) (fun _ => B n) P (fun _ => K n) m =
      (fun _ => (spectralRemoteReductionData Lambda B P K m).1 n,
       fun _ => (spectralRemoteReductionData Lambda B P K m).2 n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [spectralRemoteReductionData,ih]

theorem spectralRemoteReductionFrame_restrict
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator) (P : SpectralRemoteSuperOperator)
    (K : ℕ → ℝ → SpectralRemoteSuperOperator) (m n : ℕ) :
    spectralRemoteReductionFrame (fun _ => Lambda n) (fun _ => B n) P (fun _ => K n) m =
      fun _ => spectralRemoteReductionFrame Lambda B P K m n := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [spectralRemoteReductionFrame,spectralRemoteReductionChange,
        spectralRemoteReductionData_restrict,ih]

theorem spectralRemote_root_reduction_single
    (c : ℕ → ℝ → Fin 2 → ℝ) (B : ℕ → ℝ → SpectralRemoteOperator) (m n : ℕ)
    (hc : HasLogJetBound 0 (c n)) (hB : HasLogJetBound 0 (B n))
    (hsmall : ∀ᶠ t in atTop, ∀ k, |c n t k| ≤ 1/32) :
    let Lambda := fun j t => spectralRemoteLeadingOperator (c j t) t
    let K := fun j t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c j t))
    let d := spectralRemoteReductionData Lambda B spectralRemoteBlockOperator K m
    let T := spectralRemoteReductionFrame Lambda B spectralRemoteBlockOperator K m
    HasLogJetBound 0 (d.1 n) ∧ HasLogJetBound (-2*(m : ℝ)) (d.2 n) ∧
      HasLogJetBound (-2) (fun t => T n t-1) ∧
      HasLogJetBound 0 (fun t => Ring.inverse (T n t)) := by
  let Lambda := fun j t => spectralRemoteLeadingOperator (c j t) t
  let K := fun j t => spectralRemoteSylvesterOperator (Real.exp t) (spectralRemoteDiagonalRoot (c j t))
  have hL : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨S,hS⟩ := eventually_atTop.mp hsmall
  have hs : ∀ᶠ j : ℕ in atTop, ∀ t ∈ Ioi (j : ℝ), ∀ k, |c n t k| ≤ 1/32 := by
    filter_upwards [hL.eventually (eventually_ge_atTop S)] with j hj
    intro t ht
    exact hS t (hj.trans ht.le)
  have hd := spectralRemote_root_reduction hL (HasUniformLogJetBound.of_single hc hL)
    hs (fun _ => B n) (HasUniformLogJetBound.of_single hB hL) m
  change HasUniformLogJetBound _ _
      (spectralRemoteReductionData (fun _ => Lambda n) (fun _ => B n)
        spectralRemoteBlockOperator (fun _ => K n) m).1 ∧ _ at hd
  rw [spectralRemoteReductionData_restrict Lambda B spectralRemoteBlockOperator K m n,
    spectralRemoteReductionFrame_restrict Lambda B spectralRemoteBlockOperator K m n] at hd
  exact ⟨hd.1.to_single,hd.2.1.to_single,hd.2.2.1.to_single,hd.2.2.2.1.to_single⟩

end DefocusingNLS

end OAI
