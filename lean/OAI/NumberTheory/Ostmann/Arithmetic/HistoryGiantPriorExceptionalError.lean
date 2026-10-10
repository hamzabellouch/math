import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorExceptionalErrorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantPriorExceptionalError
open Construction SourcePriorGridDeletion ScaleBudget PrimeCellActualErrorBudget Filter

structure ErrorBounds (k : ℕ) (C G L : ℝ) (M : ℕ) (E : Finset ℕ) : Prop where
  mass_pos : 0<logCellMass G E
  inverse_mass : (logCellMass G E)⁻¹≤2*G
  deletion_small : deletionCap G E≤1
  errors : ∀ (a : ℕ) (H : ℝ), a≤HistoryGiantReplacementError.residueCostExponent k →
    0≤H → H≤(M:ℝ)^a*smoothGrowthFactor k C giant.μ L →
    deletionCap G E*(1+fullMassRatio G E)*H≤Real.exp (-Real.exp (giant.target*L)) ∧
    3*deletionCap G E*H≤Real.exp (-Real.exp (giant.target*L)) ∧
    (Real.exp 1+1)*deletionCap G E*H≤Real.exp (-Real.exp (giant.target*L)) ∧
    H*(Real.exp (1-G)/logCellMass G E)≤Real.exp (-Real.exp (giant.target*L)) ∧
    H*(8*Real.exp (-G))≤Real.exp (-Real.exp (giant.target*L))

theorem eventually_exceptional_errors (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G : ℝ) (M : ℕ), 0<M →
      Real.log (M:ℝ)≤Real.exp (giant.μ*L) → Real.exp (giant.a₀*L)≤G-1 →
      ∀E : Finset ℕ,E.card≤2 → ErrorBounds k C G L M E := by
  obtain ⟨G0,hG0⟩ := eventually_atTop.mp
    (logCell_normalization_eventually.and deletionCap_eventually_le_one)
  have ht := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop
    (show 0<giant.a₀ by norm_num [giant]))
  filter_upwards [eventually_growth_exceptionalEnvelope k C,ht.eventually_ge_atTop G0]
    with L hbudget hmin
  intro G M hM hmod hG E hE
  have hG1 : 1≤G := by linarith [Real.exp_pos (giant.a₀*L)]
  have hGG : G0≤G := by
    change G0≤Real.exp (giant.a₀*L) at hmin
    linarith
  obtain ⟨hz,hlo,hinv⟩ := (hG0 G hGG).1 E hE
  have hsmall := ((hG0 G hGG).2 E hE).2
  refine ⟨hz,hinv,hsmall,?_⟩
  intro a H ha hH0 hH
  have henv : H*exceptionalEnvelope G≤Real.exp (-Real.exp (giant.target*L)) :=
    (mul_le_mul_of_nonneg_right hH (exceptionalEnvelope_nonneg (by linarith))).trans
      (hbudget G M a hM ha hmod hG)
  obtain ⟨h1,h2,h3,h4,h5⟩ := exceptional_errors_le_envelope G E hG1 hE hz hinv hsmall
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right h1 hH0).trans (by simpa only [mul_comm H] using henv)
  · exact (mul_le_mul_of_nonneg_right h2 hH0).trans (by simpa only [mul_comm H] using henv)
  · exact (mul_le_mul_of_nonneg_right h3 hH0).trans (by simpa only [mul_comm H] using henv)
  · exact (mul_le_mul_of_nonneg_left h4 hH0).trans henv
  · exact (mul_le_mul_of_nonneg_left h5 hH0).trans henv

end Ostmann.Arithmetic.HistoryGiantPriorExceptionalError

end

end OAI
