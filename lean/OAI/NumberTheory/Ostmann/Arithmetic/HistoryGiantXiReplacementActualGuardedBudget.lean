import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryCRTIntegration HistorySignedResidues
open HistorySelectedPairDerivativeBounds ScaleBudget PrimeCellActualErrorBudget
open HistoryGiantReplacementError HistoryGiantPriorExceptionalError Filter

theorem eventually_guarded_exceptional_budget (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) {k₀ : ℕ} (hk₀ : 0 < k₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k₀ L E),
      ∀ l ≤ k₀, ∀ (h k : History l) (outside : List ℕ) (n : ℕ)
      [NeZero (comparisonModulus h k outside n)],
      Real.log (comparisonModulus h k outside n : ℝ) ≤ Real.exp (giant.μ*L) →
      Real.exp (giant.a₀*L) ≤ (C.giantCenter : ℝ)-1 →
      ∀ (deleted : Finset ℕ), deleted.card ≤ 2 →
      let A := referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l
      let H := (outside.prod : ℝ)^(2^(l+1))*A
      H*(Real.exp (1-(C.giantCenter : ℝ))/logCellMass C.giantCenter deleted) ≤
        Real.exp (-Real.exp (giant.target*L)) ∧
      H*(8*Real.exp (-(C.giantCenter : ℝ))) ≤
        Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [eventually_exceptional_errors k₀ (selectedExponent Bs BD Bz k₀)] with L hexc
  intro E C l hl h k outside n _ hmod hlo deleted hdeleted
  dsimp only
  let M := comparisonModulus h k outside n
  let A := referenceAmplitude (Bs:=Bs) (k₀:=k₀) (L:=L) l
  let F := smoothGrowthFactor k₀ (selectedExponent Bs BD Bz k₀) giant.μ L
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne _)
  have ho : (outside.prod : ℝ) ≤ M := by
    exact_mod_cast outside_prod_le_comparisonModulus h k outside n hM
  have hA : 0 ≤ A := referenceAmplitude_nonneg Bs L k₀ l
  have hAF : A ≤ F := (selected_amplitude_bound Bs BD Bz L hBs hk₀ hl).trans
    (selected_exp_le_smoothGrowth Bs BD Bz L k₀)
  have ha : 2^(l+1) ≤ residueCostExponent k₀ := by
    have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) (Nat.add_le_add_right hl 1)
    unfold residueCostExponent
    omega
  have hH : (outside.prod : ℝ)^(2^(l+1))*A ≤ (M:ℝ)^(2^(l+1))*F :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) ho _) hAF hA (by positivity)
  have he := (hexc C.giantCenter M hM hmod hlo deleted hdeleted).errors
    (2^(l+1)) ((outside.prod : ℝ)^(2^(l+1))*A) ha (by positivity) hH
  exact ⟨he.2.2.2.1,he.2.2.2.2⟩

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
