import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualCostBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceUnaryErrorBudget

namespace OAI

/-! The full path exponent has a uniform constant once the two residual
norms have polynomial bounds. The prescribed cutoff absorbs both costs. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem eventually_source_path_cost_budget (Cmarked Cunary q Cmass A_M : ℝ)
    (hAM : 0 ≤ A_M) (hchoice : 4*(max Cmarked (Cunary+6)+3/2) ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ → ℝ) (count : ℕ) (S : Finset ℕ),
      S ⊆ Finset.range count → Antitone n →
    ∀ B V ε Q μ : ℝ, 0 ≤ B → B ≤ L^Cmarked → 0 ≤ V → V ≤ L^Cunary →
      0 ≤ ε → ε ≤ L^q*Real.exp (-L*Real.log L) →
      0 ≤ Q → Q ≤ Real.exp (Cmass*Real.sqrt L) → μ ≤ 1/12 →
      (∀ j < count, L^A_M < n j) → 0 ≤ n count → Real.log (n 0) ≤ 3*L →
      Real.sqrt L*Real.sqrt 26*(L^A_M)^(-(1/2:ℝ)+μ)*B+
        (4*Real.sqrt L*L^6*((140:ℝ)^(2/3:ℝ)*(L^A_M)^(-(1/3:ℝ)+μ)*V)+
          4*Real.sqrt L*ε*(Q*∑ j ∈ S, pathDrop n j)) ≤ 3 := by
  filter_upwards [eventually_source_unary_error_budget q Cmass,
    eventually_ge_atTop (max 1 (max (Real.sqrt 26) (4*(140:ℝ)^(2/3:ℝ))))]
    with L hunary hLbig
  have hL : 1 ≤ L := (le_max_left _ _).trans hLbig
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h₁ : Real.sqrt 26 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLbig)
  have h₂ : 4*(140:ℝ)^(2/3:ℝ) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLbig)
  intro n count S hS hanti B V ε Q μ hB hBL hV hVL hε hεL hQ hQL hμ hactive hlast hlog
  have hmain := source_principal_residual_costs hL h₁ h₂ hAM hchoice hμ
  have hM : 1 ≤ L^A_M := Real.one_le_rpow hL hAM
  have herr := hunary n count S hS hanti (L^A_M) (Real.sqrt L) ε Q
    hM (Real.sqrt_nonneg L) le_rfl hε hεL hQ hQL hactive hlast hlog
  have hBterm : Real.sqrt L*Real.sqrt 26*(L^A_M)^(-(1/2:ℝ)+μ)*B ≤
      Real.sqrt L*Real.sqrt 26*L^Cmarked*(L^A_M)^(-(1/2:ℝ)+μ) := by
    calc
      _ ≤ Real.sqrt L*Real.sqrt 26*(L^A_M)^(-(1/2:ℝ)+μ)*L^Cmarked := by gcongr
      _ = _ := by ring
  have hVterm : 4*Real.sqrt L*L^6*((140:ℝ)^(2/3:ℝ)*(L^A_M)^(-(1/3:ℝ)+μ)*V) ≤
      Real.sqrt L*(4*(140:ℝ)^(2/3:ℝ))*L^(Cunary+6)*(L^A_M)^(-(1/3:ℝ)+μ) := by
    calc
      _ ≤ 4*Real.sqrt L*L^6*((140:ℝ)^(2/3:ℝ)*(L^A_M)^(-(1/3:ℝ)+μ)*L^Cunary) := by gcongr
      _ = _ := by
        have hpow : L^(6:ℝ) = L^(6:ℕ) := by exact Real.rpow_natCast L 6
        rw [Real.rpow_add hL0,hpow]
        ring
  linarith

end LipschitzHilbert

end

end OAI
