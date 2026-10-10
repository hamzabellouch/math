import OAI.NumberTheory.Ostmann.Construction.GiantNormalizationReserveBasic
import OAI.NumberTheory.Ostmann.Construction.InitialSourceChoice

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction

lemma exp_logCellMass_eq_exp_neg_giantNormalizationCost (G : ℝ) :
    Real.exp (Real.log (logCellMass G ∅))=Real.exp (-giantNormalizationCost G) := by
  simp only [giantNormalizationCost,neg_neg]

theorem initial_giant_normalization_reserve_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L:ℝ in atTop,∀E:Finset ℕ,∀C:InitialSourceChoice d Bs BD Bz k L E,
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      giantNormalizationCost C.giantCenter+Real.log 2≤(Conclusion.bulkSize k L:ℝ) := by
  filter_upwards [giantNormalizationCost_bulk_reserve_eventually hk] with L hreserve
  intro E C hGlo hGhi hclo hchi
  exact hreserve C.giantCenter (by linarith) (by linarith)

end Ostmann.Construction

end

end OAI
