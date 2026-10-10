import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainComposition

namespace OAI

/-!
# Countability of support-cell descendants

Every descendant is determined by its depth and its center in the corresponding
support lattice net. Encoding these data in a countable dependent sum proves
countability of the full descendant family, not only of each generation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem supportCellDescendant_countable {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    Countable (SupportCellDescendant μ R hR k z) := by
  let (t : ℕ) : Countable (supportLatticeNets μ R hR (k + t)).points :=
    (supportLatticeNets_countable μ R hR (k + t)).to_subtype
  let f (i : SupportCellDescendant μ R hR k z) :
      Σ t : ℕ, (supportLatticeNets μ R hR (k + t)).points :=
    ⟨i.depth, ⟨i.center, i.mem_net⟩⟩
  apply Function.Injective.countable (f := f)
  intro i j hij
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  have ht : ti = tj := congrArg Sigma.fst hij
  subst tj
  have hc : (⟨xi, hxi⟩ : (supportLatticeNets μ R hR (k + ti)).points) = ⟨xj, hxj⟩ :=
    eq_of_heq (Sigma.mk.inj_iff.mp hij).2
  have hx : xi = xj := congrArg Subtype.val hc
  subst xj
  rfl

end

end RieszRectifiability

end OAI
