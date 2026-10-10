import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.RieszExteriorAdjoint

namespace OAI

/-!
# Local and exterior capped density pairings

The ball and its closed exterior partition the global density pairing. Local
and renormalized exterior adjoint identities combine to prove integrability
and identify their sum with the negative global capped-transform pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem local_plus_exterior_capped_density_pairing {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hμ : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R ε : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hε : 0 < ε) (hεH : ε ≤ H)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M) (hg : Integrable g μ)
    (hmean : (∫ x, g x ∂μ) = 0) (hgs : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) μ ∧
      ((∫ x, scalarCappedTransform m (μ.restrict (ball a R)) e ε f x * g x ∂μ) +
        ∫ x, (∫ y in closedExterior a R,
          f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x ∂μ) =
        -(∫ y, f y * scalarCappedTransform m μ e ε g y ∂μ) := by
  have hfinite : μ (ball a R) ≠ ⊤ :=
    ne_of_lt ((hμ.2 a R hR).trans_lt ENNReal.ofReal_lt_top)
  have hfI : IntegrableOn f (ball a R) μ := by
    apply (integrableOn_const (C := M) hfinite).mono' hfm.aestronglyMeasurable.restrict
    exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using! hfb y
  obtain ⟨_, hinside, hlocal⟩ := scalarCappedTransform_adjoint m μ (μ.restrict (ball a R))
    e ε hε f g hfm hgm hfI hg
  obtain ⟨_, houtside, hfar⟩ := density_renormalized_exterior_adjoint m C μ μ hμ e a H R ε
    hH hR hHR hε hεH f g hfm hgm M hfb hg hmean hgs
  have hcomp : (ball a R)ᶜ = closedExterior a R := by
    ext y
    simp only [mem_compl_iff, mem_ball, closedExterior, mem_ofPred_eq, not_lt, dist_comm y a]
  have hI : Integrable (fun y => f y * scalarCappedTransform m μ e ε g y) μ := by
    have hinside' : IntegrableOn (fun y => f y * scalarCappedTransform m μ e ε g y) (ball a R) μ := hinside
    have hu := hinside'.union houtside
    rw [← hcomp, union_compl_self] at hu
    exact integrableOn_univ.mp hu
  refine ⟨hI, ?_⟩
  rw [hlocal, hfar, ← integral_add_compl measurableSet_ball hI, hcomp]
  ring

end

end RieszRectifiability

end OAI
