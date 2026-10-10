import OAI.Analysis.BernoulliCone.StationarityEnergy

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ}

lemma GlobalMinimizer.nonneg_of_continuous {u : Space d → ℝ}
    (hm : GlobalMinimizer u) (hc : Continuous u) : ∀ x, 0 ≤ u x := by
  obtain ⟨_,G,_,hn,_⟩ := hm
  simp only [Measure.restrict_univ] at hn
  have heq := Measure.eq_of_ae_eq (hn.mono (fun _ hx => max_eq_left hx))
    (hc.max continuous_const) hc
  intro x
  have hx := congrFun heq x
  rw [← hx]
  exact le_max_right _ _

/-- Compact rank-one domain variations give the Bernoulli stress identity
from unrestricted Sobolev minimality, including the volume term. -/
theorem GlobalMinimizer.stationarity {u : Space d → ℝ} {L : ℝ≥0}
    (hm : GlobalMinimizer u) (huLip : LipschitzWith L u)
    {a : Space d} {R : ℝ} (hR : 0 < R)
    {φ : Space d → ℝ} (hφ : Test (ball a R) φ) (e : Space d) :
    (∫ x in ball a R, Shape.stressTerm u φ e x) = 0 := by
  obtain ⟨C,hLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  let I : ℝ := ∫ x in ball a R, Shape.stressTerm u φ e x
  let B : ℝ := (2*(L:ℝ)^2*‖e‖^2*(C:ℝ)^2)*(volume (ball a R)).toReal
  have hn := hm.nonneg_of_continuous huLip.continuous
  have hε : 0 < (4*((C:ℝ)*‖e‖+1))⁻¹ := by positivity
  have hz : I/2 = 0 := by
    apply linear_coefficient_eq_zero _ B hε
    intro t ht
    obtain ⟨hK,hdet⟩ := Shape.small_parameter_bounds hφ.1 hLip e ht
    let hf := Shape.displacement_lipschitz hLip e t
    let g : Space d ≃ₜ Space d := Shape.perturbationHomeomorph hf hK
    have hg : ∀ x, g x=Shape.deform φ e t x := fun _ => rfl
    let v := fun y => u (g.symm y)
    have hvLip := huLip.comp (Shape.perturbationHomeomorph_symm_lipschitz hf hK)
    have hsup : tsupport (fun x => v x-u x) ⊆ tsupport φ :=
      Shape.pullback_diff_support (u:=u) e t g hg
    have hc : HasCompactSupport (fun x => v x-u x) :=
      hφ.2.1.of_isClosed_subset (isClosed_tsupport _) hsup
    have hcomp := hm.compare_lipschitz huLip hvLip a hR
      (Eventually.of_forall (fun x => hn (g.symm x))) hc (hsup.trans hφ.2.2)
    have hupper := Shape.general_energy_pullback_upper huLip hφ.1 hLip e t hdet g hg a R (by
      intro x hx
      by_contra hh
      exact hx (hφ.2.2 (subset_tsupport φ hh)))
    change energy (ball a R) v (gradient v) ≤ _ at hupper
    have hboth := hcomp.trans hupper
    dsimp [B,I]
    nlinarith
  exact (div_eq_zero_iff).mp hz |>.resolve_right (by norm_num)
end Bernoulli

end
end

end OAI
