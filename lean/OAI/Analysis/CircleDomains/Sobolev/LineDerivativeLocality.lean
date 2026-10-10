import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! Classical one-dimensional derivatives are local on arbitrary level sets,
outside the countable set of one-sided isolated points. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma ae_deriv_zero_of_eqOn_const {f : ℝ → ℝ} {S : Set ℝ} {c : ℝ}
    (h : EqOn f (fun _ => c) S) :
    ∀ᵐ x ∂volume, x ∈ S → deriv f x = 0 := by
  have hnull : volume {x ∈ S | 𝓝[S ∩ Ioi x] x = ⊥} = 0 :=
    countable_setOfPred_isolated_right_within.measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxs
  let : NeBot (𝓝[S ∩ Ioi x] x) := ⟨fun hbot => hx ⟨hxs, hbot⟩⟩
  have hfreq : ∃ᶠ y in 𝓝[S ∩ Ioi x] x, f y = c := by
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h hy.1
  apply deriv_zero_of_frequently_const
  exact hfreq.filter_mono (nhdsWithin_mono _ (fun y hy => ne_of_gt hy.2))

lemma ae_derivative_eq_of_eqOn {f g : ℝ → ℝ} {S : Set ℝ} (h : EqOn f g S) :
    ∀ᵐ x ∂volume, x ∈ S → ∀ a b : ℝ, HasDerivAt f a x → HasDerivAt g b x → a = b := by
  have he : EqOn (fun x => f x-g x) (fun _ => (0:ℝ)) S := fun x hx => sub_eq_zero.mpr (h hx)
  filter_upwards [ae_deriv_zero_of_eqOn_const he] with x hx hxs a b ha hb
  have hd := (ha.sub hb).deriv
  have hz := hx hxs
  change deriv (f-g) x = 0 at hz
  rw [hd] at hz
  exact sub_eq_zero.mp hz

end CircleDomainRigidity

end

end OAI
