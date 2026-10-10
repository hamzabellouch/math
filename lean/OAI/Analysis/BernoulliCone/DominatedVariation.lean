import OAI.Analysis.BernoulliCone.HalfspaceGroundstate

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ} {D : Set (Space d)}

lemma dominatedVariation_of_comparison [IsFiniteMeasure (volume.restrict D)]
    {u v : Space d → ℝ} {G V : Space d → Space d}
    (hu : H1 D u G) (hv : H10 D v V)
    (hn : ∀ᵐ x ∂volume.restrict D, 0≤u x)
    {C : ℝ} (hC : 0<C) (hbound : ∀ᵐ x ∂volume.restrict D, |v x| ≤ C*u x)
    (hmin : ∀ (w : Space d → ℝ) (W : Space d → Space d),
      H1 D w W → (∀ᵐ x ∂volume.restrict D, 0≤w x) →
      H10 D (fun x=>w x-u x) (fun x=>W x-G x) → energy D u G≤energy D w W) :
    (∫ x in D, inner ℝ (G x) (V x))=0 := by
  apply linear_coefficient_eq_zero _ (∫ x in D, ‖V x‖^2) (inv_pos.mpr hC)
  intro t ht
  have htC : |t| * C<1 := by
    calc |t| * C < C⁻¹*C := mul_lt_mul_of_pos_right ht hC
         _ = 1 := inv_mul_cancel₀ hC.ne'
  have hcontrol : ∀ᵐ x ∂volume.restrict D,
      0≤u x+t*v x ∧ ((0<u x+t*v x) ↔ 0<u x) := by
    filter_upwards [hn,hbound] with x hx hbx
    have hb : |t*v x| ≤ (|t| * C)*u x := by
      rw [abs_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left hbx (abs_nonneg t)
    by_cases hup : 0<u x
    · have hp : 0<u x+t*v x := by
        have := neg_abs_le (t*v x)
        nlinarith
      exact ⟨hp.le,iff_of_true hp hup⟩
    · have hz : u x=0 := le_antisymm (not_lt.mp hup) hx
      have hvz : v x=0 := abs_eq_zero.mp (le_antisymm (by simpa only [hz,mul_zero] using hbx) (abs_nonneg _))
      simp only [hz,hvz,mul_zero,add_zero,le_refl,lt_self_iff_false,iff_self,and_self]
  have hc := hmin (fun x=>u x+t*v x) (fun x=>G x+t • V x)
    (hu.add (hv.1.const_smul t)) (hcontrol.mono fun _ hx=>hx.1)
    (by simpa only [add_sub_cancel_left] using hv.const_smul t)
  rw [energy_affine hu.1 hu.2.1 hv.1.2.1 t (hcontrol.mono fun _ hx=>hx.2)] at hc
  linarith

lemma GlobalMinimizer.dominatedVariation {u v : Space d → ℝ} {L : ℝ≥0}
    (hm : GlobalMinimizer u) (hL : LipschitzWith L u)
    {a : Space d} {R C : ℝ} (hR : 0<R)
    {V : Space d → Space d} (hv : H10 (ball a R) v V)
    (hC : 0<C) (hbound : ∀ᵐ x ∂volume.restrict (ball a R), |v x| ≤ C*u x) :
    (∫ x in ball a R, inner ℝ (gradient u x) (V x))=0 := by
  let : IsFiniteMeasure (volume.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨_,G,hG,hn,hmin⟩ := hm
  have hu := hG a R hR (subset_univ _)
  have he := hu.gradient_unique isOpen_ball (LipschitzSobolev.h1_ball hL a R)
  have hh := dominatedVariation_of_comparison hu hv
    (ae_restrict_of_ae (by simpa only [Measure.restrict_univ] using hn)) hC hbound
    (hmin a R hR (subset_univ _))
  rw [←hh]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]
end Bernoulli

end
end

end OAI
