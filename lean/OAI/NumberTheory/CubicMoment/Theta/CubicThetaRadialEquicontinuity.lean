import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialHolder
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

namespace OAI

/-! Unit-energy cusp test functions have a common square-root modulus
of continuity and locally precompact restrictions. -/
noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace CubicFirstMoment

lemma cubicThetaRadial_derivative_energy_le (A : ℝ) (f : cubicThetaRadialTests) :
    (∫ t : ℝ, ‖deriv (f:ℝ → ℂ) t‖^2) ≤ ‖cubicThetaRadialGraph A f‖^2 := by
  have he : (∫ t : ℝ, ‖deriv (f:ℝ → ℂ) t‖^2)=
      ‖cubicThetaRadialCoordinate A 1 (cubicThetaRadialEnergyTest A f)‖^2 := by
    rw [cubicTheta_l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [cubicThetaRadialCoordinate_test A 1 f] with t ht
    rw [ht]
    rfl
  rw [he]
  exact pow_le_pow_left₀ (_root_.norm_nonneg _)
    (cubicThetaRadialCoordinate_bound A 1 (cubicThetaRadialEnergyTest A f)) 2

lemma cubicThetaRadial_unit_holder (A : ℝ) (f : cubicThetaRadialTests)
    (hf : ‖cubicThetaRadialGraph A f‖ ≤ 1) (a b : ℝ) :
    ‖(f:ℝ → ℂ) b-(f:ℝ → ℂ) a‖^2 ≤ |b-a| := by
  have he : (∫ t : ℝ, ‖deriv (f:ℝ → ℂ) t‖^2) ≤ 1 :=
    (cubicThetaRadial_derivative_energy_le A f).trans
      (by simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) hf 2)
  have horder (a b : ℝ) (hab : a ≤ b) :
      ‖(f:ℝ → ℂ) b-(f:ℝ → ℂ) a‖^2 ≤ b-a :=
    (cubicTheta_radial_holder_sq f.property.1 f.property.2.1 hab).trans
      (by simpa using mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hab))
  rcases le_total a b with hab|hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using horder a b hab
  · rw [norm_sub_rev,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hba)]
    exact horder b a hba

lemma cubicThetaRadial_unit_value (A : ℝ) (f : cubicThetaRadialTests)
    (hf : ‖cubicThetaRadialGraph A f‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(f:ℝ → ℂ) t‖^2 ≤ t := by
  have h := cubicThetaRadial_unit_holder A f hf 0 t
  simpa [f.property.2.2 0 le_rfl,abs_of_nonneg ht] using h

abbrev CubicThetaRadialUnitTests (A : ℝ) := {f : cubicThetaRadialTests | ‖cubicThetaRadialGraph A f‖ ≤ 1}

def cubicThetaRadialCompactRestriction (A R : ℝ) (f : CubicThetaRadialUnitTests A) :
    Icc (0:ℝ) R →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => (f.val:ℝ → ℂ) t.val,f.val.property.1.continuous.comp continuous_subtype_val⟩

lemma cubicThetaRadialRestriction_equicontinuous (A R : ℝ) :
    Equicontinuous (fun f : CubicThetaRadialUnitTests A => cubicThetaRadialCompactRestriction A R f) := by
  intro x
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  refine ⟨ε^2,sq_pos_of_pos hε,?_⟩
  intro y hy f
  have h := cubicThetaRadial_unit_holder A f.val f.property x.val y.val
  have hlt : ‖(f.val:ℝ → ℂ) y.val-(f.val:ℝ → ℂ) x.val‖^2 < ε^2 :=
    h.trans_lt (by simpa only [Subtype.dist_eq,Real.dist_eq] using hy)
  have hn := (sq_lt_sq₀ (_root_.norm_nonneg _) hε.le).mp hlt
  simpa only [dist_eq_norm,norm_sub_rev,cubicThetaRadialCompactRestriction,
    BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk] using hn

theorem cubicThetaRadialRestriction_precompact (A : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (closure (Set.range (cubicThetaRadialCompactRestriction A R))) := by
  let S := Set.range (cubicThetaRadialCompactRestriction A R)
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:ℂ) (Real.sqrt R))
    (isCompact_closedBall _ _)
  · rintro g t ⟨f,rfl⟩
    change dist ((f.val:ℝ → ℂ) t.val) 0 ≤ Real.sqrt R
    rw [dist_zero_right]
    have hv := (cubicThetaRadial_unit_value A f.val f.property t.property.1).trans t.property.2
    exact (Real.le_sqrt (_root_.norm_nonneg _) hR).mpr hv
  · intro x
    obtain hx := cubicThetaRadialRestriction_equicontinuous A R x
    rw [Metric.equicontinuousAt_iff] at hx ⊢
    intro ε hε
    obtain ⟨δ,hδ,hbound⟩ := hx ε hε
    refine ⟨δ,hδ,?_⟩
    rintro y hy ⟨g,⟨f,rfl⟩⟩
    exact hbound y hy f

end CubicFirstMoment

end

end OAI
