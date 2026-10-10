import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PhysicalPoisson
import OAI.Analysis.CoulombRadii.ThomasFermi.TFInterior
import OAI.Analysis.CoulombRadii.ThomasFermi.LpParameter
import OAI.Analysis.CoulombRadii.ThomasFermi.TFCountTest

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology ContDiff SchwartzMap Pointwise
noncomputable section
namespace Coulomb

instance finite_volume_ball (y : Space) (r : ℝ) : IsFiniteMeasure (volume.restrict (Metric.ball y r)) :=
  isFiniteMeasure_restrict.mpr ((measure_mono Metric.ball_subset_closedBall).trans_lt
    (isCompact_closedBall y r).measure_lt_top).ne

lemma patch_nucleus_separation {J : ℕ} (S : Nuclei J) {a b t : ℝ} (ha : 0<a) (hb : 0<b)
    (ht : t≤6*a) (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    ∀ j x, x∈Metric.ball y (t-4*b) → a≤‖x-S.position j‖ := by
  intro j x hx
  have hh : ‖x-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have H := norm_sub_le_norm_sub_add_norm_sub (S.position j) x y
  rw [norm_sub_rev (S.position j) x] at H
  linarith [hn j]

lemma patch_continuous_field {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    ContinuousOn (coreScreenedField S u) (Metric.ball y (t-4*b)) := by
  apply (coreScreenedField_continuousOn S u hu (r := t-4*b) (t := t) (by linarith)
    (fun z hz => hz) ?_).mono Metric.ball_subset_closedBall
  intro j hj
  have hh : ‖S.position j-y‖≤t-4*b := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hj
  linarith [hn j]

lemma patch_harmonic_field {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖) :
    NeutralAtom.HasWeakLaplacian (coreScreenedField S u) (Metric.ball y (t-4*b)) (fun _ => 0) := by
  apply coreScreenedField_weak_harmonic S u hu
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    have hh : ‖z-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hz'
    change t≤‖z-y‖ at hz
    linarith
  · intro j hj
    have hh : ‖S.position j-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hj
    linarith [hn j]

lemma patch_inner_ball {a b t : ℝ} (_ : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : 5*a≤t) (y : Space) : Metric.closedBall y (4*a)⊆Metric.ball y (t-4*b) := by
  intro z hz
  have hh : ‖z-y‖≤4*a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  simp only [Metric.mem_ball,dist_eq_norm]
  linarith

lemma patch_hole_density {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t≤6*a) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (W : TFLq (volume.restrict (Metric.ball y (t-4*b)))) :
    SourceFreeHoleDensity S u (scaledWindow unitWindow b hb.ne') b
      (localTFDensity measurableSet_ball W) (Metric.closedBall y (t-4*b)) {z | t≤‖z-y‖} := by
  apply localTFDensity_hole measurableSet_ball W S u _ b _ _
    (isCompact_closedBall ..) (isClosed_le continuous_const (by fun_prop)) Metric.ball_subset_closedBall hu
  · apply Set.disjoint_left.mpr
    rintro z hz ⟨v,hv,w,hw,rfl⟩
    have hv' : ‖v-y‖≤t-4*b := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hv
    have hw' : ‖w‖≤b := by
      apply le_of_not_gt
      intro hw'
      have hn' : w∉tsupport (scaledWindow unitWindow b hb.ne' : Space → ℝ) := by
        have hs : tsupport (scaledWindow unitWindow b hb.ne' : Space → ℝ)⊆Metric.closedBall 0 b := by
          apply closure_minimal _ Metric.isClosed_closedBall
          intro x hx
          simp only [Metric.mem_closedBall,dist_zero_right]
          exact le_of_not_gt (fun h => hx (scaledWindow_support unitWindow unitWindow_support hb x h))
        intro hm
        have hle : ‖w‖≤b := by simpa only [Metric.mem_closedBall,dist_zero_right] using hs hm
        linarith
      exact hn' hw
    have htri : ‖v+w-y‖≤‖v-y‖+‖w‖ := by
      simpa only [show v+w-y=(v-y)+w by abel] using norm_add_le (v-y) w
    change t≤‖v+w-y‖ at hz
    linarith
  · intro z hz x hx
    have hh : ‖x-y‖<t-4*b := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
    have H := norm_sub_le_norm_sub_add_norm_sub z x y
    change t≤‖z-y‖ at hz
    linarith
  · intro j x hx
    have H := patch_nucleus_separation S ha hb ht y hn j x hx
    rw [norm_sub_rev]
    linarith

def tfInteriorCountConstant : ℝ :=
  (tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)*(27*(Real.pi*4/3))

lemma patch_TF_test_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {a b t F : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hu : SpatiallySupported u {z | t≤‖z-y‖}) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hF : 0≤F) (hcap : ∀ x∈Metric.ball y (t-4*b), coreScreenedField S u x≤F) :
    (∫ x, localTFDensity measurableSet_ball
      (coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)) x*
      countTest y (3*a/2) x) ≤ tfInteriorCountConstant/a^3 := by
  let W := coreTFField S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn)
  have hW : ∀ᵐ x ∂volume.restrict (Metric.ball y (t-4*b)), W x≤F := by
    filter_upwards [coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn),ae_restrict_mem measurableSet_ball] with x hx hy
    exact hx ▸ hcap x hy
  have H := tfDensity_interior_bound measurableSet_ball thomasFermiKineticConstant_pos hF W hW
    (localTFMinimizer_nonneg measurableSet_ball W) (fun g hg => localTFMinimizer_minimizes measurableSet_ball W hg)
    (patch_continuous_field S u ha hb ht.2 y hu hn) Metric.isOpen_ball
    (coreTFField_coe S u measurableSet_ball ha (patch_nucleus_separation S ha hb ht.2 y hn))
    (patch_harmonic_field S u ha hb ht.2 y hu hn) ha (patch_inner_ball ha hb hsmall ht.1 y)
  have H' := tfDensity_test_bound measurableSet_ball (localTFMinimizer_nonneg measurableSet_ball W) y
    (by positivity : 0<3*a/2) (by positivity [tfInteriorConstant_nonneg thomasFermiKineticConstant,thomasFermiKineticConstant_pos] : 0≤(tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)
    (by simpa only [show 2*(3*a/2)=3*a by ring] using H)
  apply H'.trans_eq
  unfold tfInteriorCountConstant
  field_simp
  ring

end Coulomb
end

end
end

end OAI
