import OAI.Analysis.CircleDomains.Topology.PositiveJordanOrientation
import Mathlib.Topology.LocallyConstant.Basic

namespace OAI

/-! A continuous family of ambient homeomorphisms beginning at the identity
preserves the positive argument increment. No smooth isotopy theorem is assumed. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma jordanInterior_trans (H T : ℂ ≃ₜ ℂ) :
    jordanInterior (H.trans T) = T '' jordanInterior H := by
  change (T ∘ H) '' Metric.ball 0 1 = T '' (H '' Metric.ball 0 1)
  rw [image_image]
  rfl

lemma positiveJordanParametrization_transport
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    (T : A → ℂ ≃ₜ ℂ) (hT : Continuous (fun p : A × ℂ => T p.1 p.2))
    (a₀ : A) (h₀ : T a₀ = Homeomorph.refl ℂ)
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ)
    (a : A) (hreg : RegularJordanParametrization (H.trans (T a)) (T a ∘ γ)) :
    PositiveJordanParametrization (H.trans (T a)) (T a ∘ γ) := by
  refine ⟨hreg.smooth, hreg.periodic, hreg.injective, hreg.regular, hreg.boundary, ?_⟩
  intro y hy
  rw [jordanInterior_trans] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hne (b : A) (t : ℝ) : T b (γ t) - T b z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have ht := hγ.toRegular.mem_frontier t
    have he' := (T b).injective he
    rw [he', frontier, (jordanInterior_isOpen H).interior_eq] at ht
    exact ht.2 hz
  let p : A → C(unitInterval, UnitAddCircle) := fun b =>
    ⟨fun t => normalizedArgument (T b (γ t) - T b z), by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (continuousAt_normalizedArgument (hne b t)).comp
        (f := fun t : unitInterval => T b (γ t) - T b z)
        (((T b).continuous.comp (hγ.smooth.continuous.comp continuous_subtype_val)).sub
          continuous_const).continuousAt⟩
  have hp : Continuous p := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply continuous_iff_continuousAt.mpr
    intro q
    apply (continuousAt_normalizedArgument (hne q.1 q.2)).comp
      (f := fun q : A × unitInterval => T q.1 (γ q.2) - T q.1 z)
    exact ((hT.comp (continuous_fst.prodMk
      (hγ.smooth.continuous.comp (continuous_subtype_val.comp continuous_snd)))).sub
        (hT.comp (continuous_fst.prodMk continuous_const))).continuousAt
  have hi : Continuous (fun b => circlePathIncrement (p b)) := continuous_circlePathIncrement.comp hp
  have hproj (b : A) : (circlePathIncrement (p b) : UnitAddCircle) = (0 : ℝ) := by
    unfold circlePathIncrement
    rw [AddCircle.coe_sub, realCirclePathLift_projects, realCirclePathLift_projects]
    change normalizedArgument (T b (γ 1) - T b z) -
      normalizedArgument (T b (γ 0) - T b z) = _
    rw [show γ 1 = γ 0 by simpa using hγ.periodic 0, sub_self]
    rfl
  have hc := isLocallyConstant_real_lift_difference hi (continuous_const (y := (0 : ℝ))) hproj
  have he := hc.apply_eq_of_preconnectedSpace a a₀
  obtain ⟨u, hu, hu1⟩ := hγ.positive z hz
  have hstart : circlePathIncrement (p a₀) = 1 := by
    rw [circlePathIncrement_eq_lift (p a₀) u (fun t => by simpa [p, h₀] using hu t), hu1]
    ring
  refine ⟨realCirclePathLift (p a), ?_, ?_⟩
  · exact realCirclePathLift_projects (p a)
  · change circlePathIncrement (p a) - 0 = circlePathIncrement (p a₀) - 0 at he
    rw [hstart] at he
    dsimp only [circlePathIncrement] at he
    linarith

end CircleDomainRigidity

end

end OAI
