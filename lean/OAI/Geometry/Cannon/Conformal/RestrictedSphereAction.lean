import Mathlib
import OAI.Geometry.Cannon.Conformal.Center

namespace OAI

section
section
section
section
section
section
noncomputable section
namespace CannonMobius
open Set Filter Topology MeasureTheory CannonMetricQC CannonConformal
open scoped OnePoint

variable {Γ : Type*} [Group Γ]

def restrictedSphereAction (A : Γ →* (Sphere ≃ₜ Sphere)) (K : Set Sphere)
    (hK : ∀ g p, A g p ∈ K ↔ p ∈ K) : Γ →* Equiv.Perm K where
  toFun g :=
    { toFun := fun p => ⟨A g p,(hK g p).mpr p.property⟩
      invFun := fun p => ⟨A g⁻¹ p,(hK g⁻¹ p).mpr p.property⟩
      left_inv := by intro p; apply Subtype.ext; simp
      right_inv := by intro p; apply Subtype.ext; simp }
  map_one' := by ext p; change A 1 p=p; simp
  map_mul' g h := by ext p; change A (g*h) p=A g (A h p); simp

lemma sphereDerivative_one {p : Sphere} (hp : p ≠ ∞) :
    sphereDerivative (Homeomorph.refl Sphere) p=ContinuousLinearMap.id ℝ ℂ := by
  obtain ⟨point,rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp
  have he : inChart false false (Homeomorph.refl Sphere)=id := by
    funext z
    simp [inChart,chart,coordinate_coe]
  rw [sphereDerivative,he]
  exact (hasFDerivAt_id (coordinate (point : Sphere))).fderiv

lemma continuous_derivativeMatrix : Continuous derivativeMatrix := by
  unfold derivativeMatrix
  fun_prop

lemma measurable_sphereDerivative_on (f : Sphere ≃ₜ Sphere) {K : Set Sphere}
    (hK : ∀ p ∈ K, p ≠ ∞) :
    Measurable (fun p : K => sphereDerivative f p) := by
  have hc : Continuous (fun p : K => coordinate p) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (continuousAt_coordinate (hK p p.property)).comp continuous_subtype_val.continuousAt
  exact (measurable_fderiv ℝ (inChart false false f)).comp hc.measurable

lemma continuous_normalized_round :
    ContinuousOn (fun B : PlaneLinear => normalizedPull B roundForm) {B | planeDet B ≠ 0} := by
  intro B hB
  have hd : Continuous planeDet := by unfold planeDet; fun_prop
  have hp : Continuous (fun B : PlaneLinear => pullForm B roundForm) := by
    change Continuous (fun B : PlaneLinear =>
      ![roundForm 0*B 0^2+2*roundForm 1*B 0*B 2+roundForm 2*B 2^2,
        roundForm 0*B 0*B 1+roundForm 1*(B 0*B 3+B 1*B 2)+roundForm 2*B 2*B 3,
        roundForm 0*B 1^2+2*roundForm 1*B 1*B 3+roundForm 2*B 3^2])
    fun_prop
  exact ((hd.continuousAt.abs.inv₀ (abs_ne_zero.mpr hB)).smul hp.continuousAt).continuousWithinAt

lemma measurable_normalized_round :
    Measurable (fun B : PlaneLinear => normalizedPull B roundForm) := by
  have hd : Continuous planeDet := by unfold planeDet; fun_prop
  have hp : Continuous (fun B : PlaneLinear => pullForm B roundForm) := by
    change Continuous (fun B : PlaneLinear =>
      ![roundForm 0*B 0^2+2*roundForm 1*B 0*B 2+roundForm 2*B 2^2,
        roundForm 0*B 0*B 1+roundForm 1*(B 0*B 3+B 1*B 2)+roundForm 2*B 2*B 3,
        roundForm 0*B 1^2+2*roundForm 1*B 1*B 3+roundForm 2*B 3^2])
    fun_prop
  exact (hd.measurable.abs.inv).smul hp.measurable

lemma measurable_normalized_round_on (f : Sphere ≃ₜ Sphere) {K : Set Sphere}
    (hK : ∀ p ∈ K, p ≠ ∞) :
    Measurable (fun p : K => normalizedPull (derivativeMatrix (sphereDerivative f p)) roundForm) :=
  measurable_normalized_round.comp (continuous_derivativeMatrix.measurable.comp
    (measurable_sphereDerivative_on f hK))

theorem controlled_action_invariant_structure [Countable Γ]
    (A : Γ →* (Sphere ≃ₜ Sphere)) {η : CannonQM.Distortion}
    (hA : ∀ g, CannonQM.Controlled (A g) η) :
    ∃ K : Set Sphere, MeasurableSet K ∧ (∀ᵐ p ∂sphereMeasure, p ∈ K) ∧
      (∀ g p, A g p ∈ K ↔ p ∈ K) ∧
      (∀ p ∈ K, GoodDifferentials A (1+2*(η 2:ℝ)) p) ∧
      ∃ q : K → Form, Measurable q ∧
        (∀ p, LowerBound (((1+2*(η 2:ℝ))^2)⁻¹) (q p) ∧
          UpperBound ((1+2*(η 2:ℝ))^2) (q p)) ∧
        ∀ g (p : K) (hg : A g (p:Sphere) ∈ K),
          normalizedPull (derivativeMatrix (sphereDerivative (A g) p)) (q ⟨A g p,hg⟩)=q p := by
  obtain ⟨K,hKm,hKae,hK,hgood⟩ := controlled_action_derivative_core A hA
  let H : ℝ := 1+2*(η 2:ℝ)
  have hH : 0 < H := by dsimp [H]; positivity
  have hd (g : Γ) (p : K) : planeDet (derivativeMatrix (sphereDerivative (A g) p)) ≠ 0 :=
    derivativeDet_ne_zero ((hgood p p.property).2 g).2.2.1
  let B := restrictedSphereAction A K hK
  let L (g : Γ) (p : K) : Form ≃L[ℝ] Form :=
    pullbackEquiv (derivativeMatrix (sphereDerivative (A g) p)) (hd g p)
  have hcocycle (g h : Γ) (p : K) (q : Form) : L (g*h) p q=L h p (L g (B h p) q) := by
    change normalizedPull (derivativeMatrix (sphereDerivative (A (g*h)) p)) q=
      normalizedPull (derivativeMatrix (sphereDerivative (A h) p))
        (normalizedPull (derivativeMatrix (sphereDerivative (A g) (A h p))) q)
    rw [sphereDerivative_mul_on_core A hK hgood p.property,derivativeMatrix_comp,normalizedPull_mul]
  have hbound (g : Γ) (p : K) :
      LowerBound ((H^2)⁻¹) (L g p roundForm) ∧ UpperBound (H^2) (L g p roundForm) := by
    have hg := (hgood p p.property).2 g
    have hg' := (hgood (A g p) ((hK g p).mpr p.property)).2 g⁻¹
    have hcomp : (sphereDerivative (A g⁻¹) (A g p)).comp (sphereDerivative (A g) p)=
        ContinuousLinearMap.id ℝ ℂ := by
      rw [← sphereDerivative_mul_on_core A hK hgood p.property,inv_mul_cancel,map_one]
      exact sphereDerivative_one (hgood p p.property).1
    exact normalized_derivative_bounds _ _ hH hg.2.2.1 hcomp hg.2.2.2 hg'.2.2.2
  have hmeas (g : Γ) : Measurable (fun p : K => L g p roundForm) :=
    measurable_normalized_round_on (A g) (fun p hp => (hgood p hp).1)
  obtain ⟨q,hqm,hqb,hqi⟩ := invariant_measurable_form B L (fun _ => roundForm)
    (fun g p => pullbackEquiv_det _ (hd g p)) hcocycle hmeas
    (inv_pos.mpr (sq_pos_of_pos hH)) (sq_nonneg H)
    (fun g p => (hbound g p).1) (fun g p => (hbound g p).2)
  refine ⟨K,hKm,hKae,hK,hgood,q,hqm,hqb,?_⟩
  intro g p hg
  exact hqi g p

end CannonMobius

end
end
end
end
end
end
end

end OAI
