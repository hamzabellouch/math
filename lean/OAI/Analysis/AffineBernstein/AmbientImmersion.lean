import Mathlib
import OAI.Analysis.AffineBernstein.ImmersionStationary

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma parametricAreaDensity_volume_pullback {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ F) (L : E ≃L[ℝ] F) (a : F)
    {X : Space n → E} {x : Space n} (hX : DifferentiableAt ℝ X x)
    (ν : E →L[ℝ] ℝ) (ξ : E) :
    parametricAreaDensity b (fun y => a+L (X y)) (ν.comp L.symm.toContinuousLinearMap) (L ξ) x =
      parametricAreaDensity (b.map L.symm.toLinearEquiv) X ν ξ x := by
  have hS : parametricSecondForm (fun y => a+L (X y)) (ν.comp L.symm.toContinuousLinearMap) x =
      parametricSecondForm X ν x := by
    have he : (fun y => (ν.comp L.symm.toContinuousLinearMap) (a+L (X y))) =
        (fun y => ν (X y)+ν (L.symm a)) := by funext y; simp [add_comm]
    simp only [parametricSecondForm,he,hessian_add_constant]
  have hd := ((L.hasFDerivAt.comp x hX.hasFDerivAt).const_add a).fderiv
  change fderiv ℝ (fun y => a+L (X y)) x = _ at hd
  have hFr : parametricFrame (fun y => a+L (X y)) (L ξ) x =
      L ∘ parametricFrame X ξ x := by
    funext i
    rcases i with i | ⟨⟩
    · change fderiv ℝ (fun y => a+L (X y)) x (coordinateVector n i) = _
      rw [hd]
      rfl
    · rfl
  simp only [parametricAreaDensity,hS,hFr,Module.Basis.det_map]
  rfl

/- Literal local affine stationarity in any ambient vector coordinates.
The reference volume basis is transported exactly, not replaced by a
coordinate-free area axiom. -/
theorem affineMaximal_ambient_immersed_local_stationary {n : ℕ}
    {U Ω : Set (Space n)} (hU : IsOpen U) (hΩ : IsOpen Ω)
    {X : Space n → E} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : E ≃L[ℝ] (Space n × ℝ))
    (him : ∀ y ∈ U, (a+L (X y)).1 ∈ Ω ∧ (a+L (X y)).2 = u (a+L (X y)).1)
    {x₀ : Space n} (hx₀ : x₀ ∈ U) (hi : Function.Injective (fderiv ℝ X x₀)) :
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (V : Space n → E), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
      ∀ (ν : ℝ → Space n → E →L[ℝ] ℝ) (ξ : ℝ → Space n → E),
      (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => X y+t • V y) x) = 0) →
      (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
      (∀ x ∈ K, 0 < ν 0 x (L.symm ((0 : Space n),1))) →
      (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L.symm ((0 : Space n),1))) (0,x)) →
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity
        ((graphAmbientBasis n).map L.symm.toLinearEquiv)
        (fun y => X y+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  let Z : Space n → Space n × ℝ := fun y => a+L (X y)
  have hZ : ContDiffOn ℝ ∞ Z U := contDiffOn_const.add (L.contDiff.comp_contDiffOn hX)
  have hiZ : Function.Injective (fderiv ℝ Z x₀) := by
    have hd := ((L.hasFDerivAt.comp x₀
      ((hX.contDiffAt (hU.mem_nhds hx₀)).differentiableAt (by simp)).hasFDerivAt).const_add a).fderiv
    change fderiv ℝ Z x₀ = _ at hd
    rw [hd]
    exact L.injective.comp hi
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_immersed_graph_local_stationary hU hΩ hZ hu hp hm
    him hx₀ hiZ (ContinuousLinearEquiv.refl ℝ (Space n × ℝ)) 0
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hK hKW V hV hVK ν ξ hν hξ hc hcont
  have hLV : tsupport (fun y => L (V y)) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    apply hVK (subset_closure ?_)
    intro hz
    exact hy (by simp [hz])
  have hXW : ContDiffOn ℝ ∞ X W := hX.mono hWU
  have hdt (t : ℝ) (x : Space n) (hx : x ∈ W) :
      DifferentiableAt ℝ (fun y => X y+t • V y) x :=
    ((hXW.add (hV.const_smul t)).contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have he (t : ℝ) :
      (fun y => (ContinuousLinearEquiv.refl ℝ (Space n × ℝ)) (Z y)+0+t • L (V y)) =
        (fun y => a+L (X y+t • V y)) := by funext y; simp [Z,map_add,map_smul,add_assoc]
  have hh := hstat K hK hKW (fun y => L (V y)) (L.contDiff.comp_contDiffOn hV) hLV
    (fun t x => (ν t x).comp L.symm.toContinuousLinearMap) (fun t x => L (ξ t x))
    (by
      intro t x hx
      rw [he]
      have hd := ((L.hasFDerivAt.comp x (hdt t x hx).hasFDerivAt).const_add a).fderiv
      change fderiv ℝ (fun y => a+L (X y+t • V y)) x = _ at hd
      rw [hd]
      ext w
      have h0 := congrArg (fun T : Space n →L[ℝ] ℝ => T w) (hν t x hx)
      simpa using h0)
    (by intro t x hx; simpa using hξ t x hx)
    (by intro x hx; simpa using hc x hx)
    (by intro x hx; simpa using hcont x hx)
  apply hh.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  rw [he]
  exact (parametricAreaDensity_volume_pullback (graphAmbientBasis n) L a
    (hdt t x (hKW hx)) (ν t x) (ξ t x)).symm

end AffineBernstein
end

end OAI
