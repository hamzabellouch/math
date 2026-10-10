import Mathlib
import OAI.Analysis.AffineBernstein.LocalAreaStationarity
import OAI.Analysis.AffineBernstein.SmoothGraphChart

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma parametricFrame_derivative_injective {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E) (ξ : E) (x : Space n)
    (hd : b.det (parametricFrame X ξ x) ≠ 0) :
    Function.Injective (fderiv ℝ X x) := by
  have hi := ((b.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hd)).1
  have hj : LinearIndependent ℝ (fun i : Fin n => fderiv ℝ X x (coordinateVector n i)) :=
    hi.comp _ Sum.inl_injective
  apply (fderiv ℝ X x).toLinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hz : ∑ i, v i • fderiv ℝ X x (coordinateVector n i) = 0 := by
    change (fderiv ℝ X x) v = 0 at hv
    calc
      _ = fderiv ℝ X x (∑ i, v i • coordinateVector n i) := by simp
      _ = fderiv ℝ X x v := by rw [sum_coordinateVector]
      _ = 0 := hv
  have hh := Fintype.linearIndependent_iff.mp hj (fun i => v i) hz
  ext i
  exact hh i

/- Local stationarity on an arbitrary immersed parametrization of the actual
solution graph. The smooth inverse chart is produced by the inverse function
theorem, not included among the hypotheses. -/
theorem affineMaximal_immersed_graph_local_stationary {n : ℕ}
    {U Ω : Set (Space n)} (hU : IsOpen U) (hΩ : IsOpen Ω)
    {X : Space n → Space n × ℝ} {u : Space n → ℝ}
    (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    {x₀ : Space n} (hx₀ : x₀ ∈ U) (hi : Function.Injective (fderiv ℝ X x₀))
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ U ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (V : Space n → Space n × ℝ), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
      ∀ (ν : ℝ → Space n → (Space n × ℝ) →L[ℝ] ℝ) (ξ : ℝ → Space n → Space n × ℝ),
      (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => L (X y)+v+t • V y) x) = 0) →
      (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
      (∀ x ∈ K, 0 < ν 0 x (L ((0 : Space n),1))) →
      (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L ((0 : Space n),1))) (0,x)) →
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity (graphAmbientBasis n)
        (fun y => L (X y)+v+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  obtain ⟨φ,hxφ,hs,ht,he,hφ,hψ⟩ := exists_smooth_graph_chart hU hΩ hX hu him hx₀ hi
  refine ⟨φ.source,φ.open_source,hxφ,hs,?_⟩
  intro K hK hKW V hV hVK ν ξ hν hξ hc hcont
  have hg (t : ℝ) (x : Space n) (hx : x ∈ φ.source) :
      (fun y => L (X y)+v+t • V y) =ᶠ[nhds x]
        (fun y => L (φ y,u (φ y))+v+t • V y) := by
    filter_upwards [φ.open_source.mem_nhds hx] with y hy
    rw [he y hy]
  have hh := affineMaximal_local_parametric_area_stationary hΩ hK φ hφ hψ hKW ht hu hp hm
    hV hVK L v ν ξ (fun t x hx => by rw [← (hg t x hx).fderiv_eq (𝕜 := ℝ)]; exact hν t x hx)
    hξ hc hcont
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t => setIntegral_congr_fun hK.measurableSet
    (fun x hx => parametricAreaDensity_congr (graphAmbientBasis n) (hg t x (hKW hx)) _ _)

end AffineBernstein
end

end OAI
