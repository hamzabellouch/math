import Mathlib
import OAI.Analysis.AffineBernstein.FlatSupportImmersion
import OAI.Analysis.AffineBernstein.AmbientImmersion
import OAI.Analysis.AffineBernstein.SupportOrientation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ParametricBasis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametricAreaDensity_change_basis {n : ℕ}
    (b b' : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E)
    (ν : E →L[ℝ] ℝ) (ξ : E) (x : Space n) :
    parametricAreaDensity b' X ν ξ x =
      Real.rpow |b'.det b| ((n : ℝ)/((n : ℝ)+2)) * parametricAreaDensity b X ν ξ x := by
  have he : b'.det (parametricFrame X ξ x) = b'.det b * b.det (parametricFrame X ξ x) := by
    conv_lhs => rw [b'.det.eq_smul_basis_det b]
    rfl
  simp only [parametricAreaDensity,he,abs_mul]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  ring

end ParametricBasis

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/- The literal PDE supplies stationarity on every actual flat-normal support
chart. The chart inverse and conormal orientation are derived, not assumed. -/
theorem affineMaximal_flatSupport_local_stationary {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0)
    (b : Module.Basis (Fin n ⊕ Unit) ℝ (S × E))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ B) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => supportParam Y (q₀+J x)
    ∃ W : Set (Space n), IsOpen W ∧ x₀ ∈ W ∧ W ⊆ {x | (q₀+J x).1 ∈ B} ∧
      ∀ (K : Set (Space n)), IsCompact K → K ⊆ W →
      ∀ (V : Space n → S × E), ContDiffOn ℝ ∞ V W → tsupport V ⊆ K →
      ∀ (ν : ℝ → Space n → (S × E) →L[ℝ] ℝ) (ξ : ℝ → Space n → S × E),
      (∀ t x, x ∈ W → (ν t x).comp (fderiv ℝ (fun y => X y+t • V y) x) = 0) →
      (∀ t x, x ∈ W → ν t x (ξ t x) = 1) →
      (∀ x ∈ K, ν 0 x = supportConormal H (q₀+J x)) →
      (∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L.symm ((0 : Space n),1))) (0,x)) →
      HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity b
        (fun y => X y+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let X := fun x : Space n => supportParam Y (q₀+J x)
  let U := {x : Space n | (q₀+J x).1 ∈ B}
  obtain ⟨hU,hLX,him,hiLX⟩ := affineEpigraph_flat_parametrization hΩ hcv hu hp a L hB hK hzero q₀ d hd J hi hJ
  have he : (fun x => L.symm ((a+L (X x))-a)) = X := by funext x; simp
  have hX : ContDiffOn ℝ ∞ X U := by
    rw [← he]
    exact L.symm.contDiff.comp_contDiffOn (hLX.sub contDiffOn_const)
  have hiX : Function.Injective (fderiv ℝ X x₀) := by
    have hdX : fderiv ℝ (fun x => a+L (X x)) x₀ = L.toContinuousLinearMap.comp (fderiv ℝ X x₀) :=
      ((L.hasFDerivAt.comp x₀ ((hX.contDiffAt (hU.mem_nhds hx₀)).differentiableAt (by simp)).hasFDerivAt).const_add a).fderiv
    have hh := hiLX x₀ hx₀
    change Function.Injective (fderiv ℝ (fun x => a+L (X x)) x₀) at hh
    rw [hdX] at hh
    exact Function.Injective.of_comp hh
  obtain ⟨W,hW,hxW,hWU,hstat⟩ := affineMaximal_ambient_immersed_local_stationary hU hΩ hX hu hp hm a L him hx₀ hiX
  change ∃ W, _
  refine ⟨W,hW,hxW,hWU,?_⟩
  intro K hKc hKW V hV hVK ν ξ hν hξ heν hcν
  have hpos (x : Space n) (hx : x ∈ K) : 0 < ν 0 x (L.symm ((0 : Space n),1)) := by
    rw [heν x hx]
    apply affineEpigraph_supportConormal_inward hΩ hcv hu hp a L hB hK hzero (hWU (hKW hx))
    intro hz
    have hh : inner ℝ (q₀+J x).2 d = 1 := by simp [inner_add_left,hd,hJ]
    simp [hz] at hh
  have hh := hstat K hKc hKW V hV hVK ν ξ hν hξ hpos hcν
  let b₀ := (graphAmbientBasis n).map L.symm.toLinearEquiv
  let c := Real.rpow |b.det b₀| ((n : ℝ)/((n : ℝ)+2))
  have heq : (fun t : ℝ => ∫ x in K, parametricAreaDensity b (fun y => X y+t • V y) (ν t x) (ξ t x) x) =
      (fun t => c * ∫ x in K, parametricAreaDensity b₀ (fun y => X y+t • V y) (ν t x) (ξ t x) x) := by
    funext t
    simp only [parametricAreaDensity_change_basis b₀ b,← integral_const_mul]
    rfl
  rw [heq]
  convert! hh.const_mul c using 1
  simp [mul_zero]

end AffineBernstein
end

end OAI
