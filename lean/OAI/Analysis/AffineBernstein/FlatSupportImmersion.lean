import Mathlib
import OAI.Analysis.AffineBernstein.FlatTubePositive

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
lemma supportParam_transverse_immersion {H : S × E → ℝ} {Y : S × E → E}
    {q : S × E} (hH : ContDiffAt ℝ ∞ H q) (hY : DifferentiableAt ℝ Y q)
    (hgrad : ∀ᶠ p in nhds q, ∀ z : E, fderiv ℝ H p (0,z) = inner ℝ (Y p) z)
    (J : F →L[ℝ] (S × E)) (hi : Function.Injective J) (d : E)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0)
    (hpos : ∀ v : E, v ≠ 0 → inner ℝ v d = 0 →
      0 < fderiv ℝ (fderiv ℝ H) q (0,v) (0,v)) :
    Function.Injective ((fderiv ℝ (supportParam Y) q).comp J) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  change fderiv ℝ (supportParam Y) q (J v) = 0 at hv
  rw [supportParam_fderiv hY] at hv
  have hs : (J v).1 = 0 := congrArg Prod.fst hv
  have hy : fderiv ℝ Y q (J v) = 0 := congrArg Prod.snd hv
  have hv' : J v = (0,(J v).2) := Prod.ext hs rfl
  have he : (J v).2 = 0 := by
    by_contra hn
    have hp := hpos (J v).2 hn (hJ v)
    have hh := support_angular_derivative hH hY hgrad (J v) (J v).2
    rw [hy,inner_zero_right,hv'] at hh
    linarith
  apply hi
  rw [map_zero]
  exact Prod.ext hs he

variable [CompleteSpace S] [FiniteDimensional ℝ E] [Nontrivial E]

/- A flat normal parametrization of the actual affine-epigraph boundary is
smooth and immersed; it lies on the original solution graph. The local graph
inverse is therefore available without a geometric chart hypothesis. -/
theorem affineEpigraph_flat_parametrization {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0) :
    let U := {x : Space n | (q₀+J x).1 ∈ B}
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => a+L (supportParam Y (q₀+J x))
    IsOpen U ∧ ContDiffOn ℝ ∞ X U ∧
      (∀ x ∈ U, (X x).1 ∈ Ω ∧ (X x).2 = u (X x).1) ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ X x)) := by
  let U := {x : Space n | (q₀+J x).1 ∈ B}
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let X := fun x : Space n => a+L (supportParam Y (q₀+J x))
  change IsOpen U ∧ ContDiffOn ℝ ∞ X U ∧ _
  have hq (x : Space n) : inner ℝ (q₀+J x).2 d = 1 := by
    simp only [Prod.snd_add,inner_add_left,hd,hJ,add_zero]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    simpa [hz] using hq x
  have hj (x : Space n) (hx : x ∈ U) :=
    affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hx (hne x)
  have hU : IsOpen U := hB.preimage ((continuous_const.add J.continuous).fst)
  have hc (x : Space n) (hx : x ∈ U) : ContDiffAt ℝ ∞ X x := by
    have hh : ContDiffAt ℝ ∞ (supportParam Y) (q₀+J x) := contDiffAt_fst.prodMk (hj x hx).2.1
    exact contDiffAt_const.add (L.contDiff.contDiffAt.comp x
      (hh.comp x (contDiffAt_const.add J.contDiff.contDiffAt)))
  refine ⟨hU,(fun x hx => (hc x hx).contDiffWithinAt),?_,?_⟩
  · intro x hx
    have he := affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hx (hne x)
    exact ⟨he.1,(sub_eq_zero.mp he.2.1).symm⟩
  · intro x hx
    have hH : ContDiffAt ℝ ∞ H (q₀+J x) := (hj x hx).1
    have hY : ContDiffAt ℝ ∞ Y (q₀+J x) := (hj x hx).2.1
    have hf : ContDiffAt ℝ ∞ (fun y : E => H ((q₀+J x).1,y)) (q₀+J x).2 :=
      hH.comp (q₀+J x).2
        (show ContDiffAt ℝ ∞ (fun y : E => ((q₀+J x).1,y)) (q₀+J x).2 from
          contDiffAt_const.prodMk contDiffAt_id)
    have hp' (v : E) (hv : v ≠ 0) (ht : inner ℝ v d = 0) :
        0 < fderiv ℝ (fderiv ℝ H) (q₀+J x) (0,v) (0,v) := by
      apply lt_of_lt_of_eq ?_ (second_fderiv_prod_right (s := (q₀+J x).1)
        (e := (q₀+J x).2) hH v v)
      apply positive_bilinear_transverse _ (q₀+J x).2 d
        (hf.isSymmSndFDerivAt (by simp)).eq (hne x) (by rw [hq]; norm_num) _ _ hv ht
      · intro w
        exact homogeneousSupport_hessian_radial (hK _ hx) ⟨0,interior_subset (hzero _ hx)⟩ hf w
      · intro w hw hwe
        have hr := affineEpigraph_radius_positive hΩ hcv hu hp a L hB hK hzero hx (hne x) hw hwe
        rw [sphereRadius_eq_hessian hf _ _ hwe] at hr
        exact hr
    have hinj := supportParam_transverse_immersion hH (hY.differentiableAt (by simp))
      (hj x hx).2.2.2 J hi d hJ hp'
    have hD : fderiv ℝ X x = L.toContinuousLinearMap.comp
        ((fderiv ℝ (supportParam Y) (q₀+J x)).comp J) := by
      exact ((L.hasFDerivAt.comp x
        (((contDiffAt_fst.prodMk hY).differentiableAt (by simp)).hasFDerivAt.comp x
          (J.hasFDerivAt.const_add q₀))).const_add a).fderiv
    rw [hD]
    exact L.injective.comp hinj

end AffineBernstein
end

end OAI
