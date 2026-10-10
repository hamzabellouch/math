import Mathlib
import OAI.Analysis.AffineBernstein.ActualFlatFEquation
import OAI.Analysis.AffineBernstein.ActualInvariantTube
import OAI.Analysis.AffineBernstein.TubeChartConstruction
import OAI.Analysis.AffineBernstein.InverseTracePullback

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineMaximal_flat_invariant_f_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (q₀ : S × E) (hd : inner ℝ q₀.2 (bE (Sum.inr ())) = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 (bE (Sum.inr ())) = 0)
    (C : (S × E) →L[ℝ] Space n) (hC : ∀ x, C (J x) = x)
    (e : Fin n ≃ ι ⊕ κ)
    (hJb : ∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i))
    {x₀ : Space n} (hx₀ : (q₀+J x₀).1 ∈ D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let q := q₀+J x₀
    let B := tubeBaseMatrix H q bS
    let R := tubeRadiusMatrix H q bE
    let V := fun i : ι => ((bS i), (0:E))
    let W := fun i : κ => ((0:S), bE (Sum.inl i))
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let F := invariantTubeF H bS bE δ
    let P := fun y => Real.log (H y)
    let T := fun y => F y+P y
    (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
      H q*flatInversePair B V P P q -
      ((n : ℝ)+1)*H q*flatInversePair B V T T q +
      H q*flatInverseTrace R W F q + 2*H q*flatInversePair R W P F q +
      H q*flatInversePair R W F F q = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let φ := fun x => H (q₀+J x)
  let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
  let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
  let B := fun y => flatBlockHessian (fun z => -φ z) v y
  let R := fun y => flatBlockHessian φ w y
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let t := flatLogAreaRatio B R δ
  let p := fun y => Real.log (φ y)
  let f := fun y => t y-p y
  let F := invariantTubeF H bS bE δ
  let P := fun y => Real.log (H y)
  let T := fun y => F y+P y
  let U : Set (Space n) := {x | (q₀+J x).1 ∈ D}
  have hU : IsOpen U := hD.preimage (continuous_const.add J.continuous).fst
  have hxU : x₀ ∈ U := hx₀
  have hv (i : ι) : J (v i) = (bS i,0) := by simp [v,hJb,tubeTangent]
  have hw (i : κ) : J (w i) = (0,bE (Sum.inl i)) := by simp [w,hJb,tubeTangent]
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have he (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    have hinner := hq x
    simp [hz] at hinner
  have hHs (x : Space n) (hx : x ∈ U) : ContDiffAt ℝ ∞ H (q₀+J x) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hx (he x)).1
  have hfe : f =ᶠ[𝓝 x₀] (fun y => F (q₀+J y)) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    have hpos := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero hy bS bE
      (show inner ℝ (q₀+J y).2 (bE (Sum.inr ())) ≠ 0 by rw [hq]; norm_num)
    have hh := invariantTubeF_eq_flat (hHs y hy) bS bE (hq y)
      (affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hy (he y))
      hpos.2.det_pos.ne' δ
    rw [tubeBaseMatrix_eq_flatBlockHessian q₀ J (hHs y hy) bS v hv,
      tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hHs y hy) bE w hw] at hh
    exact hh.symm
  have hte : t =ᶠ[𝓝 x₀] (fun y => T (q₀+J y)) := by
    filter_upwards [hfe] with y hy
    change t y-p y = F (q₀+J y) at hy
    change t y = F (q₀+J y)+p y
    linarith
  have hF : ContDiffAt ℝ ∞ F (q₀+J x₀) :=
    affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hx₀ (he x₀) bS bE δ
  have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hx₀ (he x₀) bS bE
  have hP : ContDiffAt ℝ ∞ P (q₀+J x₀) := (hHs x₀ hxU).log hpos.2.2.ne'
  have hT : ContDiffAt ℝ ∞ T (q₀+J x₀) := hF.add hP
  have hfeq := affineMaximal_flat_tube_f_equation hΩ hcv hu hp hm a L hD hK hzero
    bS bE q₀ hd J hi hJ C hC e hJb hx₀
  change (n : ℝ) - 2*Fintype.card ι + φ x₀*flatInverseTrace (B x₀) v f x₀ -
      φ x₀*flatInversePair (B x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (B x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ + 2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0 at hfeq
  rw [flatInverseTrace_congr hfe (B x₀) v,flatInverseTrace_congr hfe (R x₀) w,
    flatInversePair_congr hte hte (B x₀) v,
    flatInversePair_congr (Filter.EventuallyEq.rfl : p =ᶠ[𝓝 x₀] p) hfe (R x₀) w,
    flatInversePair_congr hfe hfe (R x₀) w] at hfeq
  change (n : ℝ) - 2*Fintype.card ι + H (q₀+J x₀)*flatInverseTrace (B x₀) v (fun y => F (q₀+J y)) x₀ -
      H (q₀+J x₀)*flatInversePair (B x₀) v (fun y => P (q₀+J y)) (fun y => P (q₀+J y)) x₀ -
      ((n : ℝ)+1)*H (q₀+J x₀)*flatInversePair (B x₀) v (fun y => T (q₀+J y)) (fun y => T (q₀+J y)) x₀ +
      H (q₀+J x₀)*flatInverseTrace (R x₀) w (fun y => F (q₀+J y)) x₀ +
      2*H (q₀+J x₀)*flatInversePair (R x₀) w (fun y => P (q₀+J y)) (fun y => F (q₀+J y)) x₀ +
      H (q₀+J x₀)*flatInversePair (R x₀) w (fun y => F (q₀+J y)) (fun y => F (q₀+J y)) x₀ = 0 at hfeq
  rw [flatInverseTrace_affine_pullback q₀ J hF,flatInverseTrace_affine_pullback q₀ J hF,
    flatInversePair_affine_pullback q₀ J (hP.differentiableAt (by simp)) (hP.differentiableAt (by simp)),
    flatInversePair_affine_pullback q₀ J (hT.differentiableAt (by simp)) (hT.differentiableAt (by simp)),
    flatInversePair_affine_pullback q₀ J (hP.differentiableAt (by simp)) (hF.differentiableAt (by simp)),
    flatInversePair_affine_pullback q₀ J (hF.differentiableAt (by simp)) (hF.differentiableAt (by simp))] at hfeq
  have hB : B x₀ = tubeBaseMatrix H (q₀+J x₀) bS :=
    (tubeBaseMatrix_eq_flatBlockHessian q₀ J (hHs x₀ hxU) bS v hv).symm
  have hR : R x₀ = tubeRadiusMatrix H (q₀+J x₀) bE :=
    (tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hHs x₀ hxU) bE w hw).symm
  simp only [hB,hR,hv,hw] at hfeq
  exact hfeq

/- The invariant support f-equation, with all flat-normal chart data produced
from the actual frames. At a unit normal it is the round-sphere equation,
since the actual invariant scalar has zero radial derivative. -/
theorem affineMaximal_invariant_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : bE (Sum.inr ()) = e) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let q := (s,e)
    let B := tubeBaseMatrix H q bS
    let R := tubeRadiusMatrix H q bE
    let V := fun i : ι => ((bS i), (0:E))
    let W := fun i : κ => ((0:S), bE (Sum.inl i))
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let F := invariantTubeF H bS bE δ
    let P := fun y => Real.log (H y)
    let T := fun y => F y+P y
    (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
      H q*flatInversePair B V P P q -
      ((n : ℝ)+1)*H q*flatInversePair B V T T q +
      H q*flatInverseTrace R W F q + 2*H q*flatInversePair R W P F q +
      H q*flatInversePair R W F F q = 0 := by
  obtain ⟨idx⟩ := tube_dimension_equiv bS bE L
  obtain ⟨J,C,hi,hC,hJ,hJb⟩ := exists_flat_tube_chart bS bE idx
  have hd : inner ℝ (s,e).2 (bE (Sum.inr ())) = 1 := by
    rw [← he]
    simp
  have hh := affineMaximal_flat_invariant_f_equation hΩ hcv hu hp hm a L hD hK hzero bS bE
    (s,e) hd J hi hJ C hC idx hJb (x₀ := 0) (by simpa using hs)
  simpa only [map_zero,add_zero] using hh

end AffineBernstein
end

end OAI
