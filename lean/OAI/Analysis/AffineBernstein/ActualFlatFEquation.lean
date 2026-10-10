import Mathlib
import OAI.Analysis.AffineBernstein.FlatTubeChart
import OAI.Analysis.AffineBernstein.FlatFEquation

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

/- Actual original PDE implies the support tube f equation in every flat normal chart. -/
theorem affineMaximal_flat_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
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
    let φ := fun x => H (q₀+J x)
    let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
    let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
    let B := fun y => flatBlockHessian (fun z => -φ z) v y
    let R := fun y => flatBlockHessian φ w y
    let δ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let t := flatLogAreaRatio B R δ
    let p := fun y => Real.log (φ y)
    let f := fun y => t y-p y
    (n : ℝ) - 2*Fintype.card ι + φ x₀*flatInverseTrace (B x₀) v f x₀ -
      φ x₀*flatInversePair (B x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (B x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ +
      2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0 := by
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
  let W : Set (Space n) := {x | (q₀+J x).1 ∈ D}
  have hW : IsOpen W := hD.preimage (continuous_const.add J.continuous).fst
  have hxW : x₀ ∈ W := hx₀
  have hv (i : ι) : J (v i) = (bS i,0) := by simp [v,hJb,tubeTangent]
  have hw (i : κ) : J (w i) = (0,bE (Sum.inl i)) := by simp [w,hJb,tubeTangent]
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    have hinner := hq x
    simp [hz] at hinner
  have hH (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ H (q₀+J x) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hx (hne x)).1
  have hφ : ContDiffOn ℝ ∞ φ W := fun x hx =>
    ((hH x hx).comp x (contDiffAt_const.add J.contDiff.contDiffAt)).contDiffWithinAt
  have hBe (x : Space n) (hx : x ∈ W) : tubeBaseMatrix H (q₀+J x) bS = B x :=
    tubeBaseMatrix_eq_flatBlockHessian q₀ J (hH x hx) bS v hv
  have hRe (x : Space n) (hx : x ∈ W) : tubeRadiusMatrix H (q₀+J x) bE = R x :=
    tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hH x hx) bE w hw
  have hpos (x : Space n) (hx : x ∈ W) : (B x).PosDef ∧ (R x).PosDef := by
    have hh := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero hx
      (e := (q₀+J x).2) bS bE (by rw [hq x]; norm_num)
    change (tubeBaseMatrix H (q₀+J x) bS).PosDef ∧
      (tubeRadiusMatrix H (q₀+J x) bE).PosDef at hh
    rwa [hBe x hx,hRe x hx] at hh
  have hφpos (x : Space n) (hx : x ∈ W) : 0 < φ x := by
    apply supportValue_pos (hK _ hx) (hzero _ hx)
    intro hz
    exact hne x ((InnerProductSpace.toDual ℝ E).injective (by simpa using hz))
  have hB (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ (fun y i j => B y i j) x :=
    contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hx)).neg v
  have hR (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ (fun y i j => R y i j) x :=
    contDiffAt_flatBlockHessian (hφ.contDiffAt (hW.mem_nhds hx)) w
  have hdim : (Fintype.card ι : ℝ) + Fintype.card κ = n := by
    have hh := Fintype.card_congr e
    simp only [Fintype.card_fin,Fintype.card_sum] at hh
    exact_mod_cast hh.symm
  have hden : (Fintype.card ι : ℝ)+Fintype.card κ+2 ≠ 0 := by positivity
  have hc : δ*((n : ℝ)+1) = 1-δ := by
    dsimp only [δ]
    rw [hdim]
    field_simp
    ring
  have hnz : δ*((n : ℝ)+1) ≠ 0 := mul_ne_zero (one_div_ne_zero hden) (by positivity)
  have he := affineMaximal_flat_tube_euler hΩ hcv hu hp hm a L hD hK hzero bS bE
    q₀ hd J hi hJ C hC e hJb hx₀
  change (∑ j, ∑ i, (B x₀).adjugate i j * dirDeriv (v j) (dirDeriv (v i)
      (flatBaseEulerWeight B R δ)) x₀) + (∑ j, ∑ i, (R x₀).adjugate i j *
      dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x₀) = 0 at he
  have hlog := flat_log_euler_of_weighted hW hB hR
    (fun x hx => (hpos x hx).1.det_pos) (fun x hx => (hpos x hx).2.det_pos) v w hc hnz hxW he
  have ht : ContDiffOn ℝ ∞ t W := fun x hx =>
    (contDiffAt_flatLogAreaRatio (hB x hx) (hR x hx)
      (ne_of_gt (hpos x hx).1.det_pos) (ne_of_gt (hpos x hx).2.det_pos) δ).contDiffWithinAt
  have heB (y : Space n) : B y = -flatBlockHessian φ v y := flatBlockHessian_neg φ v y
  have hBd : (-flatBlockHessian φ v x₀).det ≠ 0 := by
    rw [← heB]; exact ne_of_gt (hpos x₀ hxW).1.det_pos
  change flatInverseTrace (B x₀) v t x₀ - ((n : ℝ)+1)*flatInversePair (B x₀) v t t x₀ +
    flatInverseTrace (R x₀) w t x₀ + flatInversePair (R x₀) w t t x₀ = 0 at hlog
  rw [heB] at hlog
  have hf := flat_f_equation_of_log_euler hW hφ ht hφpos v w hxW hBd
    (ne_of_gt (hpos x₀ hxW).2.det_pos) hlog
  change (Fintype.card κ : ℝ) - Fintype.card ι + φ x₀*flatInverseTrace (-flatBlockHessian φ v x₀) v f x₀ -
      φ x₀*flatInversePair (-flatBlockHessian φ v x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (-flatBlockHessian φ v x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ + 2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0 at hf
  rw [← heB] at hf
  change (n : ℝ) - 2*Fintype.card ι + φ x₀*flatInverseTrace (B x₀) v f x₀ -
      φ x₀*flatInversePair (B x₀) v p p x₀ -
      ((n : ℝ)+1)*φ x₀*flatInversePair (B x₀) v t t x₀ +
      φ x₀*flatInverseTrace (R x₀) w f x₀ + 2*φ x₀*flatInversePair (R x₀) w p f x₀ +
      φ x₀*flatInversePair (R x₀) w f f x₀ = 0
  linarith

end AffineBernstein
end

end OAI
