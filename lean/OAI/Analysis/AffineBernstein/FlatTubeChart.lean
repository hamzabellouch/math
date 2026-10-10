import Mathlib
import OAI.Analysis.AffineBernstein.ActualFlatWeakEuler
import OAI.Analysis.AffineBernstein.FlatTubeEuler
import OAI.Analysis.AffineBernstein.FlatTestHessian

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section FlatTubeChart
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype κ]

lemma tubeBaseMatrix_eq_flatBlockHessian {n : ℕ} {H : S × E → ℝ}
    (q₀ : S × E) (J : Space n →L[ℝ] S × E) {x : Space n}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x))
    (bS : Module.Basis ι ℝ S) (v : ι → Space n) (hv : ∀ i, J (v i) = (bS i,0)) :
    tubeBaseMatrix H (q₀+J x) bS =
      flatBlockHessian (fun y => -H (q₀+J y)) v x := by
  rw [flatBlockHessian_neg]
  ext i j
  change -fderiv ℝ (fderiv ℝ H) (q₀+J x) (bS i,0) (bS j,0) =
    -dirDeriv (v i) (dirDeriv (v j) (fun y => H (q₀+J y))) x
  rw [dirDeriv_eq_second (f := fun y => H (q₀+J y))
    (hH.comp x (contDiffAt_const.add J.contDiff.contDiffAt)),
    second_fderiv_affine_comp J q₀ hH,hv,hv]

lemma tubeRadiusMatrix_eq_flatBlockHessian {n : ℕ} {H : S × E → ℝ}
    (q₀ : S × E) (J : Space n →L[ℝ] S × E) {x : Space n}
    (hH : ContDiffAt ℝ ∞ H (q₀+J x))
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (w : κ → Space n)
    (hw : ∀ i, J (w i) = (0,bE (Sum.inl i))) :
    tubeRadiusMatrix H (q₀+J x) bE =
      flatBlockHessian (fun y => H (q₀+J y)) w x := by
  ext i j
  change fderiv ℝ (fderiv ℝ H) (q₀+J x) (0,bE (Sum.inl i)) (0,bE (Sum.inl j)) =
    dirDeriv (w i) (dirDeriv (w j) (fun y => H (q₀+J y))) x
  rw [dirDeriv_eq_second (f := fun y => H (q₀+J y))
    (hH.comp x (contDiffAt_const.add J.contDiff.contDiffAt)),
    second_fderiv_affine_comp J q₀ hH,hw,hw]

end FlatTubeChart

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The pointwise flat-normal tube Euler equation, derived from the original
PDE by actual support variations and two compact integrations by parts. -/
theorem affineMaximal_flat_tube_euler {n : ℕ} {Ω : Set (Space n)}
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
    (∑ j, ∑ i, (B x₀).adjugate i j * dirDeriv (v j) (dirDeriv (v i) (flatBaseEulerWeight B R δ)) x₀) +
      (∑ j, ∑ i, (R x₀).adjugate i j * dirDeriv (w j) (dirDeriv (w i) (flatAngularEulerWeight B R δ)) x₀) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let φ := fun x => H (q₀+J x)
  let v := fun i : ι => coordinateVector n (e.symm (Sum.inl i))
  let w := fun i : κ => coordinateVector n (e.symm (Sum.inr i))
  let B := fun y => flatBlockHessian (fun z => -φ z) v y
  let R := fun y => flatBlockHessian φ w y
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let ℓ := InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))
  have hℓ : ℓ q₀.2 = 1 := by simpa [ℓ,real_inner_comm] using hd
  have hℓJ (x : Space n) : ℓ (J x).2 = 0 := by simpa [ℓ,real_inner_comm] using hJ x
  have hv (i : ι) : J (v i) = (bS i,0) := by simp [v,hJb,tubeTangent]
  have hw (i : κ) : J (w i) = (0,bE (Sum.inl i)) := by simp [w,hJb,tubeTangent]
  obtain ⟨W,hW,hxW,hWD,hstat⟩ := affineMaximal_flat_tube_weak_euler hΩ hcv hu hp hm
    a L hD hK hzero bS bE q₀ hd J hi hJ C hC e hJb hx₀
  have hq (x : Space n) : inner ℝ (q₀+J x).2 (bE (Sum.inr ())) = 1 := by
    simp [inner_add_left,hd,hJ]
  have hne (x : Space n) : (q₀+J x).2 ≠ 0 := by
    intro hz
    simpa [hz] using hq x
  have hH (x : Space n) (hx : x ∈ W) : ContDiffAt ℝ ∞ H (q₀+J x) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero (hWD hx) (hne x)).1
  have hφ : ContDiffOn ℝ ∞ φ W := fun x hx =>
    ((hH x hx).comp x (contDiffAt_const.add J.contDiff.contDiffAt)).contDiffWithinAt
  have hBe (x : Space n) (hx : x ∈ W) : tubeBaseMatrix H (q₀+J x) bS = B x :=
    tubeBaseMatrix_eq_flatBlockHessian q₀ J (hH x hx) bS v hv
  have hRe (x : Space n) (hx : x ∈ W) : tubeRadiusMatrix H (q₀+J x) bE = R x :=
    tubeRadiusMatrix_eq_flatBlockHessian q₀ J (hH x hx) bE w hw
  have hpos (x : Space n) (hx : x ∈ W) : (B x).PosDef ∧ (R x).PosDef := by
    have hh := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero (hWD hx)
      (e := (q₀+J x).2) bS bE (by rw [hq x]; norm_num)
    change (tubeBaseMatrix H (q₀+J x) bS).PosDef ∧
      (tubeRadiusMatrix H (q₀+J x) bE).PosDef at hh
    rwa [hBe x hx,hRe x hx] at hh
  apply flatTubeEuler_of_stationary (μ := volume) hW φ v w δ hφ
    (fun x hx => (hpos x hx).1) (fun x hx => (hpos x hx).2) ?_ hxW
  intro η hη hc hs
  have hweak := hstat (tsupport η) hc.isCompact hs η hη Subset.rfl
  have hGBe (x : Space n) : tubeBaseMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bS =
      -flatBlockHessian η v x := by
    ext i j
    rw [flatSupportVariation_baseMatrix ℓ q₀ C J hℓ hℓJ hC hη bS bE e hJb]
    rfl
  have hGRe (x : Space n) : tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE =
      flatBlockHessian η w x := by
    ext i j
    rw [flatSupportVariation_radiusMatrix ℓ q₀ C J hℓ hℓJ hC hη bS bE e hJb]
    rfl
  have heq := setIntegral_congr_fun (μ := volume) hc.isCompact.measurableSet
    (fun x (hx : x ∈ tsupport η) =>
      congrArg₂ (fun l r => tubeAreaFirstVariation l (-flatBlockHessian η v x) r
        (flatBlockHessian η w x) δ) (hBe x (hs hx)) (hRe x (hs hx)))
  change (∫ x in tsupport η, tubeAreaFirstVariation (tubeBaseMatrix H (q₀+J x) bS)
    (tubeBaseMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bS)
    (tubeRadiusMatrix H (q₀+J x) bE)
    (tubeRadiusMatrix (flatSupportVariation ℓ q₀ C η) (q₀+J x) bE) δ) = 0 at hweak
  simp_rw [hGBe,hGRe] at hweak
  rw [heq] at hweak
  rw [← hweak]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz (l m : Space n) : dirDeriv l (dirDeriv m η) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun ht => hx ((tsupport_fderiv_apply_subset ℝ m) ((tsupport_fderiv_apply_subset ℝ l) ht))
  simp [tubeAreaFirstVariation,flatBlockHessian,hz]

end AffineBernstein
end

end OAI
