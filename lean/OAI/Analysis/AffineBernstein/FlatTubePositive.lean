import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma positive_bilinear_transverse (A : E →L[ℝ] E →L[ℝ] ℝ) (e d : E)
    (hs : ∀ v w, A v w = A w v) (he : e ≠ 0) (hed : inner ℝ e d ≠ 0)
    (hr : ∀ v, A v e = 0)
    (hp : ∀ v, v ≠ 0 → inner ℝ e v = 0 → 0 < A v v)
    {v : E} (hv : v ≠ 0) (hvd : inner ℝ v d = 0) : 0 < A v v := by
  let c := inner ℝ e v / inner ℝ e e
  let w := v-c • e
  have hee : inner ℝ e e ≠ 0 := fun hh => he (inner_self_eq_zero.mp hh)
  have hew : inner ℝ e w = 0 := by
    simp only [w,c,inner_sub_right,inner_smul_right,div_mul_cancel₀ _ hee,sub_self]
  have hw : w ≠ 0 := by
    intro hw0
    have hvce : v = c • e := sub_eq_zero.mp hw0
    have hc : c = 0 := by
      rw [hvce,real_inner_smul_left] at hvd
      exact (mul_eq_zero.mp hvd).resolve_right hed
    exact hv (by simp [hvce,hc])
  have heq : A w w = A v v := by
    simp [w,map_sub,map_smul,hr,hs e v]
  exact heq ▸ hp w hw hew

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace S] [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma flat_tubeRadiusMatrix_posDef {H : S × E → ℝ} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hpos : ∀ v : E, v ≠ 0 → inner ℝ v (bE (Sum.inr ())) = 0 →
      0 < fderiv ℝ (fderiv ℝ H) x (0,v) (0,v)) :
    (tubeRadiusMatrix H x bE).PosDef := by
  have hb : LinearIndependent ℝ (fun i : κ => ((0:S),bE (Sum.inl i))) :=
    (bE.toBasis.linearIndependent.comp _ Sum.inl_injective).map'
      (ContinuousLinearMap.inr ℝ S E).toLinearMap (by
        apply LinearMap.ker_eq_bot.mpr
        intro x y h; exact congrArg Prod.snd h)
  have hs := hH.isSymmSndFDerivAt (by simp)
  apply bilinear_matrix_posDef (fderiv ℝ (fderiv ℝ H) x) _ hb hs.eq
  intro z hz
  have heq : (∑ i, z i • ((0:S),bE (Sum.inl i))) = (0,(∑ i, z i • bE (Sum.inl i))) := by
    apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum]
  rw [heq] at hz ⊢
  apply hpos _ (by simpa using hz)
  simp [sum_inner,real_inner_smul_left,bE.inner_eq_ite]

/- Positivity of the flat-normal-chart Hessian blocks follows from the actual
strictly convex affine epigraph, not from a surrogate support-function class. -/
omit [DecidableEq ι] in
theorem affineEpigraph_flat_tube_positive {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (he : inner ℝ e (bE (Sum.inr ())) ≠ 0) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    (tubeBaseMatrix H (s,e) bS).PosDef ∧ (tubeRadiusMatrix H (s,e) bE).PosDef := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hen : e ≠ 0 := fun hh => he (by simp [hh])
  have hj := affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hs hen
  have hH : ContDiffAt ℝ ∞ H (s,e) := hj.1
  have hf : ContDiffAt ℝ ∞ (fun y : E => H (s,y)) e := hH.comp e (contDiffAt_const.prodMk contDiffAt_id)
  have hsym := hf.isSymmSndFDerivAt (by simp)
  refine ⟨tubeBaseMatrix_posDef hH bS ?_,flat_tubeRadiusMatrix_posDef hH bE ?_⟩
  · intro v hv
    rw [← second_fderiv_prod_left hH]
    exact affineEpigraph_base_hessian_negative hΩ hcv hu hp a L hB hK hzero hs hen hv
  · intro v hv ht
    rw [← second_fderiv_prod_right hH]
    apply positive_bilinear_transverse _ e (bE (Sum.inr ())) hsym.eq hen he _ _ hv ht
    · intro w
      exact homogeneousSupport_hessian_radial (hK s hs) ⟨0,interior_subset (hzero s hs)⟩ hf w
    · intro w hw hwe
      have hr := affineEpigraph_radius_positive hΩ hcv hu hp a L hB hK hzero hs hen hw hwe
      rw [sphereRadius_eq_hessian hf _ _ hwe] at hr
      exact hr

end AffineBernstein
end

end OAI
