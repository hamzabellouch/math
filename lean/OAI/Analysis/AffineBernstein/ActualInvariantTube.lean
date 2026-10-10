import Mathlib
import OAI.Analysis.AffineBernstein.FlatTubePositive
import OAI.Analysis.AffineBernstein.TubeInvariantSmooth

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

lemma affineEpigraph_support_radial {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0) (v : E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hh := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  change ContDiffAt ℝ ∞ H (s,e) at hh
  change fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0
  rw [← second_fderiv_prod_right hh]
  exact homogeneousSupport_hessian_radial (hK s hs) ⟨0,interior_subset (hzero s hs)⟩
    (hh.comp e (contDiffAt_const.prodMk contDiffAt_id)) v

/- The invariant angular determinant is strictly positive on every actual
nonzero fiber conormal, independently of the fixed orthonormal frame. -/
omit [DecidableEq ι] in
theorem affineEpigraph_invariant_tube_positive {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    (tubeBaseMatrix H (s,e) bS).PosDef ∧ 0 < tubeAngularDensity H (s,e) bE ∧ 0 < H (s,e) := by
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hn : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hunit : ‖‖e‖⁻¹ • e‖ = 1 := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  obtain ⟨c,hc⟩ := exists_orthonormalBasis_last bE hunit
  have hinner : inner ℝ e (c (Sum.inr ())) ≠ 0 := by
    rw [hc,real_inner_smul_right]
    exact mul_ne_zero (inv_ne_zero hn.ne') (real_inner_self_pos.mpr he).ne'
  have hpos := affineEpigraph_flat_tube_positive hΩ hcv hu hp a L hD hK hzero hs bS c hinner
  have hh := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  change ContDiffAt ℝ ∞ H (s,e) at hh
  refine ⟨hpos.1,?_,?_⟩
  · rw [← tubeAngularDensity_basis_independent H (s,e) bE c]
    rw [tubeAngularDensity_of_last_null hh c]
    · exact hpos.2.det_pos
    · intro v
      have hr := affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hs he v
      change fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 at hr
      rw [hc]
      have heq : ((0:S),‖e‖⁻¹ • e) = ‖e‖⁻¹ • ((0:S),e) := by simp
      rw [heq,map_smul,hr,smul_zero]
  · apply supportValue_pos (hK s hs) (hzero s hs)
    intro hz
    apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)

lemma affineEpigraph_invariant_f_smooth {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ContDiffAt ℝ ∞ (invariantTubeF H bS bE δ) (s,e) := by
  have hp' := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he bS bE
  exact contDiffAt_invariantTubeF (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
    bS bE δ hp'.1.det_pos.ne' hp'.2.1.ne' hp'.2.2.ne' he

lemma affineEpigraph_invariant_f_homogeneous {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {c : ℝ} (hc : 0 < c) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    invariantTubeF H bS bE δ (s,c • e) = invariantTubeF H bS bE δ (s,e) := by
  have hce : c • e ≠ 0 := smul_ne_zero hc.ne' he
  have hp' := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he bS bE
  exact invariantTubeF_smul hD hs hK (fun s hs => ⟨0,interior_subset (hzero s hs)⟩) hc
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hce).1 bS bE
    hp'.1.det_pos.ne' hp'.2.1.ne' hp'.2.2.ne' he

lemma affineEpigraph_invariant_f_radial {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    fderiv ℝ (invariantTubeF H bS bE δ) (s,e) (0,e) = 0 := by
  apply zeroHomogeneous_fderiv_radial
  · exact (affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hs he bS bE _).differentiableAt (by simp)
  · exact fun c hc => affineEpigraph_invariant_f_homogeneous hΩ hcv hu hp a L hD hK hzero hs he bS bE hc

end AffineBernstein
end

end OAI
