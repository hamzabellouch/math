import Mathlib
import OAI.Analysis.AffineBernstein.CapGeometry
import OAI.Analysis.AffineBernstein.UniformSphericalCap

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise
open Filter
open scoped Topology
open Filter
open scoped Topology

section CompletePositiveCap

lemma sourceEpigraph_convex {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef) :
    Convex ℝ (sourceEpigraph Ω u) :=
  (convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)).convex_epigraph

lemma sourceEpigraph_closed {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hc : EuclideanGraphComplete Ω u) : IsClosed (sourceEpigraph Ω u) :=
  isClosed_epigraph_of_complete hΩ hne hu
    (convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)) hc

end CompletePositiveCap

section AffineCapGeometry
open Metric

lemma sourceEpigraph_vertical_ray {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {z : Space n × ℝ} (hz : z ∈ sourceEpigraph Ω u) {t : ℝ} (ht : 0 ≤ t) :
    z+t • ((0 : Space n),1) ∈ sourceEpigraph Ω u := by
  change z.1+ t • (0 : Space n) ∈ Ω ∧ u (z.1+t • (0 : Space n)) ≤ z.2+t*1
  have hz' : u z.1 ≤ z.2 := hz.2
  simpa using And.intro hz.1 (by linarith : u z.1 ≤ z.2+t)

end AffineCapGeometry
open Metric
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma affineEpigraphPullback_eq_image {n : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) :
    affineEpigraphPullback Ω u a L = (fun p => L.symm (p-a)) '' sourceEpigraph Ω u := by
  ext p
  constructor
  · intro hp
    refine ⟨a+L p,hp,?_⟩
    simp
  · rintro ⟨q,hq,rfl⟩
    simpa [affineEpigraphPullback,sourceEpigraph] using hq

lemma affineEpigraphPullback_isClosed {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : IsClosed (sourceEpigraph Ω u)) (a : Space n × ℝ)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : IsClosed (affineEpigraphPullback Ω u a L) :=
  hc.preimage (continuous_const.add L.continuous)

/-- A bounded literal epigraph cap forces its pulled vertical direction to have positive height.
The cap center need only lie strictly below its top, so no global growth hypothesis is inserted. -/
lemma affineEpigraphPullback_cap_vertical_pos {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ)
    {b R : ℝ} (hR : 0 ≤ R)
    (hcap : ∀ p ∈ affineEpigraphPullback Ω u a L, ℓ p.1 ≤ b → ‖p‖ ≤ R)
    {o : S × E} (ho : o ∈ affineEpigraphPullback Ω u a L) (hob : ℓ o.1 < b) :
    0 < ℓ (L.symm ((0:Space n),(1:ℝ))).1 := by
  let q : S × E := L.symm ((0:Space n),(1:ℝ))
  have hq : q ≠ 0 := by
    intro hz
    have hh := L.symm.injective (hz.trans (map_zero _).symm)
    have := congrArg Prod.snd hh
    norm_num at this
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let e : S × E := ‖q‖⁻¹ • q
  have he : ‖e‖ = 1 := by
    simp [e,norm_smul,hn.ne']
  have hrec (t : ℝ) (ht : 0 ≤ t) : o+t • e ∈ affineEpigraphPullback Ω u a L := by
    have hpt : a+L (o+t • e) = a+L o+(t*‖q‖⁻¹) • ((0:Space n),(1:ℝ)) := by
      simp [e,q,map_add,map_smul,smul_smul,add_assoc]
    change a+L (o+t • e) ∈ sourceEpigraph Ω u
    rw [hpt]
    exact sourceEpigraph_vertical_ray ho (mul_nonneg ht (inv_nonneg.mpr hn.le))
  have h := cap_recession_component_lower
    (ℓ.comp (ContinuousLinearMap.fst ℝ S E)) hR (sub_pos.mpr hob) hcap ho
    (by dsimp; linarith) he hrec
  have hp : 0 < ℓ e.1 := (div_pos (sub_pos.mpr hob) (by linarith : 0 < 2*R+1)).trans h
  change 0 < ℓ q.1
  have heq : ℓ e.1 = ‖q‖⁻¹ * ℓ q.1 := by simp [e]
  rw [heq] at hp
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hp

variable [FiniteDimensional ℝ S] [FiniteDimensional ℝ E]

/-- Actual compact original-graph cap data, derived from an ambient cap and its inner point.
The lower height bound is explicit and uniform in the affine normalization. -/
lemma affineEpigraphPullback_graph_cap_data {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : IsClosed (sourceEpigraph Ω u))
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ)
    {b R : ℝ} (hR : 0 ≤ R)
    (hcap : ∀ p ∈ affineEpigraphPullback Ω u a L, ℓ p.1 ≤ b → ‖p‖ ≤ R)
    {o : S × E} (ho : o ∈ affineEpigraphPullback Ω u a L) (hob : ℓ o.1 < b) :
    ∃ K : Set (Space n), IsCompact K ∧ K ⊆ Ω ∧
      (∀ x ∈ Ω, x ∉ K → b ≤ pulledBaseGraphFunction u a L ℓ x) ∧
      (∀ x ∈ K, pulledBaseGraphFunction u a L ℓ x ∈ Icc (-‖ℓ‖*R) b) ∧
      (∀ x ∈ K, ‖L.symm ((x,u x)-a)‖ ≤ R) := by
  let C := affineEpigraphPullback Ω u a L
  let T := C ∩ {p | ℓ p.1 ≤ b}
  have hcC : IsClosed C := affineEpigraphPullback_isClosed hc a L
  have hcT : IsCompact T :=
    isCompact_iff_isClosed_bounded.mpr ⟨
      hcC.inter (isClosed_le (ℓ.continuous.comp continuous_fst) continuous_const),
      (Metric.isBounded_closedBall (x := (0:S × E)) (r := R)).subset (by
        intro p hp
        exact mem_closedBall_zero_iff.mpr (hcap p hp.1 hp.2))⟩
  let V := fun p : S × E => (a+L p).1
  let K := V '' T
  have hK : IsCompact K := hcT.image (continuous_const.add L.continuous).fst
  have hv := affineEpigraphPullback_cap_vertical_pos a L ℓ hR hcap ho hob
  have hgraph (p : S × E) (hp : p ∈ T) :
      L.symm (((a+L p).1,u (a+L p).1)-a) ∈ T := by
    let t := (a+L p).2-u (a+L p).1
    have ht : 0 ≤ t := sub_nonneg.mpr hp.1.2
    have he : L.symm (((a+L p).1,u (a+L p).1)-a) =
        p-t • L.symm ((0:Space n),(1:ℝ)) := by
      apply L.injective
      simp only [L.apply_symm_apply,map_sub,map_smul]
      dsimp [t]
      ext <;> simp
      ring
    refine ⟨?_,?_⟩
    · change a+L (L.symm (((a+L p).1,u (a+L p).1)-a)) ∈ sourceEpigraph Ω u
      simpa [sourceEpigraph] using And.intro hp.1.1 (le_refl (u (a+L p).1))
    · rw [he]
      change ℓ (p.1-t • (L.symm ((0:Space n),(1:ℝ))).1) ≤ b
      rw [map_sub,map_smul,smul_eq_mul]
      exact (sub_le_self _ (mul_nonneg ht hv.le)).trans hp.2
  refine ⟨K,hK,?_,?_,?_,?_⟩
  · rintro x ⟨p,hp,rfl⟩
    exact hp.1.1
  · intro x hx hxK
    by_contra hnot
    have hxb : pulledBaseGraphFunction u a L ℓ x ≤ b := (not_le.mp hnot).le
    have hp : L.symm ((x,u x)-a) ∈ T := by
      refine ⟨?_,hxb⟩
      change a+L (L.symm ((x,u x)-a)) ∈ sourceEpigraph Ω u
      simpa [sourceEpigraph] using And.intro hx (le_refl (u x))
    apply hxK
    refine ⟨L.symm ((x,u x)-a),hp,?_⟩
    simp [V]
  · rintro x ⟨p,hp,rfl⟩
    have hh := hgraph p hp
    refine ⟨?_,hh.2⟩
    have hn : ‖L.symm ((V p,u (V p))-a)‖ ≤ R := hcap _ hh.1 hh.2
    have ha : |pulledBaseGraphFunction u a L ℓ (V p)| ≤ ‖ℓ‖*R := by
      change ‖ℓ (L.symm ((V p,u (V p))-a)).1‖ ≤ ‖ℓ‖*R
      exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((norm_fst_le _).trans hn) (norm_nonneg ℓ))
    linarith [neg_abs_le (pulledBaseGraphFunction u a L ℓ (V p))]
  · rintro x ⟨p,hp,rfl⟩
    exact hcap _ (hgraph p hp).1 (hgraph p hp).2

omit [FiniteDimensional ℝ S] in
/-- A cap containing a base fiber gives compactness of that actual fiber. -/
lemma affineEpigraphPullback_fiber_isCompact {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hc : IsClosed (sourceEpigraph Ω u))
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ)
    {b R : ℝ}
    (hcap : ∀ p ∈ affineEpigraphPullback Ω u a L, ℓ p.1 ≤ b → ‖p‖ ≤ R)
    {s : S} (hs : ℓ s ≤ b) : IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L} := by
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨(affineEpigraphPullback_isClosed hc a L).preimage
    (continuous_const.prodMk continuous_id),?_⟩
  apply (Metric.isBounded_closedBall (x := (0:E)) (r := R)).subset
  intro y hy
  exact mem_closedBall_zero_iff.mpr ((norm_snd_le (s,y)).trans (hcap (s,y) hy hs))

end AffineBernstein
end

end OAI
