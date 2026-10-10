import Mathlib
import OAI.Probability.SKGap.Localization.TapPotential

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real Matrix Set Filter Function
open scoped Topology
namespace SKGap
section Basins
variable {X : Type*} [TopologicalSpace X] (T : X → X)

lemma attractionBasin_eq_iUnion {p : X} {U : Set X} (hU : IsOpen U) (hp : p ∈ U)
    (hatt : U ⊆ attractionBasin T p) :
    attractionBasin T p = ⋃ k : ℕ, (T^[k]) ⁻¹' U := by
  ext x
  constructor
  · intro hx
    have h := hx.eventually (hU.mem_nhds hp)
    obtain ⟨k, hk⟩ := h.exists
    exact mem_iUnion.mpr ⟨k, hk⟩
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact (mem_attractionBasin_iterate_iff T p x k).mp (hatt hk)

lemma isOpen_attractionBasin (hT : Continuous T) {p : X} {U : Set X}
    (hU : IsOpen U) (hp : p ∈ U) (hatt : U ⊆ attractionBasin T p) :
    IsOpen (attractionBasin T p) := by
  rw [attractionBasin_eq_iUnion T hU hp hatt]
  exact isOpen_iUnion (fun k => hU.preimage (hT.iterate k))

lemma disjoint_attractionBasins [T2Space X] {p q : X} (hpq : p ≠ q) :
    Disjoint (attractionBasin T p) (attractionBasin T q) := by
  rw [disjoint_left]
  intro x hx hy
  exact hpq (tendsto_nhds_unique hx hy)

end Basins

theorem lyapunov_unique_fixed_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [ConnectedSpace X] [T2Space X]
    (T : X → X) (hT : Continuous T) (φ : X → ℝ) (hφ : Continuous φ)
    (hstrict : ∀ x, T x ≠ x → φ (T x) < φ x)
    (hattract : ∀ p, T p = p → ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      U ⊆ attractionBasin T p) : ∃! p, T p = p := by
  have hopen (p) (hp : T p = p) : IsOpen (attractionBasin T p) := by
    obtain ⟨U, hU, hpU, hatt⟩ := hattract p hp
    exact isOpen_attractionBasin T hT hU hpU hatt
  have hcover (x : X) : ∃ p, T p = p ∧ x ∈ attractionBasin T p := by
    let U := ⋃ p : {p // T p = p}, attractionBasin T p.val
    have hU : IsOpen U := isOpen_iUnion (fun p => hopen p.val p.property)
    have hfixed (p) (hp : T p = p) : p ∈ U :=
      mem_iUnion.mpr ⟨⟨p, hp⟩, fixed_mem_attractionBasin T hp⟩
    obtain ⟨k, hk⟩ := lyapunov_eventually_hits T hT φ hφ hstrict hU hfixed x
    obtain ⟨p, hp⟩ := mem_iUnion.mp hk
    exact ⟨p.val, p.property, (mem_attractionBasin_iterate_iff T p.val x k).mp hp⟩
  obtain ⟨p, hp⟩ := lyapunov_fixed_point T φ hφ hstrict
  refine ⟨p, hp, fun q hq => ?_⟩
  by_contra hqp
  let V := ⋃ q : {q // T q = q ∧ q ≠ p}, attractionBasin T q.val
  have hV : IsOpen V := isOpen_iUnion (fun q => hopen q.val q.property.1)
  have hdisj : Disjoint (attractionBasin T p) V := by
    rw [disjoint_iUnion_right]
    intro q
    exact disjoint_attractionBasins T q.property.2.symm
  have hcov : (univ : Set X) ⊆ attractionBasin T p ∪ V := by
    intro x _
    obtain ⟨r, hr, hx⟩ := hcover x
    by_cases he : r = p
    · subst r
      exact Or.inl hx
    · exact Or.inr (mem_iUnion.mpr ⟨⟨r, hr, he⟩, hx⟩)
  have hconn := IsPreconnected.subset_or_subset (hopen p hp) hV hdisj hcov
    isPreconnected_univ
  rcases hconn with hconn | hconn
  · have hqp' := tendsto_nhds_unique (hconn (mem_univ q))
      (fixed_mem_attractionBasin T hq)
    exact hqp hqp'.symm
  · exact disjoint_left.mp hdisj (fixed_mem_attractionBasin T hp) (hconn (mem_univ p))

theorem local_contraction_attracts {X : Type*} [MetricSpace X]
    {T : X → X} {p : X} (hp : T p = p) {K : NNReal} (hK : K < 1)
    {U : Set X} (hU : U ∈ 𝓝 p) (hlip : LipschitzOnWith K T U) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ attractionBasin T p := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hpU : p ∈ U := hball (Metric.mem_ball_self hε)
  have hmaps : MapsTo T (Metric.ball p ε) (Metric.ball p ε) := by
    intro x hx
    have h := hlip.dist_le_mul x (hball hx) p hpU
    rw [hp] at h
    exact h.trans_lt ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dist x p)
      (show (K:ℝ) ≤ 1 by exact_mod_cast hK.le)).trans_lt hx)
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  intro x hx
  have hbd (n : ℕ) : dist (T^[n] x) p ≤ (K:ℝ)^n * dist x p := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      have h := hlip.dist_le_mul (T^[n] x) (hball (hmaps.iterate n hx)) p hpU
      rw [hp] at h
      exact h.trans (by simpa only [pow_succ', mul_assoc] using
        mul_le_mul_of_nonneg_left ih K.coe_nonneg)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg
    (show (K:ℝ) < 1 by exact_mod_cast hK)).mul_const (dist x p)
  rw [zero_mul] at ht
  exact Metric.tendsto_atTop.mpr (fun δ hδ => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
    exact ⟨N, fun n hn => (hbd n).trans_lt (hN n hn)⟩)

theorem strict_derivative_attracts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E → E} {p : E} {D : E →L[ℝ] E}
    (hp : T p = p) (hD : HasStrictFDerivAt T D p) (hnorm : ‖D‖ < 1) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧ U ⊆ attractionBasin T p := by
  have hn : ‖D‖₊ < 1 := by exact_mod_cast hnorm
  obtain ⟨K, hDK, hK⟩ := exists_between hn
  obtain ⟨U, hU, hlip⟩ := hD.exists_lipschitzOnWith_of_nnnorm_lt K hDK
  exact local_contraction_attracts hp hK hU hlip

end SKGap

noncomputable section
open Set Function Real
open scoped Topology NNReal
namespace SKGap
section GradientDescent
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lipschitz_gradient_remainder {φ : E → ℝ} {G : E → E} {s : Set E}
    (hs : Convex ℝ s) (hgrad : ∀ x ∈ s, HasFDerivAt φ (innerSL ℝ (G x)) x)
    {L : ℝ≥0} (hG : LipschitzOnWith L G s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    |φ y - φ x - inner ℝ (G x) (y-x)| ≤ (L:ℝ)*‖y-x‖^2 := by
  let d := y-x
  let ℓ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let f := fun t : ℝ => φ (ℓ t) - t * inner ℝ (G x) d
  let f' := fun t : ℝ => inner ℝ (G (ℓ t) - G x) d
  have hℓ (t : ℝ) : ℓ t = x + t • d := by
    simp only [ℓ, d, AffineMap.lineMap_apply_module]
    module
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ℓ t ∈ s :=
    hs.mapsTo_lineMap hx hy ht
  have hf (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt f (f' t) (Icc (0:ℝ) 1) t := by
    have hd := ((hgrad (ℓ t) (hmem t ht)).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (G x) d))
    convert! (hd.hasDerivWithinAt (s := Icc (0:ℝ) 1)) using 1
    simp only [f', innerSL_apply_apply, inner_sub_left, d, one_mul]
  have hb (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      ‖f' t‖ ≤ (L:ℝ)*‖d‖^2 := by
    have hdiff : ‖ℓ t-x‖ ≤ ‖d‖ := by
      rw [hℓ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
    have h := (hG.norm_sub_le (hmem t ⟨ht.1, ht.2.le⟩) hx).trans
      (mul_le_mul_of_nonneg_left hdiff L.coe_nonneg)
    calc
      ‖f' t‖ ≤ ‖G (ℓ t)-G x‖*‖d‖ := norm_inner_le_norm _ _
      _ ≤ ((L:ℝ)*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right h (norm_nonneg d)
      _ = _ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hf hb
  simpa only [f, ℓ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    zero_mul, sub_zero, one_mul, Real.norm_eq_abs, d, sub_right_comm] using h

theorem gradient_step_strict_descent {φ : E → ℝ} {G : E → E} {s : Set E}
    (hs : Convex ℝ s) (hgrad : ∀ x ∈ s, HasFDerivAt φ (innerSL ℝ (G x)) x)
    {L : ℝ≥0} (hG : LipschitzOnWith L G s) {ε : ℝ} (hε : 0 < ε)
    (hsmall : (L:ℝ)*ε < 1) {x : E} (hx : x ∈ s) (hstep : x-ε • G x ∈ s)
    (hGx : G x ≠ 0) : φ (x-ε • G x) < φ x := by
  have h := (le_abs_self _).trans (lipschitz_gradient_remainder hs hgrad hG hx hstep)
  have he : x-ε • G x-x = -ε • G x := by module
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos hε)] at h
  have hn : 0 < ‖G x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hGx)
  have hc : 0 < ε*(1-(L:ℝ)*ε)*‖G x‖^2 := by positivity
  nlinarith only [h, hc]

theorem gradient_step_derivative_sq_bound {D : E →L[ℝ] E} {c M ε : ℝ}
    (_hc : 0 ≤ c) (_hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hcoercive : ∀ v, c*‖v‖^2 ≤ inner ℝ v (D v)) (hbound : ‖D‖ ≤ M)
    (v : E) :
    ‖v-ε • D v‖^2 ≤ (1-2*ε*c+ε^2*M^2)*‖v‖^2 := by
  have hD : ‖D v‖ ≤ M*‖v‖ := D.le_of_opNorm_le hbound v
  have hD2 : ‖D v‖^2 ≤ M^2*‖v‖^2 := by
    nlinarith [norm_nonneg (D v), mul_nonneg _hM (norm_nonneg v)]
  have h := mul_le_mul_of_nonneg_left (hcoercive v) (show 0 ≤ 2*ε by positivity)
  have h' := mul_le_mul_of_nonneg_left hD2 (sq_nonneg ε)
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hε]
  nlinarith only [h, h']

end GradientDescent
end SKGap

end
end
end

end OAI
