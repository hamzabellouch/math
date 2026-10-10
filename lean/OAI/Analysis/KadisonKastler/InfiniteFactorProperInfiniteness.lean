import OAI.Analysis.KadisonKastler.PublishedInfiniteType
import OAI.Analysis.KadisonKastler.CountableProjectionFamilies
import Mathlib.Topology.Bases

namespace OAI

/-! # An infinite factor is properly infinite

A proper isometry supplies an infinite orthogonal sequence of equivalent
wandering projections.  A maximal orthogonal family of partial isometries
with sources under the first wandering projection covers the identity by
factoriality.  Separability makes this family countable, so its ranges can
be mapped into the even and odd wandering projections separately.

No trace, dimension function, or published projection comparison is used.
-/

namespace KadisonKastler

open Generator.Tracial
open scoped BigOperators Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private def projectionComplement (p : AlgebraProjection M) : AlgebraProjection M :=
  ⟨1 - p.val, p.property.one_sub⟩

private theorem le_projectionComplement {p q : AlgebraProjection M}
    (h : q.val * p.val = 0) : p ≤ projectionComplement q := by
  change (1 - q.val) * p.val = p.val
  rw [sub_mul, one_mul, h, sub_zero]

private theorem mul_eq_zero_of_le_complement {p q : AlgebraProjection M}
    (h : p ≤ projectionComplement q) : q.val * p.val = 0 := by
  change (1 - q.val) * p.val = p.val at h
  rw [sub_mul, one_mul] at h
  exact sub_eq_self.mp h

private theorem projection_fixed_vectors_orthogonal (p q : AlgebraProjection M)
    (hpq : p.val * q.val = 0) (x y : H)
    (hx : (p.val : H →L[ℂ] H) x = x) (hy : (q.val : H →L[ℂ] H) y = y) :
    inner ℂ x y = 0 := by
  have hstar : star (p.val : H →L[ℂ] H) = (p.val : H →L[ℂ] H) :=
    congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  calc
    inner ℂ x y = inner ℂ ((p.val : H →L[ℂ] H) x)
        ((q.val : H →L[ℂ] H) y) := by rw [hx, hy]
    _ = inner ℂ x ((p.val : H →L[ℂ] H) ((q.val : H →L[ℂ] H) y)) := by
      conv_lhs => rw [← hstar]
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    _ = 0 := by
      have hz := congrArg (fun a : Algebra M => (a : H →L[ℂ] H) y) hpq
      change (p.val : H →L[ℂ] H) ((q.val : H →L[ℂ] H) y) = 0 at hz
      rw [hz, inner_zero_right]

/-- A nonzero projection has a unit vector in its range. -/
private theorem projection_unit_vector (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ x : H, ‖x‖ = 1 ∧ (p.val : H →L[ℂ] H) x = x := by
  have hn : (p.val : H →L[ℂ] H) ≠ 0 := fun h => hp (Subtype.ext h)
  obtain ⟨x, hx⟩ : ∃ x : H, (p.val : H →L[ℂ] H) x ≠ 0 := by
    by_contra h
    apply hn
    ext x
    simpa using (not_exists.mp h x)
  let y := (p.val : H →L[ℂ] H) x
  have hy : y ≠ 0 := hx
  have hnorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  refine ⟨((‖y‖ : ℂ)⁻¹) • y, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y), inv_mul_cancel₀ hnorm]
  · rw [map_smul]
    congr 1
    change (p.val : H →L[ℂ] H) ((p.val : H →L[ℂ] H) x) =
      (p.val : H →L[ℂ] H) x
    exact congrArg (fun a : Algebra M => (a : H →L[ℂ] H) x)
      p.property.isIdempotentElem.eq

/-- Pairwise orthogonal nonzero projections in a separably acting algebra
form a countable family. -/
theorem countable_of_orthogonal_nonzero_projections [TopologicalSpace.SeparableSpace H]
    {ι : Type*} (p : ι → AlgebraProjection M)
    (hp : ∀ i, (p i).val ≠ 0)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) : Countable ι := by
  choose x hnorm hfix using fun i => projection_unit_vector (p i) (hp i)
  apply Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (x i) (1 / 2 : ℝ))
  · intro i j hij
    apply Metric.ball_disjoint_ball
    have hi := projection_fixed_vectors_orthogonal (p i) (p j) (ho hij)
      (x i) (x j) (hfix i) (hfix j)
    have he := @norm_sub_mul_self ℂ H _ _ _ (x i) (x j)
    simp only [hi, map_zero, hnorm] at he
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (x i - x j)]
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨x i, Metric.mem_ball_self (by norm_num)⟩

private def sourceFamily (p : AlgebraProjection M)
    (s : Set (PartialIsometry M)) : Prop :=
  (∀ v ∈ s, v.support ≤ p ∧ v.support.val ≠ 0) ∧
    s.Pairwise (fun v w => v.target.val * w.target.val = 0)

private theorem exists_maximal_sourceFamily (p : AlgebraProjection M) :
    ∃ s : Set (PartialIsometry M), Maximal (sourceFamily p) s := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
  constructor
  · intro v hv
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    exact (hc hs).1 v hvs
  · intro v hv w hw hvw
    obtain ⟨s, hs, hvs⟩ := Set.mem_sUnion.mp hv
    obtain ⟨t, ht, hwt⟩ := Set.mem_sUnion.mp hw
    rcases hchain.total hs ht with hst | hts
    · exact (hc ht).2 (hst hvs) hwt hvw
    · exact (hc hs).2 hvs (hts hwt) hvw

private theorem target_ne_zero_of_support_ne_zero (v : PartialIsometry M)
    (hv : v.support.val ≠ 0) : v.target.val ≠ 0 := by
  intro hz
  have he := v.target_mul
  rw [hz, zero_mul] at he
  have hi := v.initial
  rw [← he, star_zero, zero_mul] at hi
  exact hv hi.symm

/-- Every nonzero projection in a countably decomposable factor supplies a
countable partition of the identity by ranges of partial isometries whose
initial projections lie under the supplied projection. -/
theorem exists_countable_source_partition_of_projection_countability
    (hFamilies : HasCountableProjectionFamilies M)
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support ≤ p) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) ∧
      (∀ q : AlgebraProjection M, (∀ n, (a n).target ≤ q) →
        (1 : Algebra M) = q.val) := by
  classical
  obtain ⟨s, hs, hmax⟩ := exists_maximal_sourceFamily p
  have hcount : Countable s := hFamilies s
    (fun v : s => v.val.target)
    (fun v => target_ne_zero_of_support_ne_zero v.val ((hs.1 v.val v.property).2))
    (fun v w hvw => hs.2 v.property w.property (fun he => hvw (Subtype.ext he)))
  let : Encodable s := @Encodable.ofCountable s hcount
  let a (n : ℕ) : PartialIsometry M :=
    (Encodable.decode₂ s n).elim PartialIsometry.zero (fun v => v.val)
  have ha (v : s) : a (Encodable.encode v) = v.val := by
    simp only [a, Encodable.decode₂_encode, Option.elim_some]
  have has (n : ℕ) : a n = PartialIsometry.zero ∨ a n ∈ s := by
    unfold a
    cases h : Encodable.decode₂ s n with
    | none => exact Or.inl rfl
    | some v => exact Or.inr v.property
  have hap (n : ℕ) : (a n).support ≤ p := by
    rcases has n with h | h
    · rw [h]
      change p.val * 0 = 0
      exact mul_zero _
    · exact (hs.1 _ h).1
  have hao : Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) := by
    intro i j hij
    unfold a
    cases hi : Encodable.decode₂ s i with
    | none => simp [PartialIsometry.zero, PartialIsometry.target]
    | some v =>
      cases hj : Encodable.decode₂ s j with
      | none => simp [PartialIsometry.zero, PartialIsometry.target]
      | some w =>
        apply hs.2 v.property w.property
        intro hvw
        have hvwe : v = w := Subtype.ext hvw
        have hvi := Encodable.decode₂_eq_some.mp hi
        have hwj := Encodable.decode₂_eq_some.mp hj
        exact hij (hvi.symm.trans (congrArg Encodable.encode hvwe |>.trans hwj))
  refine ⟨a, hap, hao, ?_⟩
  intro q hq
  by_contra hne
  let r := projectionComplement q
  have hr : r.val ≠ 0 := by
    change 1 - q.val ≠ 0
    exact sub_ne_zero.mpr hne
  obtain ⟨v, hvp, hvr, hv0⟩ :=
    traceFree_exists_nonzero_partialIsometry_between_projections hfactor p r hp hr
  have hsq (w : PartialIsometry M) (hw : w ∈ s) : w.target ≤ q := by
    simpa only [ha ⟨w, hw⟩] using hq (Encodable.encode (⟨w, hw⟩ : s))
  have hov (w : PartialIsometry M) (hw : w ∈ s) :
      v.target.val * w.target.val = 0 := by
    have hrq : r.val * q.val = 0 := by
      change (1 - q.val) * q.val = 0
      rw [sub_mul, one_mul, q.property.isIdempotentElem.eq, sub_self]
    exact projection_orthogonal_of_le hrq hvr (hsq w hw)
  have hnew : sourceFamily p (insert v s) := by
    constructor
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact ⟨hvp, hv0⟩
      · exact hs.1 w hw
    · intro w hw z hz hwz
      rcases Set.mem_insert_iff.mp hw with hw | hw
      · subst w
        rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact (hwz rfl).elim
        · exact hov z hz
      · rcases Set.mem_insert_iff.mp hz with hz | hz
        · subst z
          exact PartialIsometry.orthogonal_reverse _ _ (hov w hw)
        · exact hs.2 hw hz hwz
  have hvs : v ∈ s := hmax hnew (Set.subset_insert v s) (Set.mem_insert v s)
  have hz : v.target.val * v.target.val = 0 := hov v hvs
  rw [v.target.property.isIdempotentElem.eq] at hz
  exact target_ne_zero_of_support_ne_zero v hv0 hz

/-- The original separably acting specialization. -/
theorem exists_countable_source_partition [TopologicalSpace.SeparableSpace H]
    (hfactor : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support ≤ p) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) ∧
      (∀ q : AlgebraProjection M, (∀ n, (a n).target ≤ q) →
        (1 : Algebra M) = q.val) :=
  exists_countable_source_partition_of_projection_countability
    (fun _ p hp ho => countable_of_orthogonal_nonzero_projections p hp ho)
    hfactor p hp

private theorem star_pow_mul_pow (w : Algebra M) (hw : star w * w = 1) (n : ℕ) :
    star (w ^ n) * w ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, star_mul]
    calc
      (star w * star (w ^ n)) * (w ^ n * w) =
          star w * (star (w ^ n) * w ^ n) * w := by simp only [mul_assoc]
      _ = 1 := by rw [ih, mul_one, hw]

private def wanderingProjection (w : Algebra M) (hw : star w * w = 1) :
    AlgebraProjection M :=
  ⟨1 - w * star w, (show IsStarProjection (w * star w) from ⟨by
    change (w * star w) * (w * star w) = w * star w
    calc
      _ = w * (star w * w) * star w := by simp only [mul_assoc]
      _ = _ := by rw [hw, mul_one], IsSelfAdjoint.mul_star_self w⟩).one_sub⟩

private theorem wanderingProjection_mul (w : Algebra M) (hw : star w * w = 1) :
    (wanderingProjection w hw).val * w = 0 := by
  change (1 - w * star w) * w = 0
  rw [sub_mul, one_mul, mul_assoc, hw, mul_one, sub_self]

private theorem wanderingProjection_mul_pow (w : Algebra M) (hw : star w * w = 1)
    {n : ℕ} (hn : 0 < n) : (wanderingProjection w hw).val * w ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, wanderingProjection_mul, zero_mul]

private def wanderingPartialIsometry (w : Algebra M) (hw : star w * w = 1) (n : ℕ) :
    PartialIsometry M where
  support := wanderingProjection w hw
  val := w ^ n * (wanderingProjection w hw).val
  initial := by
    rw [star_mul, (wanderingProjection w hw).property.isSelfAdjoint.star_eq]
    calc
      ((wanderingProjection w hw).val * star (w ^ n)) *
          (w ^ n * (wanderingProjection w hw).val) =
          (wanderingProjection w hw).val * (star (w ^ n) * w ^ n) *
            (wanderingProjection w hw).val := by simp only [mul_assoc]
      _ = (wanderingProjection w hw).val := by
        rw [star_pow_mul_pow w hw, mul_one,
          (wanderingProjection w hw).property.isIdempotentElem.eq]

private theorem wandering_cross (w : Algebra M) (hw : star w * w = 1)
    {i j : ℕ} (hij : i < j) :
    star (wanderingPartialIsometry w hw i).val *
      (wanderingPartialIsometry w hw j).val = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  change star (w ^ i * (wanderingProjection w hw).val) *
    (w ^ (i + k) * (wanderingProjection w hw).val) = 0
  rw [star_mul, (wanderingProjection w hw).property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = ((wanderingProjection w hw).val * (star (w ^ i) * w ^ i)) *
        w ^ k * (wanderingProjection w hw).val := by simp only [mul_assoc]
    _ = 0 := by
      rw [star_pow_mul_pow w hw, mul_one, wanderingProjection_mul_pow w hw hk,
        zero_mul]

private theorem wandering_targets_orthogonal (w : Algebra M) (hw : star w * w = 1) :
    Pairwise (fun i j => (wanderingPartialIsometry w hw i).target.val *
      (wanderingPartialIsometry w hw j).target.val = 0) := by
  intro i j hij
  have hforward {i j : ℕ} (hlt : i < j) :
      (wanderingPartialIsometry w hw i).target.val *
        (wanderingPartialIsometry w hw j).target.val = 0 := by
    change ((wanderingPartialIsometry w hw i).val *
      star (wanderingPartialIsometry w hw i).val) *
      ((wanderingPartialIsometry w hw j).val *
        star (wanderingPartialIsometry w hw j).val) = 0
    calc
      _ = (wanderingPartialIsometry w hw i).val *
          (star (wanderingPartialIsometry w hw i).val *
            (wanderingPartialIsometry w hw j).val) *
          star (wanderingPartialIsometry w hw j).val := by simp only [mul_assoc]
      _ = 0 := by rw [wandering_cross w hw hlt, mul_zero, zero_mul]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hforward hlt
  · exact PartialIsometry.orthogonal_reverse _ _ (hforward hgt)

private theorem orthogonal_targets_of_sums
    (a b : ℕ → PartialIsometry M) (v w : PartialIsometry M)
    (hv : ∀ p : AlgebraProjection M, v.target ≤ p ↔ ∀ i, (a i).target ≤ p)
    (hw : ∀ p : AlgebraProjection M, w.target ≤ p ↔ ∀ i, (b i).target ≤ p)
    (h : ∀ i j, (a i).target.val * (b j).target.val = 0) :
    v.target.val * w.target.val = 0 := by
  have ha (i : ℕ) : (a i).target.val * w.target.val = 0 := by
    have hh : w.target ≤ projectionComplement (a i).target :=
      (hw _).mpr (fun j => le_projectionComplement (h i j))
    exact mul_eq_zero_of_le_complement hh
  have hh : v.target ≤ projectionComplement w.target := (hv _).mpr (fun i =>
    le_projectionComplement (PartialIsometry.orthogonal_reverse _ _ (ha i)))
  exact PartialIsometry.orthogonal_reverse _ _ (mul_eq_zero_of_le_complement hh)

/-- A proper isometry in a separably acting factor yields two isometries
with orthogonal ranges. -/
theorem properlyInfiniteIdentity_of_proper_isometry [Nontrivial H]
    [TopologicalSpace.SeparableSpace H] (hM : ScalarCenter M)
    (w : Algebra M) (hw : star w * w = 1) (hproper : w * star w ≠ 1) :
    ProperlyInfiniteIdentity M := by
  have hf : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M) := by
    intro c hc
    obtain ⟨z, hz⟩ := hM c.val c.property (fun a ha =>
      congrArg Subtype.val (hc ⟨a, ha⟩))
    exact ⟨z, Subtype.ext hz⟩
  let p := wanderingProjection w hw
  have hp : p.val ≠ 0 := sub_ne_zero.mpr hproper.symm
  obtain ⟨a, hap, hao, hatotal⟩ := exists_countable_source_partition hf p hp
  let slot := wanderingPartialIsometry w hw
  let b (k n : ℕ) : PartialIsometry M :=
    (slot (2 * n + k)).compose (a n).adjoint (by
      rw [PartialIsometry.adjoint_target]
      exact hap n)
  have hbs (k n : ℕ) : (b k n).support = (a n).target := rfl
  have hbt (k n : ℕ) : (b k n).target ≤ (slot (2 * n + k)).target :=
    PartialIsometry.compose_target_le _ _ _
  have hbo (k : ℕ) : Pairwise (fun i j =>
      (b k i).target.val * (b k j).target.val = 0) := by
    intro i j hij
    exact projection_orthogonal_of_le (wandering_targets_orthogonal w hw
      (by omega : 2 * i + k ≠ 2 * j + k)) (hbt k i) (hbt k j)
  have hbi (k : ℕ) : Pairwise (fun i j =>
      (b k i).support.val * (b k j).support.val = 0) := by
    simpa only [hbs] using hao
  obtain ⟨v, _, hvs, hvt⟩ := PartialIsometry.traceFree_orthogonal_sum (b 0)
    (fun i j hij => hbi 0 hij) (fun i j hij => hbo 0 hij)
  obtain ⟨u, _, hus, hut⟩ := PartialIsometry.traceFree_orthogonal_sum (b 1)
    (fun i j hij => hbi 1 hij) (fun i j hij => hbo 1 hij)
  have hv1 : v.support.val = 1 := (hatotal _ (fun n => by
    simpa only [hbs] using (hvs v.support).mp le_rfl n)).symm
  have hu1 : u.support.val = 1 := (hatotal _ (fun n => by
    simpa only [hbs] using (hus u.support).mp le_rfl n)).symm
  have hcross : v.target.val * u.target.val = 0 := by
    apply orthogonal_targets_of_sums (b 0) (b 1) v u hvt hut
    intro i j
    exact projection_orthogonal_of_le (wandering_targets_orthogonal w hw
      (by omega : 2 * i + 0 ≠ 2 * j + 1)) (hbt 0 i) (hbt 1 j)
  have hstar : star v.val * v.target.val = star v.val := by
    simpa only [star_mul, v.target.property.isSelfAdjoint.star_eq] using
      congrArg star v.target_mul
  refine ⟨one_ne_zero, v.val, u.val, v.initial.trans hv1, u.initial.trans hu1, ?_⟩
  calc
    star v.val * u.val = (star v.val * v.target.val) * (u.target.val * u.val) := by
      rw [hstar, u.target_mul]
    _ = star v.val * (v.target.val * u.target.val) * u.val := by
      simp only [mul_assoc]
    _ = 0 := by rw [hcross, mul_zero, zero_mul]

/-- The formerly published infinite-factor projection input follows from
concrete partial-isometry comparison and separability. -/
theorem publishedInfiniteFactorProperlyInfinite :
    PublishedInfiniteFactorProperlyInfinite.{u} := by
  intro H _ _ _ _ _ M hM hInfinite
  simp only [FiniteProjectionIn, one_mul] at hInfinite
  push Not at hInfinite
  obtain ⟨w, hw, _, hproper⟩ := hInfinite
  exact properlyInfiniteIdentity_of_proper_isometry hM w hw hproper

end

end KadisonKastler

end OAI
