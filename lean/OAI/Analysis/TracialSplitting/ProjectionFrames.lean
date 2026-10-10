import OAI.Analysis.TracialSplitting.ScalarCompression

namespace OAI

universe uA uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FullProjectionFrames

open Filter Topology

open scoped CStarAlgebra

variable {A : Type uA} [CStarAlgebra A]

def finiteSandwichIdeal (e : A) : TwoSidedIdeal A :=
  .mk' {a | ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = a}
    ⟨[], by simp⟩
    (by rintro a b ⟨l, rfl⟩ ⟨m, rfl⟩; exact ⟨l ++ m, by simp⟩)
    (by
      rintro a ⟨l, rfl⟩
      refine ⟨l.map (fun v => (-v.1, v.2)), ?_⟩
      simp only [List.map_map, Function.comp_def, neg_mul]
      induction l with
      | nil => simp
      | cons v l ih => simp [ih, add_comm])
    (by
      rintro a b ⟨l, rfl⟩
      refine ⟨l.map (fun v => (a * v.1, v.2)), ?_⟩
      simp only [List.map_map, Function.comp_def, mul_assoc]
      induction l with
      | nil => simp
      | cons v l ih => simpa [mul_add, mul_assoc] using congrArg (fun z => a * v.1 * e * v.2 + z) ih)
    (by
      rintro a b ⟨l, rfl⟩
      refine ⟨l.map (fun v => (v.1, v.2 * b)), ?_⟩
      simp only [List.map_map, Function.comp_def, ← mul_assoc]
      induction l with
      | nil => simp
      | cons v l ih => simpa [add_mul, mul_assoc] using congrArg (fun z => v.1 * e * v.2 * b + z) ih)

@[simp] theorem mem_finiteSandwichIdeal (e a : A) :
    a ∈ finiteSandwichIdeal e ↔
      ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = a := by
  simp [finiteSandwichIdeal]

theorem exists_finite_fullness_approximation {e : A} (he : IsFull e) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (A × A), ‖1 - (l.map fun v => v.1 * e * v.2).sum‖ < ε := by
  have h : (1 : A) ∈ closure (finiteSandwichIdeal e : Set A) := by
    have hs : TwoSidedIdeal.span {e} ≤ finiteSandwichIdeal e := by
      apply TwoSidedIdeal.span_le.mpr
      intro a ha
      have haeq := Set.mem_singleton_iff.mp ha
      subst a
      exact (mem_finiteSandwichIdeal e e).mpr ⟨[(1, 1)], by simp⟩
    apply closure_mono (show (TwoSidedIdeal.span {e} : Set A) ⊆
      (finiteSandwichIdeal e : Set A) from hs)
    rw [he]
    trivial
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp h ε hε
  obtain ⟨l, rfl⟩ := (mem_finiteSandwichIdeal e s).mp hs
  exact ⟨l, by simpa only [dist_eq_norm] using hdist⟩

theorem exists_finite_fullness_identity {e : A} (he : IsFull e) :
    ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = 1 := by
  obtain ⟨l, hl⟩ := exists_finite_fullness_approximation he (ε := 1) zero_lt_one
  let s := (l.map fun v => v.1 * e * v.2).sum
  have hs : s ∈ finiteSandwichIdeal e := (mem_finiteSandwichIdeal e s).mpr ⟨l, rfl⟩
  have hu : IsUnit s := by
    have := (Units.oneSub (1 - s) hl).isUnit
    change IsUnit (1 - (1 - s)) at this
    simpa only [sub_sub_cancel] using this
  obtain ⟨u, hu⟩ := hu
  have hone := (finiteSandwichIdeal e).mul_mem_left (↑(u⁻¹) : A) s hs
  rw [← hu, Units.inv_mul] at hone
  exact (mem_finiteSandwichIdeal e 1).mp hone

variable [PartialOrder A] [StarOrderedRing A]

lemma star_add_mul_add_le (a b : A) :
    star (a + b) * (a + b) ≤ (2 : ℝ) • (star a * a + star b * b) := by
  have h := star_mul_self_nonneg (a - b)
  rw [← sub_nonneg]
  convert h using 1
  simp only [star_add, star_sub, two_smul]
  noncomm_ring

lemma list_square_sum_nonneg (l : List (A × A)) :
    0 ≤ (l.map fun v => star v.2 * v.2).sum := by
  induction l with
  | nil => simp
  | cons v l ih => simpa using add_nonneg (star_mul_self_nonneg v.2) ih

lemma finite_product_sum_bound (l : List (A × A)) :
    ∃ C : ℝ, 0 < C ∧
      star (l.map fun v => v.1 * v.2).sum * (l.map fun v => v.1 * v.2).sum ≤
        C • (l.map fun v => star v.2 * v.2).sum := by
  induction l with
  | nil => exact ⟨1, zero_lt_one, by simp⟩
  | cons v l ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let K := ‖star v.1 * v.1‖ + C
    have hK : 0 < K := add_pos_of_nonneg_of_pos (norm_nonneg _) hC
    have hsingle : star (v.1 * v.2) * (v.1 * v.2) ≤
        ‖star v.1 * v.1‖ • (star v.2 * v.2) := by
      simpa only [star_mul, mul_assoc] using
        (CStarAlgebra.star_left_conjugate_le_norm_smul
          (a := v.2) (b := star v.1 * v.1))
    refine ⟨2 * K, mul_pos (by norm_num) hK, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ (2 : ℝ) • (star (v.1 * v.2) * (v.1 * v.2) +
          star (l.map fun v => v.1 * v.2).sum * (l.map fun v => v.1 * v.2).sum) :=
        star_add_mul_add_le _ _
      _ ≤ (2 : ℝ) • (‖star v.1 * v.1‖ • (star v.2 * v.2) +
          C • (l.map fun v => star v.2 * v.2).sum) :=
        smul_le_smul_of_nonneg_left (add_le_add hsingle hbound) (by norm_num)
      _ ≤ (2 : ℝ) • (K • (star v.2 * v.2) +
          K • (l.map fun v => star v.2 * v.2).sum) := by
        apply smul_le_smul_of_nonneg_left _ (by norm_num)
        exact add_le_add
          (smul_le_smul_of_nonneg_right (by dsimp [K]; linarith) (star_mul_self_nonneg _))
          (smul_le_smul_of_nonneg_right (by dsimp [K]; linarith [norm_nonneg (star v.1 * v.1)])
            (list_square_sum_nonneg l))
      _ = _ := by rw [← smul_add, mul_smul]

theorem finite_gram_isUnit (l : List (A × A))
    (h : (l.map fun v => v.1 * v.2).sum = 1) :
    IsUnit (l.map fun v => star v.2 * v.2).sum := by
  obtain ⟨C, hC, hb⟩ := finite_product_sum_bound l
  rw [h, star_one, one_mul] at hb
  have hy : IsUnit (C • (l.map fun v => star v.2 * v.2).sum) :=
    CStarAlgebra.isUnit_of_le 1 hb
  have hs : IsUnit (algebraMap ℝ A C) := (isUnit_iff_ne_zero.mpr hC.ne').map _
  rw [Algebra.smul_def] at hy
  exact (hs.mul_left_iff).mp hy

theorem exists_positive_fullness_frame
    {e : A} (he : 0 ≤ e) (hfull : IsFull e) :
    ∃ x : List A, (x.map fun v => star v * e * v).sum = 1 := by
  obtain ⟨l, hl⟩ := exists_finite_fullness_identity hfull
  let t := CFC.sqrt e
  have ht : IsSelfAdjoint t := .of_nonneg (CFC.sqrt_nonneg e)
  have ht2 : t * t = e := CFC.sqrt_mul_sqrt_self e
  let w : List (A × A) := l.map fun v => (v.1 * t, t * v.2)
  have hw : (w.map fun v => v.1 * v.2).sum = 1 := by
    simpa only [w, List.map_map, Function.comp_def, mul_assoc, ← mul_assoc t t, ht2] using hl
  let y := (w.map fun v => star v.2 * v.2).sum
  have hy : IsStrictlyPositive y :=
    IsStrictlyPositive.iff_of_unital.mpr ⟨list_square_sum_nonneg w, finite_gram_isUnit w hw⟩
  let z := CFC.rpow y (-(1 / 2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have hzyz : z * y * z = 1 := CFC.conjugate_rpow_neg_one_half y hy
  refine ⟨l.map (fun v => v.2 * z), ?_⟩
  have hysum : y = (l.map fun v => star v.2 * e * v.2).sum := by
    simp only [y, w, List.map_map, Function.comp_def, star_mul, ht.star_eq,
      mul_assoc, ← mul_assoc t t, ht2]
  rw [hysum] at hzyz
  rw [List.map_map]
  convert hzyz using 1
  have hdist (m : List (A × A)) :
      (m.map fun v => star (v.2 * z) * e * (v.2 * z)).sum =
        z * (m.map fun v => star v.2 * e * v.2).sum * z := by
    induction m with
    | nil => simp
    | cons v m ih =>
      simp only [List.map_cons, List.sum_cons, star_mul, hz.star_eq, mul_add, add_mul]
      simpa only [mul_assoc, star_mul, hz.star_eq] using
        congrArg (fun a => z * star v.2 * e * v.2 * z + a) ih
  exact hdist l

end FullProjectionFrames

section ColumnSplitting

variable {D : Type uD} [CStarAlgebra D]

def ProjectionSubequivalent (e g : D) : Prop :=
  ∃ v : D, star v * v = e ∧ g * v = v

lemma partialIsometry_right_support {v e : D} (he : IsStarProjection e)
    (hv : star v * v = e) : v * e = v := by
  apply sub_eq_zero.mp
  apply (CStarRing.star_mul_self_eq_zero_iff _).mp
  calc
    star (v * e - v) * (v * e - v) =
        e * (star v * v) * e - e * (star v * v) - (star v * v) * e + star v * v := by
      rw [star_sub, star_mul, he.isSelfAdjoint.star_eq]
      noncomm_ring
    _ = 0 := by simp only [hv, he.isIdempotentElem.eq, sub_self, zero_sub, neg_add_cancel]

lemma ProjectionSubequivalent.refl (e : D) (he : IsStarProjection e) :
    ProjectionSubequivalent e e :=
  ⟨e, by rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem], he.isIdempotentElem⟩

lemma ProjectionSubequivalent.zero (g : D) : ProjectionSubequivalent 0 g :=
  ⟨0, by simp, by simp⟩

lemma ProjectionSubequivalent.trans {e f g : D}
    (h₁ : ProjectionSubequivalent e f)
    (h₂ : ProjectionSubequivalent f g) : ProjectionSubequivalent e g := by
  obtain ⟨v, hv, hfv⟩ := h₁
  obtain ⟨w, hw, hgw⟩ := h₂
  refine ⟨w * v, ?_, ?_⟩
  · simp only [star_mul]
    calc
      star v * star w * (w * v) = star v * (star w * w) * v := by simp only [mul_assoc]
      _ = e := by rw [hw, mul_assoc, hfv, hv]
  · rw [← mul_assoc, hgw]

variable [PartialOrder D] [StarOrderedRing D]

lemma ProjectionSubequivalent.of_le {e g : D} (he : IsStarProjection e)
    (hg : IsStarProjection g) (h : e ≤ g) : ProjectionSubequivalent e g :=
  ⟨e, by rw [he.isSelfAdjoint.star_eq, he.isIdempotentElem],
    (he.le_iff_mul_eq_right hg).mp h⟩

lemma ProjectionSubequivalent.final_projection {e g : D} (he : IsStarProjection e)
    (hg : IsStarProjection g) (h : ProjectionSubequivalent e g) :
    ∃ v : D, star v * v = e ∧ IsStarProjection (v * star v) ∧ v * star v ≤ g := by
  obtain ⟨v, hv, hgv⟩ := h
  have hf : IsStarProjection (v * star v) :=
    ⟨isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star.mp
      (hv ▸ he.isIdempotentElem), by simp only [IsSelfAdjoint, star_mul, star_star]⟩
  exact ⟨v, hv, hf, (hf.le_iff_mul_eq_right hg).mpr (by rw [← mul_assoc, hgv])⟩

lemma ProjectionSubequivalent.trace_le (τ : TracialState D) {e g : D}
    (he : IsStarProjection e) (hg : IsStarProjection g)
    (h : ProjectionSubequivalent e g) : (τ.functional e).re ≤ (τ.functional g).re := by
  obtain ⟨v, hv, _, hle⟩ := h.final_projection he hg
  have h := τ.functional.monotone hle
  rw [← hv, τ.tracial (star v) v]
  exact (Complex.le_def.mp h).1

lemma exists_corner_normalizer {p a : D} (hp : IsStarProjection p) (ha : 0 ≤ a)
    {c : ℝ} (hc : 0 < c) (hbound : c • p ≤ p * a * p) :
    ∃ z : ProjectionCorner hp, IsSelfAdjoint z ∧
      (z : D) * a * (z : D) = p := by
  let b := ProjectionCorner.compress hp a
  have hb : 0 ≤ b := ProjectionCorner.compress_nonneg hp ha
  have hcpos : IsStrictlyPositive (c • (1 : ProjectionCorner hp)) := by
    apply IsStrictlyPositive.iff_of_unital.mpr
    refine ⟨smul_nonneg hc.le zero_le_one, ?_⟩
    rw [Algebra.smul_def, mul_one]
    exact (isUnit_iff_ne_zero.mpr hc.ne').map (algebraMap ℝ (ProjectionCorner hp))
  have hbpos : IsStrictlyPositive b := hcpos.of_le hbound
  let z := CFC.rpow b (-(1 / 2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have hzbz : z * b * z = 1 := CFC.conjugate_rpow_neg_one_half b hbpos
  refine ⟨z, hz, ?_⟩
  have h := congrArg (fun x : ProjectionCorner hp => (x : D)) hzbz
  change (z : D) * (p * a * p) * (z : D) = p at h
  simp only [← mul_assoc] at h
  rw [z.property.2] at h
  simpa only [mul_assoc, z.property.1] using h

lemma projectionSubequivalent_of_compression {e g v : D}
    (he : IsStarProjection e) (hgv : g * v = v)
    {c : ℝ} (hc : 0 < c) (hbound : c • e ≤ e * (star v * v) * e) :
    ProjectionSubequivalent e g := by
  obtain ⟨z, hz, hnorm⟩ := exists_corner_normalizer he (star_mul_self_nonneg v) hc hbound
  refine ⟨v * (z : D), ?_, by rw [← mul_assoc, hgv]⟩
  rw [star_mul, (ProjectionCorner.isSelfAdjoint_coe he hz).star_eq]
  simpa only [mul_assoc] using hnorm

lemma exists_spectral_cut (hRR : RealRankZero D) {a : D} (ha : IsSelfAdjoint a)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧
      (t - ε) • e ≤ e * a * e ∧
      (1 - e) * a * (1 - e) ≤ (t + ε) • (1 - e) := by
  obtain ⟨b, hb, hbf, hba⟩ := hRR a ha ε hε
  have hbf' := realSpectrum_finite hb hbf
  let e := spectralThreshold b t
  have he : IsStarProjection e := spectralThreshold_projection hbf' t
  have hr : IsStarProjection (1 - e) := he.one_sub
  have hn : ‖b - a‖ ≤ ε := (norm_sub_rev b a ▸ hba.le)
  refine ⟨e, he, ?_, ?_⟩
  · calc
      (t - ε) • e = t • e - ε • e := sub_smul _ _ _
      _ ≤ e * b * e - ‖b - a‖ • e := sub_le_sub
        (spectralThreshold_lower hb hbf' t)
        (smul_le_smul_of_nonneg_right hn he.nonneg)
      _ ≤ e * a * e := compress_perturbation_lower hb ha he
  · calc
      (1 - e) * a * (1 - e) ≤ (1 - e) * b * (1 - e) + ‖b - a‖ • (1 - e) :=
        compress_perturbation_upper hb ha hr
      _ ≤ t • (1 - e) + ε • (1 - e) := add_le_add
        (spectralThreshold_complement_upper hb hbf' t)
        (smul_le_smul_of_nonneg_right hn hr.nonneg)
      _ = (t + ε) • (1 - e) := (add_smul _ _ _).symm

omit [PartialOrder D] [StarOrderedRing D] in
lemma ProjectionCorner.coe_mul_compress_mul {p : D} (hp : IsStarProjection p)
    (x y : ProjectionCorner hp) (a : D) :
    ((x * compress hp a * y : ProjectionCorner hp) : D) = (x : D) * a * (y : D) := by
  change (x : D) * (p * a * p) * (y : D) = _
  simp only [← mul_assoc]
  rw [x.property.2]
  simp only [mul_assoc, y.property.1]

lemma exists_column_cut (hRR : RealRankZero D) {f a : D} (hf : IsStarProjection f)
    (ha : IsSelfAdjoint a) :
    ∃ e : D, IsStarProjection e ∧ e ≤ f ∧
      (3 / 8 : ℝ) • e ≤ e * a * e ∧
      (f - e) * a * (f - e) ≤ (5 / 8 : ℝ) • (f - e) := by
  let b := ProjectionCorner.compress hf a
  have hb : IsSelfAdjoint b := by
    apply Subtype.ext
    change star (f * a * f) = f * a * f
    simpa only [hf.isSelfAdjoint.star_eq] using (ha.conjugate f).star_eq
  obtain ⟨e, he, hlow, hupp⟩ := exists_spectral_cut (realRankZero_corner hRR hf) hb
    (1 / 2) (ε := 1 / 8) (by norm_num)
  have he' : IsStarProjection (e : D) := he.map (ProjectionCorner.inclusion hf)
  refine ⟨(e : D), he', (he'.le_iff_mul_eq_right hf).mpr e.property.1, ?_, ?_⟩
  · norm_num only [show (1 / 2 - 1 / 8 : ℝ) = 3 / 8 by norm_num] at hlow
    have h : (3 / 8 : ℝ) • (e : D) ≤ ((e * b * e : ProjectionCorner hf) : D) := hlow
    rwa [ProjectionCorner.coe_mul_compress_mul] at h
  · norm_num only [show (1 / 2 + 1 / 8 : ℝ) = 5 / 8 by norm_num] at hupp
    have h : (((1 - e) * b * (1 - e) : ProjectionCorner hf) : D) ≤
        (5 / 8 : ℝ) • (f - (e : D)) := hupp
    rwa [ProjectionCorner.coe_mul_compress_mul] at h

theorem split_column (hRR : RealRankZero D) (n : ℕ) {f : D}
    (hf : IsStarProjection f) (g v : Fin n → D)
    (hg : ∀ i, IsStarProjection (g i))
    (hleft : ∀ i, g i * v i = v i) (hsum : ∑ i, star (v i) * v i = f) :
    ∃ e : Fin n → D, (∀ i, IsStarProjection (e i)) ∧
      Pairwise (fun i j => e i * e j = 0) ∧
      (∑ i, e i = f) ∧ ∀ i, ProjectionSubequivalent (e i) (g i) := by
  induction n generalizing f with
  | zero =>
    have hf0 : f = 0 := by simpa using hsum.symm
    refine ⟨Fin.elim0, (fun i => Fin.elim0 i), ?_, ?_, (fun i => Fin.elim0 i)⟩
    · intro i; exact Fin.elim0 i
    · simp [hf0]
  | succ n ih =>
    let a := star (v 0) * v 0
    have ha : IsSelfAdjoint a := (star_mul_self_nonneg (v 0)).isSelfAdjoint
    obtain ⟨e, he, hef, hlow, hupp⟩ := exists_column_cut hRR hf ha
    let r := f - e
    have hr : IsStarProjection r := (he.le_iff_sub hf).mp hef
    have hef' : e * f = e := (he.le_iff_mul_eq_left hf).mp hef
    have hfe : f * e = e := (he.le_iff_mul_eq_right hf).mp hef
    have hrf : r * f = r := by simp only [r, sub_mul, hf.isIdempotentElem.eq, hef']
    have her : e * r = 0 := by simp only [r, mul_sub, hef', he.isIdempotentElem.eq, sub_self]
    have hre : r * e = 0 := by simp only [r, sub_mul, hfe, he.isIdempotentElem.eq, sub_self]
    have hecomp : ProjectionSubequivalent e (g 0) :=
      projectionSubequivalent_of_compression he (hleft 0) (by norm_num : (0 : ℝ) < 3 / 8) hlow
    let q := ∑ i : Fin n, star (v i.succ) * v i.succ
    have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => star_mul_self_nonneg _
    have hqeq : a + q = f := by simpa only [Fin.sum_univ_succ] using hsum
    have hrq : r * q * r = r - r * a * r := by
      calc
        r * q * r = r * f * r - r * a * r := by rw [← hqeq]; noncomm_ring
        _ = r - r * a * r := by rw [hrf, hr.isIdempotentElem]
    have hbound : (3 / 8 : ℝ) • r ≤ r * q * r := by
      calc
        (3 / 8 : ℝ) • r = r - (5 / 8 : ℝ) • r := by
          calc
            (3 / 8 : ℝ) • r = (1 - 5 / 8 : ℝ) • r := by norm_num
            _ = r - (5 / 8 : ℝ) • r := by rw [sub_smul, one_smul]
        _ ≤ r - r * a * r := sub_le_sub_left hupp r
        _ = r * q * r := hrq.symm
    obtain ⟨z, hz, hnorm⟩ := exists_corner_normalizer hr hq
      (by norm_num : (0 : ℝ) < 3 / 8) hbound
    let w : Fin n → D := fun i => v i.succ * (z : D)
    have hwleft (i : Fin n) : g i.succ * w i = w i := by
      dsimp [w]; rw [← mul_assoc, hleft]
    have hzstar : star (z : D) = (z : D) := (ProjectionCorner.isSelfAdjoint_coe hr hz).star_eq
    have hwsum : ∑ i : Fin n, star (w i) * w i = r := by
      calc
        _ = (z : D) * q * (z : D) := by
          simp only [w, q, star_mul, hzstar, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = r := hnorm
    obtain ⟨E, hE, hEorth, hEsum, hEcomp⟩ := ih hr (fun i => g i.succ) w
      (fun i => hg i.succ) hwleft hwsum
    have hEr (i : Fin n) : E i ≤ r := by
      rw [← hEsum]
      exact Finset.single_le_sum (fun j _ => (hE j).nonneg) (Finset.mem_univ i)
    have hEright (i : Fin n) : E i * r = E i := ((hE i).le_iff_mul_eq_left hr).mp (hEr i)
    have hEleft (i : Fin n) : r * E i = E i := ((hE i).le_iff_mul_eq_right hr).mp (hEr i)
    refine ⟨Fin.cases e E, ?_, ?_, ?_, ?_⟩
    · intro i; cases i using Fin.cases with
      | zero => exact he
      | succ i => exact hE i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j =>
          change e * E j = 0
          rw [← hEleft j, ← mul_assoc, her, zero_mul]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          change E i * e = 0
          rw [← hEright i, mul_assoc, hre, mul_zero]
        | succ j =>
          exact hEorth (fun h => hij (congrArg Fin.succ h))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, hEsum]
      dsimp [r]; abel
    · intro i; cases i using Fin.cases with
      | zero => exact hecomp
      | succ i => exact hEcomp i

end ColumnSplitting

section ProjectionRefinement

variable {D : Type uD} [CStarAlgebra D]

lemma mul_eq_zero_of_supports {a b p q : D} (ha : a * p = a)
    (hb : q * b = b) (hpq : p * q = 0) : a * b = 0 := by
  calc
    a * b = (a * p) * (q * b) := by rw [ha, hb]
    _ = a * (p * q) * b := by simp only [mul_assoc]
    _ = 0 := by rw [hpq, mul_zero, zero_mul]

lemma projection_mul_zero_symm {p q : D} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : p * q = 0) : q * p = 0 := by
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, star_zero]
    using congrArg star h

lemma ProjectionSubequivalent.range {e v : D} (he : IsStarProjection e)
    (hv : star v * v = e) :
    ProjectionSubequivalent e (v * star v) ∧ ProjectionSubequivalent (v * star v) e := by
  have hve : v * e = v := partialIsometry_right_support he hv
  refine ⟨⟨v, hv, ?_⟩, ⟨star v, by simp only [star_star], ?_⟩⟩
  · rw [mul_assoc, hv, hve]
  · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star hve

lemma ProjectionSubequivalent.orthogonal_add {e f p q : D}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0)
    (he : ProjectionSubequivalent e p) (hf : ProjectionSubequivalent f q) :
    ProjectionSubequivalent (e + f) (p + q) := by
  obtain ⟨v, hv, hpv⟩ := he
  obtain ⟨w, hw, hqw⟩ := hf
  have hqp := projection_mul_zero_symm hp hq hpq
  have hvp : star v * p = star v := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hwq : star w * q = star w := by
    simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hqw
  have hvw : star v * w = 0 := mul_eq_zero_of_supports hvp hqw hpq
  have hwv : star w * v = 0 := mul_eq_zero_of_supports hwq hpv hqp
  have hpw : p * w = 0 := mul_eq_zero_of_supports hp.isIdempotentElem hqw hpq
  have hqv : q * v = 0 := mul_eq_zero_of_supports hq.isIdempotentElem hpv hqp
  exact ⟨v + w, by simp only [star_add, add_mul, mul_add, hv, hw, hvw, hwv, add_zero,
    zero_add], by simp only [add_mul, mul_add, hpv, hqw, hpw, hqv, add_zero, zero_add]⟩

variable [PartialOrder D] [StarOrderedRing D]

lemma comparison_pair (hRR : RealRankZero D) {x y h : D}
    (hx : IsStarProjection x) (hy : IsStarProjection y) (hh : IsStarProjection h)
    (hxy : x * y = 0) (hxh : ProjectionSubequivalent x h)
    (hyh : ProjectionSubequivalent y h) :
    ∃ k z : D, IsStarProjection k ∧ IsStarProjection z ∧ k + z = x + y ∧
      x ≤ z ∧ ProjectionSubequivalent k z ∧ ProjectionSubequivalent z h := by
  obtain ⟨w, hw, hwproj, hwle⟩ := hxh.final_projection hx hh
  obtain ⟨u, hu, hhu⟩ := hyh
  let p := w * star w
  have hp : IsStarProjection p := hwproj
  have hq : IsStarProjection (h - p) := (hp.le_iff_sub hh).mp hwle
  have hpq : p * (h - p) = 0 := by
    rw [mul_sub, (hp.le_iff_mul_eq_left hh).mp hwle, hp.isIdempotentElem, sub_self]
  let targets : Fin 2 → D := ![p, h - p]
  let v : Fin 2 → D := ![p * u, (h - p) * u]
  have ht (i : Fin 2) : IsStarProjection (targets i) := by
    fin_cases i
    · exact hp
    · exact hq
  have hvleft (i : Fin 2) : targets i * v i = v i := by
    fin_cases i
    · change p * (p * u) = p * u
      rw [← mul_assoc, hp.isIdempotentElem]
    · change (h - p) * ((h - p) * u) = (h - p) * u
      rw [← mul_assoc, hq.isIdempotentElem]
  have hvsum : ∑ i, star (v i) * v i = y := by
    rw [Fin.sum_univ_two]
    change star (p * u) * (p * u) + star ((h - p) * u) * ((h - p) * u) = y
    simp only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    calc
      _ = star u * p * u + star u * (h - p) * u := by
        simp only [mul_assoc, ← mul_assoc p p, hp.isIdempotentElem.eq,
          ← mul_assoc (h - p) (h - p), hq.isIdempotentElem.eq]
      _ = star u * h * u := by noncomm_ring
      _ = y := by rw [mul_assoc, hhu, hu]
  obtain ⟨E, hE, hEorth, hEsum, hEcomp⟩ := split_column hRR 2 hy targets v ht hvleft hvsum
  have hsum : E 0 + E 1 = y := by simpa only [Fin.sum_univ_two] using hEsum
  have h01 : E 0 * E 1 = 0 := hEorth (by decide : (0 : Fin 2) ≠ 1)
  have hE0y : E 0 ≤ y := by rw [← hsum]; exact le_add_of_nonneg_right (hE 1).nonneg
  have hE1y : E 1 ≤ y := by rw [← hsum]; exact le_add_of_nonneg_left (hE 0).nonneg
  have hx1 : x * E 1 = 0 := mul_eq_zero_of_supports hx.isIdempotentElem
    (((hE 1).le_iff_mul_eq_right hy).mp hE1y) hxy
  have hx0 : x * E 0 = 0 := mul_eq_zero_of_supports hx.isIdempotentElem
    (((hE 0).le_iff_mul_eq_right hy).mp hE0y) hxy
  have hz : IsStarProjection (x + E 1) := hx.add (hE 1) hx1
  have hxz : x ≤ x + E 1 := le_add_of_nonneg_right (hE 1).nonneg
  have h0xcomp : ProjectionSubequivalent (E 0) x :=
    (hEcomp 0).trans (ProjectionSubequivalent.range hx hw).2
  have hzcomp : ProjectionSubequivalent (x + E 1) h := by
    have hc := ProjectionSubequivalent.orthogonal_add hp hq hpq
      (ProjectionSubequivalent.range hx hw).1 (hEcomp 1)
    simpa only [add_sub_cancel] using hc
  refine ⟨E 0, x + E 1, hE 0, hz, ?_, hxz,
    h0xcomp.trans (ProjectionSubequivalent.of_le hx hz hxz), hzcomp⟩
  rw [← hsum]
  abel

end ProjectionRefinement

end CurrentMain

end

end

end OAI
