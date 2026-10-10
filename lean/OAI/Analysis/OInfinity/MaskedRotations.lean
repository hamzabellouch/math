import OAI.Analysis.OInfinity.RelativeGramCorrection
import OAI.Analysis.OInfinity.BergSeam
import OAI.Analysis.OInfinity.CornerContractionPath

namespace OAI

/-! # Genuine rotations on the retained cyclic cells

The corrected rows have a common initial projection. Cutting them by its
orthogonal cells gives actual square-zero partial isometries and hence a
connected unitary for any finite collection of angles. The removed cell
is absent from both initial rows; the complement of their final ranges is
retained. No claim that the ambient zero cell is fixed is made.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

/-- The partial isometry between the two copies of a retained cell. -/
def maskedRotationPiece (r t f : E) : E := t * f * star r

omit [Fintype I] [DecidableEq I] in
lemma maskedRotationPiece_relations (p r t f : E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : IsStarProjection f) (hpf : p * f = f) :
    maskedRotationPiece r t f * star (maskedRotationPiece r t f) *
        maskedRotationPiece r t f = maskedRotationPiece r t f ∧
      maskedRotationPiece r t f * maskedRotationPiece r t f = 0 ∧
      bergSupport (maskedRotationPiece r t f) = r * f * star r + t * f * star t := by
  have hfr : star (r * f) * (r * f) = f := by
    rw [star_mul, hf.isSelfAdjoint.star_eq]
    calc
      _ = f * (star r * r) * f := by noncomm_ring
      _ = f := by rw [hr, mul_assoc, hpf, hf.isIdempotentElem.eq]
  have hft : star (t * f) * (t * f) = f := by
    rw [star_mul, hf.isSelfAdjoint.star_eq]
    calc
      _ = f * (star t * t) * f := by noncomm_ring
      _ = f := by rw [ht, mul_assoc, hpf, hf.isIdempotentElem.eq]
  have hcross : star (r * f) * (t * f) = 0 := by
    rw [star_mul]
    calc
      _ = star f * (star r * t) * f := by noncomm_ring
      _ = 0 := by rw [hrt, mul_zero, zero_mul]
  have hrf : (r * f) * f = r * f := by rw [mul_assoc, hf.isIdempotentElem.eq]
  have htf : (t * f) * f = t * f := by rw [mul_assoc, hf.isIdempotentElem.eq]
  have heq : (t * f) * star (r * f) = maskedRotationPiece r t f := by
    rw [star_mul, hf.isSelfAdjoint.star_eq]
    change (t * f) * (f * star r) = t * f * star r
    rw [← mul_assoc, htf]
  obtain ⟨ha, haa, hi, ho⟩ := cornerRotation_relations f (r * f) (t * f)
    hfr hft hcross hrf htf
  rw [heq] at ha haa hi ho
  refine ⟨ha, haa, ?_⟩
  unfold bergSupport
  rw [hi, ho, star_mul, star_mul, hf.isSelfAdjoint.star_eq]
  calc
    _ = r * (f * f) * star r + t * (f * f) * star t := by noncomm_ring
    _ = _ := by rw [hf.isIdempotentElem.eq]

omit [Fintype I] [DecidableEq I] in
lemma maskedRotationPiece_support_orthogonal (p r t f g : E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : IsStarProjection f) (hg : IsStarProjection g)
    (hpf : p * f = f) (hpg : p * g = g) (hfg : f * g = 0) :
    bergSupport (maskedRotationPiece r t f) * bergSupport (maskedRotationPiece r t g) = 0 := by
  have htr : star t * r = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hrt
  rw [(maskedRotationPiece_relations p r t f hr ht hrt hf hpf).2.2,
    (maskedRotationPiece_relations p r t g hr ht hrt hg hpg).2.2]
  have hrr : (r * f * star r) * (r * g * star r) = 0 := by
    calc
      _ = r * (f * (star r * r) * g) * star r := by noncomm_ring
      _ = 0 := by rw [hr, mul_assoc f p g, hpg, hfg, mul_zero, zero_mul]
  have htt : (t * f * star t) * (t * g * star t) = 0 := by
    calc
      _ = t * (f * (star t * t) * g) * star t := by noncomm_ring
      _ = 0 := by rw [ht, mul_assoc f p g, hpg, hfg, mul_zero, zero_mul]
  have hrt' : (r * f * star r) * (t * g * star t) = 0 := by
    calc
      _ = r * f * (star r * t) * g * star t := by noncomm_ring
      _ = 0 := by rw [hrt]; simp
  have htr' : (t * f * star t) * (r * g * star r) = 0 := by
    calc
      _ = t * f * (star t * r) * g * star r := by noncomm_ring
      _ = 0 := by rw [htr]; simp
  rw [add_mul, mul_add, mul_add, hrr, htt, hrt', htr']
  simp only [zero_add]

/-- A finite family of the corrected cell rotations is an actual unitary. -/
def maskedRotationUnitary (p r t : E) (f : I → E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : ∀ i, IsStarProjection (f i)) (hpf : ∀ i, p * f i = f i)
    (ho : ∀ i j, i ≠ j → f i * f j = 0) (θ : I → ℝ) : unitary E :=
  ⟨bergFiniteRotation (fun i => maskedRotationPiece r t (f i)) Finset.univ θ,
    bergFiniteRotation_mem _ _ θ
      (fun i _ => (maskedRotationPiece_relations p r t (f i) hr ht hrt (hf i) (hpf i)).1)
      (fun i _ => (maskedRotationPiece_relations p r t (f i) hr ht hrt (hf i) (hpf i)).2.1)
      (fun i _ j _ hij => maskedRotationPiece_support_orthogonal p r t (f i) (f j)
        hr ht hrt (hf i) (hf j) (hpf i) (hpf j) (ho i j hij))⟩

omit [DecidableEq I] in
lemma maskedRotationUnitary_zero (p r t : E) (f : I → E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : ∀ i, IsStarProjection (f i)) (hpf : ∀ i, p * f i = f i)
    (ho : ∀ i j, i ≠ j → f i * f j = 0) :
    maskedRotationUnitary p r t f hr ht hrt hf hpf ho (fun _ => 0) = 1 := by
  apply Subtype.ext
  change 1 + (∑ i, (partialIsometryBergRotation (maskedRotationPiece r t (f i)) 0 - 1)) = 1
  simp only [partialIsometryBergRotation_zero, sub_self, Finset.sum_const_zero, add_zero]

omit [DecidableEq I] in
lemma maskedRotationUnitary_continuous (p r t : E) (f : I → E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : ∀ i, IsStarProjection (f i)) (hpf : ∀ i, p * f i = f i)
    (ho : ∀ i j, i ≠ j → f i * f j = 0) (θ : I → ℝ) :
    Continuous (fun x : ℝ => maskedRotationUnitary p r t f hr ht hrt hf hpf ho
      (fun i => x * θ i)) := by
  apply Continuous.subtype_mk
  unfold bergFiniteRotation
  apply continuous_const.add
  apply continuous_finsetSum
  intro i _
  exact ((partialIsometryBergRotation_continuous _).comp
    (continuous_id.mul continuous_const)).sub continuous_const

omit [DecidableEq I] in
lemma maskedRotationUnitary_joined (p r t : E) (f : I → E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : ∀ i, IsStarProjection (f i)) (hpf : ∀ i, p * f i = f i)
    (ho : ∀ i j, i ≠ j → f i * f j = 0) (θ : I → ℝ) :
    Joined (1 : unitary E) (maskedRotationUnitary p r t f hr ht hrt hf hpf ho θ) := by
  let g (x : unitInterval) := maskedRotationUnitary p r t f hr ht hrt hf hpf ho
    (fun i => (x : ℝ) * θ i)
  have hg : Continuous g := (maskedRotationUnitary_continuous p r t f hr ht hrt hf hpf ho θ).comp
    continuous_subtype_val
  refine ⟨{ toContinuousMap := ⟨g, hg⟩, source' := ?_, target' := ?_ }⟩
  · change maskedRotationUnitary p r t f hr ht hrt hf hpf ho
      (fun i => ((0 : unitInterval) : ℝ) * θ i) = 1
    have hzero : ((0 : unitInterval) : ℝ) = 0 := rfl
    simp only [hzero, zero_mul]
    exact maskedRotationUnitary_zero p r t f hr ht hrt hf hpf ho
  · change maskedRotationUnitary p r t f hr ht hrt hf hpf ho
      (fun i => ((1 : unitInterval) : ℝ) * θ i) = _
    have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
    simp only [hone, one_mul]

omit [DecidableEq I] in
lemma maskedRotationUnitary_sub_norm_le (p r t : E) (f : I → E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : ∀ i, IsStarProjection (f i)) (hpf : ∀ i, p * f i = f i)
    (ho : ∀ i j, i ≠ j → f i * f j = 0)
    (θ φ : I → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hθ : ∀ i, |θ i - φ i| ≤ δ) :
    ‖(maskedRotationUnitary p r t f hr ht hrt hf hpf ho θ : E) -
        maskedRotationUnitary p r t f hr ht hrt hf hpf ho φ‖ ≤ 2 * δ :=
  bergFiniteRotation_sub_norm_le _ _ _ _
    (fun i _ => (maskedRotationPiece_relations p r t (f i) hr ht hrt (hf i) (hpf i)).1)
    (fun i _ => (maskedRotationPiece_relations p r t (f i) hr ht hrt (hf i) (hpf i)).2.1)
    (fun i _ j _ hij => maskedRotationPiece_support_orthogonal p r t (f i) (f j)
      hr ht hrt (hf i) (hf j) (hpf i) (hpf j) (ho i j hij)) δ hδ (fun i _ => hθ i)

/-- The two diagonal coefficients of the finite angular profile. -/
def maskedAngleCos (f : I → E) (θ : I → ℝ) : E :=
  ∑ i, (Real.cos (θ i) - 1) • f i

def maskedAngleSin (f : I → E) (θ : I → ℝ) : E :=
  ∑ i, Real.sin (θ i) • f i

omit [Fintype I] [DecidableEq I] in
/-- Polynomial comparison expression, also defined for uncorrected rows. -/
def maskedRotationModel (r t c s : E) : E :=
  1 + r * c * star r + t * c * star t + t * s * star r - r * s * star t

omit [DecidableEq I] in
lemma maskedRotationUnitary_formula (p r t : E) (f : I → E)
    (hr : star r * r = p) (ht : star t * t = p) (hrt : star r * t = 0)
    (hf : ∀ i, IsStarProjection (f i)) (hpf : ∀ i, p * f i = f i)
    (ho : ∀ i j, i ≠ j → f i * f j = 0) (θ : I → ℝ) :
    (maskedRotationUnitary p r t f hr ht hrt hf hpf ho θ : E) =
      maskedRotationModel r t (maskedAngleCos f θ) (maskedAngleSin f θ) := by
  have hterm (i : I) :
      partialIsometryBergRotation (maskedRotationPiece r t (f i)) (θ i) - 1 =
        (Real.cos (θ i) - 1) • (r * f i * star r + t * f i * star t) +
          Real.sin (θ i) • (t * f i * star r - r * f i * star t) := by
    unfold partialIsometryBergRotation bergRotationCore
    rw [(maskedRotationPiece_relations p r t (f i) hr ht hrt (hf i) (hpf i)).2.2]
    unfold bergSkew maskedRotationPiece
    rw [star_mul, star_mul, star_star, (hf i).isSelfAdjoint.star_eq]
    simp only [mul_assoc]
    module
  change 1 + (∑ i, (partialIsometryBergRotation (maskedRotationPiece r t (f i)) (θ i) - 1)) = _
  simp only [hterm, maskedRotationModel, maskedAngleCos, maskedAngleSin,
    Finset.mul_sum, Finset.sum_mul, smul_add, smul_sub, mul_smul_comm,
    smul_mul_assoc, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc]
  abel

private lemma masked_weighted_projection_norm (f : I → E)
    (hf : ∀ i, IsStarProjection (f i))
    (ho : ∀ i j, i ≠ j → f i * f j = 0)
    (w : I → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ i, |w i| ≤ M) :
    ‖∑ i, w i • f i‖ ≤ M := by
  apply orthogonalSupported_sum_norm_le _ ?_ ?_ M hM ?_
  · intro i j hij
    rw [star_smul, star_trivial, (hf i).isSelfAdjoint.star_eq,
      smul_mul_smul_comm, ho i j hij, smul_zero]
  · intro i j hij
    rw [star_smul, star_trivial, (hf j).isSelfAdjoint.star_eq,
      smul_mul_smul_comm, ho i j hij, smul_zero]
  · intro i
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (hw i) (hf i).norm_le (norm_nonneg _) hM).trans_eq (mul_one M)

lemma maskedAngleCos_norm_le (f : I → E) (hf : ∀ i, IsStarProjection (f i))
    (ho : ∀ i j, i ≠ j → f i * f j = 0) (θ : I → ℝ) :
    ‖maskedAngleCos f θ‖ ≤ 2 := by
  apply masked_weighted_projection_norm f hf ho _ 2 (by norm_num)
  intro i
  apply (abs_sub (Real.cos (θ i)) 1).trans
  rw [abs_one]
  linarith [Real.abs_cos_le_one (θ i)]

lemma maskedAngleSin_norm_le (f : I → E) (hf : ∀ i, IsStarProjection (f i))
    (ho : ∀ i j, i ≠ j → f i * f j = 0) (θ : I → ℝ) :
    ‖maskedAngleSin f θ‖ ≤ 1 :=
  masked_weighted_projection_norm f hf ho _ 1 zero_le_one (fun i => Real.abs_sin_le_one (θ i))

omit [Fintype I] [DecidableEq I] in
private lemma rotation_sandwich_difference (r t a b c : E) (ε : ℝ)
    (hr : ‖r - a‖ ≤ ε) (ht : ‖t - b‖ ≤ ε) (ha : ‖a‖ ≤ 1) (htn : ‖t‖ ≤ 1) :
    ‖r * c * star t - a * c * star b‖ ≤ 2 * ε * ‖c‖ := by
  have he : r * c * star t - a * c * star b =
      (r - a) * c * star t + a * c * star (t - b) := by
    rw [star_sub]
    noncomm_ring
  have hε : 0 ≤ ε := (norm_nonneg (r - a)).trans hr
  rw [he]
  calc
    _ ≤ ‖(r - a) * c * star t‖ + ‖a * c * star (t - b)‖ := norm_add_le _ _
    _ ≤ (‖r - a‖ * ‖c‖) * ‖t‖ + (‖a‖ * ‖c‖) * ‖t - b‖ := by
      apply add_le_add
      · simpa only [norm_star] using (norm_mul_le ((r - a) * c) (star t)).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      · simpa only [norm_star] using (norm_mul_le (a * c) (star (t - b))).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (ε * ‖c‖) * 1 + (1 * ‖c‖) * ε := by gcongr
    _ = _ := by ring

omit [Fintype I] [DecidableEq I] in
lemma maskedRotationModel_sub_norm_le (r t a b c s : E) (ε : ℝ) (hε : 0 ≤ ε)
    (hr : ‖r - a‖ ≤ ε) (ht : ‖t - b‖ ≤ ε)
    (hrn : ‖r‖ ≤ 1) (htn : ‖t‖ ≤ 1) (han : ‖a‖ ≤ 1) (hbn : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 2) (hs : ‖s‖ ≤ 1) :
    ‖maskedRotationModel r t c s - maskedRotationModel a b c s‖ ≤ 12 * ε := by
  have hrr : ‖r * c * star r - a * c * star a‖ ≤ 4 * ε :=
    (rotation_sandwich_difference r r a a c ε hr hr han hrn).trans (by nlinarith)
  have htt : ‖t * c * star t - b * c * star b‖ ≤ 4 * ε :=
    (rotation_sandwich_difference t t b b c ε ht ht hbn htn).trans (by nlinarith)
  have htr : ‖t * s * star r - b * s * star a‖ ≤ 2 * ε :=
    (rotation_sandwich_difference t r b a s ε ht hr hbn hrn).trans (by nlinarith)
  have hrt' : ‖r * s * star t - a * s * star b‖ ≤ 2 * ε :=
    (rotation_sandwich_difference r t a b s ε hr ht han htn).trans (by nlinarith)
  have he : maskedRotationModel r t c s - maskedRotationModel a b c s =
      ((r * c * star r - a * c * star a) + (t * c * star t - b * c * star b)) +
        (t * s * star r - b * s * star a) - (r * s * star t - a * s * star b) := by
    unfold maskedRotationModel
    abel
  rw [he]
  calc
    _ ≤ ‖(r * c * star r - a * c * star a) + (t * c * star t - b * c * star b)‖ +
        ‖t * s * star r - b * s * star a‖ + ‖r * s * star t - a * s * star b‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 12 * ε := by
      have hh := norm_add_le (r * c * star r - a * c * star a) (t * c * star t - b * c * star b)
      linarith

omit [Fintype I] in
/-- Masking a single cell preserves the remaining orthogonal projections. -/
lemma retainedCell_properties (e : I → E) (o : I)
    (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) :
    (∀ i, IsStarProjection (maskedBandCoefficients e o i)) ∧
      (∀ i, (1 - e o) * maskedBandCoefficients e o i = maskedBandCoefficients e o i) ∧
      (∀ i j, i ≠ j → maskedBandCoefficients e o i * maskedBandCoefficients e o j = 0) := by
  constructor
  · intro i
    by_cases hi : i = o
    · simp only [maskedBandCoefficients, ite_eq_left hi]
      exact IsStarProjection.zero E
    · simpa only [maskedBandCoefficients, ite_eq_right hi] using he i
  constructor
  · intro i
    by_cases hi : i = o
    · simp only [maskedBandCoefficients, ite_eq_left hi, mul_zero]
    · simp only [maskedBandCoefficients, ite_eq_right hi, sub_mul, one_mul,
        ho o i (Ne.symm hi), sub_zero]
  · intro i j hij
    by_cases hi : i = o
    · simp only [maskedBandCoefficients, ite_eq_left hi, zero_mul]
    by_cases hj : j = o
    · simp only [maskedBandCoefficients, ite_eq_left hj, mul_zero]
    simp only [maskedBandCoefficients, ite_eq_right hi, ite_eq_right hj, ho i j hij]

omit [Fintype I] [DecidableEq I] in
private lemma relativeInitial_norm_le (p x : E) (hp : IsStarProjection p)
    (hx : star x * x = p) : ‖x‖ ≤ 1 := by
  have hh := congrArg norm hx
  rw [CStarRing.norm_star_mul_self] at hh
  nlinarith [hp.norm_le, norm_nonneg x]

section ActualRows
variable [PartialOrder E] [StarOrderedRing E]

omit [Fintype I] [DecidableEq I] in
/-- The rotation unitary is constructed for the actual cyclic partition and
masked iterated row words. Its polynomial comparison error is independent
of the number of cells. This does not assert the cocycle equation. -/
lemma exists_actual_masked_rotation (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (m : ℕ) (hm : 1 < 2 ^ m) (θ : ZMod (2 ^ m) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (e : ZMod (2 ^ m) → E) (u : unitary E),
      (∀ j, IsStarProjection (e j)) ∧
      (∀ j k, j ≠ k → e j * e k = 0) ∧ (∑ j, e j) = 1 ∧
      Joined (1 : unitary E) u ∧
      ‖(u : E) - maskedRotationModel
        (maskedTowerBand e (Equiv.addRight 2)
          (fun j => finiteRowShiftIterate s j.val (s 0 * s 0)) 0)
        (maskedTowerBand e (Equiv.addRight 1)
          (fun j => finiteRowShiftIterate s j.val (s 1)) 0)
        (maskedAngleCos (maskedBandCoefficients e 0) θ)
        (maskedAngleSin (maskedBandCoefficients e 0) θ)‖ ≤ 12 * ε := by
  obtain ⟨e, r, t, he, ho, hesum, hrp, htp, hr, ht, hrt, hra, htb⟩ :=
    exists_masked_binary_rotation_rows s hs hsum m hm ε hε
  let f := maskedBandCoefficients e 0
  obtain ⟨hf, hpf, hfo⟩ := retainedCell_properties e 0 he ho
  let u := maskedRotationUnitary (1 - e 0) r t f hr ht hrt hf hpf hfo θ
  refine ⟨e, u, he, ho, hesum, maskedRotationUnitary_joined _ _ _ _ _ _ _ _ _ _ θ, ?_⟩
  rw [maskedRotationUnitary_formula]
  have hpn : IsStarProjection (1 - e 0) := (he 0).one_sub
  have hsn (i : Fin 2) : ‖s i‖ ≤ 1 :=
    relativeInitial_norm_le 1 (s i) (IsStarProjection.one E) (by simpa only [ite_true] using hs i i)
  have han : ‖s 0 * s 0‖ ≤ 1 :=
    (norm_mul_le _ _).trans ((mul_le_mul (hsn 0) (hsn 0) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hband (x : E) (hx : ‖x‖ ≤ 1) (d : ZMod (2 ^ m)) :
      ‖maskedTowerBand e (Equiv.addRight d)
        (fun j => finiteRowShiftIterate s j.val x) 0‖ ≤ 1 := by
    apply towerBand_norm_le e (Equiv.addRight d) _ he ho 1 zero_le_one
    intro j
    by_cases hj : j = 0
    · simp only [maskedBandCoefficients, ite_eq_left hj, norm_zero, zero_le_one]
    · simp only [maskedBandCoefficients, ite_eq_right hj]
      exact (binaryRowIterate_norm_le s hs j.val x).trans hx
  exact maskedRotationModel_sub_norm_le _ _ _ _ _ _ ε hε.le hra.le htb.le
    (relativeInitial_norm_le _ _ hpn hr) (relativeInitial_norm_le _ _ hpn ht)
    (hband _ han 2) (hband _ (hsn 1) 1)
    (maskedAngleCos_norm_le f hf hfo θ) (maskedAngleSin_norm_le f hf hfo θ)

end ActualRows

end WeakPureInfiniteness

end

end OAI
