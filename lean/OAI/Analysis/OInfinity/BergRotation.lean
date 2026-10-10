import Mathlib

namespace OAI

/-! # Corner rotations for the O∞ half-flip boundary

A square-zero partial isometry determines a genuine rotation between its
orthogonal initial and final corners. The formulas below retain the terminal
corner explicitly. They do not assert that a finite recursive tower has a
small terminal defect.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The sum of the orthogonal initial and final projections. -/
def bergSupport (a : E) : E := star a * a + a * star a

/-- The skew-adjoint generator of the corner rotation. -/
def bergSkew (a : E) : E := a - star a

private lemma berg_word_relations (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    a * (star a * a) = a ∧ star a * (a * star a) = star a ∧
      (∀ x : E, a * (a * x) = 0) ∧ (∀ x : E, star a * (star a * x) = 0) := by
  have h1 : a * (star a * a) = a := by simpa only [mul_assoc] using ha
  have h2 : star a * (a * star a) = star a := by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star ha
  have hss : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star haa
  refine ⟨h1, h2, ?_, ?_⟩
  · intro x
    rw [← mul_assoc, haa, zero_mul]
  · intro x
    rw [← mul_assoc, hss, zero_mul]

lemma bergSupport_star (a : E) : star (bergSupport a) = bergSupport a := by
  simp only [bergSupport, star_add, star_mul, star_star]

lemma bergSkew_star (a : E) : star (bergSkew a) = -bergSkew a := by
  simp only [bergSkew, star_sub, star_star]
  abel

lemma bergSupport_sq (a : E) (ha : a * star a * a = a) (haa : a * a = 0) :
    bergSupport a * bergSupport a = bergSupport a := by
  obtain ⟨h1, h2, h3, h4⟩ := berg_word_relations a ha haa
  unfold bergSupport
  noncomm_ring [h1, h2, h3, h4]

lemma bergSkew_sq (a : E) (haa : a * a = 0) :
    bergSkew a * bergSkew a = -bergSupport a := by
  have hss : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star haa
  unfold bergSkew bergSupport
  noncomm_ring [haa, hss]

lemma bergSupport_mul_skew (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    bergSupport a * bergSkew a = bergSkew a := by
  obtain ⟨h1, h2, h3, h4⟩ := berg_word_relations a ha haa
  have hss : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star haa
  unfold bergSupport bergSkew
  noncomm_ring [h1, h2, h3, h4, haa, hss]

lemma bergSkew_mul_support (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    bergSkew a * bergSupport a = bergSkew a := by
  obtain ⟨h1, h2, h3, h4⟩ := berg_word_relations a ha haa
  unfold bergSupport bergSkew
  noncomm_ring [h1, h2, h3, h4]

/-- Polynomial form of a rotation; `c` and `s` will be cosine and sine. -/
def bergRotationCore (a : E) (c s : ℝ) : E :=
  (1 - bergSupport a) + c • bergSupport a + s • bergSkew a

lemma bergRotationCore_star (a : E) (c s : ℝ) :
    star (bergRotationCore a c s) = bergRotationCore a c (-s) := by
  simp only [bergRotationCore, star_add, star_sub, star_one, star_smul,
    star_trivial, bergSupport_star, bergSkew_star, smul_neg, neg_smul]

lemma bergRotationCore_one_zero (a : E) : bergRotationCore a 1 0 = 1 := by
  simp only [bergRotationCore, one_smul, zero_smul, add_zero]
  abel

lemma bergRotationCore_mul (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) (c s d t : ℝ) :
    bergRotationCore a c s * bergRotationCore a d t =
      bergRotationCore a (c * d - s * t) (c * t + s * d) := by
  let p := bergSupport a
  let k := bergSkew a
  let e := 1 - p
  have hpp : p * p = p := bergSupport_sq a ha haa
  have hkk : k * k = -p := bergSkew_sq a haa
  have hpk : p * k = k := bergSupport_mul_skew a ha haa
  have hkp : k * p = k := bergSkew_mul_support a ha haa
  have hee : e * e = e := by dsimp only [e]; noncomm_ring [hpp]
  have hep : e * p = 0 := by dsimp only [e]; noncomm_ring [hpp]
  have hpe : p * e = 0 := by dsimp only [e]; noncomm_ring [hpp]
  have hek : e * k = 0 := by dsimp only [e]; noncomm_ring [hpk]
  have hke : k * e = 0 := by dsimp only [e]; noncomm_ring [hkp]
  change (e + c • p + s • k) * (e + d • p + t • k) =
    e + (c * d - s * t) • p + (c * t + s * d) • k
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hee, hep, hpe, hek, hke, hpp, hpk, hkp, hkk, smul_zero,
    zero_add, add_zero, smul_neg]
  module

/-- Rotate from the initial corner toward the final corner by angle `θ`. -/
def partialIsometryBergRotation (a : E) (θ : ℝ) : E :=
  bergRotationCore a (Real.cos θ) (Real.sin θ)

lemma partialIsometryBergRotation_star (a : E) (θ : ℝ) :
    star (partialIsometryBergRotation a θ) = partialIsometryBergRotation a (-θ) := by
  simp only [partialIsometryBergRotation, bergRotationCore_star, Real.cos_neg, Real.sin_neg]

lemma partialIsometryBergRotation_mul (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) (θ φ : ℝ) :
    partialIsometryBergRotation a θ * partialIsometryBergRotation a φ =
      partialIsometryBergRotation a (θ + φ) := by
  simp only [partialIsometryBergRotation, bergRotationCore_mul a ha haa,
    Real.cos_add, Real.sin_add]
  congr 1
  ring

@[simp] lemma partialIsometryBergRotation_zero (a : E) :
    partialIsometryBergRotation a 0 = 1 := by
  simp only [partialIsometryBergRotation, Real.cos_zero, Real.sin_zero,
    bergRotationCore_one_zero]

lemma partialIsometryBergRotation_mem (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) (θ : ℝ) :
    partialIsometryBergRotation a θ ∈ unitary E := by
  constructor
  · rw [partialIsometryBergRotation_star, partialIsometryBergRotation_mul a ha haa,
      neg_add_cancel, partialIsometryBergRotation_zero]
  · rw [partialIsometryBergRotation_star, partialIsometryBergRotation_mul a ha haa,
      add_neg_cancel, partialIsometryBergRotation_zero]

def partialIsometryBergRotationUnitary (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) (θ : ℝ) : unitary E :=
  ⟨partialIsometryBergRotation a θ, partialIsometryBergRotation_mem a ha haa θ⟩

lemma partialIsometryBergRotation_continuous (a : E) :
    Continuous (partialIsometryBergRotation a) := by
  unfold partialIsometryBergRotation bergRotationCore
  fun_prop

lemma partialIsometryBergRotationUnitary_continuous (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    Continuous (partialIsometryBergRotationUnitary a ha haa) :=
  (partialIsometryBergRotation_continuous a).subtype_mk _

/-- The explicit angular path supplies connectedness, including the terminal
quarter-turn, without selecting a logarithm. -/
lemma partialIsometryBergRotationUnitary_joined (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) (θ : ℝ) :
    Joined (1 : unitary E) (partialIsometryBergRotationUnitary a ha haa θ) := by
  let f (t : unitInterval) := partialIsometryBergRotationUnitary a ha haa (θ * (t : ℝ))
  have hf : Continuous f := (partialIsometryBergRotationUnitary_continuous a ha haa).comp
    (continuous_const.mul continuous_subtype_val)
  refine ⟨{ toContinuousMap := ⟨f, hf⟩, source' := ?_, target' := ?_ }⟩
  · apply Subtype.ext
    change partialIsometryBergRotation a (θ * ((0 : unitInterval) : ℝ)) = 1
    simp
  · apply Subtype.ext
    change partialIsometryBergRotation a (θ * ((1 : unitInterval) : ℝ)) =
      partialIsometryBergRotation a θ
    simp

lemma bergSupport_norm_le_one (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) : ‖bergSupport a‖ ≤ 1 := by
  have h := congrArg norm (bergSupport_sq a ha haa)
  have hs : IsSelfAdjoint (bergSupport a) := bergSupport_star a
  rw [hs.norm_mul_self] at h
  nlinarith [norm_nonneg (bergSupport a)]

lemma bergSkew_norm_le_one (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) : ‖bergSkew a‖ ≤ 1 := by
  have he : star (bergSkew a) * bergSkew a = bergSupport a := by
    rw [bergSkew_star, neg_mul, bergSkew_sq a haa, neg_neg]
  have h := congrArg norm he
  rw [CStarRing.norm_star_mul_self] at h
  have hp := bergSupport_norm_le_one a ha haa
  nlinarith [norm_nonneg (bergSkew a)]

/-- The norm cost of changing an angular terminal boundary is at most twice
its angular change, independently of the size of the ambient algebra. -/
lemma partialIsometryBergRotation_sub_norm_le (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) (θ φ : ℝ) :
    ‖partialIsometryBergRotation a θ - partialIsometryBergRotation a φ‖ ≤
      2 * |θ - φ| := by
  have he : partialIsometryBergRotation a θ - partialIsometryBergRotation a φ =
      (Real.cos θ - Real.cos φ) • bergSupport a +
        (Real.sin θ - Real.sin φ) • bergSkew a := by
    unfold partialIsometryBergRotation bergRotationCore
    module
  have hp := bergSupport_norm_le_one a ha haa
  have hk := bergSkew_norm_le_one a ha haa
  rw [he]
  calc
    _ ≤ ‖(Real.cos θ - Real.cos φ) • bergSupport a‖ +
        ‖(Real.sin θ - Real.sin φ) • bergSkew a‖ := norm_add_le _ _
    _ = |Real.cos θ - Real.cos φ| * ‖bergSupport a‖ +
        |Real.sin θ - Real.sin φ| * ‖bergSkew a‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |Real.cos θ - Real.cos φ| + |Real.sin θ - Real.sin φ| := by
      exact add_le_add
        (by simpa using mul_le_mul_of_nonneg_left hp (abs_nonneg _))
        (by simpa using mul_le_mul_of_nonneg_left hk (abs_nonneg _))
    _ ≤ |θ - φ| + |θ - φ| :=
      add_le_add (Real.abs_cos_sub_cos_le θ φ) (Real.abs_sin_sub_sin_le θ φ)
    _ = _ := by ring

/-- Exact covariance of the two corner generators passes through the
rotation polynomial. This is the local shift identity used at a tower seam. -/
lemma partialIsometryBergRotation_intertwining (a b x : E)
    (ha : x * a = b * x) (hs : x * star a = star b * x) (θ : ℝ) :
    x * partialIsometryBergRotation a θ = partialIsometryBergRotation b θ * x := by
  have hp : x * bergSupport a = bergSupport b * x := by
    unfold bergSupport
    calc
      _ = (x * star a) * a + (x * a) * star a := by noncomm_ring
      _ = (star b * x) * a + (b * x) * star a := by rw [ha, hs]
      _ = star b * (x * a) + b * (x * star a) := by noncomm_ring
      _ = _ := by rw [ha, hs]; noncomm_ring
  have hk : x * bergSkew a = bergSkew b * x := by
    simp only [bergSkew, mul_sub, sub_mul, ha, hs]
  unfold partialIsometryBergRotation bergRotationCore
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul,
    mul_smul_comm, smul_mul_assoc, hp, hk]

/-- At a terminal seam, exact covariance leaves only the change of angle.
The bound states the defect that still has to be controlled by the chosen
finite tower; it does not assume that this angle change is already small. -/
lemma partialIsometryBergRotation_seam_norm_le (a b x : E)
    (hb : b * star b * b = b) (hbb : b * b = 0)
    (ha : x * a = b * x) (hs : x * star a = star b * x) (θ φ : ℝ) :
    ‖partialIsometryBergRotation b θ * x - x * partialIsometryBergRotation a φ‖ ≤
      (2 * |θ - φ|) * ‖x‖ := by
  rw [partialIsometryBergRotation_intertwining a b x ha hs φ, ← sub_mul]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (partialIsometryBergRotation_sub_norm_le b hb hbb θ φ) (norm_nonneg x))

/-- The quarter-turn carries the initial projection onto the given partial
isometry. This explicitly records which terminal corner is moved. -/
lemma partialIsometryBergRotation_quarter_mul_initial (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    partialIsometryBergRotation a (Real.pi / 2) * (star a * a) = a := by
  obtain ⟨h1, h2, h3, h4⟩ := berg_word_relations a ha haa
  simp only [partialIsometryBergRotation, Real.cos_pi_div_two, Real.sin_pi_div_two,
    bergRotationCore, zero_smul, one_smul, add_zero]
  unfold bergSupport bergSkew
  noncomm_ring [h1, h2, h3, h4]

/-- Two simultaneous corner rotations. The right corner is moved first. -/
def doubleBergRotation (a b : E) (θ : ℝ) : E :=
  partialIsometryBergRotation b θ * partialIsometryBergRotation a θ

lemma doubleBergRotation_mem (a b : E)
    (ha : a * star a * a = a) (haa : a * a = 0)
    (hb : b * star b * b = b) (hbb : b * b = 0) (θ : ℝ) :
    doubleBergRotation a b θ ∈ unitary E :=
  (unitary E).mul_mem (partialIsometryBergRotation_mem b hb hbb θ)
    (partialIsometryBergRotation_mem a ha haa θ)

lemma doubleBergRotation_continuous (a b : E) : Continuous (doubleBergRotation a b) :=
  (partialIsometryBergRotation_continuous b).mul (partialIsometryBergRotation_continuous a)

@[simp] lemma doubleBergRotation_zero (a b : E) : doubleBergRotation a b 0 = 1 := by
  simp only [doubleBergRotation, partialIsometryBergRotation_zero, one_mul]

lemma doubleBergRotation_sub_norm_le (a b : E)
    (ha : a * star a * a = a) (haa : a * a = 0)
    (hb : b * star b * b = b) (hbb : b * b = 0) (θ φ : ℝ) :
    ‖doubleBergRotation a b θ - doubleBergRotation a b φ‖ ≤ 4 * |θ - φ| := by
  have he : doubleBergRotation a b θ - doubleBergRotation a b φ =
      partialIsometryBergRotation b θ *
          (partialIsometryBergRotation a θ - partialIsometryBergRotation a φ) +
        (partialIsometryBergRotation b θ - partialIsometryBergRotation b φ) *
          partialIsometryBergRotation a φ := by
    unfold doubleBergRotation
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖partialIsometryBergRotation b θ *
        (partialIsometryBergRotation a θ - partialIsometryBergRotation a φ)‖ +
        ‖(partialIsometryBergRotation b θ - partialIsometryBergRotation b φ) *
          partialIsometryBergRotation a φ‖ := norm_add_le _ _
    _ = ‖partialIsometryBergRotation a θ - partialIsometryBergRotation a φ‖ +
        ‖partialIsometryBergRotation b θ - partialIsometryBergRotation b φ‖ := by
      rw [CStarRing.norm_mem_unitary_mul _ (partialIsometryBergRotation_mem b hb hbb θ),
        CStarRing.norm_mul_mem_unitary _ (partialIsometryBergRotation_mem a ha haa φ)]
    _ ≤ 2 * |θ - φ| + 2 * |θ - φ| :=
      add_le_add (partialIsometryBergRotation_sub_norm_le a ha haa θ φ)
        (partialIsometryBergRotation_sub_norm_le b hb hbb θ φ)
    _ = _ := by ring

lemma doubleBergRotation_quarter_mul_initial (a b : E)
    (ha : a * star a * a = a) (haa : a * a = 0)
    (hb : b * star b * b = b) (hbb : b * b = 0)
    (hba : (star b * b) * a = a) :
    doubleBergRotation a b (Real.pi / 2) * (star a * a) = b * a := by
  rw [doubleBergRotation, mul_assoc,
    partialIsometryBergRotation_quarter_mul_initial a ha haa]
  calc
    _ = partialIsometryBergRotation b (Real.pi / 2) * ((star b * b) * a) := by rw [hba]
    _ = (partialIsometryBergRotation b (Real.pi / 2) * (star b * b)) * a := by
      noncomm_ring
    _ = b * a := by rw [partialIsometryBergRotation_quarter_mul_initial b hb hbb]

private lemma bergCompletion_corner_data (v r : E)
    (hv : v * star v * v = v) (hr : star r * r = 1)
    (hpr : (star v * v) * r = 0) (hqr : (v * star v) * r = 0) :
    let p := star v * v
    let a := r * p
    let b := v * star r
    a * star a * a = a ∧ a * a = 0 ∧ b * star b * b = b ∧ b * b = 0 ∧
      star a * a = p ∧ (star b * b) * a = a ∧ b * a = v := by
  let p := star v * v
  let a := r * p
  let b := v * star r
  change a * star a * a = a ∧ a * a = 0 ∧ b * star b * b = b ∧ b * b = 0 ∧
    star a * a = p ∧ (star b * b) * a = a ∧ b * a = v
  have hp : star p = p := by simp only [p, star_mul, star_star]
  have hpp : p * p = p := by
    dsimp only [p]
    calc
      _ = star v * (v * star v * v) := by noncomm_ring
      _ = _ := by rw [hv]
  have hrv : star r * v = 0 := by
    have hz : star r * (v * star v) = 0 := by
      simpa only [star_mul, star_star, star_zero] using congrArg star hqr
    calc
      _ = star r * (v * star v * v) := by rw [hv]
      _ = 0 := by rw [← mul_assoc, hz, zero_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [a]
    rw [star_mul, hp]
    calc
      _ = r * (p * p) * (star r * r) * p := by noncomm_ring
      _ = _ := by rw [hpp, hr, mul_one, mul_assoc, hpp]
  · dsimp only [a]
    calc
      _ = r * (p * r) * p := by noncomm_ring
      _ = 0 := by rw [hpr, mul_zero, zero_mul]
  · dsimp only [b]
    rw [star_mul, star_star]
    calc
      _ = v * (star r * r) * star v * v * star r := by noncomm_ring
      _ = _ := by rw [hr, mul_one, hv]
  · dsimp only [b]
    calc
      _ = v * (star r * v) * star r := by noncomm_ring
      _ = 0 := by rw [hrv, mul_zero, zero_mul]
  · dsimp only [a]
    rw [star_mul, hp]
    calc
      _ = p * (star r * r) * p := by noncomm_ring
      _ = p := by rw [hr, mul_one, hpp]
  · dsimp only [a, b]
    rw [star_mul, star_star]
    calc
      _ = r * p * (star r * r) * p := by dsimp only [p]; noncomm_ring
      _ = _ := by rw [hr, mul_one, mul_assoc, hpp]
  · dsimp only [a, b]
    calc
      _ = v * (star r * r) * p := by noncomm_ring
      _ = v := by rw [hr, mul_one]; simpa only [p, mul_assoc] using hv

/-- An explicit angular path completing a partial isometry through a common
spare range. Only its quarter-turn endpoint is required to extend `v`. -/
def partialIsometryBergCompletion (v r : E) (θ : ℝ) : E :=
  doubleBergRotation (r * (star v * v)) (v * star r) θ

/-- The completion path is uniformly controlled in its angular parameter. -/
lemma exists_controlled_berg_completion_path (v r : E)
    (hv : v * star v * v = v) (hr : star r * r = 1)
    (hpr : (star v * v) * r = 0) (hqr : (v * star v) * r = 0) :
    ∃ u : ℝ → unitary E, Continuous u ∧ (u 0 : E) = 1 ∧
      (u (Real.pi / 2) : E) * (star v * v) = v ∧
      (∀ θ, (u θ : E) = partialIsometryBergCompletion v r θ) ∧
      ∀ θ φ, ‖(u θ : E) - u φ‖ ≤ 4 * |θ - φ| := by
  obtain ⟨ha, haa, hb, hbb, hai, hba, hcomp⟩ :=
    bergCompletion_corner_data v r hv hr hpr hqr
  let a := r * (star v * v)
  let b := v * star r
  let u (θ : ℝ) : unitary E :=
    ⟨doubleBergRotation a b θ, doubleBergRotation_mem a b ha haa hb hbb θ⟩
  refine ⟨u, (doubleBergRotation_continuous a b).subtype_mk _,
    doubleBergRotation_zero a b, ?_, fun _ => rfl, ?_⟩
  · change doubleBergRotation a b (Real.pi / 2) * (star v * v) = v
    rw [← hai, doubleBergRotation_quarter_mul_initial a b ha haa hb hbb hba, hcomp]
  · intro θ φ
    exact doubleBergRotation_sub_norm_le a b ha haa hb hbb θ φ

end WeakPureInfiniteness

end

end OAI
