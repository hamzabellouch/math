import OAI.Analysis.OInfinity.CornerContraction

namespace OAI

/-! # Controlled cancellation paths in a fixed corner

A relative unitary compressed into one range cancels its adjoint compressed
into an orthogonal equivalent range by an explicit quarter-turn. The path
has an angular Lipschitz bound independent of that unitary. Its complement
is retained throughout; this does not construct a fixed approximately
central corner for a growing family of cocycles.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Extend a unitary in the initial corner of `a` by the identity elsewhere. -/
def cornerCompression (a z : E) : E := a * z * star a + (1 - a * star a)

lemma cornerCompression_star (a z : E) :
    star (cornerCompression a z) = cornerCompression a (star z) := by
  simp only [cornerCompression, star_add, star_sub, star_mul, star_star, star_one]
  noncomm_ring

lemma cornerCompression_mul (q a z w : E) (haa : star a * a = q)
    (haq : a * q = a) (hzq : z * q = z) :
    cornerCompression a z * cornerCompression a w = cornerCompression a (z * w) := by
  have hp : (a * star a) * (a * star a) = a * star a := by
    calc
      _ = a * (star a * a) * star a := by noncomm_ring
      _ = _ := by rw [haa, haq]
  have hza : (a * z * star a) * (a * star a) = a * z * star a := by
    calc
      _ = a * (z * (star a * a)) * star a := by noncomm_ring
      _ = _ := by rw [haa, hzq]
  have haw : (a * star a) * (a * w * star a) = a * w * star a := by
    calc
      _ = (a * (star a * a)) * w * star a := by noncomm_ring
      _ = _ := by rw [haa, haq]
  have hzw : (a * z * star a) * (a * w * star a) = a * (z * w) * star a := by
    calc
      _ = a * (z * (star a * a)) * w * star a := by noncomm_ring
      _ = _ := by rw [haa, hzq]; noncomm_ring
  calc
    _ = (a * z * star a) * (a * w * star a) + a * z * star a -
        (a * z * star a) * (a * star a) + a * w * star a -
        (a * star a) * (a * w * star a) + 1 - a * star a - a * star a +
        (a * star a) * (a * star a) := by
      unfold cornerCompression
      noncomm_ring
    _ = cornerCompression a (z * w) := by
      rw [hzw, hza, haw, hp]
      unfold cornerCompression
      noncomm_ring

lemma cornerCompression_unit (q a : E) (haq : a * q = a) :
    cornerCompression a q = 1 := by
  unfold cornerCompression
  rw [haq]
  noncomm_ring

lemma cornerCompression_mem (q a z : E) (hqstar : star q = q)
    (haa : star a * a = q) (haq : a * q = a)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q) :
    cornerCompression a z ∈ unitary E := by
  have hszq : star z * q = star z := by
    simpa only [star_mul, hqstar] using congrArg star hqz
  constructor
  · rw [cornerCompression_star, cornerCompression_mul q a (star z) z haa haq hszq,
      hzz, cornerCompression_unit q a haq]
  · rw [cornerCompression_star, cornerCompression_mul q a z (star z) haa haq hzq,
      hzz', cornerCompression_unit q a haq]

lemma cornerCompression_conjugate (u a z : E) (hu : u * star u = 1) :
    u * cornerCompression a z * star u = cornerCompression (u * a) z := by
  simp only [cornerCompression, star_mul]
  noncomm_ring [hu]

lemma cornerCompression_neg (a z : E) :
    cornerCompression (-a) z = cornerCompression a z := by
  simp only [cornerCompression, star_neg, neg_mul, mul_neg, neg_neg]

/-- The cancellation uses the rotation from the first range to the second. -/
def cornerCancellationPath (a b z : E) (θ : ℝ) : E :=
  cornerCompression a z * partialIsometryBergRotation (b * star a) θ *
    cornerCompression b (star z) * star (partialIsometryBergRotation (b * star a) θ)

lemma cornerRotation_relations (q a b : E) (haa : star a * a = q)
    (hbb : star b * b = q) (hab : star a * b = 0)
    (haq : a * q = a) (hbq : b * q = b) :
    (b * star a) * star (b * star a) * (b * star a) = b * star a ∧
      (b * star a) * (b * star a) = 0 ∧
      star (b * star a) * (b * star a) = a * star a ∧
      (b * star a) * star (b * star a) = b * star b := by
  have hi : star (b * star a) * (b * star a) = a * star a := by
    rw [star_mul, star_star]
    calc
      _ = (a * (star b * b)) * star a := by noncomm_ring
      _ = _ := by rw [hbb, haq]
  have hf : (b * star a) * star (b * star a) = b * star b := by
    rw [star_mul, star_star]
    calc
      _ = (b * (star a * a)) * star b := by noncomm_ring
      _ = _ := by rw [haa, hbq]
  refine ⟨?_, ?_, hi, hf⟩
  · rw [hf]
    calc
      _ = (b * (star b * b)) * star a := by noncomm_ring
      _ = _ := by rw [hbb, hbq]
  · calc
      _ = b * (star a * b) * star a := by noncomm_ring
      _ = 0 := by rw [hab, mul_zero, zero_mul]

lemma cornerRotation_quarter_mul_second (q a b : E)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (haq : a * q = a) (hbq : b * q = b) :
    partialIsometryBergRotation (b * star a) (Real.pi / 2) * b = -a := by
  obtain ⟨_, _, hi, hf⟩ := cornerRotation_relations q a b haa hbb hab haq hbq
  have hr : partialIsometryBergRotation (b * star a) (Real.pi / 2) =
      (1 - a * star a - b * star b) + (b * star a - a * star b) := by
    unfold partialIsometryBergRotation
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp only [bergRotationCore, zero_smul, one_smul, add_zero]
    unfold bergSupport bergSkew
    rw [hi, hf]
    simp only [star_mul, star_star]
    noncomm_ring
  have habb : (a * star a) * b = 0 := by rw [mul_assoc, hab, mul_zero]
  have hbbb : (b * star b) * b = b := by rw [mul_assoc, hbb, hbq]
  have hbaba : (b * star a) * b = 0 := by rw [mul_assoc, hab, mul_zero]
  have habb' : (a * star b) * b = a := by rw [mul_assoc, hbb, haq]
  rw [hr, add_mul, sub_mul, sub_mul, one_mul, sub_mul,
    habb, hbbb, hbaba, habb']
  abel

lemma cornerCancellationPath_zero (a b z : E) :
    cornerCancellationPath a b z 0 = cornerCompression a z * cornerCompression b (star z) := by
  simp only [cornerCancellationPath, partialIsometryBergRotation_zero, star_one, mul_one]

lemma cornerCancellationPath_continuous (a b z : E) :
    Continuous (cornerCancellationPath a b z) := by
  unfold cornerCancellationPath
  exact (((continuous_const.mul (partialIsometryBergRotation_continuous _)).mul
    continuous_const).mul (partialIsometryBergRotation_continuous _).star)

lemma cornerCancellationPath_mem (q a b z : E) (hqstar : star q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (haq : a * q = a) (hbq : b * q = b)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q) (θ : ℝ) :
    cornerCancellationPath a b z θ ∈ unitary E := by
  have hszq : star z * q = star z := by
    simpa only [star_mul, hqstar] using congrArg star hqz
  have hqsz : q * star z = star z := by
    simpa only [star_mul, hqstar] using congrArg star hzq
  have ha := cornerCompression_mem q a z hqstar haa haq hqz hzq hzz hzz'
  have hb := cornerCompression_mem q b (star z) hqstar hbb hbq hqsz hszq
    (by simpa only [star_star] using hzz') (by simpa only [star_star] using hzz)
  obtain ⟨hr, hrr, _, _⟩ := cornerRotation_relations q a b haa hbb hab haq hbq
  have hR := partialIsometryBergRotation_mem (b * star a) hr hrr θ
  exact (unitary E).mul_mem ((unitary E).mul_mem ((unitary E).mul_mem ha hR) hb)
    (Unitary.star_mem hR)

lemma cornerCancellationPath_quarter (q a b z : E) (hqstar : star q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (haq : a * q = a) (hbq : b * q = b)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q) :
    cornerCancellationPath a b z (Real.pi / 2) = 1 := by
  obtain ⟨hr, hrr, _, _⟩ := cornerRotation_relations q a b haa hbb hab haq hbq
  have hR := partialIsometryBergRotation_mem (b * star a) hr hrr (Real.pi / 2)
  have hc : partialIsometryBergRotation (b * star a) (Real.pi / 2) *
      cornerCompression b (star z) * star (partialIsometryBergRotation (b * star a) (Real.pi / 2)) =
      cornerCompression a (star z) := by
    rw [cornerCompression_conjugate _ _ _ hR.2,
      cornerRotation_quarter_mul_second q a b haa hbb hab haq hbq, cornerCompression_neg]
  calc
    _ = cornerCompression a z *
        (partialIsometryBergRotation (b * star a) (Real.pi / 2) *
          cornerCompression b (star z) *
            star (partialIsometryBergRotation (b * star a) (Real.pi / 2))) := by
      unfold cornerCancellationPath
      noncomm_ring
    _ = cornerCompression a z * cornerCompression a (star z) := by rw [hc]
    _ = 1 := by
      rw [← cornerCompression_star]
      exact (cornerCompression_mem q a z hqstar haa haq hqz hzq hzz hzz').2

lemma cornerCancellationPath_sub_norm_le (q a b z : E) (hqstar : star q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (haq : a * q = a) (hbq : b * q = b)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q) (θ φ : ℝ) :
    ‖cornerCancellationPath a b z θ - cornerCancellationPath a b z φ‖ ≤ 4 * |θ - φ| := by
  have hszq : star z * q = star z := by
    simpa only [star_mul, hqstar] using congrArg star hqz
  have hqsz : q * star z = star z := by
    simpa only [star_mul, hqstar] using congrArg star hzq
  have hA := cornerCompression_mem q a z hqstar haa haq hqz hzq hzz hzz'
  have hB := cornerCompression_mem q b (star z) hqstar hbb hbq hqsz hszq
    (by simpa only [star_star] using hzz') (by simpa only [star_star] using hzz)
  obtain ⟨hr, hrr, _, _⟩ := cornerRotation_relations q a b haa hbb hab haq hbq
  let R := partialIsometryBergRotation (b * star a)
  have hR (t : ℝ) := partialIsometryBergRotation_mem (b * star a) hr hrr t
  have he : cornerCancellationPath a b z θ - cornerCancellationPath a b z φ =
      cornerCompression a z * (R θ - R φ) * cornerCompression b (star z) * star (R θ) +
        cornerCompression a z * R φ * cornerCompression b (star z) * (star (R θ) - star (R φ)) := by
    dsimp only [R, cornerCancellationPath]
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖cornerCompression a z * (R θ - R φ) * cornerCompression b (star z) * star (R θ)‖ +
        ‖cornerCompression a z * R φ * cornerCompression b (star z) * (star (R θ) - star (R φ))‖ := norm_add_le _ _
    _ = ‖R θ - R φ‖ + ‖R θ - R φ‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (hR θ)),
        CStarRing.norm_mul_mem_unitary _ hB, CStarRing.norm_mem_unitary_mul _ hA,
        CStarRing.norm_mem_unitary_mul _ ((unitary E).mul_mem ((unitary E).mul_mem hA (hR φ)) hB),
        ← star_sub, norm_star]
    _ ≤ 2 * |θ - φ| + 2 * |θ - φ| := add_le_add
      (partialIsometryBergRotation_sub_norm_le _ hr hrr θ φ)
      (partialIsometryBergRotation_sub_norm_le _ hr hrr θ φ)
    _ = 4 * |θ - φ| := by ring

/-- An actual unitary path with fixed angular cost, including both endpoints. -/
lemma exists_controlled_cornerCancellation_path (q a b z : E) (hqstar : star q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (haq : a * q = a) (hbq : b * q = b)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q) :
    ∃ u : ℝ → unitary E, Continuous u ∧
      (u 0 : E) = cornerCompression a z * cornerCompression b (star z) ∧
      (u (Real.pi / 2) : E) = 1 ∧
      ∀ θ φ, ‖(u θ : E) - u φ‖ ≤ 4 * |θ - φ| := by
  let u (θ : ℝ) : unitary E := ⟨cornerCancellationPath a b z θ,
    cornerCancellationPath_mem q a b z hqstar haa hbb hab haq hbq hqz hzq hzz hzz' θ⟩
  refine ⟨u, (cornerCancellationPath_continuous a b z).subtype_mk _,
    cornerCancellationPath_zero a b z,
    cornerCancellationPath_quarter q a b z hqstar haa hbb hab haq hbq hqz hzq hzz hzz', ?_⟩
  exact cornerCancellationPath_sub_norm_le q a b z hqstar haa hbb hab haq hbq hqz hzq hzz hzz'

end WeakPureInfiniteness

end

end OAI
