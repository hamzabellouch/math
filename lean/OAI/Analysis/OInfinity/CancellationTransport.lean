import OAI.Analysis.OInfinity.CancellationBandwidth
import OAI.Analysis.OInfinity.ToeplitzCompression

namespace OAI

/-! # Actual tower transport for the cancellation path

Two row words move a cyclic tower by their respective degrees. If the
unitary coefficient almost commutes with that tower, the explicit
cancellation path has three transported components, with a uniform error
independent of the tower height. No gauge action on the ambient algebra is
assumed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma transport_product_bound (x y e f g : E) :
    ‖x * y * e - g * (x * y)‖ ≤
      ‖x‖ * ‖y * e - f * y‖ + ‖x * f - g * x‖ * ‖y‖ := by
  have he : x * y * e - g * (x * y) =
      x * (y * e - f * y) + (x * f - g * x) * y := by noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

private lemma tower_adjoint_transport {N : ℕ} (e : ZMod N → E)
    (he : ∀ k, star (e k) = e k) (b : E) (d : ZMod N) (δ : ℝ)
    (hb : ∀ k, ‖b * e k - e (k + d) * b‖ ≤ δ) (k : ZMod N) :
    ‖star b * e k - e (k - d) * star b‖ ≤ δ := by
  have h := hb (k - d)
  rw [sub_add_cancel] at h
  have hs : ‖b * e (k - d) - e k * b‖ =
      ‖star b * e k - e (k - d) * star b‖ := by
    rw [← norm_star (b * e (k - d) - e k * b), star_sub, star_mul, star_mul, he, he]
    exact norm_sub_rev _ _
  rwa [hs] at h

/-- A word, a nearly central coefficient, and an adjoint word transport
by the difference of the two word degrees. -/
lemma tower_sandwich_transport {N : ℕ} (e : ZMod N → E)
    (he : ∀ k, star (e k) = e k) (a b v : E) (da db : ZMod N)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (han : ‖a‖ ≤ 1) (hbn : ‖b‖ ≤ 1) (hvn : ‖v‖ ≤ 2)
    (ha : ∀ k, ‖a * e k - e (k + da) * a‖ ≤ δ)
    (hb : ∀ k, ‖b * e k - e (k + db) * b‖ ≤ δ)
    (hv : ∀ k, ‖v * e k - e k * v‖ ≤ δ) (k : ZMod N) :
    ‖a * v * star b * e k - e (k + da - db) * (a * v * star b)‖ ≤ 5 * δ := by
  have havn : ‖a * v‖ ≤ 2 := by
    calc
      _ ≤ ‖a‖ * ‖v‖ := norm_mul_le _ _
      _ ≤ 1 * 2 := mul_le_mul han hvn (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hbsn : ‖star b‖ ≤ 1 := by simpa only [norm_star] using hbn
  have hav (j : ZMod N) : ‖a * v * e j - e (j + da) * (a * v)‖ ≤ 3 * δ := by
    apply (transport_product_bound a v (e j) (e j) (e (j + da))).trans
    calc
      _ ≤ 1 * δ + δ * 2 := add_le_add
        (mul_le_mul han (hv j) (norm_nonneg _) (by norm_num))
        (mul_le_mul (ha j) hvn (norm_nonneg _) hδ)
      _ = _ := by ring
  have hind : (k - db) + da = k + da - db := by abel
  have hav' := hav (k - db)
  rw [hind] at hav'
  apply (transport_product_bound (a * v) (star b) (e k) (e (k - db))
    (e (k + da - db))).trans
  calc
    _ ≤ 2 * δ + (3 * δ) * 1 := add_le_add
      (mul_le_mul havn (tower_adjoint_transport e he b db δ hb k) (norm_nonneg _) (by norm_num))
      (mul_le_mul hav' hbsn (norm_nonneg _) (by positivity))
    _ = _ := by ring

private lemma transport_unitary_norm_le (u : unitary E) : ‖(u : E)‖ ≤ 1 := by
  have hn1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
    (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
  have h := congrArg norm u.property.1
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (u : E)]

private lemma tower_unitary_sub_one {N : ℕ} (e : ZMod N → E)
    (u : unitary E) (δ : ℝ)
    (hu : ∀ k, ‖(u : E) * e k - e k * u‖ ≤ δ) :
    ‖(u : E) - 1‖ ≤ 2 ∧ ∀ k, ‖((u : E) - 1) * e k - e k * ((u : E) - 1)‖ ≤ δ := by
  have hn1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
    (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
  refine ⟨(norm_sub_le _ _).trans (by linarith [transport_unitary_norm_le u]), ?_⟩
  intro k
  have heq : ((u : E) - 1) * e k - e k * ((u : E) - 1) =
      (u : E) * e k - e k * u := by noncomm_ring
  rw [heq]
  exact hu k

/-- The three components of the genuine cancellation path move the
cyclic indices by `0`, `da-db`, and `db-da`, with error at most `20δ`.
All premises concern the supplied tower and the actual input words. -/
lemma cornerCancellationPath_tower_transport {N : ℕ} (e : ZMod N → E)
    (he : ∀ k, star (e k) = e k) (a b : E) (u : unitary E)
    (haa : star a * a = 1) (hbb : star b * b = 1) (hab : star a * b = 0)
    (da db : ZMod N) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ k, ‖a * e k - e (k + da) * a‖ ≤ δ)
    (hb : ∀ k, ‖b * e k - e (k + db) * b‖ ≤ δ)
    (hu : ∀ k, ‖(u : E) * e k - e k * u‖ ≤ δ) (θ : ℝ) (k : ZMod N) :
    ‖cornerCancellationPath a b u θ * e k -
      (e k * (1 + (Real.cos θ ^ 2) •
          (a * ((u : E) - 1) * star a + b * (star (u : E) - 1) * star b)) +
        e (k + da - db) * ((Real.sin θ * Real.cos θ) •
          (a * ((u : E) - 1) * star b)) -
        e (k + db - da) * ((Real.sin θ * Real.cos θ) •
          (b * (star (u : E) - 1) * star a)))‖ ≤ 20 * δ := by
  have han : ‖a‖ ≤ 1 := by
    have h := congrArg norm haa
    rw [CStarRing.norm_star_mul_self] at h
    have hn1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
      (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
    nlinarith [norm_nonneg a]
  have hbn : ‖b‖ ≤ 1 := by
    have h := congrArg norm hbb
    rw [CStarRing.norm_star_mul_self] at h
    have hn1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
      (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
    nlinarith [norm_nonneg b]
  have huStar (j : ZMod N) : ‖star (u : E) * e j - e j * star (u : E)‖ ≤ δ := by
    calc
      _ = ‖e j * star (u : E) - star (u : E) * e j‖ := norm_sub_rev _ _
      _ = ‖e j * (u : E) - (u : E) * e j‖ := toeplitz_star_commutator_norm _ _ (he j)
      _ = ‖(u : E) * e j - e j * u‖ := norm_sub_rev _ _
      _ ≤ δ := hu j
  let v := (u : E) - 1
  let w := star (u : E) - 1
  obtain ⟨hvn, hv⟩ := tower_unitary_sub_one e u δ hu
  obtain ⟨hwn, hw⟩ := tower_unitary_sub_one e (star u) δ huStar
  let A := a * v * star a
  let B := b * w * star b
  let C := a * v * star b
  let D := b * w * star a
  have hA : ‖A * e k - e k * A‖ ≤ 5 * δ := by
    simpa only [add_sub_cancel_right] using
      tower_sandwich_transport e he a a v da da δ hδ han han hvn ha ha hv k
  have hB : ‖B * e k - e k * B‖ ≤ 5 * δ := by
    simpa only [add_sub_cancel_right] using
      tower_sandwich_transport e he b b w db db δ hδ hbn hbn hwn hb hb hw k
  have hC := tower_sandwich_transport e he a b v da db δ hδ han hbn hvn ha hb hv k
  have hD := tower_sandwich_transport e he b a w db da δ hδ hbn han hwn hb ha hw k
  have hAB : ‖(A + B) * e k - e k * (A + B)‖ ≤ 10 * δ := by
    have heq : (A+B)*e k-e k*(A+B) = (A*e k-e k*A)+(B*e k-e k*B) := by noncomm_ring
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith)
  have hcos : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hsc : |Real.sin θ * Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one θ) (Real.abs_cos_le_one θ)
      (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have heq : cornerCancellationPath a b u θ * e k -
      (e k * (1 + (Real.cos θ ^ 2) • (A+B)) +
        e (k+da-db) * ((Real.sin θ * Real.cos θ) • C) -
        e (k+db-da) * ((Real.sin θ * Real.cos θ) • D)) =
      (Real.cos θ ^ 2) • ((A+B)*e k-e k*(A+B)) +
        (Real.sin θ * Real.cos θ) • (C*e k-e (k+da-db)*C) -
        (Real.sin θ * Real.cos θ) • (D*e k-e (k+db-da)*D) := by
    rw [cornerCancellationPath_three_terms a b u haa hbb hab u.property.2 θ]
    change (1 + (Real.cos θ ^ 2) • (A+B) + (Real.sin θ * Real.cos θ) • (C-D))*e k- _ = _
    simp only [add_mul, sub_mul, mul_add, mul_one, one_mul,
      smul_mul_assoc, mul_smul_comm, smul_sub]
    module
  change ‖cornerCancellationPath a b u θ * e k -
      (e k * (1 + (Real.cos θ ^ 2) • (A+B)) +
        e (k+da-db) * ((Real.sin θ * Real.cos θ) • C) -
        e (k+db-da) * ((Real.sin θ * Real.cos θ) • D))‖ ≤ _
  rw [heq]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 1 * (10*δ) + 1 * (5*δ) + 1 * (5*δ) := add_le_add
      (add_le_add (mul_le_mul hcos hAB (norm_nonneg _) (by norm_num))
        (mul_le_mul hsc hC (norm_nonneg _) (by norm_num)))
      (mul_le_mul hsc hD (norm_nonneg _) (by norm_num))
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
