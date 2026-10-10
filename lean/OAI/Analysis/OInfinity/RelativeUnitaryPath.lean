import OAI.Analysis.OInfinity.CornerShortPath

namespace OAI

/-! # Uniform paths for relative unitaries

In a fixed corner carrying a coisometric pair, a relative unitary that almost
commutes with that pair admits an explicit uniform path bound. The endpoint
is extended by the identity on the ambient complement. The existence of such
a pair in a prescribed corner is an input, not a consequence asserted here.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Extend a relative unitary by the identity on the complementary corner. -/
def relativeUnitaryExtension (q z : E) : E := z + (1 - q)

lemma relativeUnitaryExtension_mem (q z : E) (hqstar : star q = q)
    (hqq : q * q = q) (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q) :
    relativeUnitaryExtension q z ∈ unitary E := by
  have hsq : star z * q = star z := by
    simpa only [star_mul, hqstar] using congrArg star hqz
  have hqs : q * star z = star z := by
    simpa only [star_mul, hqstar] using congrArg star hzq
  constructor
  · simp only [relativeUnitaryExtension, star_add, star_sub, star_one, hqstar]
    noncomm_ring [hqq, hqz, hsq, hzz]
  · simp only [relativeUnitaryExtension, star_add, star_sub, star_one, hqstar]
    noncomm_ring [hqq, hzq, hqs, hzz']

lemma relativeUnitaryExtension_decomposition_error (q a b z : E)
    (hsum : a * star a + b * star b = q) (hzq : z * q = z)
    (hab : star a * b = 0) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (haz : ‖z * a - a * z‖ ≤ δ) (hbz : ‖z * b - b * z‖ ≤ δ) :
    ‖relativeUnitaryExtension q z - cornerCompression a z * cornerCompression b z‖ ≤ 2 * δ := by
  have he : relativeUnitaryExtension q z - cornerCompression a z * cornerCompression b z =
      (z * a - a * z) * star a + (z * b - b * z) * star b := by
    rw [cornerCompression_pair_product a b z z hab]
    unfold relativeUnitaryExtension
    calc
      _ = z - (a * z * star a + b * z * star b) := by rw [← hsum]; abel
      _ = z * (a * star a + b * star b) - (a * z * star a + b * z * star b) := by
        rw [hsum, hzq]
      _ = _ := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(z * a - a * z) * star a‖ + ‖(z * b - b * z) * star b‖ := norm_add_le _ _
    _ ≤ ‖z * a - a * z‖ * ‖a‖ + ‖z * b - b * z‖ * ‖b‖ := by
      simpa only [norm_star] using add_le_add
        (norm_mul_le (z * a - a * z) (star a))
        (norm_mul_le (z * b - b * z) (star b))
    _ ≤ δ * 1 + δ * 1 := by gcongr
    _ = 2 * δ := by ring

lemma unitaryPath_mul_sub_norm_le {a b c d : unitary E}
    (p : Path a b) (q : Path c d) (L K : ℝ)
    (hp : ∀ t s, ‖(p t : E) - p s‖ ≤ L * |(t : ℝ) - s|)
    (hq : ∀ t s, ‖(q t : E) - q s‖ ≤ K * |(t : ℝ) - s|) :
    ∀ t s, ‖((p.mul q) t : E) - (p.mul q) s‖ ≤ (L + K) * |(t : ℝ) - s| := by
  intro t s
  have he : ((p.mul q) t : E) - (p.mul q) s =
      (p t : E) * ((q t : E) - q s) + ((p t : E) - p s) * (q s : E) := by
    change (p t : E) * (q t : E) - (p s : E) * (q s : E) = _
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(p t : E) * ((q t : E) - q s)‖ + ‖((p t : E) - p s) * (q s : E)‖ := norm_add_le _ _
    _ = ‖(q t : E) - q s‖ + ‖(p t : E) - p s‖ := by
      rw [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary]
    _ ≤ K * |(t : ℝ) - s| + L * |(t : ℝ) - s| := add_le_add (hq t s) (hp t s)
    _ = _ := by ring

/-- The fixed-pair hypotheses give a numerical bound independent of the
relative unitary. The ambient complement is present in the initial point. -/
lemma exists_uniform_relativeUnitary_path (q a b z : E)
    (hqstar : star q = q) (hqq : q * q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : 4 * δ < 2)
    (haz : ‖z * a - a * z‖ ≤ δ) (hbz : ‖z * b - b * z‖ ≤ δ) :
    ∃ u : unitary E, (u : E) = relativeUnitaryExtension q z ∧
      ∃ p : Path u 1, ∀ t s, ‖(p t : E) - p s‖ ≤ (32 * Real.pi) * |(t : ℝ) - s| := by
  obtain ⟨u, hu, p, hp⟩ := exists_uniform_compressed_unitary_path q a b z hqstar hqq
    haa hbb hab hsum hqz hzq hzz hzz' δ hδ hsmall haz hbz
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  have hsum' : b * star b + a * star a = q := by rw [add_comm]; exact hsum
  obtain ⟨v, hv, r, hr⟩ := exists_uniform_compressed_unitary_path q b a z hqstar hqq
    hbb haa hba hsum' hqz hzq hzz hzz' δ hδ hsmall hbz haz
  let w : unitary E := ⟨relativeUnitaryExtension q z,
    relativeUnitaryExtension_mem q z hqstar hqq hqz hzq hzz hzz'⟩
  have hnq : ‖q‖ ≤ 1 := by
    have h := congrArg norm hqq
    have hs : IsSelfAdjoint q := hqstar
    rw [hs.norm_mul_self] at h
    nlinarith [norm_nonneg q]
  have hna : ‖a‖ ≤ 1 := by
    have h := congrArg norm haa
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg a]
  have hnb : ‖b‖ ≤ 1 := by
    have h := congrArg norm hbb
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg b]
  have hclose : ‖((u * v : unitary E) : E) - w‖ < 2 := by
    change ‖(u : E) * (v : E) - relativeUnitaryExtension q z‖ < 2
    rw [hu, hv, norm_sub_rev]
    exact (relativeUnitaryExtension_decomposition_error q a b z hsum hzq hab
      hna hnb δ hδ haz hbz).trans_lt (by linarith)
  let middle := Unitary.path w (u * v) hclose
  let productPath : Path (u * v) 1 := (p.mul r).cast rfl (by simp)
  have hm : ∀ t s, ‖(middle t : E) - middle s‖ ≤ (16 * Real.pi) * |(t : ℝ) - s| := by
    intro t s
    exact (unitary_shortPath_sub_norm_le w (u * v) hclose t s).trans (by
      nlinarith [Real.pi_pos, abs_nonneg ((t : ℝ) - s)])
  have hpr : ∀ t s, ‖(productPath t : E) - productPath s‖ ≤
      (16 * Real.pi) * |(t : ℝ) - s| := by
    intro t s
    change ‖((p.mul r) t : E) - (p.mul r) s‖ ≤ _
    simpa only [show 8 * Real.pi + 8 * Real.pi = 16 * Real.pi by ring] using
      unitaryPath_mul_sub_norm_le p r (8 * Real.pi) (8 * Real.pi) hp hr t s
  refine ⟨w, rfl, middle.trans productPath, ?_⟩
  intro t s
  simpa only [show 2 * (16 * Real.pi) = 32 * Real.pi by ring] using
    unitaryPath_trans_sub_norm_le middle productPath (16 * Real.pi) hm hpr t s

end WeakPureInfiniteness

end

end OAI
