import OAI.Analysis.OInfinity.CornerContractionPath

namespace OAI

/-! # Two controlled stabilization paths

The first path adds a cancelling pair on the two spare branches. The second
contracts the folded pair. Their endpoints differ by at most four times the
commutator error. The common corner and the ambient complement remain
explicit; no central corner for an arbitrary growing cocycle is asserted.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma orthogonal_extension_mul (d p c w : E)
    (hdc : d * c = 0) (hpc : p * c = 0) :
    (d + (1 - p)) * cornerCompression c w =
      d + c * w * star c + 1 - p - c * star c := by
  have hdw : d * (c * w * star c) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hdc, zero_mul, zero_mul]
  have hdp : d * (c * star c) = 0 := by rw [← mul_assoc, hdc, zero_mul]
  have hpw : p * (c * w * star c) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hpc, zero_mul, zero_mul]
  have hpp : p * (c * star c) = 0 := by rw [← mul_assoc, hpc, zero_mul]
  calc
    _ = d * (c * w * star c) + d - d * (c * star c) + c * w * star c +
        1 - c * star c - p * (c * w * star c) - p + p * (c * star c) := by
      unfold cornerCompression
      noncomm_ring
    _ = _ := by rw [hdw, hdp, hpw, hpp]; noncomm_ring

lemma cornerCompression_pair_product (a b z w : E) (hab : star a * b = 0) :
    cornerCompression a z * cornerCompression b w =
      a * z * star a + b * w * star b + 1 - a * star a - b * star b := by
  apply orthogonal_extension_mul
  · calc
      _ = a * z * (star a * b) := by noncomm_ring
      _ = 0 := by rw [hab, mul_zero]
  · rw [mul_assoc, hab, mul_zero]

lemma cornerCompression_triple_product (a b c z w x : E)
    (hab : star a * b = 0) (hac : star a * c = 0) (hbc : star b * c = 0) :
    cornerCompression a z * cornerCompression b w * cornerCompression c x =
      a * z * star a + b * w * star b + c * x * star c + 1 -
        (a * star a + b * star b + c * star c) := by
  have hd : (a * z * star a + b * w * star b) * c = 0 := by
    rw [add_mul]
    calc
      _ = a * z * (star a * c) + b * w * (star b * c) := by noncomm_ring
      _ = 0 := by rw [hac, hbc, mul_zero, mul_zero, add_zero]
  have hp : (a * star a + b * star b) * c = 0 := by
    rw [add_mul, mul_assoc, mul_assoc, hac, hbc, mul_zero, mul_zero, add_zero]
  calc
    _ = ((a * z * star a + b * w * star b) +
        (1 - (a * star a + b * star b))) * cornerCompression c x := by
      rw [cornerCompression_pair_product a b z w hab]
      congr 1
      noncomm_ring
    _ = _ := by
      rw [orthogonal_extension_mul _ _ _ _ hd hp]
      noncomm_ring

/-- Add an adjoint-cancelling pair to the two spare branches. -/
def cornerStabilizationFirstPath (a b z : E) (θ : ℝ) : E :=
  cornerCompression a z * cornerCancellationPath (b * a) (b * b) z (Real.pi / 2 - θ)

/-- Contract the folded first two branches against the third branch. -/
def cornerStabilizationSecondPath (a b z : E) (θ : ℝ) : E :=
  cornerCancellationPath (cornerPairFold a b) (b * b) z θ

private lemma projection_norm_bound (q : E) (hqstar : star q = q) (hqq : q * q = q) :
    ‖q‖ ≤ 1 := by
  have h := congrArg norm hqq
  have hs : IsSelfAdjoint q := hqstar
  rw [hs.norm_mul_self] at h
  nlinarith [norm_nonneg q]

private lemma relative_isometry_norm_bound (q a : E) (haa : star a * a = q)
    (hq : ‖q‖ ≤ 1) : ‖a‖ ≤ 1 := by
  have h := congrArg norm haa
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg a]

/-- The two explicit controlled paths leave precisely the small endpoint gap.
Their common relative unit is the supplied projection `q`. -/
lemma exists_controlled_cornerStabilization_paths (q a b z : E)
    (hqstar : star q = q) (hqq : q * q = q)
    (haa : star a * a = q) (hbb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q)
    (hqz : q * z = z) (hzq : z * q = z)
    (hzz : star z * z = q) (hzz' : z * star z = q)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (haz : ‖z * a - a * z‖ ≤ δ) (hbz : ‖z * b - b * z‖ ≤ δ) :
    ∃ u v : ℝ → unitary E, Continuous u ∧ Continuous v ∧
      (u 0 : E) = cornerCompression a z ∧ (v (Real.pi / 2) : E) = 1 ∧
      ‖(u (Real.pi / 2) : E) - v 0‖ ≤ 4 * δ ∧
      (∀ θ φ, ‖(u θ : E) - u φ‖ ≤ 4 * |θ - φ|) ∧
      (∀ θ φ, ‖(v θ : E) - v φ‖ ≤ 4 * |θ - φ|) := by
  have hs := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hf : star (b * a) * (b * a) = q := by
    simpa [cornerThreeBranch] using cornerThreeBranch_gram q a b hqstar hqq haa hbb hab hsum 1 1
  have hg : star (b * b) * (b * b) = q := by
    simpa [cornerThreeBranch] using cornerThreeBranch_gram q a b hqstar hqq haa hbb hab hsum 2 2
  have hfg : star (b * a) * (b * b) = 0 := by
    simpa [cornerThreeBranch] using cornerThreeBranch_gram q a b hqstar hqq haa hbb hab hsum 1 2
  have hfq : (b * a) * q = b * a := by rw [mul_assoc, hs.2.1]
  have hgq : (b * b) * q = b * b := by rw [mul_assoc, hs.2.2.2]
  have hp := cornerPairFold_properties q a b hqstar hqq haa hbb hab hsum
  have hvq := relativeIsometry_mul_support (cornerPairFold a b) q hp.1 hqstar hqq
  have huA := cornerCompression_mem q a z hqstar haa hs.2.1 hqz hzq hzz hzz'
  let u (θ : ℝ) : unitary E := ⟨cornerStabilizationFirstPath a b z θ,
    (unitary E).mul_mem huA
      (cornerCancellationPath_mem q (b * a) (b * b) z hqstar hf hg hfg hfq hgq
        hqz hzq hzz hzz' (Real.pi / 2 - θ))⟩
  let v (θ : ℝ) : unitary E := ⟨cornerStabilizationSecondPath a b z θ,
    cornerCancellationPath_mem q (cornerPairFold a b) (b * b) z hqstar
      hp.1 hp.2.1 hp.2.2.1 hvq hgq hqz hzq hzz hzz' θ⟩
  have hu0 : (u 0 : E) = cornerCompression a z := by
    change cornerCompression a z * cornerCancellationPath (b * a) (b * b) z (Real.pi / 2 - 0) = _
    rw [sub_zero, cornerCancellationPath_quarter q (b * a) (b * b) z hqstar
      hf hg hfg hfq hgq hqz hzq hzz hzz', mul_one]
  have hv1 : (v (Real.pi / 2) : E) = 1 :=
    cornerCancellationPath_quarter q (cornerPairFold a b) (b * b) z hqstar
      hp.1 hp.2.1 hp.2.2.1 hvq hgq hqz hzq hzz hzz'
  have haF : star a * (b * a) = 0 := by rw [← mul_assoc, hab, zero_mul]
  have haG : star a * (b * b) = 0 := by rw [← mul_assoc, hab, zero_mul]
  have hu1 : (u (Real.pi / 2) : E) =
      a * z * star a + (b * a) * z * star (b * a) + (b * b) * star z * star (b * b) + 1 - q := by
    change cornerCompression a z * cornerCancellationPath (b * a) (b * b) z
      (Real.pi / 2 - Real.pi / 2) = _
    rw [sub_self, cornerCancellationPath_zero, ← mul_assoc,
      cornerCompression_triple_product a (b * a) (b * b) z z (star z) haF haG hfg,
      cornerThreeBranch_sum q a b hqstar hqq haa hbb hab hsum]
  have hv0 : (v 0 : E) =
      cornerPairFold a b * z * star (cornerPairFold a b) +
        (b * b) * star z * star (b * b) + 1 - q := by
    change cornerCancellationPath (cornerPairFold a b) (b * b) z 0 = _
    rw [cornerCancellationPath_zero,
      cornerCompression_pair_product _ _ _ _ hp.2.2.1]
    rw [← hp.2.2.2]
    noncomm_ring
  have hnq := projection_norm_bound q hqstar hqq
  have hna := relative_isometry_norm_bound q a haa hnq
  have hnb := relative_isometry_norm_bound q b hbb hnq
  have hnf := relative_isometry_norm_bound q (b * a) hf hnq
  have hgap : ‖(u (Real.pi / 2) : E) - v 0‖ ≤ 4 * δ := by
    rw [hu1, hv0]
    have he : a * z * star a + (b * a) * z * star (b * a) +
        (b * b) * star z * star (b * b) + 1 - q -
        (cornerPairFold a b * z * star (cornerPairFold a b) +
          (b * b) * star z * star (b * b) + 1 - q) =
        (a * z * star a + (b * a) * z * star (b * a)) -
          cornerPairFold a b * z * star (cornerPairFold a b) := by abel
    rw [he, norm_sub_rev]
    exact cornerPairFold_conjugation_error q a b a (b * a) z haa hbb hab
      hqz hna hnb hna hnf δ hδ haz hbz
  refine ⟨u, v, ?_, ?_, hu0, hv1, hgap, ?_, ?_⟩
  · exact (continuous_const.mul ((cornerCancellationPath_continuous (b * a) (b * b) z).comp
      (continuous_const.sub continuous_id))).subtype_mk _
  · exact (cornerCancellationPath_continuous (cornerPairFold a b) (b * b) z).subtype_mk _
  · intro θ φ
    change ‖cornerCompression a z * cornerCancellationPath (b * a) (b * b) z (Real.pi / 2 - θ) -
      cornerCompression a z * cornerCancellationPath (b * a) (b * b) z (Real.pi / 2 - φ)‖ ≤ _
    rw [← mul_sub, CStarRing.norm_mem_unitary_mul _ huA]
    have h := cornerCancellationPath_sub_norm_le q (b * a) (b * b) z hqstar
      hf hg hfg hfq hgq hqz hzq hzz hzz' (Real.pi / 2 - θ) (Real.pi / 2 - φ)
    have he : Real.pi / 2 - θ - (Real.pi / 2 - φ) = -(θ - φ) := by ring
    simpa only [he, abs_neg] using h
  · intro θ φ
    exact cornerCancellationPath_sub_norm_le q (cornerPairFold a b) (b * b) z hqstar
      hp.1 hp.2.1 hp.2.2.1 hvq hgq hqz hzq hzz hzz' θ φ

end WeakPureInfiniteness

end

end OAI
