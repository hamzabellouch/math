import OAI.Analysis.TriangularHilbert.Support

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def weightedGram (B : Matrix ι ι ℂ) (w : ι → ℝ) : Matrix ι ι ℂ :=
  Bᴴ * Matrix.diagonal (fun i => (w i : ℂ)) * B

lemma weightedGram_posSemidef (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) : (weightedGram B w).PosSemidef :=
  (Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hw i))).conjTranspose_mul_mul_same B

lemma weightedGram_isHermitian (B : Matrix ι ι ℂ) (w : ι → ℝ) :
    (weightedGram B w).IsHermitian := by
  have hd : (Matrix.diagonal (fun i => (w i : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    simp
  exact Matrix.isHermitian_conjTranspose_mul_mul B hd

lemma weightedGram_mul_zero {B Q : Matrix ι ι ℂ} {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hz : weightedGram B w * Q = 0) : B * Q = 0 := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (w i : ℂ))
  have hD : D.PosDef := Matrix.PosDef.diagonal (fun i => RCLike.ofReal_pos.mpr (hw i))
  have hs : (CFC.sqrt D).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).isHermitian
  have hunit : IsUnit (CFC.sqrt D) :=
    (Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.sqrt D hD.isStrictlyPositive)).isUnit
  have hgram : (CFC.sqrt D * B)ᴴ * (CFC.sqrt D * B) = weightedGram B w := by
    calc
      _ = Bᴴ * (CFC.sqrt D * CFC.sqrt D) * B := by
        rw [Matrix.conjTranspose_mul, hs.eq]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg]; rfl
  have hsq : (CFC.sqrt D * B * Q)ᴴ * (CFC.sqrt D * B * Q) = 0 := by
    calc
      _ = Qᴴ * ((CFC.sqrt D * B)ᴴ * (CFC.sqrt D * B)) * Q := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Qᴴ * (weightedGram B w * Q) := by rw [hgram, Matrix.mul_assoc]
      _ = 0 := by rw [hz, mul_zero]
  have hzero := (CStarRing.star_mul_self_eq_zero_iff _).mp hsq
  apply hunit.mul_left_cancel
  simpa only [Matrix.mul_assoc, mul_zero] using hzero

lemma weightedGram_kernel_projection (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) :
    ∃ Q : Matrix ι ι ℂ, Q.PosSemidef ∧ Q * Q = Q ∧ B * Q = 0 ∧
      (weightedGram B w + Q).PosDef := by
  obtain ⟨Q, hQ, hQQ, hPQ, _, hPD⟩ :=
    exists_kernel_projection (weightedGram_posSemidef B (fun i => (hw i).le))
  exact ⟨Q, hQ, hQQ, weightedGram_mul_zero hw hPQ, hPD⟩

lemma weightedGram_mul_eq_zero (B Q : Matrix ι ι ℂ) (w : ι → ℝ) (hz : B * Q = 0) :
    weightedGram B w * Q = 0 := by
  simp only [weightedGram, Matrix.mul_assoc, hz, mul_zero]

lemma diagonal_real_hasDerivAt {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => Matrix.diagonal (fun i => (w t i : ℂ)))
      (Matrix.diagonal (fun i => (w' i : ℂ))) x := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.diagonal_apply_eq] using (hd i).ofReal_comp
  · simpa only [Matrix.diagonal_apply_ne _ hij] using
      (hasDerivAt_const x (0 : ℂ))

lemma weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => weightedGram B (w t)) (weightedGram B w') x :=
  ((diagonal_real_hasDerivAt hd).const_mul Bᴴ).mul_const B

theorem energy_weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w : ℝ → ι → ℝ} {w' : ι → ℝ} {x : ℝ}
    (hw : ∀ᶠ t in 𝓝 x, ∀ i, 0 < w t i)
    (hd : ∀ i, HasDerivAt (fun t => w t i) (w' i) x) :
    HasDerivAt (fun t => energy (weightedGram B (w t)))
      (energyGradient (weightedGram B (w x)) (weightedGram B w')) x := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw.self_of_nhds
  exact energy_supported_path_hasDerivAt hQ hQQ hPD
    (hw.mono fun t ht => weightedGram_posSemidef B (fun i => (ht i).le))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (w t) hBQ)
    (weightedGram_hasDerivAt B hd)

theorem energyGradient_weightedGram_hasDerivAt (B : Matrix ι ι ℂ)
    {w k : ℝ → ι → ℝ} {w' k' : ι → ℝ} {x : ℝ}
    (hw : ∀ᶠ t in 𝓝 x, ∀ i, 0 < w t i)
    (hdw : ∀ i, HasDerivAt (fun t => w t i) (w' i) x)
    (hdk : ∀ i, HasDerivAt (fun t => k t i) (k' i) x) :
    HasDerivAt (fun t => energyGradient (weightedGram B (w t)) (weightedGram B (k t)))
      (hessianPair (weightedGram B (w x)) (weightedGram B (k x)) (weightedGram B w') +
        energyGradient (weightedGram B (w x)) (weightedGram B k')) x := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw.self_of_nhds
  exact energyGradient_supported_path_hasDerivAt hQ hQQ hPD
    (hw.mono fun t ht => weightedGram_posSemidef B (fun i => (ht i).le))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (w t) hBQ)
    (Eventually.of_forall fun t => weightedGram_isHermitian B (k t))
    (Eventually.of_forall fun t => weightedGram_mul_eq_zero B Q (k t) hBQ)
    (weightedGram_hasDerivAt B hdw) (weightedGram_hasDerivAt B hdk)

end
end TriangularHilbert.MatrixEnergy
end

end OAI
