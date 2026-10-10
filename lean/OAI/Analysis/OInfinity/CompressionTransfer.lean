import OAI.Analysis.OInfinity.RelativeUnitaryPath

namespace OAI

/-! # Moving a compression into a spare corner

Orthogonal isometries give a uniform path between the two compressions of a
unitary. If the second range is in `q`, its endpoint is exactly a relative
unitary extended by `1-q`. Centrality of that relative unitary with respect
to a coisometric pair in `q` remains a separate obligation.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Move the first compression to the second by rotating the cancelling pair. -/
def compressionTransferPath (a b z : E) (θ : ℝ) : E :=
  cornerCancellationPath a b z θ * cornerCompression b z

lemma exists_controlled_compressionTransfer (a b : E)
    (haa : star a * a = 1) (hbb : star b * b = 1) (hab : star a * b = 0)
    (z : unitary E) :
    ∃ u v : unitary E, (u : E) = cornerCompression a z ∧
      (v : E) = cornerCompression b z ∧ ∃ p : Path u v,
      ∀ t s, ‖(p t : E) - p s‖ ≤ (2 * Real.pi) * |(t : ℝ) - s| := by
  have hB := cornerCompression_mem (1 : E) b (z : E) (star_one _) hbb (mul_one _)
    (one_mul _) (mul_one _) z.property.1 z.property.2
  let u (θ : ℝ) : unitary E := ⟨compressionTransferPath a b z θ,
    (unitary E).mul_mem
      (cornerCancellationPath_mem (1 : E) a b z (star_one _) haa hbb hab
        (mul_one _) (mul_one _) (one_mul _) (mul_one _) z.property.1 z.property.2 θ) hB⟩
  have huc : Continuous u := ((cornerCancellationPath_continuous a b z).mul
    continuous_const).subtype_mk _
  have hu0 : (u 0 : E) = cornerCompression a z := by
    change cornerCancellationPath a b z 0 * cornerCompression b z = _
    rw [cornerCancellationPath_zero, mul_assoc, ← cornerCompression_star, hB.1, mul_one]
  have hu1 : (u (Real.pi / 2) : E) = cornerCompression b z := by
    change cornerCancellationPath a b z (Real.pi / 2) * cornerCompression b z = _
    rw [cornerCancellationPath_quarter (1 : E) a b z (star_one _) haa hbb hab
      (mul_one _) (mul_one _) (one_mul _) (mul_one _) z.property.1 z.property.2, one_mul]
  have hub : ∀ θ φ, ‖(u θ : E) - u φ‖ ≤ 4 * |θ - φ| := by
    intro θ φ
    change ‖cornerCancellationPath a b z θ * cornerCompression b z -
      cornerCancellationPath a b z φ * cornerCompression b z‖ ≤ _
    rw [← sub_mul, CStarRing.norm_mul_mem_unitary _ hB]
    exact cornerCancellationPath_sub_norm_le (1 : E) a b z (star_one _) haa hbb hab
      (mul_one _) (mul_one _) (one_mul _) (mul_one _) z.property.1 z.property.2 θ φ
  exact ⟨u 0, u (Real.pi / 2), hu0, hu1, unitaryQuarterPath u huc,
    unitaryQuarterPath_sub_norm_le u huc hub⟩

/-- The moved compression as an element of the specified relative corner. -/
def compressedRelativeUnitary (q b z : E) : E := b * z * star b + (q - b * star b)

lemma compressedRelativeUnitary_extension (q b z : E) :
    relativeUnitaryExtension q (compressedRelativeUnitary q b z) = cornerCompression b z := by
  unfold relativeUnitaryExtension compressedRelativeUnitary cornerCompression
  abel

lemma compressedRelativeUnitary_properties (q b : E)
    (hqstar : star q = q) (hqq : q * q = q) (hqb : q * b = b)
    (hbb : star b * b = 1) (z : unitary E) :
    q * compressedRelativeUnitary q b z = compressedRelativeUnitary q b z ∧
      compressedRelativeUnitary q b z * q = compressedRelativeUnitary q b z ∧
      star (compressedRelativeUnitary q b z) * compressedRelativeUnitary q b z = q ∧
      compressedRelativeUnitary q b z * star (compressedRelativeUnitary q b z) = q := by
  let x : E := b * (z : E) * star b
  let p : E := b * star b
  have hpstar : star p = p := by simp only [p, star_mul, star_star]
  have hbq : star b * q = star b := by
    simpa only [star_mul, hqstar] using congrArg star hqb
  have hpq : p * q = p := by dsimp only [p]; rw [mul_assoc, hbq]
  have hqp : q * p = p := by dsimp only [p]; rw [← mul_assoc, hqb]
  have hpp : p * p = p := by
    change (b * star b) * (b * star b) = b * star b
    calc
      _ = b * (star b * b) * star b := by noncomm_ring
      _ = _ := by rw [hbb, mul_one]
  have hqx : q * x = x := by dsimp only [x]; rw [← mul_assoc, ← mul_assoc, hqb]
  have hxq : x * q = x := by
    dsimp only [x]
    rw [mul_assoc, mul_assoc, hbq, mul_assoc]
  have hpx : p * x = x := by
    change (b * star b) * (b * (z : E) * star b) = _
    calc
      _ = b * (star b * b) * (z : E) * star b := by noncomm_ring
      _ = _ := by rw [hbb, mul_one]
  have hxp : x * p = x := by
    change (b * (z : E) * star b) * (b * star b) = _
    calc
      _ = b * (z : E) * (star b * b) * star b := by noncomm_ring
      _ = _ := by rw [hbb, mul_one]
  have hsxq : star x * q = star x := by
    simpa only [star_mul, hqstar] using congrArg star hqx
  have hqsx : q * star x = star x := by
    simpa only [star_mul, hqstar] using congrArg star hxq
  have hsxp : star x * p = star x := by
    simpa only [star_mul, hpstar] using congrArg star hpx
  have hpsx : p * star x = star x := by
    simpa only [star_mul, hpstar] using congrArg star hxp
  have hxx : star x * x = p := by
    dsimp only [x]
    rw [star_mul, star_mul, star_star]
    calc
      _ = b * star (z : E) * (star b * b) * (z : E) * star b := by noncomm_ring
      _ = p := by rw [hbb, mul_one, mul_assoc b, z.property.1, mul_one]
  have hxx' : x * star x = p := by
    dsimp only [x]
    rw [star_mul, star_mul, star_star]
    calc
      _ = b * (z : E) * (star b * b) * star (z : E) * star b := by noncomm_ring
      _ = p := by rw [hbb, mul_one, mul_assoc b, z.property.2, mul_one]
  change q * (x + (q - p)) = x + (q - p) ∧
    (x + (q - p)) * q = x + (q - p) ∧
    star (x + (q - p)) * (x + (q - p)) = q ∧
    (x + (q - p)) * star (x + (q - p)) = q
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_add, mul_sub, hqx, hqq, hqp]
  · rw [add_mul, sub_mul, hxq, hqq, hpq]
  · rw [star_add, star_sub, hqstar, hpstar]
    noncomm_ring [hxx, hsxq, hsxp, hqx, hpx, hqq, hqp, hpq, hpp]
  · rw [star_add, star_sub, hqstar, hpstar]
    noncomm_ring [hxx', hxq, hxp, hqsx, hpsx, hqq, hqp, hpq, hpp]

/-- This exact formula records the extra commutators required after transfer.
Centrality of `z` alone does not remove the range-projection terms. -/
lemma compressedRelativeUnitary_commutator (q b z y : E) :
    compressedRelativeUnitary q b z * y - y * compressedRelativeUnitary q b z =
      b * (z * y - y * z) * star b +
        (b * y - y * b) * (z - 1) * star b +
        b * (z - 1) * (star b * y - y * star b) + (q * y - y * q) := by
  unfold compressedRelativeUnitary
  noncomm_ring

end WeakPureInfiniteness

end

end OAI
