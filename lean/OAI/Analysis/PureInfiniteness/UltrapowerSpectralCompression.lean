import OAI.Analysis.PureInfiniteness.NonunitalFiniteCompression
import OAI.Analysis.PureInfiniteness.NonunitalSampledRow
import OAI.Analysis.PureInfiniteness.NonunitalJointPartition

namespace OAI

/-! Quantitative finite spectral abelianization in a norm ultrapower. The
coefficient bound is chosen before the mesh, as required for taking the mesh
to zero. The resulting compressor is an element of the original ultrapower. -/

noncomputable section
open scoped BigOperators NNReal

namespace WeakPureInfiniteness

variable {A I : Type*} [NonUnitalCStarAlgebra A] [Fintype I] [DecidableEq I]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

/-- The two-pass Gram construction and the joint spectral partition give one
contractive compression, preserving the first two moments and making its
image of one coefficient approximately commute with the selected elements. -/
theorem ultrapower_spectral_compression_bounds (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (b : N) (hb : IsSelfAdjoint b) (δ η : ℝ≥0) (hδ : 0 < δ) (hη : 0 < η)
    (hcut : (δ + η : ℝ≥0) < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∃ v : N, ‖v‖ ≤ 1 ∧ ∀ i,
        ‖star v * a i * v - a i‖ ≤
          (2 * r * Real.sqrt ((5 : ℝ) ^ Fintype.card I)) * C +
            (r + (δ + η : ℝ≥0) * (‖a i‖ + r)) ∧
        ‖star v * (a i * a i) * v - a i * a i‖ ≤
          (‖a i‖ + ((∑ k, ‖a k‖) + 2)) *
            ((2 * r * Real.sqrt ((5 : ℝ) ^ Fintype.card I)) * C) +
            (r ^ 2 + (δ + η : ℝ≥0) * (‖a i * a i‖ + r ^ 2)) ∧
        ‖a i * (star v * b * v) - (star v * b * v) * a i‖ ≤
          (2 * r + 2 * Real.sqrt (r ^ 2 + r * (2 * ‖a i‖ + r))) * ‖b‖ := by
  obtain ⟨C, hC, hrows⟩ := ultrapower_relative_cut_gram_row hP U δ η hδ hη
  refine ⟨C, hC, ?_⟩
  intro r hr hr1
  obtain ⟨n, f, g, t, hfg, _, hgsum, ht0, hfirst, hcomm, _, hsecond, hquad, htR⟩ :=
    exists_nonunital_joint_partition a ha hc r hr
  obtain ⟨d, hd, H, hentry, hH, hgram, hoff⟩ :=
    hrows n f (fun j => (hfg j).1) (fun j => (hfg j).2.1) b
  let v := finiteRowCompression H g
  have hgp : ∀ j, 0 ≤ g j := fun j => (hfg j).2.2.1
  have hfp : ∀ j, 0 ≤ f j := fun j => (hfg j).1
  have hsupport : ∀ j, f j * g j = g j := fun j => (hfg j).2.2.2.2
  have hcut0 : 0 ≤ ((δ + η : ℝ≥0) : ℝ) := (δ + η).2
  have hcut1 : ((δ + η : ℝ≥0) : ℝ) < 1 := hcut
  let q : ℝ := 2 * r * Real.sqrt ((5 : ℝ) ^ Fintype.card I)
  let E : ℝ := q * C
  let R : ℝ := (∑ k, ‖a k‖) + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hq2 : q ^ 2 = 4 * r ^ 2 * (5 : ℝ) ^ Fintype.card I := by
    dsimp [q]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hrow (i : I) :
      ‖unitizationOneByOne (a i) * rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ N) H -
        rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ N) H * scalarSample (t i)‖ ≤ E := by
    apply nonunital_sampled_row_error_norm_le (a i) f d (t i) H hentry
      (ha i).isSelfAdjoint hfp (fun j => (hcomm i j).1) C q hC hq hd
    rw [hq2]
    exact hquad i
  refine ⟨v, finiteRowCompression_norm_le_one H g hH hgp hgsum, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · exact nonunital_finite_compression_preservation H f g (t i) (a i) hH hfp hgp
      hgsum hsupport (δ + η) r E hcut0 hcut1 hgram (hfirst i) (hrow i)
  · have hsrow := nonunital_squared_row_error_norm_le (a i) H (t i) E R hR
      (ht0 i) (fun j => (htR i j).trans (by dsimp [R]; linarith)) (hrow i)
    exact nonunital_finite_compression_preservation H f g (fun j => (t i j) ^ 2)
      (a i * a i) hH hfp hgp hgsum hsupport (δ + η) (r ^ 2) ((‖a i‖ + R) * E)
      hcut0 hcut1 hgram (hsecond i) hsrow
  · exact nonunital_finite_compression_commutator H hH g hgp hgsum (t i) (a i) b hb
      hoff r (r ^ 2) (hfirst i) (hsecond i)

end WeakPureInfiniteness

end

end OAI
