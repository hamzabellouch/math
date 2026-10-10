import OAI.Analysis.PureInfiniteness.ReindexGramRow
import OAI.Analysis.PureInfiniteness.RepeatedSpectralError
import OAI.Analysis.PureInfiniteness.NonunitalCrossCompression
import OAI.Analysis.PureInfiniteness.NonunitalJointPartition

namespace OAI

/-! Quantitative finite amplification over a commuting positive family. Each
copy has the same return moments; different copies have small mixed moments. -/

noncomputable section
open scoped BigOperators NNReal

namespace WeakPureInfiniteness

variable {A I M : Type*} [NonUnitalCStarAlgebra A]
  [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
  (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ Filter.atTop)]

local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

theorem ultrapower_copy_compression_bounds (hP : MainGap.PropertyP A)
    (a : I → N) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i j, Commute (a i) (a j))
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∃ v : M → N, (∀ j, ‖v j‖ ≤ 1) ∧ ∀ i,
        (∀ j k, ‖star (v j) * a i * v k - (if j = k then a i else 0)‖ ≤
          (2 * r * Real.sqrt ((Fintype.card M : ℝ) * (5 : ℝ) ^ Fintype.card I)) * C +
            (r + δ * (‖a i‖ + r))) ∧
        (∀ j, ‖star (v j) * (a i * a i) * v j - a i * a i‖ ≤
          (‖a i‖ + ((∑ k, ‖a k‖) + 2)) *
            ((2 * r * Real.sqrt ((Fintype.card M : ℝ) * (5 : ℝ) ^ Fintype.card I)) * C) +
            (r ^ 2 + δ * (‖a i * a i‖ + r ^ 2))) := by
  obtain ⟨C, hC, hrows⟩ := ultrapower_cut_gram_row hP U δ hδ
  refine ⟨C, hC, ?_⟩
  intro r hr hr1
  obtain ⟨n, f, g, t, hfg, _, hgsum, ht0, hfirst, hcomm, _, hsecond, hquad, htR⟩ :=
    exists_nonunital_joint_partition a ha hc r hr
  let e : M × Fin n ≃ Fin (Fintype.card (M × Fin n)) := Fintype.equivFin _
  obtain ⟨d₀, hd₀, H₀, hentry₀, _, hgram₀⟩ := hrows _
    (fun j => f (e.symm j).2) (fun j => (hfg (e.symm j).2).1)
    (fun j => (hfg (e.symm j).2).2.1)
  obtain ⟨d, hd, H, hentry, hH, hgram⟩ := reindex_cut_gram_row e
    (fun p => f p.2) (fun p => (hfg p.2).1) (fun p => (hfg p.2).2.1)
    δ C δ.2 d₀ hd₀ H₀ hentry₀ hgram₀
  let G (j : M) := supportedSpectralCopy g j
  let v (j : M) := finiteRowCompression H (G j)
  have hfp : ∀ p : M × Fin n, 0 ≤ f p.2 := fun p => (hfg p.2).1
  have hgp (j : M) : ∀ p, 0 ≤ G j p :=
    supportedSpectralCopy_nonneg g (fun k => (hfg k).2.2.1) j
  have hgn (j : M) : ‖∑ p, G j p‖ ≤ 1 := by
    simpa only [G, sum_supportedSpectralCopy] using hgsum
  have hsupport (j : M) (p : M × Fin n) : f p.2 * G j p = G j p :=
    supportedSpectralCopy_support f g (fun k => (hfg k).2.2.2.2) j p
  let q : ℝ := 2 * r * Real.sqrt ((Fintype.card M : ℝ) * (5 : ℝ) ^ Fintype.card I)
  let E := q * C
  let R : ℝ := (∑ k, ‖a k‖) + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hq2 : q ^ 2 = 4 * r ^ 2 * ((Fintype.card M : ℝ) * (5 : ℝ) ^ Fintype.card I) := by
    dsimp [q]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hrow (i : I) :
      ‖unitizationOneByOne (a i) * rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ N) H -
        rectangularMap (Unitization.inrNonUnitalStarAlgHom ℂ N) H *
          scalarSample (fun p : M × Fin n => t i p.2)‖ ≤ E := by
    apply nonunital_sampled_row_error_norm_le (a i) (fun p => f p.2) d
      (fun p => t i p.2) H hentry (ha i).isSelfAdjoint hfp
      (fun p => (hcomm i p.2).1) C q hC hq hd
    rw [hq2]
    exact (repeated_sampledQuadratic_norm_le (M := M) (a i) f (t i) _ (hquad i)).trans_eq (by ring)
  have hmom (i : I) (j : M) : ‖a i - ∑ p, (t i p.2 : ℂ) • G j p‖ ≤ r := by
    dsimp only [G]
    rw [sum_smul_supportedSpectralCopy g (fun k : Fin n => (t i k : ℂ)) j]
    exact hfirst i
  have hmom2 (i : I) (j : M) :
      ‖a i * a i - ∑ p, (((t i p.2) ^ 2 : ℝ) : ℂ) • G j p‖ ≤ r ^ 2 := by
    dsimp only [G]
    rw [sum_smul_supportedSpectralCopy g (fun k : Fin n => (((t i k) ^ 2 : ℝ) : ℂ)) j]
    exact hsecond i
  refine ⟨v, fun j => finiteRowCompression_norm_le_one H (G j) hH (hgp j) (hgn j), ?_⟩
  intro i
  refine ⟨?_, ?_⟩
  · intro j k
    by_cases hjk : j = k
    · subst k
      simp only [↓reduceIte]
      exact nonunital_finite_compression_preservation H (fun p => f p.2) (G j)
        (fun p => t i p.2) (a i) hH hfp (hgp j) (hgn j) (hsupport j)
        δ r E δ.2 hδ1 hgram (hmom i j) (hrow i)
    · simp only [hjk, ↓reduceIte, sub_zero]
      have he := nonunital_cross_compression_norm_le H (fun p => f p.2) (G j) (G k)
        (fun p => t i p.2) (a i) δ E δ.2 hH hfp (hgp j) (hgp k) (hgn j) (hgn k)
        (supportedSpectralCopy_disjoint g j k hjk) hgram (hrow i)
      exact he.trans (le_add_of_nonneg_right (by positivity))
  · intro j
    have hsrow := nonunital_squared_row_error_norm_le (a i) H
      (fun p : M × Fin n => t i p.2) E R hR (fun p => ht0 i p.2)
      (fun p => (htR i p.2).trans (by dsimp [R]; linarith)) (hrow i)
    exact nonunital_finite_compression_preservation H (fun p => f p.2) (G j)
      (fun p => (t i p.2) ^ 2) (a i * a i) hH hfp (hgp j) (hgn j) (hsupport j)
      δ (r ^ 2) ((‖a i‖ + R) * E) δ.2 hδ1 hgram (hmom2 i j) hsrow

end WeakPureInfiniteness

end

end OAI
