import OAI.Analysis.KadisonSimilarity.FreeProduct.ArcFourier
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialCompression

namespace OAI

/-! The finite narrow-arc compression, assembled from the trace calculation,
the dihedral expectation, and the actual Fourier integral. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The finite operator matrix identity used by the Hankel test. Every entry
comes from tracial vectors and the two expectation identities. -/
theorem narrow_arc_tracial_compression
    {N : ℕ} (hN : 0 < N)
    (A : StarSubalgebra ℂ R) (τ : R →ₗ[ℂ] ℂ)
    (V : R →ₗ[ℂ] H) (L : R →ₗ[ℂ] (H →L[ℂ] H))
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (v : A → K) (hv : DenseRange v) (ρ : R →ₗ[ℂ] (K →L[ℂ] K))
    (hρ : ∀ (a b : A) x,
      inner ℂ (v a) (ρ x (v b)) = τ (star (a : R) * x * (b : R)))
    (hρone : ρ 1 = ContinuousLinearMap.id ℂ K)
    (E₀ EC : R →ₗ[ℂ] R)
    (htrace : ∀ x, τ (E₀ x) = τ x)
    (hbase : ∀ (a b : A) x, E₀ ((a : R) * x * (b : R)) =
      (a : R) * E₀ x * (b : R))
    (w d : Rˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (e f h : R) (he : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (t : ℝ) (ht : 0 < t) (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → K →L[ℂ] H)
    (hU : ∀ i (a : A), U i (v a) =
      c • V (e * (↑(w ^ (-(i.val : ℤ))) : R) * (a : R)))
    (hEC : EC h = (2 * (t : ℂ)) ^ 2 • (f * dihedralHalfProjection d))
    (hbimod : ∀ j k : ℤ, EC ((↑(w ^ j) : R) * h * (↑(w ^ (-k)) : R)) =
      (↑(w ^ j) : R) * EC h * (↑(w ^ (-k)) : R))
    (htower : ∀ j k : ℤ,
      E₀ (EC ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R))) =
        E₀ ((↑((w) ^ j) : R) * h * (↑((w) ^ (-k)) : R)))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : R) * f = f * (↑(w ^ j) : R))
    (hrot : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R)) =
      arcFourierIntegral (arcWidth N) l • (1 : R))
    (href : ∀ l : ℤ, E₀ (f * (↑(w ^ l) : R) * (↑(w⁻¹ * d) : R)) =
      arcFourierIntegral (arcWidth N) l • (↑(w⁻¹ * d) : R)) :
    (sumColumns U).adjoint.comp ((L h).comp (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ K +
        (arcHankelMatrix N i j : ℂ) • ρ (↑(w⁻¹ * d) : R)) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hentry : ∀ i j : Fin N,
      (U i).adjoint.comp ((L h).comp (U j)) =
        (t : ℂ)⁻¹ • ρ (((2 * (t : ℂ)) ^ 2 / 2) •
          (arcFourierIntegral (arcWidth N) ((i.val : ℤ) - j.val) • (1 : R) +
            arcFourierIntegral (arcWidth N) ((i.val : ℤ) + j.val + 1) •
              (↑(w⁻¹ * d) : R))) := by
    intro i j
    rw [tracial_word_compression_entry A τ V L hinner hleft v hv ρ hρ E₀ htrace hbase
      w hw e h he heh hhe c (t : ℂ)⁻¹ hc i.val j.val (U i) (U j) (hU i) (hU j),
      compressed_dihedral_fourier_entry w d hd f h EC E₀
        (arcFourierIntegral (arcWidth N)) (2 * (t : ℂ)) hEC hbimod htower hcomm hrot href]
  have hmatrix := finite_dihedral_compression U (L h) ρ hρone
    (↑(w⁻¹ * d) : R) (arcFourierIntegral (arcWidth N)) (t : ℂ) htc hentry
  have hθ : 0 ≤ arcWidth N := (arcWidth_pos hN).le
  have hπ : arcWidth N ≤ Real.pi := by
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hwidth : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have hcoeff : ∀ i j : Fin N,
      realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) + j.val + 1) =
        arcHankelMatrix N i j := by
    intro i j
    have h := realArcFourierCoefficient_pos_index (N := N)
      (l := i.val + j.val + 1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, arcHankelMatrix] using h
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat,
    arcFourierIntegral_eq_real hθ hπ, hcoeff] using hmatrix

end KadisonSimilarity

end

end OAI
