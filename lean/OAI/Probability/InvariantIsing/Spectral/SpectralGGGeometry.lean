import OAI.Probability.InvariantIsing.Spectral.SpectralArrayGeometry

namespace OAI

/-! Published ultrametricity and synchronization applied to spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma spectralGram_diagonal {m : ℕ} {x : SpectralArray m} (hG : SpectralGram x)
    (q : Fin m → ℝ) (hd : ∀ i a, (x (i,i) a : ℝ) = q a) (a : Fin m) :
    GramDiagonal (q a) (spectralCoordinateArray a x) :=
  ⟨hG a, fun i => hd i a⟩

def spectralLinearEntry {m : ℕ} (w : Fin m → ℝ) (x : SpectralEntry m) : ℝ :=
  ∑ a, w a * (x a : ℝ)

def spectralLinearArray {m : ℕ} (w : Fin m → ℝ) (x : SpectralArray m) : RealArray :=
  fun i j => spectralLinearEntry w (x (i,j))

lemma continuous_spectralLinearEntry {m : ℕ} (w : Fin m → ℝ) :
    Continuous (spectralLinearEntry w) := by
  unfold spectralLinearEntry
  fun_prop

lemma continuous_spectralLinearArray {m : ℕ} (w : Fin m → ℝ) :
    Continuous (spectralLinearArray w) := by
  unfold spectralLinearArray spectralLinearEntry
  fun_prop

lemma spectralGram_linear {m : ℕ} {x : SpectralArray m} (hG : SpectralGram x)
    (q w : Fin m → ℝ) (hd : ∀ i a, (x (i,i) a : ℝ) = q a)
    (hw : ∀ a, 0 ≤ w a) :
    GramDiagonal (∑ a, w a * q a) (spectralLinearArray w x) := by
  constructor
  · intro n
    have hp := Matrix.posSemidef_sum Finset.univ (fun a _ => (hG a n).smul (hw a))
    have he : (fun i j : Fin n => spectralLinearArray w x i j) =
        ∑ a : Fin m, w a • (fun i j : Fin n => spectralCoordinateArray a x i j) := by
      ext i j
      simp [spectralLinearArray, spectralLinearEntry, spectralCoordinateArray]
    rw [he]
    exact hp
  · intro i
    simp only [spectralLinearArray, spectralLinearEntry, hd]

lemma spectralGG_coordinate_nonnegative {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ a, 0 ≤ (x (0,1) a : ℝ) := by
  apply ae_all_iff.mpr
  intro a
  exact gg_pair_nonnegative_ae (continuous_spectralCoordinateArray a).measurable
    (hgg.real_map (f := fun x => (x a : ℝ)) (by fun_prop)) (hq a)
    (by filter_upwards [hG, hd] with x hx hdx; exact spectralGram_diagonal hx q hdx a)

lemma spectralGG_linear_ultrametric {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), IsUltrametricArray (spectralLinearArray w x) := by
  exact gg_ultrametric_ae (continuous_spectralLinearArray w).measurable
    (scalar_of_spectral_exchangeable hE (spectralLinearEntry w)
      (continuous_spectralLinearEntry w).measurable)
    (hgg.real_map (continuous_spectralLinearEntry w).measurable)
    (Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (hq a))
    (by filter_upwards [hG, hd] with x hx hdx; exact spectralGram_linear hx q w hdx hw)

/-- Nonnegative combinations of the actual spectral and tree coordinates have
ordered joint support. This is the finite-vector consequence used for the
manuscript's simultaneous overlap paths. -/
theorem spectralGG_support_ordered {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w z : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a) :
    let ν := (Q : Measure (SpectralArray m)).map
      (fun x => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1))
    ∀ x ∈ ν.support, ∀ y ∈ ν.support, x.1 < y.1 → x.2 ≤ y.2 := by
  have hsum := spectralGG_linear_ultrametric hgg hG q hq hd hE
    (w + z) (fun a => add_nonneg (hw a) (hz a))
  have he (x : SpectralArray m) : spectralLinearArray (w + z) x =
      fun i j => spectralLinearArray w x i j + spectralLinearArray z x i j := by
    funext i j
    simp only [spectralLinearArray, spectralLinearEntry, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simp_rw [he] at hsum
  exact jointGG_support_ordered (continuous_spectralLinearArray w).measurable
    (continuous_spectralLinearArray z).measurable
    (hgg.map (f := fun x => (spectralLinearEntry w x, spectralLinearEntry z x))
      ((continuous_spectralLinearEntry w).prodMk (continuous_spectralLinearEntry z)).measurable)
    (spectralGG_linear_ultrametric hgg hG q hq hd hE w hw)
    (spectralGG_linear_ultrametric hgg hG q hq hd hE z hz) hsum
    (by filter_upwards [hG, hd] with x hx hdx
        exact (spectralGram_linear hx q w hdx hw).symm)
    (by filter_upwards [hG, hd] with x hx hdx
        exact (spectralGram_linear hx q z hdx hz).symm)

end InvariantIsing

end

end OAI
