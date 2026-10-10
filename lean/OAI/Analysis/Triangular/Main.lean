import OAI.Analysis.Triangular.Schwartz.GaussianPair

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap lp
open Complex Matrix

namespace AtomicTriangular.Construction

end AtomicTriangular.Construction

namespace AtomicTriangular.Construction

lemma finiteCoordinates_coefficientInput (C : ℝ) (a : TrigonometricCoefficients)
    (w : TailCoefficients) (i : Fin 22) :
    finiteCoordinates (coefficientInput C a w) i = a i := by
  unfold finiteCoordinates coefficientInput
  split_ifs with hi
  · exact congrArg (fun j : Fin 22 => a j) (Fin.ext (by dsimp; omega))
  · exact congrArg (fun j : Fin 22 => a j) (Fin.ext (by dsimp; omega))

lemma actualInput_fixed_zero (side : Fin 2) {z : ℝ} (hz : 0 < z) (hzB : z ≤ Z) :
    (actualInput side z hz hzB).finiteC 0 = 11/25 ∧
    (actualInput side z hz hzB).finiteD 0 = 0 := by
  constructor
  · change finiteApprox side (actualParameter z) 0 +
      extendFiniteError (actualFiniteError side z hz hzB) 0 = 11/25
    erw [finiteApprox_fixed side (actualParameter z) 0,
      extendFiniteError_fixed (actualFiniteError side z hz hzB) 0,
      add_zero, gamma_actual]
    rfl
  · change finiteApprox side (actualParameter z) 1 +
      extendFiniteError (actualFiniteError side z hz hzB) 1 = 0
    erw [finiteApprox_fixed side (actualParameter z) 1,
      extendFiniteError_fixed (actualFiniteError side z hz hzB) 1,
      add_zero, gamma_actual]
    rfl

lemma largeGaussian_hasAtomicConstruction {α : ℝ} (hα : 1 ≤ α) :
    HasAtomicConstruction α (largeGaussianPair hα).first := by
  let z := gaussianZ α
  have hz : 0 < z := (gaussianZ_bounds hα).1
  have hzB : z ≤ Z := (gaussianZ_bounds hα).2.le
  refine ⟨FiniteCertificate.minusBlock_isUnit, FiniteCertificate.plusBlock_isUnit,
    Uplus_equation, Uminus_equation,
    (fun side => actualInput side z hz hzB),
    (fun side i => actualFiniteError side z hz hzB i), ?_, ?_, ?_⟩
  · intro side
    obtain ⟨hc, hd⟩ := actualInput_fixed_zero side hz hzB
    refine ⟨rfl, hc, hd, ?_⟩
    intro i
    dsimp only
    rw [actualInput, finiteCoordinates_coefficientInput]
    rfl
  · intro side
    refine ⟨?_, (actualInput side z hz hzB).summable, ?_⟩
    · simpa only [AtomicTriangular.L1Kernel.l1_norm, tsum_fintype] using
        actualFiniteError_norm side hz hzB
    · change (∑' n : TailNode,
        (|actualTail side z hz hzB (n,0)| + |actualTail side z hz hzB (n,1)|)) < _
      rw [tail_pairs_norm]
      exact actualTail_norm side hz hzB
  · intro x
    change ((((normalizingDen z)⁻¹ *
        pairSchwartz (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) x : ℝ) : ℂ)) = _
    rw [Complex.ofReal_mul, Complex.ofReal_inv, ← pairComplex_eq, fourier_inputComplex]
    simp only [pairComplex, Pi.add_apply]
    ring

end AtomicTriangular.Construction

namespace AtomicTriangular

theorem sharp_gaussian_minorants_atomic (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → Construction.HasAtomicConstruction α f) := by
  let p := gaussianPair α hα
  refine ⟨p.first, p.first_radial, p.minorant, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [p.fourier_first]
    exact ⟨rfl, p.positive w⟩
  · intro a ha ha0
    obtain ⟨n, hn⟩ := A_radial_node ha ha0
    exact p.contact a n hn
  · intro w hw hw0
    obtain ⟨n, hn⟩ := dualA_radial_node hw hw0
    rw [p.fourier_first, p.zeros w n hn, ofReal_zero]
  · intro hlarge
    change Construction.HasAtomicConstruction α (gaussianPair α hα).first
    rw [gaussianPair, dite_eq_left hlarge]
    exact Construction.largeGaussian_hasAtomicConstruction hlarge

end AtomicTriangular

end

end OAI
