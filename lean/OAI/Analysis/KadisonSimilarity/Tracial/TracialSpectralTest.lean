import OAI.Analysis.KadisonSimilarity.Tracial.TracialSpectralNorm
import OAI.Analysis.KadisonSimilarity.Tracial.TracialSpectralColumns

namespace OAI

/-! Construction of the actual operator tested by the free-corner argument.
Its norm and Fourier matrix are conclusions from the elementary published
creation model and the local spectral arc, rather than input estimates. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D C R : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)] [IsClosed (C : Set P)]
  (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

local notation "dU" => symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)
local notation "sU" => symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)
local notation "p" => dihedralHalfProjection
  (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))

variable
  (hp : IsStarProjection (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))))
  (hpD : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ D)
  (hpC : dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq)) ∈ C)
  (htp : G.trace (dihedralHalfProjection
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))) = (1 / 2 : ℂ))

local notation "DA" => CStarCorner.subalgebra p hp D hpD
local notation "CA" => CStarCorner.subalgebra p hp C hpC

omit [IsClosed (A : Set P)] in
/-- A spectral arc supplies an actual small corner operator with the precise
finite Hankel compression required by propagation. -/
theorem exists_actual_spectral_test
    (K : StarSubalgebra ℂ (CStarCorner p hp))
    [IsClosed (K : Set (CStarCorner p hp))]
    (hK : (factorAlgebra DA CA).topologicalClosure = K)
    (compression : RicardXuCompressionInput ((G.halfCornerGeometry dU hp htp).baseGeometry K)
      ((DA).comap K.subtype) ((CA).comap K.subtype))
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCR : C ≤ R) (hDR : D ≤ R) (hfaithful : Function.Injective G.vector)
    (hdC : (d : P) ∈ C) (hsC : (s : P) ∈ C)
    (hdense : ∀ x, x ∈ R → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(s : P)}) : Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑((dU * sU) ^ j) : P) ∈ C)
    (hfree : ScalarFree (CStarCorner.normalizedTrace p hp G.trace) DA CA)
    (hep : p * (e : P) = (e : P)) (hpe : (e : P) * p = (e : P))
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C (dU * sU) dU (arcWidth N))
    (hwidth : 4 * arcWidth N ≤ 2 * t)
    (Y : H →L[ℂ] H) {ε : ℝ}
    (hcorner : ∀ x : CStarCorner (e : P)
      ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
        congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩,
      ‖commutator Y (G.left (x : P))‖ ≤ ε * ‖x‖) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ 3 * (2 * t) ∧
      ‖commutator Y T‖ ≤ ε * ‖T‖ ∧
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
          (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
            ContinuousLinearMap.id ℂ (G.baseSpace A) +
          (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s) := by
  let h := (e : P) * (F.element * p) * (e : P)
  let T := G.left h
  have hπ : arcWidth N ≤ Real.pi := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hw : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have heP : IsStarProjection (e : P) :=
    ⟨congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq,
      congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq⟩
  let eC : CStarCorner p hp := ⟨e, hep, hpe⟩
  have heC : IsStarProjection eC :=
    ⟨Subtype.ext heP.isIdempotentElem.eq, Subtype.ext heP.isSelfAdjoint.star_eq⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · change ‖G.left h‖ ≤ _
    rw [G.norm_left hfaithful]
    exact G.norm_spectral_arc_compression C D (dU * sU) dU hp hpC hpD htp K hK compression
      hfaithful hfree hdC F (arcWidth_pos hN).le hπ eC heC e.property ht.le hte hwidth
  · have hc := hcorner (CStarCorner.compress (e : P) heP (F.element * p))
    change ‖commutator Y (G.left h)‖ ≤ ε * ‖h‖ at hc
    change ‖commutator Y (G.left h)‖ ≤ ε * ‖G.left h‖
    rwa [G.norm_left hfaithful]
  · exact G.spectral_arc_actual_columns A D hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte C R E EC hCR hDR hfaithful hdC hsC hdense hpower hp hpD htp
      hfree hep hpe hN F

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
