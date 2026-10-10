import OAI.Analysis.KadisonKastler.HilbertSumIsometryMap
import OAI.Analysis.KadisonKastler.CountableConjugacyAssembly
import OAI.Analysis.KadisonKastler.CanonicalAmplification

namespace OAI

/-! # Coordinate changes in a countable block decomposition -/

namespace KadisonKastler

noncomputable section

variable {E F : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℂ (E n)]
  [∀ n, NormedAddCommGroup (F n)] [∀ n, InnerProductSpace ℂ (F n)]
  (e : ∀ n, E n ≃ₗᵢ[ℂ] F n)

def hilbertSumCoordinateEquiv : lp E 2 ≃ₗᵢ[ℂ] lp F 2 :=
  LinearIsometryEquiv.ofSurjective (hilbertSumIsometryMap (fun n => (e n).toLinearIsometry)) (by
    intro g
    apply (hilbertSumIsometryMap_range (fun n => (e n).toLinearIsometry) g).mpr
    intro n
    exact ⟨(e n).symm (g n), (e n).apply_symm_apply (g n)⟩)

@[simp] theorem hilbertSumCoordinateEquiv_apply (f : lp E 2) (n : ℕ) :
    hilbertSumCoordinateEquiv e f n = e n (f n) := rfl

theorem hilbertSumCoordinateEquiv_symm_apply (f : lp F 2) (n : ℕ) :
    (hilbertSumCoordinateEquiv e).symm f n = (e n).symm (f n) := by
  apply (e n).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (fun g : lp F 2 => g n) ((hilbertSumCoordinateEquiv e).apply_symm_apply f)

variable [∀ n, CompleteSpace (E n)] [∀ n, CompleteSpace (F n)]

theorem representsBlockOperators_coordinate_transport
    (R : ∀ n, E n →L[ℂ] E n) (T : lp E 2 →L[ℂ] lp E 2)
    (hT : RepresentsBlockOperators R T) :
    RepresentsBlockOperators (fun n => (e n).conjStarAlgEquiv (R n))
      ((hilbertSumCoordinateEquiv e).conjStarAlgEquiv T) := by
  intro f n
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    hilbertSumCoordinateEquiv_apply]
  rw [hT ((hilbertSumCoordinateEquiv e).symm f) n,
    hilbertSumCoordinateEquiv_symm_apply]

theorem blockAlgebraDecomposition_coordinate_transport
    (M : ∀ n, VonNeumannAlgebra (E n)) (A : VonNeumannAlgebra (lp E 2))
    (hA : BlockAlgebraDecomposition M A) :
    BlockAlgebraDecomposition (fun n => spatialTransportAlgebra (e n) (M n))
      (spatialTransportAlgebra (hilbertSumCoordinateEquiv e) A) := by
  constructor
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨R, hn, hR, ha⟩ := hA.decompose T hT
    refine ⟨fun n => (e n).conjStarAlgEquiv (R n), ?_, ?_,
      representsBlockOperators_coordinate_transport e R T ha⟩
    · intro n
      change ‖(e n).conjStarAlgEquiv (R n)‖ ≤
        ‖(hilbertSumCoordinateEquiv e).conjStarAlgEquiv T‖
      simpa only [norm_spatialConjugate] using hn n
    · intro n
      exact ⟨R n, hR n, rfl⟩
  · intro R C hC hn hR
    let S := fun n => (e n).conjStarAlgEquiv.symm (R n)
    have hSn (n : ℕ) : ‖S n‖ ≤ C := by
      simpa only [S, LinearIsometryEquiv.symm_conjStarAlgEquiv, norm_spatialConjugate] using hn n
    have hSM (n : ℕ) : S n ∈ M n :=
      (mem_spatialTransportAlgebra (e n) (M n) (R n)).mp (hR n)
    obtain ⟨T, hT, ha⟩ := hA.reconstruct S C hC hSn hSM
    refine ⟨(hilbertSumCoordinateEquiv e).conjStarAlgEquiv T, ⟨T, hT, rfl⟩, ?_⟩
    simpa only [S, StarAlgEquiv.apply_symm_apply] using
      representsBlockOperators_coordinate_transport e S T ha

end

end KadisonKastler

end OAI
