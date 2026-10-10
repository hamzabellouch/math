import OAI.NumberTheory.Ostmann.Supply.TensorModeEnergy
import OAI.NumberTheory.Ostmann.Supply.TensorModePolynomial

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators
open scoped TensorProduct BigOperators

theorem norm_inner_of_lowModes_support {E F : ℕ → FiniteHilbertSpace} (n K : ℕ)
    (T : tensorSpace (fun i => augmentedSpace (E i)) n →L[ℂ]
      tensorSpace (fun i => augmentedSpace (F i)) n)
    (hT : T = ((lowModes F n K).comp T).comp (lowModes E n K))
    (v : tensorSpace (fun i => augmentedSpace (F i)) n)
    (w : tensorSpace (fun i => augmentedSpace (E i)) n) :
    ‖inner ℂ v (T w)‖ ≤ ‖T‖ * ‖lowModes F n K v‖ * ‖lowModes E n K w‖ := by
  have he : inner ℂ v (T w) =
      inner ℂ (lowModes F n K v) (T (lowModes E n K w)) := by
    calc
      _ = inner ℂ v (lowModes F n K (T (lowModes E n K w))) :=
        congrArg (fun L => inner ℂ v (L w)) hT
      _ = _ := by
        have h := (lowModes_star F n K).isSelfAdjoint.isSymmetric v (T (lowModes E n K w))
        exact h.symm
  rw [he]
  calc
    _ ≤ ‖lowModes F n K v‖ * ‖T (lowModes E n K w)‖ := norm_inner_le_norm _ _
    _ ≤ ‖lowModes F n K v‖ * (‖T‖ * ‖lowModes E n K w‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

theorem norm_inner_rectangularTruncation {E F : ℕ → FiniteHilbertSpace}
    (c : ∀ i, (ℕ × ℕ) →₀ (augmentedSpace (E i) →L[ℂ] augmentedSpace (F i))) (n K : ℕ)
    (hout : ∀ i < n, (centeredPart (F i)).comp (c i (0,0)) = 0)
    (hin : ∀ i < n, (c i (0,0)).comp (centeredPart (E i)) = 0)
    (v : tensorSpace (fun i => augmentedSpace (F i)) n)
    (w : tensorSpace (fun i => augmentedSpace (E i)) n) :
    ‖inner ℂ v (BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K w)‖ ≤
      ‖BivariateTruncation.rectangularTruncation (tensorFamilyPolynomial c n) K‖ *
        ‖lowModes F n (2*K) v‖ * ‖lowModes E n (2*K) w‖ :=
  norm_inner_of_lowModes_support n (2*K) _
    (rectangularTruncation_lowModes c n K hout hin) v w

end Ostmann.Supply.TensorModes

end

end OAI
