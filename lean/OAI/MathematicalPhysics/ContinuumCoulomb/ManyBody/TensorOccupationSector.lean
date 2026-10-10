import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.OccupationSector
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockTensorCompression

namespace OAI

/-! Every antisymmetric coefficient tensor lies in the complete fixed-particle
occupation sector, including tensors obtained by continuum projection. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb
open Laughlin.Fock HubbardGlobal

theorem totalNumber_wedgeModes {Q n : ℕ} (v : Fin n → Fin (Q+1)) :
    totalNumber Q (wedgeModes n v) = (n:ℂ) • wedgeModes n v := by
  simp only [totalNumber,LinearMap.sum_apply,number,transfer_wedgeModes]
  rw [Finset.sum_comm]
  have hi (k : Fin n) :
      (∑ i : Fin (Q+1), delta i (v k) •
        wedgeModes n (fun a => if a=k then i else v a)) = wedgeModes n v := by
    simp only [delta,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    congr 1
    funext a
    split_ifs with h
    · subst a
      rfl
    · rfl
  simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ]

theorem totalNumber_normalizedTensorExterior {Q n : ℕ} (ψ : Laughlin.State n Q) :
    totalNumber Q (normalizedTensorExterior n Q ψ) =
      (n:ℂ) • normalizedTensorExterior n Q ψ := by
  simp only [normalizedTensorExterior,tensorExterior,map_smul,map_sum]
  have he (a : Laughlin.Configuration n Q) :
      totalNumber Q (ExteriorAlgebra.ιMulti ℂ n (fun i => mode (a i))) =
        (n:ℂ) • ExteriorAlgebra.ιMulti ℂ n (fun i => mode (a i)) :=
    totalNumber_wedgeModes a
  simp only [he,Finset.smul_sum,smul_smul]
  congr 1
  funext a
  congr 1
  ring

theorem normalizedTensorExterior_occupationSupport {Q n : ℕ} (ψ : Laughlin.State n Q)
    (A : Finset (Fin (Q+1))) (hA : A.card ≠ n) :
    (fockBasis Q).repr (normalizedTensorExterior n Q ψ) A = 0 :=
  totalNumber_eigen_coordinate_zero n _ (totalNumber_normalizedTensorExterior ψ) A hA

theorem exists_occupationTensor {Q n : ℕ} (ψ : Laughlin.State n Q)
    (hψ : Laughlin.Antisymmetric ψ) :
    ∃ c : EuclideanSpace ℂ (SlaterOccupation.Occupied Q n),
      FockSlaterTensor.occupationTensor c = ψ ∧
      OccupationFock.vector c = normalizedTensorExterior n Q ψ := by
  obtain ⟨c,hc⟩ := OccupationFock.exists_vector_of_support _
    (normalizedTensorExterior_occupationSupport ψ)
  refine ⟨c,?_,hc⟩
  have he := congrArg (normalizedTensorReadout n Q)
    ((OccupationFock.vector_normalizedTensorExterior c).symm.trans hc)
  simpa only [normalizedTensorReadout_left_inverse n Q _
    (FockSlaterTensor.occupationTensor_antisymmetric c),
    normalizedTensorReadout_left_inverse n Q ψ hψ] using he

end ContinuumCoulomb

end

end OAI
