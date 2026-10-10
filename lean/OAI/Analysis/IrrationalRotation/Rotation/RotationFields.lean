import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplier
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem commute_star_left_of_mem_unitary {A B : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ unitary (Hilbert →L[ℂ] Hilbert)) (hAB : Commute A B) :
    Commute (star A) B := by
  obtain ⟨h₁, h₂⟩ := Unitary.mem_iff.mp hA
  show star A * B = B * star A
  calc
    star A * B = star A * (B * (A * star A)) := by rw [h₂, mul_one]
    _ = star A * ((A * B) * star A) := by rw [← mul_assoc B A, ← hAB.eq]
    _ = (star A * A) * (B * star A) := by simp only [mul_assoc]
    _ = B * star A := by rw [h₁, one_mul]

theorem U_commutes_multiplier (g : Lp ℂ ∞ circleMeasure) :
    Commute U (L2Multiplication.multiplier (E := Fiber) g) := by
  show U * L2Multiplication.multiplier g = L2Multiplication.multiplier g * U
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [U_coordinates_ae (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ, L2Multiplication.multiplier_coe g (U ξ),
    U_coordinates_ae ξ] with x hU hM hMU hUξ
  intro k
  change U (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (U ξ) x k
  rw [hU k, hM, hMU]
  change g x * ξ x (k - 1) = g x * U ξ x k
  rw [hUξ k]

theorem representation_commutes_multiplier (θ : ℝ) (a : C(Circle, ℂ))
    (g : Lp ℂ ∞ circleMeasure) :
    Commute (representation θ a) (L2Multiplication.multiplier (E := Fiber) g) := by
  show representation θ a * L2Multiplication.multiplier g =
    L2Multiplication.multiplier g * representation θ a
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ a (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ,
    L2Multiplication.multiplier_coe g (representation θ a ξ),
    representation_coordinates_ae θ a ξ] with x ha hM hMa haξ
  intro k
  change representation θ a (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (representation θ a ξ) x k
  rw [ha k, hM, hMa]
  change a (action θ k x) * (g x * ξ x k) =
    g x * representation θ a ξ x k
  rw [haξ k]
  ring

theorem multiplier_mem_commutant (θ : ℝ) (g : Lp ℂ ∞ circleMeasure) :
    L2Multiplication.multiplier (E := Fiber) g ∈ (algebra θ).commutant := by
  apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
  intro A hA
  rcases Set.mem_insert_iff.mp hA with rfl | hA
  · exact ⟨(U_commutes_multiplier g).eq,
      (commute_star_left_of_mem_unitary U_mem_unitary (U_commutes_multiplier g)).eq⟩
  · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
    subst A
    have hcomm := representation_commutes_multiplier θ character g
    exact ⟨hcomm.eq,
      (commute_star_left_of_mem_unitary (V_mem_unitary θ) hcomm).eq⟩

theorem algebra_commutes_multiplier (θ : ℝ) {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) (g : Lp ℂ ∞ circleMeasure) :
    Commute T (L2Multiplication.multiplier (E := Fiber) g) := by
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (multiplier_mem_commutant θ g)) T hT

end Invariant233.Rotation

end

end OAI
