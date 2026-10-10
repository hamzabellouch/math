import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternOrbit
import OAI.Probability.InvariantIsing.Pressure.GroundStateFinite
import OAI.Probability.InvariantIsing.Pressure.RandomSpectralMeasurability

namespace OAI

/-! Actual Gaussian-pattern maximum energies and their finite-temperature squeeze. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace InvariantIsing

def gaussianPatternGroundEnergy {N m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  (N : ℝ)⁻¹*Finset.univ.sup' Finset.univ_nonempty
    (fun σ : Spin N => ε/(2*N)*‖gaussianPatternSum z σ‖^2)

lemma measurable_gaussianPatternGroundEnergy (N m : ℕ) (ε : ℝ) :
    Measurable (gaussianPatternGroundEnergy (N := N) (m := m) ε) := by
  have hm (σ : Spin N) : Measurable (fun z : EuclideanSpace ℝ (Fin N × Fin m) =>
      ε/(2*N)*‖gaussianPatternSum z σ‖^2) := by
    have hs : Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin m) => gaussianPatternSum z σ) := by
      unfold gaussianPatternSum gaussianPatternArray
      fun_prop
    exact (hs.measurable.norm.pow_const 2).const_mul _
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun σ _ => hm σ)
  convert hh.const_mul (N : ℝ)⁻¹ using 1
  funext z
  simp only [gaussianPatternGroundEnergy,Finset.sup'_apply]

lemma gaussianPatternGroundEnergy_squeeze {N m : ℕ} (hN : 0 < N) (ε β : ℝ)
    (hβ : 0 < β) (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternPressure (ε*β) z/β ≤ gaussianPatternGroundEnergy ε z ∧
    gaussianPatternGroundEnergy ε z ≤ gaussianPatternPressure (ε*β) z/β+Real.log 2/β := by
  let E := fun σ : Spin N => ε/(2*N)*‖gaussianPatternSum z σ‖^2
  have hval : (N : ℝ)*gaussianPatternGroundEnergy ε z=
      Finset.univ.sup' Finset.univ_nonempty E := by
    unfold gaussianPatternGroundEnergy
    rw [← mul_assoc,mul_inv_cancel₀ (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne'),one_mul]
  have hb : ∀ σ, E σ ≤ N*gaussianPatternGroundEnergy ε z := by
    rw [hval]
    exact fun σ => Finset.le_sup' E (Finset.mem_univ σ)
  have ha : ∃ σ, E σ=N*gaussianPatternGroundEnergy ε z := by
    obtain ⟨σ,_,hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty E
    exact ⟨σ,hσ.symm.trans hval.symm⟩
  have hh := finite_groundState_squeeze hN E β (gaussianPatternGroundEnergy ε z) hβ hb ha
  have hp : gaussianPatternPressure (ε*β) z=(N : ℝ)⁻¹*logPartition (fun σ => β*E σ) := by
    unfold gaussianPatternPressure
    congr 2
    funext σ
    dsimp [E]
    ring
  rw [hp]
  exact ⟨hh.2,by linarith [hh.1]⟩

lemma gaussianPatternGroundEnergy_orbit {N m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    ∃ V : Orthogonal N, gaussianPatternGroundEnergy ε z=
      groundStateEnergy (fun i => ε*gaussianPatternEigenvalues z i) (matrixRotation V⁻¹) := by
  obtain ⟨V,hV⟩ := gaussianPattern_diagonalization z
  refine ⟨V,?_⟩
  have he (σ : Spin N) : ε/(2*N)*‖gaussianPatternSum z σ‖^2=
      rotatedEnergy (fun i => ε*gaussianPatternEigenvalues z i) (matrixRotation V⁻¹) σ := by
    rw [← gaussianPattern_energy,gaussianPatternCoupling_smul,hV,cavityConjugate_diagonal_smul]
    exact cavityQuadratic_inverse_rotation _ V σ
  unfold gaussianPatternGroundEnergy groundStateEnergy
  simp only [he]

lemma abs_gaussianPatternGroundEnergy_le {n m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin (n+1) × Fin m)) :
    |gaussianPatternGroundEnergy ε z| ≤
      spectralRadius (fun i => ε*gaussianPatternEigenvalues z i)/2 := by
  obtain ⟨V,hV⟩ := gaussianPatternGroundEnergy_orbit ε z
  rw [hV]
  exact abs_groundStateEnergy_le (Nat.succ_pos n) _ _ _ (abs_le_spectralRadius _)

lemma gaussianPatternGroundEnergy_nonneg {N m : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : 0 ≤ gaussianPatternGroundEnergy ε z := by
  apply mul_nonneg (by positivity)
  exact (mul_nonneg (div_nonneg hε (by positivity)) (sq_nonneg _)).trans
    (Finset.le_sup' (fun σ : Spin N => ε/(2*N)*‖gaussianPatternSum z σ‖^2)
      (Finset.mem_univ (fun _ => false)))

lemma gaussianPatternGroundEnergy_nonpos {N m : ℕ} (ε : ℝ) (hε : ε ≤ 0)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : gaussianPatternGroundEnergy ε z ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply Finset.sup'_le
  intro σ _
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hε (by positivity)) (sq_nonneg _)

end InvariantIsing

end

end OAI
