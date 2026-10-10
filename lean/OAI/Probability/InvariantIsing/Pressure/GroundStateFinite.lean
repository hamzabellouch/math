import OAI.Probability.InvariantIsing.Pressure.PhysicalPressureMean
import OAI.Probability.InvariantIsing.Pressure.ThermalPressure

namespace OAI

/-! The actual maximum Ising energy and its uniform finite-temperature squeeze. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace InvariantIsing

def groundStateEnergy {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N) : ℝ :=
  (N : ℝ)⁻¹ * Finset.univ.sup' Finset.univ_nonempty (rotatedEnergy eig U)

lemma groundStateEnergy_attained {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) :
    (∀ σ, rotatedEnergy eig U σ ≤ N*groundStateEnergy eig U) ∧
      ∃ σ, rotatedEnergy eig U σ=N*groundStateEnergy eig U := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N : ℝ)*groundStateEnergy eig U=
      Finset.univ.sup' Finset.univ_nonempty (rotatedEnergy eig U) := by
    unfold groundStateEnergy
    field_simp
  rw [he]
  constructor
  · intro σ
    exact Finset.le_sup' _ (Finset.mem_univ σ)
  · obtain ⟨σ,_,hσ⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (rotatedEnergy eig U)
    exact ⟨σ,hσ.symm⟩

lemma groundStateEnergy_squeeze {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (β : ℝ) (hβ : 0 < β) :
    rotatedPressure (fun i => β*eig i) U (fun _ => 0)/β ≤ groundStateEnergy eig U ∧
      groundStateEnergy eig U ≤
        rotatedPressure (fun i => β*eig i) U (fun _ => 0)/β+Real.log 2/β := by
  have he := groundStateEnergy_attained hN eig U
  have hh := finite_groundState_squeeze hN (rotatedEnergy eig U) β
    (groundStateEnergy eig U) hβ he.1 he.2
  have hp : rotatedPressure (fun i => β*eig i) U (fun _ => 0)=
      (N : ℝ)⁻¹*logPartition (fun σ => β*rotatedEnergy eig U σ) := by
    simp only [rotatedPressure,rotatedEnergy_scale,fieldEnergy,zero_mul,Finset.sum_const_zero,add_zero]
  rw [hp]
  exact ⟨hh.2,by linarith [hh.1]⟩

lemma abs_groundStateEnergy_le {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (K : ℝ) (hK : ∀ i, |eig i| ≤ K) :
    |groundStateEnergy eig U| ≤ K/2 := by
  obtain ⟨σ,hσ⟩ := (groundStateEnergy_attained hN eig U).2
  have hh := abs_rotatedEnergy_le eig U K hK σ
  rw [hσ,abs_mul,abs_of_nonneg (Nat.cast_nonneg N)] at hh
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  nlinarith

lemma measurable_groundStateEnergy {N : ℕ} (eig : Fin N → ℝ) :
    Measurable (fun V : SpecialOrthogonal N => groundStateEnergy eig (specialRotation V)) := by
  have hE (σ : Spin N) : Measurable (fun V : SpecialOrthogonal N =>
      rotatedEnergy eig (specialRotation V) σ) :=
    (Finset.measurable_sum _ fun i _ =>
      ((measurable_specialRotation_eval (spinVector σ) i).pow_const 2).const_mul (eig i)).const_mul _
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun σ _ => hE σ)
  convert hh.const_mul (N : ℝ)⁻¹ using 1
  funext V
  simp only [groundStateEnergy,Finset.sup'_apply]

lemma measurable_physical_groundStateEnergy {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) :
    Measurable (fun V : Orthogonal N => groundStateEnergy eig (matrixRotation V⁻¹)) := by
  have hm := (measurable_groundStateEnergy eig).comp
    ((measurable_cavityOrientationLift hN).comp measurable_inv)
  convert hm using 1
  funext V
  simp only [Function.comp_apply,groundStateEnergy,cavityOrientationLift_energy]

end InvariantIsing

end

end OAI
