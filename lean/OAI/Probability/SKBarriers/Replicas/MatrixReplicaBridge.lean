import Mathlib
import OAI.Probability.SKBarriers.Coverage.PressureGapFiniteInf
import OAI.Probability.SKBarriers.Replicas.MatrixSKGuerra

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def replicaGram {n d : ℕ} (s : ReplicaConfig n d) (a b : Fin d) : ℝ := overlap (s a) (s b)

def matrixReplicaSet (n d : ℕ) (D : Fin d → Fin d → ℝ) : Finset (ReplicaConfig n d) := by
  classical
  exact Finset.univ.filter (fun s => replicaGram s=D)

@[simp] theorem mem_matrixReplicaSet {n d : ℕ} (D : Fin d → Fin d → ℝ) (s : ReplicaConfig n d) :
    s∈matrixReplicaSet n d D ↔ replicaGram s=D := by
  classical
  simp [matrixReplicaSet]

def matrixReplicaEquiv (n d : ℕ) (D : Fin d → Fin d → ℝ) :
    MatrixStates n d D ≃ {s : ReplicaConfig n d // s∈matrixReplicaSet n d D} where
  toFun s := ⟨fun a i => s.val i a,(mem_matrixReplicaSet D _).mpr s.property⟩
  invFun s := ⟨fun i a => s.val a i,(mem_matrixReplicaSet D _).mp s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem matrixReplicaSet_nonempty_iff {n d : ℕ} (D : Fin d → Fin d → ℝ) :
    (matrixReplicaSet n d D).Nonempty ↔ Nonempty (MatrixStates n d D) := by
  rw [← Finset.nonempty_coe_sort]
  exact (matrixReplicaEquiv n d D).nonempty_congr.symm

theorem restrictedPressure_matrixReplicaSet (n d : ℕ) (β : ℝ) (D : Fin d → Fin d → ℝ) :
    restrictedPressure β (matrixReplicaSet n d D)=matrixConstrainedPressure n d β D := by
  classical
  unfold restrictedPressure matrixConstrainedPressure
  congr 1
  apply integral_congr_ae
  filter_upwards [] with J
  unfold restrictedLogPartition restrictedPartition replicaEnergy
  congr 1
  rw [← Finset.sum_coe_sort]
  exact ((matrixReplicaEquiv n d D).sum_comp (fun s => Real.exp (β*∑ a,hamiltonian J (s.val a)))).symm

end SK.Analytic

end
end

end OAI
