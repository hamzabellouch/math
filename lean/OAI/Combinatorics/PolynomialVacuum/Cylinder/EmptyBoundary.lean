import OAI.Combinatorics.PolynomialVacuum.Cylinder.CodedPartition

namespace OAI

namespace PolynomialVacuumCylinder
open Classical Filter PolynomialVacuumAlgebra
open scoped Topology
variable {M H : ℕ} [NeZero M]
noncomputable def emptyArcSystem : ArcSystem (bandSites M H) := ⟨∅,by simp⟩

namespace ArcSystem

theorem empty_of_matches (S : ArcSystem (bandSites M H))
    (h : matchesBoundary (recoverVertical H S.current) (fun _=>.zero) (fun _=>.zero)) :
    S=emptyArcSystem := by
  apply Subtype.ext
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  have hf : orientedFlow S.current A.start= -1 := by
    rw [S.on_member A hA A.start.1 A.start_mem A.start.2,A.current_at_start]
  have h0:=congrFun h.1 A.port.2
  have ht:=congrFun h.2 A.port.2
  rw [A.start_port] at hf
  cases hp:A.port.1
  · simp only [hp,Bool.false_eq_true,ite_false,orientedFlow_up] at hf
    simp [recoverVertical,hf,spinOfCharge] at h0
  · simp only [hp,ite_true,orientedFlow_down,edgeOf] at hf
    norm_num at hf
    have he : S.current ((A.port.2,(H : ℤ)),0)=1 := by linarith
    simp [recoverVertical,he,spinOfCharge] at ht
end ArcSystem

theorem empty_partition_one (H : ℕ) :
    (∑S : ArcSystem (bandSites M H),if matchesBoundary (recoverVertical H S.current)
      (fun _=>.zero) (fun _=>.zero) then S.weight else 0)=(1 : ℂ) := by
  rw [Finset.sum_eq_single (emptyArcSystem (M:=M) (H:=H))]
  · have hz : recoverVertical H (0 : Edge M →₀ ℤ)=(fun _ _=>Spin.zero) := by
      funext j i; simp [recoverVertical,spinOfCharge]
    simp [emptyArcSystem,ArcSystem.current,ArcSystem.weight,matchesBoundary,hz]
  · intro S _ hS
    have hn : ¬matchesBoundary (recoverVertical H S.current) (fun _=>.zero) (fun _=>.zero) := by
      intro hh; exact hS (S.empty_of_matches hh)
    exact ite_eq_right hn
  · simp

theorem arcLimit_empty : arcLimit (M:=M) (fun _=>.zero) (fun _=>.zero)=1 := by
  have ht:=partition_tendsto (M:=M) (fun _=>Spin.zero) (fun _=>Spin.zero)
  simp only [empty_partition_one] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds
end PolynomialVacuumCylinder
namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder Filter
open scoped Topology

theorem physicalTransfer_powers_empty (N H : ℕ) (hH : 0<H) :
    (physicalTransfer (N+1) zeta^H) (fun _=>Spin.zero) (fun _=>Spin.zero)=1 := by
  rw [physicalTransfer_pow_arcs N H hH]
  change (∑S : ArcSystem (bandSites (N+1) H), if matchesBoundary (recoverVertical H S.current)
    (fun _=>.zero) (fun _=>.zero) then S.weight else 0)=1
  exact empty_partition_one H
end PolynomialVacuumAlgebra

end OAI
