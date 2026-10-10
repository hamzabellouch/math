import OAI.Combinatorics.PolynomialVacuum.Pairing.DecoratedStack
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackSeams
import OAI.Combinatorics.PolynomialVacuum.Pairing.UpperLimit

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder Filter
open scoped Topology

noncomputable def physicalCutDiagonal (N k : ℕ) (κ : ℂ) : (Fin (N+1) → Spin) → ℂ :=
  fun s=>(κ/zeta)^cylinderBlockCharge k (cylinderState N s)

theorem decorated_rows_split (N L K k : ℕ) (κ : ℂ) :
    (fun j : Fin (L+(K+1))=>decoratedTransfer N (seamTwists (L+(K+1)) L j) (seamDecoration L k κ j))=
      Fin.append (fun _ : Fin L=>physicalTransfer (N+1) zeta)
        (Fin.cons (physicalTransfer (N+1) zeta⁻¹*Matrix.diagonal (physicalCutDiagonal N k κ))
          (fun _ : Fin K=>physicalTransfer (N+1) zeta⁻¹)) := by
  funext j
  refine Fin.addCases (fun i=>?_) (fun i=>?_) j
  · rw [Fin.append_left]
    ext out inp
    have hi : i.val≠L := by omega
    simp [decoratedTransfer,seamTwists,seamDecoration,Fin.val_castAdd,i.isLt,hi]
  · rw [Fin.append_right]
    refine Fin.cases ?_ (fun i=>?_) i
    · simp only [Fin.cons_zero]
      ext out inp
      simp [decoratedTransfer,seamTwists,seamDecoration,physicalCutDiagonal,Matrix.mul_diagonal]
    · simp only [Fin.cons_succ]
      ext out inp
      have hi : ¬L+i.succ.val<L := by simp only [Fin.val_succ]; omega
      have he : L+i.succ.val≠L := by simp only [Fin.val_succ]; omega
      simp [decoratedTransfer,seamTwists,seamDecoration]

 
noncomputable def finitePhysicalContraction (N k H : ℕ) (κ : ℂ) : ℂ :=
  ∑s : Fin (N+1) → Spin,(physicalTransfer (N+1) zeta⁻¹^(H+1)) (fun _=>.zero) s*
    physicalCutDiagonal N k κ s*(physicalTransfer (N+1) zeta^H) s (fun _=>.zero)

theorem finitePhysicalContraction_rows (N k H : ℕ) (κ : ℂ) :
    finitePhysicalContraction N k H κ=
      layerProduct (fun j : Fin (H+(H+1))=>decoratedTransfer N
        (seamTwists (H+(H+1)) H j) (seamDecoration H k κ j)) (fun _=>.zero) (fun _=>.zero) := by
  rw [decorated_rows_split,layerProduct_marked]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  rfl

theorem finitePhysicalContraction_tendsto (N k : ℕ) (κ : ℂ) :
    Tendsto (fun H=>finitePhysicalContraction N k H κ) atTop
      (nhds (∑s : Fin (N+1) → Spin,
        AnalyticVacuum.normalizedVacuum (N+1) (fun _=>1) s*physicalCutDiagonal N k κ s*
          AnalyticVacuum.normalizedVacuum (N+1) (fun _=>1) s)) := by
  apply tendsto_finsetSum
  intro s _
  have hu:=(physicalUpper_tendsto N s).comp (tendsto_add_atTop_nat 1)
  have hl : Tendsto (fun H=>(physicalTransfer (N+1) zeta^H) s (fun _=>.zero)) atTop
      (nhds (AnalyticVacuum.normalizedVacuum (N+1) (fun _=>1) s)) := by
    rw [AnalyticVacuum.normalizedVacuum_homogeneous]
    exact physicalTransfer_powers_tendsto N s (fun _=>.zero)
  exact (hu.mul_const _).mul hl

end PolynomialVacuumAlgebra

end OAI
