import OAI.Analysis.TriangularHilbert.JumpScalar

namespace OAI

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators
noncomputable section

lemma finite_mesh_mass_le (D : Finset ℤ) {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (p : ℝ) :
    (∑ i : D, weight h (h*(i:ℤ)) p σ) ≤ meshMassConstant := by
  let N := supportRadius D 0
  have hD : D ⊆ intInterval 0 N := by
    intro m hm
    rw [mem_intInterval_iff_dist]
    exact Finset.le_sup (f := fun k : ℤ => (k-0).natAbs) hm
  rw [Finset.sum_coe_sort D (fun i : ℤ => weight h (h*(i:ℝ)) p σ)]
  have hi : (∑ i ∈ D, weight h (h*(i:ℝ)) p σ) ≤ ∑ i ∈ intInterval 0 N, weight h (h*(i:ℝ)) p σ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hD
    intro i _ _
    exact (weight_pos hh ((sq_pos_of_pos hh).trans_le hσ) _ _).le
  apply hi.trans
  rw [intInterval_sum_fin]
  have he (i : Fin (2*N+1)) : weight h (h*((0-(N:ℤ)+(i:ℕ):ℤ):ℝ)) p σ =
      h*density σ ((-(h*N)-p)+h*i) := by
    unfold weight
    congr 2
    push_cast
    ring
  simp_rw [he]
  exact mesh_mass_le hh hσ (-(h*N)-p) (2*N+1)

lemma finite_mesh_totalPlaneEnergy_le (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    {h : ℝ} (hh : 0 < h) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ v, h^2 ≤ σ v) :
    totalPlaneEnergy A h (fun i => h*(i:ℤ)) d σ ≤
      2*Real.sqrt 2*meshMassConstant*arrayCubic A h := by
  exact totalPlaneEnergy_le_mass A hh _ d (fun v => (sq_pos_of_pos hh).trans_le (hσ v)) meshMassConstant_pos.le
    (fun p v => finite_mesh_mass_le D hh (hσ v) (p v))
end
end TriangularHilbert.Heat
end

end OAI
