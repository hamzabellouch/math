import Mathlib

namespace OAI


noncomputable section

open MeasureTheory Module Submodule
open scoped BigOperators

namespace Problem355.LatticeLowerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {n : ℕ}

theorem volumeReal_fundamentalDomain_orthonormal (o : OrthonormalBasis (Fin n) ℝ E) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [measureReal_def,
    measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  change (volume (parallelepiped o)).toReal = 1
  rw [o.volume_parallelepiped]
  simp

theorem covolume_span_basis_le_prod_norm (b : Basis (Fin n) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ≤ ∏ i, ‖b i‖ := by
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b
  have hvol : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 :=
    volumeReal_fundamentalDomain_orthonormal o
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis, hvol, mul_one]
  change |(InnerProductSpace.gramSchmidtOrthonormalBasis (Module.finrank_eq_card_basis b) b).toBasis.det b| ≤ _
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det, Finset.abs_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro i _
  calc
    |@inner ℝ E _ (o i) (b i)| ≤ ‖o i‖ * ‖b i‖ := abs_real_inner_le_norm _ _
    _ = ‖b i‖ := by rw [o.norm_eq_one]; ring

theorem covolume_mono_reverse (L₁ L₂ : Submodule ℤ E)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂] (hL : L₁ ≤ L₂) :
    ZLattice.covolume L₂ ≤ ZLattice.covolume L₁ := by
  have hratio := ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ hL
  have hpos : 0 < (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [← hratio]
    exact div_pos (ZLattice.covolume_pos L₁) (ZLattice.covolume_pos L₂)
  have hnat : 1 ≤ L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
    have : 0 < L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by exact_mod_cast hpos
    omega
  have hone : (1 : ℝ) ≤ ZLattice.covolume L₁ / ZLattice.covolume L₂ := by
    rw [hratio]
    exact_mod_cast hnat
  have hh := (le_div_iff₀ (ZLattice.covolume_pos L₂)).mp hone
  simpa only [one_mul] using hh

theorem covolume_le_prod_norm (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L) :
    ZLattice.covolume L ≤ ∏ i, ‖b i‖ := by
  have hspan : Submodule.span ℤ (Set.range b) ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  exact (covolume_mono_reverse _ _ hspan).trans (covolume_span_basis_le_prod_norm b)

theorem relIndex_span_basis_le (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : ∀ i, b i ∈ L) :
    ((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≤
      (∏ i, ‖b i‖) / ZLattice.covolume L := by
  have hspan : Submodule.span ℤ (Set.range b) ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  rw [← ZLattice.covolume_div_covolume_eq_relIndex' _ _ hspan]
  exact div_le_div_of_nonneg_right (covolume_span_basis_le_prod_norm b)
    (ZLattice.covolume_pos L).le

end Problem355.LatticeLowerProduct

end

end OAI
