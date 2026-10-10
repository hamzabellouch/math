import OAI.Geometry.HeilbronnTriangle.LatticePacking

namespace OAI


namespace Problem355.FiniteIndexPlane

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

theorem discrete_of_le (Γ L : Submodule ℤ E) [DiscreteTopology L]
    (hΓL : Γ ≤ L) : DiscreteTopology Γ := by
  apply DiscreteTopology.of_continuous_injective
    (f := Submodule.inclusion hΓL) _ (Submodule.inclusion_injective hΓL)
  change Continuous (fun x : Γ => (⟨x.1, hΓL x.2⟩ : L))
  fun_prop

theorem relIndex_nsmul_mem (Γ L : Submodule ℤ E) (x : E) (hx : x ∈ L) :
    Γ.toAddSubgroup.relIndex L.toAddSubgroup • x ∈ Γ := by
  exact (Γ.toAddSubgroup.addSubgroupOf L.toAddSubgroup).nsmul_index_mem
    (⟨x, hx⟩ : L.toAddSubgroup)

theorem isZLattice_of_relIndex_ne_zero [NormedSpace ℝ E] (Γ L : Submodule ℤ E)
    [DiscreteTopology Γ] [DiscreteTopology L] [IsZLattice ℝ L]
    (hindex : Γ.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    IsZLattice ℝ Γ := by
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := L)]
  apply Submodule.span_le.mpr
  intro x hx
  change x ∈ Submodule.span ℝ (Γ : Set E)
  have hmem := Submodule.subset_span (R := ℝ) (relIndex_nsmul_mem Γ L x hx)
  have hreal : (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hindex
  have hscaled := (Submodule.span ℝ (Γ : Set E)).smul_mem
    (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ)⁻¹ hmem
  simpa only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hreal, one_smul] using hscaled

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem covolume_eq_index_mul (Γ L : Submodule ℤ E)
    [DiscreteTopology Γ] [DiscreteTopology L] [IsZLattice ℝ Γ] [IsZLattice ℝ L]
    (hΓL : Γ ≤ L) :
    ZLattice.covolume Γ =
      (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L := by
  have hvol := ZLattice.covolume_pos L volume
  exact (div_eq_iff hvol.ne').mp
    (ZLattice.covolume_div_covolume_eq_relIndex' Γ L hΓL)

theorem spanning_triples_card_le (hdim : Module.finrank ℝ E = 2)
    (Γ L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hΓL : Γ ≤ L) (m : ℕ) (hm : 0 < m)
    (hindex : Γ.toAddSubgroup.relIndex L.toAddSubgroup = m)
    (A : Finset (Fin 3 → Γ)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)]) :
    (A.card : ℝ) ≤
      (9 * Real.pi * R ^ 2 / ((m : ℝ) * ZLattice.covolume L)) ^ 3 := by
  let : DiscreteTopology Γ := discrete_of_le Γ L hΓL
  let : IsZLattice ℝ Γ := isZLattice_of_relIndex_ne_zero Γ L (by omega)
  have h := LatticePacking.plane_spanning_triples_card_le hdim Γ A R hR hA hpair
  rwa [covolume_eq_index_mul Γ L hΓL, hindex] at h

end Problem355.FiniteIndexPlane

end OAI
