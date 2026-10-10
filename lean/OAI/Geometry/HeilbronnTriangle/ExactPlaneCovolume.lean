import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice
import OAI.Geometry.HeilbronnTriangle.IntegralPlaneDeterminant

namespace OAI


noncomputable section

namespace Problem355.IntegralPlaneLattice

open Module
open scoped BigOperators Matrix

theorem lattice_covolume_of_equiv
    (y z : Fin 3 → ℤ) (hyz : ∑ i, y i * z i = 1)
    (e : integerPlane y ≃ₗ[ℤ] lattice y)
    (he : ∀ v, (((e v : lattice y) : plane y) :
      EuclideanSpace ℝ (Fin 3)) = castVec (v : Fin 3 → ℤ)) :
    ZLattice.covolume (lattice y) = ‖castVec y‖ := by
  let := isZLattice y z hyz
  let f : (Fin 3 → ℤ) →ₗ[ℤ] ℤ := integerDot y
  have hfz : f z = 1 := hyz
  have hf : f ≠ 0 := by
    intro h
    have hh := hfz
    rw [h] at hh
    norm_num at hh
  let bZ : Basis (Fin 2) ℤ f.ker :=
    Classical.choice (LatticeSplit.exists_plane_kernel_basis f hf)
  let b : Basis (Fin 2) ℤ (lattice y) := bZ.map e
  let emb := (plane y).subtypeₗᵢ
  have hb (i : Fin 2) : emb (b i) = castVec (bZ i : Fin 3 → ℤ) := by
    exact he (bZ i)
  have hdet : |Matrix.det ![(emb (b 0)).ofLp, (emb (b 1)).ofLp,
      (castVec z).ofLp]| = 1 := by
    rw [hb 0, hb 1]
    exact Lattice.abs_det_primitive_kernel_basis_extension f z hfz bZ
  have hzero (i : Fin 2) : (emb (b i)).ofLp ⬝ᵥ (castVec y).ofLp = 0 := by
    rw [dotProduct_comm]
    exact (b i : plane y).property
  have hheight : (castVec y).ofLp ⬝ᵥ (castVec z).ofLp = (1 : ℝ) := by
    change (∑ i, (y i : ℝ) * (z i : ℝ)) = 1
    exact_mod_cast hyz
  have h := Lattice.covolume_eq_index_mul_norm_div
    (lattice y) b emb (castVec z).ofLp (castVec y).ofLp
    1 1 (hzero 0) (hzero 1) hdet hheight (by norm_num)
  simpa only [one_mul, div_one, WithLp.toLp_ofLp] using h

theorem lattice_covolume (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1) :
    ZLattice.covolume (lattice y) = ‖castVec y‖ := by
  apply lattice_covolume_of_equiv y z hyz (kernelEquiv y)
  intro v
  rfl

theorem latticeIn_covolume
    (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (g : ℤ) (hg : 0 < g)
    (hdiv : ∀ v : L, g ∣ y ⬝ᵥ (v : Fin 3 → ℤ))
    (u : L) (hu : y ⬝ᵥ (u : Fin 3 → ℤ) = g) :
    ZLattice.covolume (latticeIn y L) =
      (L.toAddSubgroup.index : ℝ) * ‖castVec y‖ / (g : ℝ) := by
  let := latticeIn_isZLattice y z hyz L E hE hL
  let f := (integerDot y).comp L.subtype
  let e : f.ker ≃ₗ[ℤ] latticeIn y L :=
    (LatticeSplit.restrictedKernelEquiv L (integerDot y)).trans (kernelEquivIn y L)
  let bZ : Basis (Fin 2) ℤ f.ker :=
    (integerBasisIn y z hyz L E hE hL).map
      (LatticeSplit.restrictedKernelEquiv L (integerDot y)).symm
  let b : Basis (Fin 2) ℤ (latticeIn y L) := bZ.map e
  let emb := (plane y).subtypeₗᵢ
  have hb (i : Fin 2) : emb (b i) = castVec ((bZ i : L) : Fin 3 → ℤ) := by
    rfl
  have hdet : |Matrix.det ![(emb (b 0)).ofLp, (emb (b 1)).ofLp,
      (castVec (u : Fin 3 → ℤ)).ofLp]| = (L.toAddSubgroup.index : ℝ) := by
    rw [hb 0, hb 1]
    exact Lattice.abs_det_kernel_basis_extension L f g (ne_of_gt hg) hdiv u hu bZ
  have hzero (i : Fin 2) : (emb (b i)).ofLp ⬝ᵥ (castVec y).ofLp = 0 := by
    rw [dotProduct_comm]
    exact (b i : plane y).property
  have hheight : (castVec y).ofLp ⬝ᵥ (castVec (u : Fin 3 → ℤ)).ofLp = (g : ℝ) := by
    change (∑ i, (y i : ℝ) * ((u : Fin 3 → ℤ) i : ℝ)) = (g : ℝ)
    exact_mod_cast hu
  have h := Lattice.covolume_eq_index_mul_norm_div
    (latticeIn y L) b emb (castVec (u : Fin 3 → ℤ)).ofLp (castVec y).ofLp
    (L.toAddSubgroup.index : ℝ) (g : ℝ) (hzero 0) (hzero 1) hdet hheight
    (by exact_mod_cast hg)
  simpa only [WithLp.toLp_ofLp] using h

theorem exists_generator_covolume
    (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℤ) (hE : E ≠ 0)
    (hL : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    ∃ g : ℤ, 0 < g ∧ g ∣ E ∧
      (∀ v : L, g ∣ y ⬝ᵥ (v : Fin 3 → ℤ)) ∧
      (∃ u : L, y ⬝ᵥ (u : Fin 3 → ℤ) = g) ∧
      ZLattice.covolume (latticeIn y L) =
        (L.toAddSubgroup.index : ℝ) * ‖castVec y‖ / (g : ℝ) := by
  let f := (integerDot y).comp L.subtype
  have hf : f ≠ 0 := by
    intro hf
    have he := LinearMap.congr_fun hf (⟨E • z, hL z⟩ : L)
    change integerDot y (E • z) = 0 at he
    rw [map_smul] at he
    change E * (y ⬝ᵥ z) = 0 at he
    rw [hyz, mul_one] at he
    exact hE he
  obtain ⟨g, hg, hdiv, u, hu⟩ := LatticeSplit.exists_positive_image_generator f hf
  have hgd : g ∣ E := by
    have h := hdiv (⟨E • z, hL z⟩ : L)
    change g ∣ integerDot y (E • z) at h
    rw [map_smul] at h
    change g ∣ E * (y ⬝ᵥ z) at h
    simpa only [hyz, mul_one] using h
  exact ⟨g, hg, hgd, hdiv, ⟨u, hu⟩,
    latticeIn_covolume y z hyz L E hE hL g hg hdiv u hu⟩

theorem latticeIn_covolume_of_index_ne_zero
    (y z : Fin 3 → ℤ) (hyz : y ⬝ᵥ z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (hindex : L.toAddSubgroup.index ≠ 0)
    (g : ℤ) (hg : 0 < g)
    (hdiv : ∀ v : L, g ∣ y ⬝ᵥ (v : Fin 3 → ℤ))
    (u : L) (hu : y ⬝ᵥ (u : Fin 3 → ℤ) = g) :
    ZLattice.covolume (latticeIn y L) =
      (L.toAddSubgroup.index : ℝ) * ‖castVec y‖ / (g : ℝ) := by
  apply latticeIn_covolume y z hyz L (L.toAddSubgroup.index : ℤ)
    (by exact_mod_cast hindex) _ g hg hdiv u hu
  intro v
  simpa using L.toAddSubgroup.nsmul_index_mem v

end Problem355.IntegralPlaneLattice

end

end OAI
