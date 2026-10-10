import OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

namespace PiExponent.ProjectiveCurveTwoAffine
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] [Fintype σ]

def linearEquation (v : σ → K) : MvPolynomial σ K := ∑ i, C (v i) * X i

theorem linearEquation_homogeneous (v : σ → K) :
    linearEquation v ∈ PolyGrade K σ 1 :=
  IsHomogeneous.sum _ _ _ (fun _i _ => isHomogeneous_C_mul_X _ _)

def linearEquationLinear : (σ → K) →ₗ[K] MvPolynomial σ K where
  toFun := linearEquation
  map_add' v w := by simp [linearEquation, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [linearEquation, Algebra.smul_def, Finset.mul_sum, mul_assoc]

theorem linearEquation_single_one [DecidableEq σ] (i : σ) :
    linearEquation (Pi.single i (1 : K)) = X i := by
  classical
  simp [linearEquation, Pi.single_apply, apply_ite, ite_mul]

theorem exists_hyperplane_avoiding {K σ ι : Type} [Field K] [Infinite K]
    [Fintype σ] [Finite ι] (x : ι → Proj (PolyGrade K σ)) :
    ∃ v : σ → K, ∀ i, x i ∈ Proj.basicOpen (PolyGrade K σ) (linearEquation v) := by
  classical
  let bad (i : ι) : Submodule K (σ → K) :=
    ((x i).asHomogeneousIdeal.toIdeal.restrictScalars K).comap
      (linearEquationLinear (K := K) (σ := σ))
  have hbad (i : ι) : bad i ≠ ⊤ := by
    intro h
    have hx : x i ∈ ⨆ j : σ, Proj.basicOpen (PolyGrade K σ) (X j) := by
      rw [standardChart_cover]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    have hm : Pi.single j (1 : K) ∈ bad i := h ▸ Submodule.mem_top
    change linearEquation (Pi.single j (1 : K)) ∈ (x i).asHomogeneousIdeal at hm
    rw [linearEquation_single_one] at hm
    exact hj hm
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨v, hv⟩

theorem two_affine_cover_of_affine_projective_map
    {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {Y : Scheme.{0}} [IsIntegral Y] [NoetherianSpace Y]
    (j : Y ⟶ Proj (PolyGrade K σ)) [IsAffineHom j]
    (hd : topologicalKrullDim Y ≤ 1) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  classical
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hy : j y ∈ ⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (X i) := by
    rw [standardChart_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  let U := j ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (X i)
  have hU : IsAffineOpen U := (standardChart_isAffineOpen i).preimage j
  let Z : Set Y := (U : Set Y)ᶜ
  have hZ : Z.Finite := proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl (by
    intro h
    have hyZ : y ∈ Z := h ▸ Set.mem_univ y
    exact hyZ hi)
  let : Finite Z := hZ.to_subtype
  obtain ⟨v, hv⟩ := exists_hyperplane_avoiding (fun z : Z => j z.val)
  let V := j ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (linearEquation v)
  have hV : IsAffineOpen V :=
    (Proj.isAffineOpen_basicOpen _ _ (linearEquation_homogeneous v) (by decide)).preimage j
  refine ⟨U, V, hU, hV, top_unique ?_⟩
  intro z _
  by_cases hz : z ∈ U
  · exact Or.inl hz
  · exact Or.inr (hv ⟨z, hz⟩)

theorem two_affine_cover_of_closed_embedding
    {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {Y : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    (j : Y ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion j]
    (hd : topologicalKrullDim Y ≤ 1) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ :=
  two_affine_cover_of_affine_projective_map j hd

end
end PiExponent.ProjectiveCurveTwoAffine

end OAI
