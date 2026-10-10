import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProductLieAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! # A common BCH formula for two nilpotent Lie groups

Apply the published finite Dynkin identity once to the product group, then
project to each factor. The projections preserve the actual tangent bracket.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

attribute [local instance] productSelfChartedSpace

variable {E G F H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H] [T2Space H]

/-- The product is packaged solely to instantiate the existing published
input. Its measurable structure is the Borel structure of the product. -/
def exponentialProductLieModel
    (cG : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    (cH : GroupLieAlgebra (𝓘(ℝ, F)) H ≃ₜ H) :
    NilpotentLieModel (GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) := by
  letI : MeasurableSpace (G × H) := borel (G × H)
  letI : BorelSpace (G × H) := ⟨rfl⟩
  exact {
    modelSpace := E × F
    carrier := G × H
    simplyConnectedSpace := (cG.prodCongr cH).symm.toHomotopyEquiv.simplyConnectedSpace
    equiv := LieEquiv.refl }

theorem exists_common_dynkin_formula
    (hG : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (hH : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F)) H))
    (dynkin : NilpotentDynkinExpansionInput (E × F) (G × H))
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hExpG : IsGroupExponential ExpG) (hExpH : IsGroupExponential ExpH) :
    ∃ c : ℕ, ∃ coeff : DynkinCoefficients c 2,
      (∀ x y, ExpG x * ExpG y = ExpG (finiteDynkinPolynomial coeff ![x, y])) ∧
      (∀ x y, ExpH x * ExpH y = ExpH (finiteDynkinPolynomial coeff ![x, y])) := by
  have hn := product_tangent_nilpotent hG hH
  obtain ⟨c, hc⟩ := (isNilpotent_iff ℝ _ _).mp hn
  let ExpP : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) → G × H := groupExponential
  have hExpP : IsGroupExponential ExpP := groupExponential_isGroupExponential
  have hfst (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
      (ExpP v).1 = ExpG (productFstLieHom (E := E) (F := F) (G := G) (H := H) v) :=
    hExpP.map_of_mdifferentiable hExpG (MonoidHom.fst G H)
      (contMDiff_product_fst.mdifferentiable (by simp)) v
  have hsnd (v : GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H)) :
      (ExpP v).2 = ExpH (productSndLieHom (E := E) (F := F) (G := G) (H := H) v) :=
    hExpP.map_of_mdifferentiable hExpH (MonoidHom.snd G H)
      (contMDiff_product_snd.mdifferentiable (by simp)) v
  obtain ⟨coeff, _, hprod⟩ := dynkin ExpP hExpP c hc 2
  refine ⟨c, coeff, ?_, ?_⟩
  · intro x y
    let X : Fin 2 → GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) := ![(x, 0), (y, 0)]
    have hp := congrArg Prod.fst (hprod X)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Prod.fst_mul] at hp
    rw [hfst, hfst, hfst, finiteDynkinPolynomial_map] at hp
    have hX : (fun i => productFstLieHom (E := E) (F := F) (G := G) (H := H) (X i)) =
        ![x, y] := by
      funext i
      rw [productFstLieHom_apply]
      fin_cases i <;> rfl
    rw [hX] at hp
    simp only [productFstLieHom_apply] at hp
    rw [show (X 0).1 = x from rfl, show (X (Fin.succ 0)).1 = y from rfl] at hp
    exact hp
  · intro x y
    let X : Fin 2 → GroupLieAlgebra (𝓘(ℝ, E × F)) (G × H) := ![(0, x), (0, y)]
    have hp := congrArg Prod.snd (hprod X)
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      mul_one, Prod.snd_mul] at hp
    rw [hsnd, hsnd, hsnd, finiteDynkinPolynomial_map] at hp
    have hX : (fun i => productSndLieHom (E := E) (F := F) (G := G) (H := H) (X i)) =
        ![x, y] := by
      funext i
      rw [productSndLieHom_apply]
      fin_cases i <;> rfl
    rw [hX] at hp
    simp only [productSndLieHom_apply] at hp
    rw [show (X 0).2 = x from rfl, show (X (Fin.succ 0)).2 = y from rfl] at hp
    exact hp

end PolycyclicRecognition

end

end OAI
