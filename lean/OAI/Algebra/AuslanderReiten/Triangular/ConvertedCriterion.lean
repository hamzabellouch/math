import OAI.Algebra.AuslanderReiten.Cones.ConeCriterion
import OAI.Algebra.AuslanderReiten.Triangular.TriangularCochain
import OAI.Algebra.AuslanderReiten.Triangular.ConvertedStructure

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison TriangularInduction
open CochainComplex CochainComplex.HomComplex

universe u

variable {k : Type u} [Field k] (q : k) (B : Type u)
variable [AddCommGroup B] [Module k B] [Module (A k q) B] [Module (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q) B] [SMulCommClass (A k q) (A k q)ᵐᵒᵖ B]
variable [IsScalarTower k (A k q) B] [IsScalarTower k (A k q)ᵐᵒᵖ B]
variable [SMulCommClass k (A k q)ᵐᵒᵖ B]
variable [Module.Finite k B]
variable [Module.Finite (A k q) B] [Module.Projective (A k q) B]
variable [Module.Finite (A k q)ᵐᵒᵖ B] [Module.Projective (A k q)ᵐᵒᵖ B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : CochainComplex (ModuleCat.{u} (A k q)) ℤ)
variable (φ : jCochain (k := k) (F := B) P ⟶ eCochain (k := k) (F := B) P)

theorem convertedCone_mainConclusions (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (hP : TotallyAcyclicCochain P)
    (hinj : ∀ n : ℕ, 0 < n → Function.Injective (coneComparison φ (n : ℤ)))
    (hsurj : ∀ n : ℕ, Function.Surjective (coneComparison φ (n : ℤ)))
    (hker : ∃ w : CohomologyClass (eCochain (k := k) (F := B) P)
        (eCochain (k := k) (F := B) P) 0 ×
        CohomologyClass (jCochain (k := k) (F := B) P)
        (jCochain (k := k) (F := B) P) 0,
      w ≠ 0 ∧ coneComparison φ 0 w = 0) :
    MainConclusions k (ConvertedAlgebra k q B) (ConeModule φ) := by
  have hJ := jCochain_totallyAcyclic (k := k) (F := B) P hP
  have hE := eCochain_totallyAcyclic (k := k) (F := B) P hP
  obtain ⟨hnp, hgp, hself, hreg⟩ := coneModule_properties (k := k) φ hJ hE
    (eToJCochain_eq_zero k (A k q) B P P) hinj hsurj hker
  have hC := (mappingCone_totallyAcyclic φ hJ hE).to_chain
  let := hC.finite 0
  let : Module.Finite k ((chainOfCochain (mappingCone φ)).X 0) :=
    Module.Finite.trans (ConvertedAlgebra k q B) _
  exact ⟨inferInstance, inferInstance, hnp, hgp, hself, hreg,
    ⟨ConvertedAlgebra.semisimpleQuotientEquiv q B⟩,
    ConvertedAlgebra.jacobson_fourth_ne_bot q B hq hq1⟩

end ArExplicit

end

end OAI
