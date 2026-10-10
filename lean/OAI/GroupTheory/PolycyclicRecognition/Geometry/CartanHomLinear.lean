import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHomLinear
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes

namespace OAI

/-! # Linear logarithms of homomorphisms on the actual Cartan factor -/

noncomputable section

namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- A continuous additive-target homomorphism is real-linear on Cartan
logarithms, derived from the published finite BCH identity. -/
theorem exists_linearMap_on_cartan
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd) :
    ∃ A : H →ₗ[ℝ] W, ∀ v : H, A v = (l (Exp v)).toAdd := by
  let b := finBasis ℝ H
  let e : H → G := fun x => F.inclusionD (F.ExpD (F.D.equiv x))
  have he (x : H) : e x = Exp x := F.compatibleD x
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  have hinj : Function.Injective e :=
    F.closedD.injective.comp (hbijD.injective.comp F.D.equiv.injective)
  have hzero : e 0 = 1 := by simp [e, F.isExpD.map_zero]
  have hadd (x : H) (s t : ℝ) : e ((s + t) • x) = e (s • x) * e (t • x) := by
    simp only [e, map_smul, F.isExpD.map_add_smul, map_mul]
  have hcont : Continuous (fun x : Fin (finrank ℝ H) → ℝ => e (b.equivFun.symm x)) := by
    change Continuous (F.inclusionD ∘ F.ExpD ∘ F.D.equiv ∘ b.equivFun.symm)
    rw [← show chartD = F.ExpD from funext hchartD]
    exact F.closedD.continuous.comp (chartD.continuous.comp
      (F.D.equiv.toLinearMap.comp b.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinD F.D.equiv F.ExpD F.isExpD hc 2
  have hmul (x y : H) : e (finiteDynkinPolynomial coeff ![x, y]) = e x * e y := by
    have hp := congrArg F.inclusionD (hprod ![x, y]).symm
    simpa [List.ofFn_succ, e] using hp
  obtain ⟨A, hA⟩ := exists_linearMap_of_exponential_hom b e hinj hzero hadd hcont coeff hmul l hl
  exact ⟨A, fun v => by simpa only [he] using hA v⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI
