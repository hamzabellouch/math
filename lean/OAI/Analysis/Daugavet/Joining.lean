import OAI.Analysis.Daugavet.ProductApproximation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uX uY uB uIota uKappa uBeta

namespace ExactModuli.KW
section CoordinateJoining
variable {β : Type uBeta} {κ : Type uKappa} {ι : Type uIota} [Fintype β] [Fintype κ] [Fintype ι]

def joinedCoordinates (d : β ⊕ (κ × ι) → ℕ) (ω : KWOmega) : cube β × (κ → cube ι) :=
  splitCoordinates (fun i => ω (d i))

lemma joinedCoordinates_mp (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    MeasurePreserving (joinedCoordinates d) kwMeasure ((cubeMeasure β).prod (arrayMeasure κ ι)) :=
  splitCoordinates_mp.comp (finite_coordinates_mp d hd)

def joinedL1 (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    Lp ℝ 1 ((cubeMeasure β).prod (arrayMeasure κ ι)) →ₗᵢ[ℝ] KWL1 :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (joinedCoordinates_mp d hd)

lemma joinedL1_range (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    (joinedL1 d hd).toLinearMap.range ≤ (coordinatesL1 d hd).toLinearMap.range := by
  rintro g ⟨f, rfl⟩
  refine ⟨Lp.compMeasurePreserving splitCoordinates splitCoordinates_mp f, ?_⟩
  exact (Lp.compMeasurePreserving_comp_apply f splitCoordinates_mp (finite_coordinates_mp d hd)).symm

lemma joinedL1_old (c : β → ℕ) (hc : Function.Injective c)
    (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) (hdc : ∀ b, d (Sum.inl b) = c b)
    (f : Lp ℝ 1 (cubeMeasure β)) :
    joinedL1 d hd (oldL1 f) = coordinatesL1 c hc f := by
  change (Lp.compMeasurePreserving (joinedCoordinates d) (joinedCoordinates_mp d hd))
      ((Lp.compMeasurePreserving Prod.fst measurePreserving_fst) f) = _
  rw [← Lp.compMeasurePreserving_comp_apply f measurePreserving_fst (joinedCoordinates_mp d hd)]
  have he : Prod.fst ∘ joinedCoordinates d = (fun ω : KWOmega => fun b => ω (c b)) := by
    funext ω b
    simp only [Function.comp_apply, joinedCoordinates, splitCoordinates, hdc]
  simp only [he]
  rfl

lemma joinedL1_measureDistance (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d)
    (f g : Lp ℝ 1 ((cubeMeasure β).prod (arrayMeasure κ ι))) :
    measureDistance kwMeasure (joinedL1 d hd f) (joinedL1 d hd g) =
      measureDistance ((cubeMeasure β).prod (arrayMeasure κ ι)) f g :=
  measureDistance_pullback (joinedCoordinates_mp d hd) f g

end CoordinateJoining

section Model
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma finiteDimensional_model (L : X →ₗᵢ[ℝ] Y) (G : Submodule ℝ Y) [FiniteDimensional ℝ G] :
    FiniteDimensional ℝ (G.comap L.toLinearMap) := by
  let T : G.comap L.toLinearMap →ₗ[ℝ] G :=
    (L.toLinearMap.domRestrict (G.comap L.toLinearMap)).codRestrict G (fun x => x.property)
  apply FiniteDimensional.of_injective T
  intro x y h
  apply Subtype.ext
  apply L.injective
  exact congrArg Subtype.val h

end Model

section ProductBasis
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]

omit [IsProbabilityMeasure μ] in
lemma productOperator_single [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (u : κ → Lp ℝ 1 μ) (k : κ) (j : ι) :
    ∃ a : κ → ι → ℝ, productOperator hp u (0,a) = atomL1 hp (u k) k j := by
  classical
  refine ⟨fun k' j' => if k' = k then (if j' = j then 1 else 0) else 0, ?_⟩
  simp [productOperator, matrixCombination, ite_smul]

end ProductBasis
end ExactModuli.KW

end

end OAI
