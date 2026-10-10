import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma infinitePi_sumPiEquivProdPi_symm {ι κ : Type*} {X : ι ⊕ κ → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.infinitePi fun i => μ (.inl i)).prod
      (Measure.infinitePi fun i => μ (.inr i))).map
        (MeasurableEquiv.sumPiEquivProdPi X).symm = Measure.infinitePi μ := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
    (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have he : (MeasurableEquiv.sumPiEquivProdPi X).symm ⁻¹' ((s : Set (ι ⊕ κ)).pi t) =
      (s.toLeft : Set ι).pi (fun i => t (.inl i)) ×ˢ
      (s.toRight : Set κ).pi (fun i => t (.inr i)) := by
    ext p
    simp only [mem_preimage,mem_pi,mem_prod,Finset.mem_coe,Finset.mem_toLeft,Finset.mem_toRight]
    constructor
    · intro h
      exact ⟨fun i hi => h (.inl i) hi,fun i hi => h (.inr i) hi⟩
    · rintro ⟨h₁,h₂⟩ (i|i) hi
      · exact h₁ i hi
      · exact h₂ i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun _ _ => ht _),
    Measure.infinitePi_pi _ (fun _ _ => ht _),Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]

lemma infinitePi_zip {ι A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : ι → Measure A) (ν : ι → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  let e := MeasurableEquiv.arrowProdEquivProdArrow A B s
  have hm : Measurable (Prod.map (Finset.restrict s : (ι → A) → (s → A))
      (Finset.restrict s : (ι → B) → (s → B))) := by fun_prop
  have hp : ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p (i : s) => (p.1 i,p.2 i)) = Measure.pi (fun i : s => (μ i).prod (ν i)) := by
    calc
      _ = (((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
        (Prod.map (Finset.restrict s) (Finset.restrict s))).map e.symm := by
          rw [Measure.map_map e.symm.measurable hm]
          rfl
      _ = _ := by
        rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
          Measure.infinitePi_map_restrict,Measure.infinitePi_map_restrict]
        exact (measurePreserving_arrowProdEquivProdArrow A B s (fun i => μ i) (fun i => ν i)).symm.map_eq
  have he : (fun p : (ι → A) × (ι → B) => fun i => (p.1 i,p.2 i)) ⁻¹'
      (s : Set ι).pi t =
      (fun p : (ι → A) × (ι → B) => fun i : s => (p.1 i,p.2 i)) ⁻¹'
        (univ.pi (fun i : s => t i)) := by
    ext p
    simp [Set.mem_pi]
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet fun i _ => ht i),he,
    ← Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi fun i : s => ht i),hp,Measure.pi_pi]
  exact Finset.prod_attach s (fun i => (μ i).prod (ν i) (t i))

end SphericalPerceptronFreeEnergy
end

end OAI
