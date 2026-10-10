import OAI.NumberTheory.Jacobsthal.Estimates.HarmonicConditioning
import OAI.NumberTheory.Jacobsthal.Partitions.ActualBoxFourSum

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.BoxWitnessFactorization
open ErdosCofactorChoices ErdosInverseCells ErdosInverseSampling
open TwoPrimeObservableSum ParentTailPartition ParentCofactorChoices BinCutSelections FourCoordinateBoxSum CanonicalSubsetBox

attribute [local instance] Classical.propDecidable

noncomputable def selectionWitnessMass {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (i j : Fin n) (W : (ℕ × ℕ) → ℕ → Prop) : ℝ :=
  ∑ f ∈ (selections P m).filter (fun f => W (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j)),
    (selectionProduct f:ℝ)⁻¹

theorem witness_three_sum (P Q U : Finset ℕ) (W : (ℕ × ℕ) → ℕ → Prop) :
    weightedWitness P Q U W=∑ p ∈ P,∑ u ∈ U,∑ q ∈ Q,
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*(if W (p,q) u then 1 else 0) := by
  unfold weightedWitness witnessPairs
  simp only [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,tripleWeight]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  apply Finset.sum_congr rfl
  intro q _hq
  split_ifs <;> ring

theorem four_sum_descendants (P Q U D : Finset ℕ) (G : ℕ → ℕ → ℕ → ℝ) :
    (∑ p ∈ P,∑ u ∈ U,∑ q ∈ Q,∑ d ∈ D,
      ((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p q u)=
      harmonicMass D*(∑ p ∈ P,∑ u ∈ U,∑ q ∈ Q,((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*G p q u) := by
  have hh : ∀ p u q : ℕ,(∑ d ∈ D,((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹*(d:ℝ)⁻¹)*G p q u)=
      harmonicMass D*(((p:ℝ)⁻¹*(u:ℝ)⁻¹*(q:ℝ)⁻¹)*G p q u) := by
    intro p u q
    rw [harmonicMass,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  simp_rw [hh]
  simp only [← Finset.mul_sum]

theorem selection_witness_factor {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) (W : (ℕ × ℕ) → ℕ → Prop) :
    selectionWitnessMass P m i j W=
      harmonicMass (cofactorChoices P (belowMultiplicity m j))*
        weightedWitness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) W := by
  have hh := four_coordinate_sum P m hP hd i j hji hi hj (fun p u q _d => if W (p,q) u then (1:ℝ) else 0)
  have he : selectionWitnessMass P m i j W=
      ∑ f ∈ selections P m,(selectionProduct f:ℝ)⁻¹*
        (if W (pickedPrime f i,selectionProduct (parentCofactorSelection f i j)) (pickedPrime f j) then 1 else 0) := by
    simp only [selectionWitnessMass,Finset.sum_filter,mul_ite,mul_one,mul_zero]
  rw [he,hh,four_sum_descendants,witness_three_sum]

theorem full_box_mass_factor {n : ℕ} (P : Fin n → Finset ℕ) (m : Fin n → ℕ)
    (hP : ∀ i,∀ p ∈ P i,p.Prime) (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (i j : Fin n) (hji : j < i) (hi : m i=1) (hj : m j=1) :
    selectionMass P m=harmonicMass (cofactorChoices P (belowMultiplicity m j))*
      (harmonicMass (P i)*harmonicMass (cofactorChoices P (parentCofactorMultiplicity m i j))*harmonicMass (P j)) := by
  have hh := selection_witness_factor P m hP hd i j hji hi hj (fun _ _ => True)
  have he : weightedWitness (P i) (cofactorChoices P (parentCofactorMultiplicity m i j)) (P j) (fun _ _ => True)=
      harmonicMass (P i)*harmonicMass (cofactorChoices P (parentCofactorMultiplicity m i j))*harmonicMass (P j) := by
    unfold weightedWitness witnessPairs
    simp only [Finset.filter_true_of_mem (fun _ _ => trivial)]
    exact triple_weight_sum _ _ _
  simpa only [selectionWitnessMass,Finset.filter_true_of_mem (fun _ _ => trivial),selectionMass,he] using hh
end NumberTheoryLean.BoxWitnessFactorization


end Erdos970

end OAI
