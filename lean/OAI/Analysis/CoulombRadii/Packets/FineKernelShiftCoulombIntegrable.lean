import Mathlib
import OAI.Analysis.CoulombRadii.Screening.CoreScreenedField
import OAI.Analysis.CoulombRadii.FieldAnalysis.RetainedFineDensity

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set
open scoped BigOperators Matrix ENNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma fineKernel_shift_coulomb_integrable {b : ℝ} (hb : 0 < b) (a x : Space) :
    Integrable (fun y => coulombKernel (a-y)*fineKernel b (y-x)) := by
  have h := (fineKernel_coulomb_integrable hb (a-x)).comp_sub_right x
  apply h.congr
  exact Eventually.of_forall (fun y => by
    change coulombKernel (a-x-(y-x))*fineKernel b (y-x) = _
    rw [show a-x-(y-x) = a-y by abel])

lemma fineKernel_shift_coulomb_eq {b : ℝ} (hb : 0 < b) (a x : Space)
    (hsep : Real.sqrt 3*b ≤ ‖a-x‖) :
    (∫ y, coulombKernel (a-y)*fineKernel b (y-x)) = coulombKernel (a-x) := by
  rw [fineKernel_shift_coulomb_integral, fineKernel_coulomb_eq hb hsep]

lemma retainedFineDensity_coulomb_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) (a : Space) :
    Integrable (fun y => coulombKernel (a-y)*retainedFineDensity b r x y) := by
  simp only [retainedFineDensity, Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => fineKernel_shift_coulomb_integrable hb a (x i))

lemma retainedFineDensity_coulomb_eq {n : ℕ} {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) (a : Space)
    (hsep : ∀ i ∈ r, Real.sqrt 3*b ≤ ‖a-x i‖) :
    (∫ y, coulombKernel (a-y)*retainedFineDensity b r x y) = ∑ i ∈ r, coulombKernel (a-x i) := by
  simp only [retainedFineDensity, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => fineKernel_shift_coulomb_integrable hb a (x i))]
  exact Finset.sum_congr rfl (fun i hi => fineKernel_shift_coulomb_eq hb a (x i) (hsep i hi))

lemma coreCoulombPotential_fine_atom_eq {m : ℕ} (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A) {b : ℝ} (hb : 0 < b) (a : Space)
    (hsep : ∀ z ∈ A, Real.sqrt 3*b ≤ ‖z-a‖) :
    (∫ y, coreCoulombPotential u y*fineKernel b (y-a)) = coreCoulombPotential u a := by
  rw [coreCoulombPotential_fubini u _ (fineKernel_shift_integrable hb a)]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x = 0
  · simp [he]
  · have ha : position x i ∈ A := (by_contra (fun hn => he (hx hn)) : x ∈ allPositions A) i
    rw [fineKernel_shift_coulomb_eq hb _ _ (hsep _ ha)]

lemma coreCoulombPotential_retainedFine_eq {m n : ℕ} (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space)
    (hsep : ∀ z ∈ A, ∀ i ∈ r, Real.sqrt 3*b ≤ ‖z-x i‖) :
    (∫ y, coreCoulombPotential u y*retainedFineDensity b r x y) =
      ∑ i ∈ r, coreCoulombPotential u (x i) := by
  simp only [retainedFineDensity, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => coreCoulombPotential_mul_integrable u _ (fineKernel_shift_integrable hb (x i)))]
  exact Finset.sum_congr rfl (fun i hi => coreCoulombPotential_fine_atom_eq u hu hb (x i) (fun z hz => hsep z hz i hi))

lemma attraction_retainedFine_integrable {M n : ℕ} (S : Nuclei M) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space) :
    Integrable (fun y => attraction S y*retainedFineDensity b r x y) := by
  simp only [attraction, Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  have h := (retainedFineDensity_coulomb_integrable hb r x (S.position j)).const_mul (S.charge j)
  apply h.congr
  exact Eventually.of_forall (fun y => by dsimp only; rw [coulombKernel_sub_comm y]; ring)

lemma attraction_retainedFine_eq {M n : ℕ} (S : Nuclei M) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space)
    (hsep : ∀ j i, i ∈ r → Real.sqrt 3*b ≤ ‖S.position j-x i‖) :
    (∫ y, attraction S y*retainedFineDensity b r x y) = ∑ i ∈ r, attraction S (x i) := by
  have hi (j : Fin M) : Integrable (fun y => S.charge j*(coulombKernel (S.position j-y)*retainedFineDensity b r x y)) :=
    (retainedFineDensity_coulomb_integrable hb r x (S.position j)).const_mul _
  simp only [attraction, Finset.sum_mul]
  simp_rw [coulombKernel_sub_comm _ (S.position _), mul_assoc]
  rw [integral_finsetSum _ (fun j _ => hi j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, retainedFineDensity_coulomb_eq hb r x _ (hsep j), Finset.mul_sum]

lemma coreScreenedField_retainedFine_integrable {M m n : ℕ} (S : Nuclei M)
    (u : H1Vector m) {b : ℝ} (hb : 0 < b) (r : Finset (Fin n)) (x : Fin n → Space) :
    Integrable (fun y => coreScreenedField S u y*retainedFineDensity b r x y) := by
  apply Integrable.congr ((attraction_retainedFine_integrable S hb r x).sub
      (coreCoulombPotential_mul_integrable u _ (retainedFineDensity_integrable hb r x)))
  exact Eventually.of_forall fun y => (sub_mul _ _ _).symm

lemma coreScreenedField_retainedFine_eq {M m n : ℕ} (S : Nuclei M)
    (u : H1Vector m) {A : Set Space} (hu : SpatiallySupported u A) {b : ℝ} (hb : 0 < b)
    (r : Finset (Fin n)) (x : Fin n → Space)
    (hnuc : ∀ j i, i ∈ r → Real.sqrt 3*b ≤ ‖S.position j-x i‖)
    (hcore : ∀ z ∈ A, ∀ i ∈ r, Real.sqrt 3*b ≤ ‖z-x i‖) :
    (∫ y, coreScreenedField S u y*retainedFineDensity b r x y) =
      ∑ i ∈ r, coreScreenedField S u (x i) := by
  simp only [coreScreenedField,sub_mul]
  rw [integral_sub (attraction_retainedFine_integrable S hb r x)
    (coreCoulombPotential_mul_integrable u _ (retainedFineDensity_integrable hb r x)),
    attraction_retainedFine_eq S hb r x hnuc,
    coreCoulombPotential_retainedFine_eq u hu hb r x hcore, Finset.sum_sub_distrib]

end Coulomb

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
