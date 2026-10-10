import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.NuclearPotential

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
namespace Coulomb
def leftPotential {m k : ℕ} (W : Configuration m → ℝ) (x : Configuration (m+k)) : ℝ :=
  W ((joinConfiguration m k).symm x).1
def rightPotential {m k : ℕ} (W : Configuration k → ℝ) (x : Configuration (m+k)) : ℝ :=
  W ((joinConfiguration m k).symm x).2

def crossEnergy {m k : ℕ} (u : H1Vector m) (v : H1Vector k) : ℝ :=
  potentialEnergy (fun x => crossPotential ((joinConfiguration m k).symm x).1
    ((joinConfiguration m k).symm x).2) (u.tensor v)

lemma tensor_leftPotential_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration m → ℝ) (hW : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2))
    (s : Spins (m+k)) :
    Integrable (fun x => leftPotential W x*‖(u.tensor v).value s x‖^2) := by
  have hp : Integrable (fun z : Configuration m × Configuration k =>
      (W z.1*‖u.value (s ∘ Fin.castAdd k) z.1‖^2)*‖v.value (s ∘ Fin.natAdd m) z.2‖^2)
      (volume.prod volume) :=
    (hW (s ∘ Fin.castAdd k)).mul_prod ((v.value_L2 (s ∘ Fin.natAdd m)).norm.integrable_sq)
  have H := (joinConfiguration_symm_measurePreserving m k).integrable_comp_of_integrable hp
  apply H.congr
  filter_upwards [] with x
  change (W _*‖u.value _ _‖^2)*‖v.value _ _‖^2 = W _*‖u.value _ _*v.value _ _‖^2
  rw [norm_mul,mul_pow,mul_assoc]
  rfl

lemma tensor_rightPotential_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration k → ℝ) (hW : ∀ s, Integrable (fun x => W x*‖v.value s x‖^2))
    (s : Spins (m+k)) :
    Integrable (fun x => rightPotential W x*‖(u.tensor v).value s x‖^2) := by
  have hp : Integrable (fun z : Configuration m × Configuration k =>
      ‖u.value (s ∘ Fin.castAdd k) z.1‖^2*(W z.2*‖v.value (s ∘ Fin.natAdd m) z.2‖^2))
      (volume.prod volume) :=
    ((u.value_L2 (s ∘ Fin.castAdd k)).norm.integrable_sq).mul_prod (hW (s ∘ Fin.natAdd m))
  have H := (joinConfiguration_symm_measurePreserving m k).integrable_comp_of_integrable hp
  apply H.congr
  filter_upwards [] with x
  change ‖u.value _ _‖^2*(W _*‖v.value _ _‖^2) = W _*‖u.value _ _*v.value _ _‖^2
  rw [norm_mul,mul_pow,mul_left_comm]
  rfl

lemma potentialEnergy_tensor_left {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration m → ℝ) :
    potentialEnergy (leftPotential W) (u.tensor v) = potentialEnergy W u*mass v := by
  have hi (s : Spins (m+k)) : (∫ x, leftPotential W x*‖(u.tensor v).value s x‖^2) =
      (∫ x, W x*‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, ‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
    rw [← (joinConfiguration_measurePreserving m k).integral_comp'
      (fun x => leftPotential W x*‖(u.tensor v).value s x‖^2)]
    change (∫ z : Configuration m × Configuration k,
      leftPotential W (joinConfiguration m k z)*‖tensorValue u v s (joinConfiguration m k z)‖^2
        ∂(volume.prod volume)) = _
    simp only [leftPotential, ContinuousLinearEquiv.symm_apply_apply, tensorValue_join,norm_mul,mul_pow,← mul_assoc]
    exact integral_prod_mul (μ := volume) (ν := volume)
      (fun x : Configuration m => W x*‖u.value (s ∘ Fin.castAdd k) x‖^2)
      (fun y : Configuration k => ‖v.value (s ∘ Fin.natAdd m) y‖^2)
  unfold potentialEnergy mass
  rw [sum_joinSpins]
  simp_rw [hi, joinSpins_left, joinSpins_right]
  rw [Finset.sum_mul_sum]

lemma potentialEnergy_tensor_right {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration k → ℝ) :
    potentialEnergy (rightPotential W) (u.tensor v) = mass u*potentialEnergy W v := by
  have hi (s : Spins (m+k)) : (∫ x, rightPotential W x*‖(u.tensor v).value s x‖^2) =
      (∫ x, ‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, W y*‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
    rw [← (joinConfiguration_measurePreserving m k).integral_comp'
      (fun x => rightPotential W x*‖(u.tensor v).value s x‖^2)]
    change (∫ z : Configuration m × Configuration k,
      rightPotential W (joinConfiguration m k z)*‖tensorValue u v s (joinConfiguration m k z)‖^2
        ∂(volume.prod volume)) = _
    simp only [rightPotential, ContinuousLinearEquiv.symm_apply_apply,tensorValue_join,norm_mul,mul_pow]
    simp_rw [mul_left_comm (W _) (‖u.value _ _‖^2)]
    exact integral_prod_mul (μ := volume) (ν := volume)
      (fun x : Configuration m => ‖u.value (s ∘ Fin.castAdd k) x‖^2)
      (fun y : Configuration k => W y*‖v.value (s ∘ Fin.natAdd m) y‖^2)
  unfold potentialEnergy mass
  rw [sum_joinSpins]
  simp_rw [hi, joinSpins_left, joinSpins_right]
  rw [Finset.sum_mul_sum]

lemma potentialEnergy_add {n : ℕ} (u : H1Vector n) (V W : Configuration n → ℝ)
    (hV : ∀ s, Integrable (fun x => V x*‖u.value s x‖^2))
    (hW : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2)) :
    potentialEnergy (fun x => V x+W x) u = potentialEnergy V u+potentialEnergy W u := by
  simp only [potentialEnergy,add_mul]
  simp_rw [integral_add (hV _) (hW _)]
  rw [Finset.sum_add_distrib]

lemma nuclearPotential_split {M m k : ℕ} (S : Nuclei M) (x : Configuration (m+k)) :
    nuclearPotential S x = leftPotential (nuclearPotential S) x+
      rightPotential (nuclearPotential S) x := by
  have H := nuclearPotential_join S ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,leftPotential,rightPotential] using H

lemma pairPotential_split {m k : ℕ} (x : Configuration (m+k)) :
    pairPotential x = leftPotential pairPotential x+rightPotential pairPotential x+
      crossPotential ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2 := by
  have H := pairPotential_join ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,leftPotential,rightPotential] using H

lemma nuclearEnergy_tensor {M m k : ℕ} (S : Nuclei M) (u : H1Vector m) (v : H1Vector k) :
    nuclearEnergy S (u.tensor v) = nuclearEnergy S u*mass v+mass u*nuclearEnergy S v := by
  change potentialEnergy (nuclearPotential S) (u.tensor v) = _
  rw [show (nuclearPotential S : Configuration (m+k) → ℝ) = fun x =>
      leftPotential (nuclearPotential S) x+rightPotential (nuclearPotential S) x
      from funext (nuclearPotential_split S)]
  have h1 : ∀ s, Integrable (fun x => leftPotential (nuclearPotential S) x*‖(u.tensor v).value s x‖^2) :=
    tensor_leftPotential_integrable u v (nuclearPotential S) (u.nuclear_integrable S)
  have h2 : ∀ s, Integrable (fun x => rightPotential (nuclearPotential S) x*‖(u.tensor v).value s x‖^2) :=
    tensor_rightPotential_integrable u v (nuclearPotential S) (v.nuclear_integrable S)
  rw [potentialEnergy_add _ _ _ h1 h2,
      potentialEnergy_tensor_left,potentialEnergy_tensor_right]
  rfl

lemma tensor_crossPotential_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) : Integrable (fun x =>
      crossPotential ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2 *
        ‖(u.tensor v).value s x‖^2) := by
  have H := ((u.tensor v).pair_integrable s).sub
    ((tensor_leftPotential_integrable u v pairPotential u.pair_integrable s).add
      (tensor_rightPotential_integrable u v pairPotential v.pair_integrable s))
  convert H using 1
  funext x
  change _ = pairPotential x*_-(_+_)
  rw [pairPotential_split]
  ring

lemma pairEnergy_tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    pairEnergy (u.tensor v) = pairEnergy u*mass v+mass u*pairEnergy v+crossEnergy u v := by
  change potentialEnergy pairPotential (u.tensor v) = _
  rw [show (pairPotential : Configuration (m+k) → ℝ) = fun x =>
      (leftPotential pairPotential x+rightPotential pairPotential x)+
      crossPotential ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2
      from funext pairPotential_split]
  have h1 := tensor_leftPotential_integrable u v pairPotential u.pair_integrable
  have h2 := tensor_rightPotential_integrable u v pairPotential v.pair_integrable
  have h12 : ∀ s, Integrable (fun x => (leftPotential pairPotential x+rightPotential pairPotential x)*
      ‖(u.tensor v).value s x‖^2) := by
    intro s
    apply ((h1 s).add (h2 s)).congr
    filter_upwards [] with x
    exact (add_mul _ _ _).symm
  rw [potentialEnergy_add _ _ _ h12
      (tensor_crossPotential_integrable u v),
      potentialEnergy_add _ _ _ h1 h2,potentialEnergy_tensor_left,potentialEnergy_tensor_right]
  rfl

lemma form_wedge {M m k : ℕ} (S : Nuclei M) (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    form S (u.wedge v) = form S u*mass v+mass u*form S v+crossEnergy u v := by
  unfold form
  rw [kinetic_wedge u v hu hv A B hsu hsv hA hB hAB,
    nuclearEnergy_wedge_tensor S u v hu hv A B hsu hsv hAB,
    pairEnergy_wedge_tensor u v hu hv A B hsu hsv hAB,nuclearEnergy_tensor,pairEnergy_tensor]
  ring
end Coulomb

end

end OAI
