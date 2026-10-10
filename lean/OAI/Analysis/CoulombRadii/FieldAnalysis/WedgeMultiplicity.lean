import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.NormSqSumCosets

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
lemma mass_permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) :
    mass (u.permutation p) = mass u := by
  calc
    _ = mass (u.pullback (permutationIsometry p)) := by
      unfold mass
      change (∑ s, ∫ x, ‖(u.pullback (permutationIsometry p)).value (permutationSpins p s) x‖^2) = _
      exact Equiv.sum_comp (permutationSpins p) (fun s => ∫ x, ‖(u.pullback (permutationIsometry p)).value s x‖^2)
    _ = _ := mass_pullback _ _
lemma kinetic_permutation {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n)) :
    kinetic (u.permutation p) = kinetic u := by
  calc
    _ = kinetic (u.pullback (permutationIsometry p)) := by
      unfold kinetic
      congr 1
      change (∑ s, ∑ a, ∫ x, ‖(u.pullback (permutationIsometry p)).gradient (permutationSpins p s) a x‖^2) = _
      exact Equiv.sum_comp (permutationSpins p) (fun s => ∑ a, ∫ x, ‖(u.pullback (permutationIsometry p)).gradient s a x‖^2)
    _ = _ := kinetic_pullback _ _

lemma mass_fullAntisymmetrize_of_sq {n : ℕ} (u : H1Vector n) (c : ℝ)
    (h : ∀ s, ∀ᵐ x ∂volume, ‖u.fullAntisymmetrize.value s x‖^2 =
      c*∑ p : Equiv.Perm (Fin n), ‖(u.permutation p).value s x‖^2) :
    mass u.fullAntisymmetrize = c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ)*mass u := by
  have hi (s : Spins n) : (∫ x, ‖u.fullAntisymmetrize.value s x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∫ x, ‖(u.permutation p).value s x‖^2 := by
    rw [integral_congr_ae (h s), integral_const_mul,
      integral_finsetSum _ (fun p _ => ((u.permutation p).value_L2 s).norm.integrable_sq)]
  unfold mass
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_comm]
  change c*(∑ p : Equiv.Perm (Fin n), mass (u.permutation p)) = _
  simp_rw [mass_permutation]
  simp [mass, mul_assoc]

lemma kinetic_fullAntisymmetrize_of_sq {n : ℕ} (u : H1Vector n) (c : ℝ)
    (h : ∀ s a, ∀ᵐ x ∂volume, ‖u.fullAntisymmetrize.gradient s a x‖^2 =
      c*∑ p : Equiv.Perm (Fin n), ‖(u.permutation p).gradient s a x‖^2) :
    kinetic u.fullAntisymmetrize = c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ)*kinetic u := by
  have hi (s : Spins n) (a : Fin n × Fin 3) : (∫ x, ‖u.fullAntisymmetrize.gradient s a x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∫ x, ‖(u.permutation p).gradient s a x‖^2 := by
    rw [integral_congr_ae (h s a), integral_const_mul,
      integral_finsetSum _ (fun p _ => ((u.permutation p).partial_L2 s a).norm.integrable_sq)]
  have hf : (∑ s, ∑ a, ∫ x, ‖u.fullAntisymmetrize.gradient s a x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∑ s, ∑ a, ∫ x, ‖(u.permutation p).gradient s a x‖^2 := by
    simp_rw [hi, ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.sum_comm (γ := Fin n × Fin 3)]
    rw [Finset.sum_comm]
  unfold kinetic
  rw [hf]
  calc
    _ = c*∑ p : Equiv.Perm (Fin n), kinetic (u.permutation p) := by
      simp only [kinetic, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring_nf
    _ = _ := by
      simp_rw [kinetic_permutation]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change c*((Fintype.card (Equiv.Perm (Fin n)) : ℝ)*kinetic u) = _
      unfold kinetic
      ring

lemma mass_scale {n : ℕ} (u : H1Vector n) (c : ℂ) :
    mass (u.scale c) = ‖c‖^2*mass u := by
  simp only [mass,H1Vector.scale,norm_mul,mul_pow,integral_const_mul,← Finset.mul_sum]
lemma kinetic_scale {n : ℕ} (u : H1Vector n) (c : ℂ) :
    kinetic (u.scale c) = ‖c‖^2*kinetic u := by
  simp only [kinetic,H1Vector.scale,norm_mul,mul_pow,integral_const_mul,← Finset.mul_sum]
  ring
lemma antisymmetric_scale {n : ℕ} (u : H1Vector n) (hu : Antisymmetric u) (c : ℂ) :
    Antisymmetric (u.scale c) := by
  intro p s
  filter_upwards [hu p s] with x hx
  change c*u.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ)*(c*u.value s x)
  rw [hx]
  ring

def wedgeMultiplicity (m k : ℕ) : ℝ :=
  (Fintype.card (blockGroup m k) : ℝ)*(Fintype.card (Equiv.Perm (Fin (m+k))) : ℝ)

lemma wedgeMultiplicity_pos (m k : ℕ) : 0 < wedgeMultiplicity m k := by
  unfold wedgeMultiplicity
  positivity

def H1Vector.wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k) : H1Vector (m+k) :=
  (u.tensor v).fullAntisymmetrize.scale ((Real.sqrt (wedgeMultiplicity m k))⁻¹ : ℝ)

lemma wedge_normalizer_sq (m k : ℕ) :
    ‖(((Real.sqrt (wedgeMultiplicity m k))⁻¹ : ℝ) : ℂ)‖^2 = (wedgeMultiplicity m k)⁻¹ := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (le_of_lt (wedgeMultiplicity_pos m k))]

lemma wedge_antisymmetric {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    Antisymmetric (u.wedge v) :=
  antisymmetric_scale _ (fullAntisymmetrize_antisymmetric _) _

lemma mass_wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B) (hAB : Disjoint A B) :
    mass (u.wedge v) = mass u*mass v := by
  unfold H1Vector.wedge
  rw [mass_scale, wedge_normalizer_sq,
    mass_fullAntisymmetrize_of_sq (u.tensor v) _
      (separated_fullAntisymmetrize_value_sq u v hu hv A B hsu hsv hAB)]
  change (wedgeMultiplicity m k)⁻¹*(wedgeMultiplicity m k*mass (u.tensor v)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (wedgeMultiplicity_pos m k)), one_mul, mass_tensor]

lemma kinetic_wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    kinetic (u.wedge v) = kinetic u*mass v+mass u*kinetic v := by
  unfold H1Vector.wedge
  rw [kinetic_scale, wedge_normalizer_sq,
    kinetic_fullAntisymmetrize_of_sq (u.tensor v) _
      (separated_fullAntisymmetrize_gradient_sq u v hu hv A B hsu hsv hA hB hAB)]
  change (wedgeMultiplicity m k)⁻¹*(wedgeMultiplicity m k*kinetic (u.tensor v)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (wedgeMultiplicity_pos m k)), one_mul, kinetic_tensor]

def potentialEnergy {n : ℕ} (W : Configuration n → ℝ) (u : H1Vector n) : ℝ :=
  ∑ s, ∫ x, W x*‖u.value s x‖^2

lemma permute_integral_real {n : ℕ} (p : Equiv.Perm (Fin n)) (F : Configuration n → ℝ) :
    (∫ x, F (permute p x)) = ∫ x, F x := by
  exact (show MeasurePreserving (permutationIsometry p).toHomeomorph.toMeasurableEquiv
    volume volume from (permutationIsometry p).measurePreserving).integral_comp' F

lemma potential_integrable_permutation {n : ℕ} (W : Configuration n → ℝ)
    (hW : ∀ p x, W (permute p x) = W x) (u : H1Vector n)
    (hi : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2))
    (p : Equiv.Perm (Fin n)) (s : Spins n) :
    Integrable (fun x => W x*‖(u.permutation p).value s x‖^2) := by
  have H := (permute_measurePreserving p).integrable_comp_of_integrable (hi (s ∘ p))
  simpa only [Function.comp_def, hW, permutation_value] using H

lemma potentialEnergy_permutation {n : ℕ} (W : Configuration n → ℝ)
    (hW : ∀ p x, W (permute p x) = W x) (u : H1Vector n)
    (p : Equiv.Perm (Fin n)) : potentialEnergy W (u.permutation p) = potentialEnergy W u := by
  unfold potentialEnergy
  have H (s : Spins n) : (∫ x, W x*‖(u.permutation p).value s x‖^2) =
      ∫ x, W x*‖u.value (s ∘ p) x‖^2 := by
    simpa only [hW, permutation_value] using
      (permute_integral_real p (fun x => W x*‖u.value (s ∘ p) x‖^2))
  simp_rw [H]
  exact Equiv.sum_comp (permutationSpins p) (fun s => ∫ x, W x*‖u.value s x‖^2)

lemma potentialEnergy_fullAntisymmetrize_of_sq {n : ℕ} (u : H1Vector n) (c : ℝ)
    (W : Configuration n → ℝ) (hW : ∀ p x, W (permute p x) = W x)
    (hi : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2))
    (h : ∀ s, ∀ᵐ x ∂volume, ‖u.fullAntisymmetrize.value s x‖^2 =
      c*∑ p : Equiv.Perm (Fin n), ‖(u.permutation p).value s x‖^2) :
    potentialEnergy W u.fullAntisymmetrize =
      c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ)*potentialEnergy W u := by
  have he (s : Spins n) : (∫ x, W x*‖u.fullAntisymmetrize.value s x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∫ x, W x*‖(u.permutation p).value s x‖^2 := by
    rw [integral_congr_ae ((h s).mono (fun x hx => congrArg (W x*·) hx))]
    simp_rw [mul_left_comm (W _) c, Finset.mul_sum]
    rw [integral_finsetSum _
      (fun p _ => (potential_integrable_permutation W hW u hi p s).const_mul c)]
    simp only [integral_const_mul]
  unfold potentialEnergy
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  change c*(∑ p : Equiv.Perm (Fin n), potentialEnergy W (u.permutation p)) = _
  simp_rw [potentialEnergy_permutation W hW]
  simp [potentialEnergy, mul_assoc]

lemma potentialEnergy_scale {n : ℕ} (W : Configuration n → ℝ) (u : H1Vector n) (c : ℂ) :
    potentialEnergy W (u.scale c) = ‖c‖^2*potentialEnergy W u := by
  simp only [potentialEnergy,H1Vector.scale,norm_mul,mul_pow]
  simp_rw [mul_left_comm (W _) (‖c‖^2),integral_const_mul,← Finset.mul_sum]

lemma potentialEnergy_wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B) (hAB : Disjoint A B)
    (W : Configuration (m+k) → ℝ) (hW : ∀ p x, W (permute p x) = W x)
    (hi : ∀ s, Integrable (fun x => W x*‖(u.tensor v).value s x‖^2)) :
    potentialEnergy W (u.wedge v) = potentialEnergy W (u.tensor v) := by
  unfold H1Vector.wedge
  rw [potentialEnergy_scale, wedge_normalizer_sq,
    potentialEnergy_fullAntisymmetrize_of_sq (u.tensor v) _ W hW hi
      (separated_fullAntisymmetrize_value_sq u v hu hv A B hsu hsv hAB)]
  change (wedgeMultiplicity m k)⁻¹*(wedgeMultiplicity m k*potentialEnergy W (u.tensor v)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (wedgeMultiplicity_pos m k)), one_mul]
end Coulomb

end

end OAI
