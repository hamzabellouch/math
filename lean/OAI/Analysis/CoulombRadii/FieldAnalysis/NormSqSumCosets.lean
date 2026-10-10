import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PermuteJoinBlock

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
lemma norm_sq_sum_cosets {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (f : G → ℂ)
    (hc : ∀ p q, conj (f p)*f q = if p⁻¹*q ∈ H then ((‖f p‖^2 : ℝ) : ℂ) else 0) :
    ‖∑ p, f p‖^2 = (Fintype.card H : ℝ)*∑ p, ‖f p‖^2 := by
  apply Complex.ofReal_injective
  push_cast
  rw [← Complex.conj_mul', map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, hc]
  have hi (p : G) :
      (∑ q : G, if p⁻¹*q ∈ H then ((‖f p‖^2 : ℝ) : ℂ) else (0:ℂ)) =
        (Fintype.card H : ℂ)*(‖f p‖^2 : ℝ) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft p)]
    change (∑ r : G, if p⁻¹*(p*r) ∈ H then ((‖f p‖^2 : ℝ) : ℂ) else 0) = _
    simp only [inv_mul_cancel_left]
    rw [← Finset.sum_filter]
    simp [Fintype.card_subtype]
  simp_rw [hi]
  push_cast
  rfl

lemma signed_coset_correlation {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : ∀ p, χ p*χ p = 1) (hχr : ∀ p, conj (χ p) = χ p)
    (H : Subgroup G) (f : G → ℂ)
    (hc : ∀ p h, h ∈ H → f (p*h) = χ h*f p)
    (hz : ∀ p q, p⁻¹*q ∉ H → conj (f p)*f q = 0) (p q : G) :
    conj (χ p*f p)*(χ q*f q) =
      if p⁻¹*q ∈ H then ((‖χ p*f p‖^2 : ℝ) : ℂ) else 0 := by
  by_cases h : p⁻¹*q ∈ H
  · rw [ite_eq_left h]
    have hq : q = p*(p⁻¹*q) := by group
    have hf := hc p (p⁻¹*q) h
    rw [← hq] at hf
    rw [hf]
    conv_lhs => arg 2; arg 1; rw [hq, map_mul]
    have he : χ p * χ (p⁻¹*q) * (χ (p⁻¹*q)*f p) = χ p*f p := by
      rw [mul_assoc, ← mul_assoc (χ (p⁻¹*q)), hχ, one_mul]
    rw [he, Complex.conj_mul']
    push_cast
    rfl
  · rw [ite_eq_right h, map_mul, hχr]
    calc
      _ = χ p*χ q*(conj (f p)*f q) := by ring
      _ = 0 := by rw [hz p q h, mul_zero]

lemma norm_sq_signed_sum_cosets {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : ∀ p, χ p*χ p = 1) (hχr : ∀ p, conj (χ p) = χ p)
    (H : Subgroup G) (f : G → ℂ)
    (hc : ∀ p h, h ∈ H → f (p*h) = χ h*f p)
    (hz : ∀ p q, p⁻¹*q ∉ H → conj (f p)*f q = 0) :
    ‖∑ p, χ p*f p‖^2 = (Fintype.card H : ℝ)*∑ p, ‖f p‖^2 := by
  rw [norm_sq_sum_cosets H (fun p => χ p*f p)
    (signed_coset_correlation χ hχ hχr H f hc hz)]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have hn : ‖χ p‖^2 = 1 := by
    have H := congrArg norm (hχ p)
    simpa [norm_mul, pow_two] using H
  rw [norm_mul, mul_pow, hn, one_mul]
lemma permutation_mul_value {n : ℕ} (u : H1Vector n) (p q : Equiv.Perm (Fin n))
    (s : Spins n) (x : Configuration n) :
    (u.permutation (p*q)).value s x = ((u.permutation q).permutation p).value s x := by
  simp only [permutation_value, permute_mul]
  rfl
lemma permutation_mul_gradient {n : ℕ} (u : H1Vector n) (p q : Equiv.Perm (Fin n))
    (s : Spins n) (a : Fin n × Fin 3) (x : Configuration n) :
    (u.permutation (p*q)).gradient s a x = ((u.permutation q).permutation p).gradient s a x := by
  simp only [permutation_gradient, permute_mul]
  rfl

lemma permutation_value_covariance {n : ℕ} (u : H1Vector n) (h : Equiv.Perm (Fin n))
    (c : ℂ) (hc : ∀ s, (u.permutation h).value s =ᵐ[volume] fun x => c*u.value s x)
    (p : Equiv.Perm (Fin n)) (s : Spins n) :
    (u.permutation (p*h)).value s =ᵐ[volume] fun x => c*(u.permutation p).value s x := by
  have H := (permute_measurePreserving p).quasiMeasurePreserving.ae (hc (s ∘ p))
  filter_upwards [H] with x hx
  rw [permutation_mul_value, permutation_value, permutation_value]
  exact hx

lemma permutation_gradient_covariance {n : ℕ} (u : H1Vector n) (h : Equiv.Perm (Fin n))
    (c : ℂ) (hc : ∀ s, (u.permutation h).value s =ᵐ[volume] fun x => c*u.value s x)
    (p : Equiv.Perm (Fin n)) (s : Spins n) (a : Fin n × Fin 3) :
    (u.permutation (p*h)).gradient s a =ᵐ[volume]
      fun x => c*(u.permutation p).gradient s a x := by
  have hg := H1Vector.gradient_congr_ae (u.permutation h) (u.scale c) hc
    (s ∘ p) (p.symm a.1,a.2)
  have H := (permute_measurePreserving p).quasiMeasurePreserving.ae hg
  filter_upwards [H] with x hx
  rw [permutation_mul_gradient]
  simpa only [permutation_gradient, H1Vector.scale] using hx

def complexSign (n : ℕ) : Equiv.Perm (Fin n) →* ℂ where
  toFun := fun p => ((p.sign : ℤ) : ℂ)
  map_one' := by simp
  map_mul' := by intro p q; simp

lemma complexSign_sq {n : ℕ} (p : Equiv.Perm (Fin n)) : complexSign n p*complexSign n p = 1 :=
  sign_complex_sq p
lemma complexSign_real {n : ℕ} (p : Equiv.Perm (Fin n)) : conj (complexSign n p) = complexSign n p := by
  simp [complexSign]

lemma fullAntisymmetrize_gradient {n : ℕ} (u : H1Vector n) (s : Spins n)
    (a : Fin n × Fin 3) (x : Configuration n) :
    u.fullAntisymmetrize.gradient s a x =
      ∑ p : Equiv.Perm (Fin n), complexSign n p*(u.permutation p).gradient s a x := rfl

lemma separated_fullAntisymmetrize_value_sq {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B) (hAB : Disjoint A B)
    (s : Spins (m+k)) :
    ∀ᵐ x ∂volume, ‖(u.tensor v).fullAntisymmetrize.value s x‖^2 =
      (Fintype.card (blockGroup m k) : ℝ)*
        ∑ p : Equiv.Perm (Fin (m+k)), ‖((u.tensor v).permutation p).value s x‖^2 := by
  have hc : ∀ᵐ x ∂volume, ∀ p : Equiv.Perm (Fin (m+k)), ∀ h : Equiv.Perm (Fin (m+k)),
      h ∈ blockGroup m k →
      ((u.tensor v).permutation (p*h)).value s x =
        complexSign (m+k) h*((u.tensor v).permutation p).value s x := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro h
    by_cases hh : h ∈ blockGroup m k
    · exact (permutation_value_covariance (u.tensor v) h _
        (tensor_block_covariance u v hu hv h hh) p s).mono (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun x h => (hh h).elim)
  have hz : ∀ᵐ x ∂volume, ∀ p q : Equiv.Perm (Fin (m+k)), p⁻¹*q ∉ blockGroup m k →
      conj (((u.tensor v).permutation p).value s x)*((u.tensor v).permutation q).value s x = 0 := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro q
    by_cases h : p⁻¹*q ∈ blockGroup m k
    · exact Filter.Eventually.of_forall (fun x hn => (hn h).elim)
    · exact (configSupported_value_orthogonal (u.tensor v) (blockRegion m k A B)
        (tensor_configSupported u v A B hsu hsv) p q
        (blockRegion_orbit_disjoint hAB p q h) s).mono (fun x hx _ => hx)
  filter_upwards [hc,hz] with x hx hy
  change ‖∑ p : Equiv.Perm (Fin (m+k)), complexSign (m+k) p*
    ((u.tensor v).permutation p).value s x‖^2 = _
  exact norm_sq_signed_sum_cosets (complexSign (m+k)) complexSign_sq complexSign_real
    (blockGroup m k) (fun p => ((u.tensor v).permutation p).value s x) hx hy

lemma separated_fullAntisymmetrize_gradient_sq {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3) :
    ∀ᵐ x ∂volume, ‖(u.tensor v).fullAntisymmetrize.gradient s a x‖^2 =
      (Fintype.card (blockGroup m k) : ℝ)*
        ∑ p : Equiv.Perm (Fin (m+k)), ‖((u.tensor v).permutation p).gradient s a x‖^2 := by
  have hc : ∀ᵐ x ∂volume, ∀ p : Equiv.Perm (Fin (m+k)), ∀ h : Equiv.Perm (Fin (m+k)),
      h ∈ blockGroup m k →
      ((u.tensor v).permutation (p*h)).gradient s a x =
        complexSign (m+k) h*((u.tensor v).permutation p).gradient s a x := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro h
    by_cases hh : h ∈ blockGroup m k
    · exact (permutation_gradient_covariance (u.tensor v) h _
        (tensor_block_covariance u v hu hv h hh) p s a).mono (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun x h => (hh h).elim)
  have hz : ∀ᵐ x ∂volume, ∀ p q : Equiv.Perm (Fin (m+k)), p⁻¹*q ∉ blockGroup m k →
      conj (((u.tensor v).permutation p).gradient s a x)*((u.tensor v).permutation q).gradient s a x = 0 := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro q
    by_cases h : p⁻¹*q ∈ blockGroup m k
    · exact Filter.Eventually.of_forall (fun x hn => (hn h).elim)
    · exact (configSupported_gradient_orthogonal (u.tensor v) (blockRegion m k A B)
        (tensor_configSupported u v A B hsu hsv) (isClosed_blockRegion hA hB) p q
        (blockRegion_orbit_disjoint hAB p q h) s a).mono (fun x hx _ => hx)
  filter_upwards [hc,hz] with x hx hy
  rw [fullAntisymmetrize_gradient]
  exact norm_sq_signed_sum_cosets (complexSign (m+k)) complexSign_sq complexSign_real
    (blockGroup m k) (fun p => ((u.tensor v).permutation p).gradient s a x) hx hy
end Coulomb

end

end OAI
