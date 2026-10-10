import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Colon
import OAI.NumberTheory.PiExponent.Analysis.HilbertSeries

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem ideal_le_colon_singleton (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) : I ≤ I.colon {f} := by
  intro p hp
  apply Submodule.mem_colon_singleton.mpr
  simpa only [smul_eq_mul] using I.mul_mem_right f hp

omit [Finite σ] in
theorem quotientSectionFactor_colon_ker (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n) =
      LinearMap.ker (quotientSectionMultiply I f hf n) := by
  ext x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
  change Ideal.Quotient.mk I p = x.1 at hpx
  simp only [LinearMap.mem_ker, Subtype.ext_iff]
  change (Ideal.Quotient.factorₐ k (ideal_le_colon_singleton I f)) x.1 = 0 ↔
    x.1 * Ideal.Quotient.mk I f = 0
  rw [← hpx]
  change Ideal.Quotient.mk (I.colon {f}) p = 0 ↔
    Ideal.Quotient.mk I (p * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    Submodule.mem_colon_singleton, smul_eq_mul]

theorem quotientSectionMultiply_range_finrank_colon
    (I : Ideal (MvPolynomial σ k)) {d : ℕ}
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (LinearMap.range (quotientSectionMultiply I f hf n)) =
      Module.finrank k (quotientSection (I.colon {f}) n) := by
  let φ := quotientSectionFactor I (I.colon {f}) (ideal_le_colon_singleton I f) n
  have hd := (LinearMap.ker φ).finrank_quotient_add_finrank
  let e := φ.quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (I.colon {f}) (ideal_le_colon_singleton I f) n)
  rw [e.finrank_eq] at hd
  change Module.finrank k (quotientSection (I.colon {f}) n) +
    Module.finrank k (LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n)) = _ at hd
  rw [quotientSectionFactor_colon_ker I f hf n] at hd
  have hm := (quotientSectionMultiply I f hf n).finrank_range_add_finrank_ker
  omega

theorem colon_hilbert_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection (I.colon {f}) n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank
  rw [quotientSectionMultiply_range_finrank_colon I f hf n,
    ← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

theorem sectionHilbertSeries_colon_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) :
    sectionHilbertSeries I = sectionHilbertSeries (Ideal.span {f} ⊔ I) +
      PowerSeries.X ^ d * sectionHilbertSeries (I.colon {f}) := by
  ext n
  rw [map_add, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := colon_hilbert_step I hI f hf (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right hdn, add_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn)).symm

end PiExponentJets.W64

end OAI
