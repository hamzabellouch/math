import OAI.Analysis.Mahler.SpecialLeadingTerm
import OAI.Analysis.Mahler.StripGeometry

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter Finset Asymptotics
open scoped Topology
open MahlerConformal
variable {n N : ℕ}

/-- Squared Euclidean norm of the actual holomorphic vector, in coordinates. -/
noncomputable def specialTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) : ℝ :=
  ∑ j, ‖specialMap A m z j‖^2

lemma specialTau_eq_stripTau (A : Matrix (Fin N) (Fin n) ℝ) (m : ℕ) (z : Fin n → ℂ) :
    specialTau A m z = stripTau A m (complexToReal z) := by
  simpa only [specialTau,specialMap,complexRow_eq_stripCoordinate] using!
    (stripTau_eq_sum_norm_sq (fun j i => A j i) m (complexToReal z)).symm

/-- The compact-closure premise transfers to actual complex coordinates. -/
theorem specialTau_compact_closure (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 0 < m)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure {z | z ∈ complexStripDomain A ∧ specialTau A m z < R}) ∧
      closure {z | z ∈ complexStripDomain A ∧ specialTau A m z < R} ⊆ complexStripDomain A := by
  have h := strip_sublevel_compact_closure A hA hm hR hR1
  let S := {z | z ∈ stripDomain A ∧ stripTau A m z < R}
  let K := (complexRealEquiv (n := n)) ⁻¹' closure S
  have hK : IsCompact K := complexRealEquiv.toHomeomorph.isCompact_preimage.mpr h.1
  have hs : {z | z ∈ complexStripDomain A ∧ specialTau A m z < R} ⊆ K := by
    intro z hz
    apply subset_closure
    have hu := hz.1
    rw [complexStripDomain_eq_preimage] at hu
    exact ⟨hu,by
      change stripTau A m (complexToReal z) < R
      simpa only [specialTau_eq_stripTau] using hz.2⟩
  have hclosure := closure_minimal hs hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure hclosure,?_⟩
  intro z hz
  have hmem : complexToReal z ∈ closure S := hclosure hz
  rw [complexStripDomain_eq_preimage]
  exact h.2 hmem

theorem specialMap_mass_hypotheses (A : Matrix (Fin N) (Fin n) ℝ)
    (hA : Function.Injective (measurement A)) {m : ℕ} (hm : 2 ≤ m) :
    IsOpen (complexStripDomain A) ∧ (0 : Fin n → ℂ) ∈ complexStripDomain A ∧
    DifferentiableOn ℂ (specialMap A m) (complexStripDomain A) ∧
    (∀ z ∈ complexStripDomain A, specialMap A m z = 0 ↔ z = 0) ∧
    (∀ j : Fin N, (specialLeadingPolynomial A m j).IsHomogeneous m) ∧
    (∀ z : Fin n → ℂ, ∀ j : Fin N,
      MvPolynomial.eval z (specialLeadingPolynomial A m j) = specialLeadingMap A m z j) ∧
    (∀ z : Fin n → ℂ, specialLeadingMap A m z = 0 ↔ z = 0) ∧
    ((fun z : Fin n → ℂ => specialMap A m z-specialLeadingMap A m z) =O[𝓝 0]
      (fun z : Fin n → ℂ => ‖z‖^(m+1))) ∧
    (∀ R : ℝ, 0 < R → R < 1 →
      IsCompact (closure {z | z ∈ complexStripDomain A ∧ (∑ j, ‖specialMap A m z j‖^2) < R}) ∧
      closure {z | z ∈ complexStripDomain A ∧ (∑ j, ‖specialMap A m z j‖^2) < R} ⊆ complexStripDomain A) := by
  have hm0 : 0 < m := by omega
  exact ⟨isOpen_complexStripDomain A,zero_mem_complexStripDomain A,
    differentiableOn_specialMap A m,fun _ hz => specialMap_eq_zero_iff A hA hm0 hz,
    specialLeadingPolynomial_homogeneous A m,fun z j => specialLeadingPolynomial_eval A m j z,
    specialLeadingMap_eq_zero_iff A hA hm0,specialMap_leading_remainder A m,
    fun _ hR hR1 => specialTau_compact_closure A hA hm0 hR hR1⟩

end SymmetricMahler

end OAI
