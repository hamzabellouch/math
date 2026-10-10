import OAI.Analysis.KadisonKastler.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Published small-normalizer factorization and its consequence

The factorization hypothesis is Proposition 3.2 of
Cameron–Christensen–Sinclair–Smith–White–Wiggins, *Kadison–Kastler stable
factors*, Duke Math. J. 163 (2014), 2639–2686.  That proposition factors
two sufficiently close normalizers through the algebra and its commutant.

Its specialization at the identity gives the small exact normalizer lemma
used in §7 of *Universal strong Kadison–Kastler stability* (2026), with
radius one and displacement constant four, under the stated factorization
hypothesis.
-/

namespace KadisonKastler

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A unitary in an algebra commutes with a unitary in its commutant. -/
theorem commute_of_mem_algebra_mem_commutant {P : VonNeumannAlgebra H}
    {a b : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P)
    (hb : (b : H →L[ℂ] H) ∈ P.commutant) :
    Commute (a : H →L[ℂ] H) (b : H →L[ℂ] H) :=
  VonNeumannAlgebra.mem_commutant_iff.mp hb _ ha

/-- Unitaries belonging to the algebra normalize it. -/
theorem conjugates_self_of_mem {P : VonNeumannAlgebra H}
    {a : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P) :
    Conjugates a P P := by
  change unitaryConj a '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem ha hx) (star_mem ha)
  · intro hy
    refine ⟨unitaryConj (star a) y, ?_, ?_⟩
    · exact mul_mem (mul_mem (star_mem ha) hy)
        (by simpa only [Unitary.coe_star, star_star] using ha)
    · simpa only [star_star] using unitaryConj_star_unitaryConj (star a) y

/-- Unitaries in the commutant act trivially on the algebra by conjugation. -/
theorem unitaryConj_eq_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant)
    {x : H →L[ℂ] H} (hx : x ∈ P) : unitaryConj b x = x := by
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  rw [unitaryConj, ← hcomm, mul_assoc,
    Unitary.mul_star_self_of_mem b.property, mul_one]

theorem conjugates_self_of_mem_commutant {P : VonNeumannAlgebra H}
    {b : unitary (H →L[ℂ] H)} (hb : (b : H →L[ℂ] H) ∈ P.commutant) :
    Conjugates b P P := by
  change unitaryConj b '' (P : Set (H →L[ℂ] H)) = (P : Set (H →L[ℂ] H))
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [unitaryConj_eq_self_of_mem_commutant hb hy] using hy
  · intro hx
    exact ⟨x, hx, unitaryConj_eq_self_of_mem_commutant hb hx⟩

/-- A product of an algebra unitary and a commutant unitary normalizes the algebra. -/
theorem conjugates_self_of_separate_factors {P : VonNeumannAlgebra H}
    {a b : unitary (H →L[ℂ] H)} (ha : (a : H →L[ℂ] H) ∈ P)
    (hb : (b : H →L[ℂ] H) ∈ P.commutant) : Conjugates (a * b) P P :=
  (conjugates_self_of_mem_commutant hb).trans (conjugates_self_of_mem ha)

/-- Precisely the quantitative normalizer factorization of CCSSWW (2014),
Proposition 3.2. Distances are written in the symmetric order `u₂ - u₁`. -/
def PublishedNormalizerFactorization : Prop :=
  ∀ (P : VonNeumannAlgebra H) (u₁ u₂ : unitary (H →L[ℂ] H)),
    Conjugates u₁ P P → Conjugates u₂ P P →
    ‖(u₂ : H →L[ℂ] H) - (u₁ : H →L[ℂ] H)‖ < 1 →
    ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      u₂ = u₁ * a * b ∧
      ‖(a : H →L[ℂ] H) - 1‖ ≤ Real.sqrt 2 * ‖(u₂ : H →L[ℂ] H) - u₁‖ ∧
      ‖(b : H →L[ℂ] H) - 1‖ ≤
        (Real.sqrt 2 + 1) * ‖(u₂ : H →L[ℂ] H) - u₁‖

/-- The small exact normalizer consequence of the published factorization.
Unlike the application in the manuscript, this input already applies to
arbitrary von Neumann algebras. -/
theorem small_exact_normalizer
    (hPublished : PublishedNormalizerFactorization (H := H))
    {P : VonNeumannAlgebra H} {v : unitary (H →L[ℂ] H)}
    (hv : Conjugates v P P) (hsmall : ‖(v : H →L[ℂ] H) - 1‖ < 1) :
    ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      v = a * b ∧
      ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤
        4 * ‖(v : H →L[ℂ] H) - 1‖ := by
  obtain ⟨a, b, ha, hb, hab, hna, hnb⟩ :=
    hPublished P 1 v (conjugates_one P) hv (by simpa using hsmall)
  refine ⟨a, b, ha, hb, by simpa using hab, ?_⟩
  simp only [OneMemClass.coe_one] at hna hnb
  have hsqrt : Real.sqrt 2 < (3 / 2 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hconstant : 2 * Real.sqrt 2 + 1 ≤ 4 := by linarith
  calc
    ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤
        Real.sqrt 2 * ‖(v : H →L[ℂ] H) - 1‖ +
          (Real.sqrt 2 + 1) * ‖(v : H →L[ℂ] H) - 1‖ := add_le_add hna hnb
    _ = (2 * Real.sqrt 2 + 1) * ‖(v : H →L[ℂ] H) - 1‖ := by ring
    _ ≤ 4 * ‖(v : H →L[ℂ] H) - 1‖ :=
      mul_le_mul_of_nonneg_right hconstant (norm_nonneg _)

end KadisonKastler

end OAI
