import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.EndpointSupports

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real SupportMixtures
open scoped Classical BigOperators
noncomputable section
variable {A B Ω Θ : Type*} [Fintype A] [Fintype B] [Fintype Ω] [Fintype Θ]

namespace AuxiliarySupport
variable {p : Law A} {good : Finset A} {M κ : ℝ}

def setLaw (X : AuxiliarySupport p good M κ) : Law (Finset A) :=
  X.law.map (fun b => levelSet p b ∩ good)

lemma setLaw_support (X : AuxiliarySupport p good M κ) (S : Finset A)
    (hS : X.setLaw.mass S ≠ 0) :
    S ⊆ good ∧ M * exp (-κ) / 2 ≤ (S.card : ℝ) ∧ (S.card : ℝ) ≤ M := by
  obtain ⟨b,hb,rfl⟩ := X.law.map_support (fun b => levelSet p b ∩ good) S hS
  exact ⟨inter_subset_right, X.size b⟩

lemma setLaw_sum (X : AuxiliarySupport p good M κ) (f : Finset A → ℝ) :
    (∑ S, X.setLaw.mass S * f S) =
      ∑ b, X.law.mass b * f (levelSet p b ∩ good) :=
  X.law.sum_map _ f

lemma setLaw_density (X : AuxiliarySupport p good M κ) (a : A) :
    (∑ S, X.setLaw.mass S * kernel S a) ≤
      4 * exp 1 * (if a ∈ good then p.mass a else 0) := by
  rw [X.setLaw_sum]
  by_cases ha : a ∈ good
  · simpa only [ite_eq_left ha, kernel] using X.density a
  · simp only [kernel, mem_inter, ha, and_false, ite_false, mul_zero, sum_const_zero,
      le_refl]

lemma setLaw_nonempty (X : AuxiliarySupport p good M κ) (hM : 0 < M)
    (S : Finset A) (hS : X.setLaw.mass S ≠ 0) : S.Nonempty := by
  have hh := (X.setLaw_support S hS).2.1
  apply card_pos.mp
  have : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast this

end AuxiliarySupport

def Law.withKernel (μ : Law Ω) (θ : Ω → Θ) (ρ : Θ → Law A) : Law (Ω × A) where
  mass x := μ.mass x.1 * (ρ (θ x.1)).mass x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((ρ (θ x.1)).nonneg x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, Law.total, mul_one]

omit [Fintype Θ] in
@[simp] lemma Law.withKernel_mass (μ : Law Ω) (θ : Ω → Θ) (ρ : Θ → Law A)
    (ω : Ω) (a : A) : (μ.withKernel θ ρ).mass (ω,a) =
      μ.mass ω * (ρ (θ ω)).mass a := rfl

omit [Fintype Θ] in
lemma Law.withKernel_fst (μ : Law Ω) (θ : Ω → Θ) (ρ : Θ → Law A) :
    (μ.withKernel θ ρ).fst = μ := by
  ext ω
  simp only [Law.fst, Law.withKernel_mass, ← mul_sum, Law.total, mul_one]

omit [Fintype Θ] in
lemma Law.withKernel_sum (μ : Law Ω) (θ : Ω → Θ) (ρ : Θ → Law A)
    (f : Ω → A → ℝ) :
    (∑ x, (μ.withKernel θ ρ).mass x * f x.1 x.2) =
      ∑ ω, μ.mass ω * ∑ a, (ρ (θ ω)).mass a * f ω a := by
  simp only [Fintype.sum_prod_type, Law.withKernel_mass, mul_sum, mul_assoc]

lemma Law.withKernel_history_sum (μ : Law Ω) (θ : Ω → Θ) (ρ : Θ → Law A)
    (f : Θ → A → ℝ) :
    (∑ x, (μ.withKernel θ ρ).mass x * f (θ x.1) x.2) =
      ∑ z, (μ.map θ).mass z * ∑ a, (ρ z).mass a * f z a := by
  exact (μ.withKernel_sum θ ρ (fun ω a => f (θ ω) a)).trans
    (μ.sum_map θ (fun z => ∑ a, (ρ z).mass a * f z a)).symm

lemma Law.withKernel_bound (μ : Law Ω) (θ : Ω → Θ) (ρ : Θ → Law A)
    (f : Ω → A → ℝ) (g : Θ → ℝ)
    (h : ∀ ω, μ.mass ω ≠ 0 → (∑ a, (ρ (θ ω)).mass a * f ω a) ≤ g (θ ω)) :
    (∑ x, (μ.withKernel θ ρ).mass x * f x.1 x.2) ≤
      ∑ z, (μ.map θ).mass z * g z := by
  rw [μ.withKernel_sum, μ.sum_map]
  apply sum_le_sum
  intro ω _
  by_cases hω : μ.mass ω = 0
  · simp only [hω, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h ω hω) (μ.nonneg ω)

end
end SharpLogRamsey.Selection

end

end OAI
