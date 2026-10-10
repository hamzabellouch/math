import Mathlib
import OAI.RepresentationTheory.PartialPermutation.DegreeTransfer

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation
noncomputable section

lemma inverseDegreeSum_nonneg (G : Type*) [Group G] [Fintype G] (u : ℝ) :
    0 ≤ inverseDegreeSum G u := by
  exact Finset.sum_nonneg (fun c _ => Real.rpow_nonneg (by positivity) _)

lemma smallDegreeSum_le_inverseDegreeSum (G : Type*) [Group G] [Fintype G]
    {u R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    smallDegreeSum G R ≤ R^(u+2) * inverseDegreeSum G u := by
  rw [smallDegreeSum, inverseDegreeSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · have hd : 0 < (irreducibleDegree c : ℝ) := by
      have : Nontrivial (irreducibleSpace c) :=
        IsSimpleModule.nontrivial ℂ[G] (irreducibleRep c).asModule
      exact_mod_cast (Module.finrank_pos : 0 < irreducibleDegree c)
    calc
      (irreducibleDegree c : ℝ)^2 =
          (irreducibleDegree c : ℝ)^(u+2) * (irreducibleDegree c : ℝ)^(-u) := by
        rw [← Real.rpow_add hd]
        ring_nf
        rw [Real.rpow_two]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hd.le hc (by linarith)) (Real.rpow_nonneg hd.le _)
  · positivity

variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {b : ℕ} (H : Fin b → Subgroup G)

theorem inverse_degree_sum_transfer [Representation.IsIrreducible ρ]
    (hb : 0 < b) (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (f : G → ℝ) (B u : ℝ) (hf : ∀ g, 0 ≤ f g) (hu : 0 < u)
    (hcap : ∀ i, LeftCosetCap f (H i) B) :
    hsNormSq (complexFourier ρ (fun g => f g)) ≤
      B * mass f * (Module.finrank ℂ V : ℝ)^(-1 + (u+2)/(b : ℝ)) *
        ∑ i, inverseDegreeSum (H i) u := by
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hD : 0 < (Module.finrank ℂ V : ℝ) := by exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℂ V)
  have hB : 0 ≤ B := by
    let i : Fin b := ⟨0, hb⟩
    have hp : (0 : ℝ) < (H i).index := by
      exact_mod_cast Nat.pos_of_ne_zero (H i).index_ne_zero_of_finite
    have hz : 0 ≤ B / (H i).index :=
      (Finset.sum_nonneg (fun (g : H i) _ => hf (1*g))).trans (hcap i 1)
    simpa only [div_mul_cancel₀ B hp.ne'] using mul_nonneg hz hp.le
  have hm : 0 ≤ mass f := Finset.sum_nonneg (fun g _ => hf g)
  have ht := small_degree_sum_transfer ρ H hb hρ hcomm f B hf hcap
  have hs : ∑ i, smallDegreeSum (H i) ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))) ≤
      (Module.finrank ℂ V : ℝ)^((u+2)/(b : ℝ)) * ∑ i, inverseDegreeSum (H i) u := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have ht := smallDegreeSum_le_inverseDegreeSum (H i) hu (Real.rpow_pos_of_pos hD (1/(b : ℝ)))
    rw [← Real.rpow_mul hD.le] at ht
    convert ht using 1; congr 2; ring
  have hn := ht.trans (mul_le_mul_of_nonneg_left hs (mul_nonneg hB hm))
  apply (mul_le_mul_iff_right₀ hD).mp
  calc
    _ ≤ _ := hn
    _ = _ := by
      rw [show (u+2)/(b : ℝ) = (-1+(u+2)/(b : ℝ))+1 by ring,
        Real.rpow_add hD, Real.rpow_one]
      ring_nf

end
end PartialPermutation

end

end OAI
