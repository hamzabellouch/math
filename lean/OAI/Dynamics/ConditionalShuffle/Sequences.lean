import OAI.Dynamics.ConditionalShuffle.SignProduct

namespace OAI

noncomputable section
namespace Thorp.Fourier
open scoped Classical
variable {G : Type} [Fintype G] [group_G : Group G]

lemma tv_realProduct (n : ℕ) (μ ν : Fin n → G → ℝ)
    (hμ : ∀ i g, 0 ≤ μ i g) (hμ1 : ∀ i, ∑ g, μ i g = 1)
    (hν : ∀ i g, 0 ≤ ν i g) (hν1 : ∀ i, ∑ g, ν i g = 1) :
    tv (realProduct n μ) (realProduct n ν) ≤ ∑ i, tv (μ i) (ν i) := by
  induction n with
  | zero => simp [realProduct, tv]
  | succ n ih =>
      rw [realProduct, realProduct, Fin.sum_univ_castSucc]
      calc
        _ ≤ tv (μ (Fin.last n)) (ν (Fin.last n)) +
            tv (realProduct n (Fin.init μ)) (realProduct n (Fin.init ν)) :=
          tv_realConv _ _ _ _ (hν _) (hν1 _)
            (realProduct_nonneg _ _ (fun i => hμ i.castSucc))
            (realProduct_sum _ _ (fun i => hμ1 i.castSucc))
        _ ≤ _ := by
          have hh := ih (Fin.init μ) (Fin.init ν) (fun i => hμ i.castSucc) (fun i => hμ1 i.castSucc)
            (fun i => hν i.castSucc) (fun i => hν1 i.castSucc)
          dsimp only [Fin.init] at hh
          linarith

lemma character_probability_norm (χ : G → ℂ) (hχ : ∀ g, ‖χ g‖ ≤ 1)
    (μ : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1) :
    ‖∑ g, (μ g : ℂ) * χ g‖ ≤ 1 := by
  let retained_group_G := group_G
  calc
    _ ≤ ∑ g, ‖(μ g : ℂ) * χ g‖ := norm_sum_le _ _
    _ ≤ ∑ g, μ g := by
      apply Finset.sum_le_sum
      intro g _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ g)]
      exact (mul_le_mul_of_nonneg_left (hχ g) (hμ g)).trans_eq (mul_one _)
    _ = 1 := hμ1

lemma character_realProduct_last (χ : G →* ℂ) (hχ : ∀ g, ‖χ g‖ ≤ 1)
    (n : ℕ) (μ : Fin (n + 1) → G → ℝ)
    (hμ : ∀ i g, 0 ≤ μ i g) (h1 : ∀ i, ∑ g, μ i g = 1) :
    ‖∑ g, (realProduct (n + 1) μ g : ℂ) * χ g‖ ≤
      ‖∑ g, (μ (Fin.last n) g : ℂ) * χ g‖ := by
  rw [realProduct, realConv_character, norm_mul]
  have h := character_probability_norm χ hχ (realProduct n (Fin.init μ))
    (realProduct_nonneg _ _ (fun i => hμ i.castSucc))
    (realProduct_sum _ _ (fun i => h1 i.castSucc))
  simpa using mul_le_mul_of_nonneg_left h (norm_nonneg (∑ g, (μ (Fin.last n) g : ℂ) * χ g))

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
open Thorp.Fourier
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Nontrivial α]

lemma error_sum_sqrt_bound (a b δ S : ℝ) (hδ : 0 ≤ δ) (hS : 0 ≤ S) (hb0 : 0 ≤ b)
    (hb : b ≤ 2 * δ) (ha : a ^ 2 ≤ 2 * b ^ 2 + S) (ha0 : 0 ≤ a) :
    a ≤ 4 * δ + Real.sqrt S := by
  have hsq : a ^ 2 ≤ (4 * δ + Real.sqrt S) ^ 2 := by
    have hh := mul_self_le_mul_self hb0 hb
    have hs := Real.sq_sqrt hS
    have hz := Real.sqrt_nonneg S
    nlinarith [mul_nonneg hδ hz]
  exact (sq_le_sq₀ ha0 (by positivity)).mp hsq

theorem repaired_eight_tv (hn : 16 ≤ Fintype.card α)
    (ψ : (Fin 8 → Equiv.Perm β) →* Equiv.Perm α) (μ : Fin 8 → Equiv.Perm α → ℝ)
    (hμ : ∀ i g, 0 ≤ μ i g) (h1 : ∀ i, ∑ g, μ i g = 1)
    (hc : 2 * ((Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α)) < 1)
    (hb : ∀ i, Trim.signDichotomy (μ i)) :
    tv (realProduct 8 μ) (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) ≤
      4 * (∑ i, Trim.discarded ψ (μ i)) + (1/2 : ℝ) * Real.sqrt
        ((32 * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α)) := by
  let ν := fun i => Trim.repair ψ (μ i)
  let δ := ∑ i, Trim.discarded ψ (μ i)
  have hδ : 0 ≤ δ := Finset.sum_nonneg (fun i _ => Trim.discarded_nonneg ψ (μ i) (hμ i))
  have hν : ∀ i g, 0 ≤ ν i g := fun i => Trim.repair_nonneg ψ (μ i) (hμ i)
  have hν1 : ∀ i, ∑ g, ν i g = 1 := fun i => Trim.repair_sum ψ (μ i) (h1 i)
  have hcoset : ∀ j i g, ∑ h, ν j (g * ψ (Pi.mulSingle i h)) ≤
      4 * (Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α) := by
    intro j i g
    convert Trim.repair_coset ψ (μ j) (hμ j) i g using 1
    apply Finset.sum_congr rfl
    intro h _
    congr 4
    exact Subsingleton.elim _ _
  have hdist : tv (realProduct 8 μ) (realProduct 8 ν) ≤ 2 * δ := by
    apply (tv_realProduct 8 μ ν hμ h1 hν hν1).trans
    dsimp only [δ]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => Trim.repair_tv ψ (μ i) (hμ i) (h1 i))
  have hlast : Trim.discarded ψ (μ (Fin.last 7)) ≤ δ :=
    Finset.single_le_sum (fun i _ => Trim.discarded_nonneg ψ (μ i) (hμ i)) (Finset.mem_univ _)
  have hpar : ‖∑ g, (realProduct 8 ν g : ℂ) * complexSign g‖ ≤ 2 * δ := by
    apply (character_realProduct_last complexSign (fun g => (complexSign_norm g).le) 7 ν hν hν1).trans
    exact (Trim.repair_bias ψ (μ _) (hμ _) (h1 _) hc (hb _)).trans (by linarith)
  have hfour := permutation_eight_sequence_bound hn ψ ν 4 hν hν1 (by norm_num) hcoset
  norm_num only [show (8 : ℝ) * 4 = 32 by norm_num] at hfour
  let S := (32 * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α)
  have hS : 0 ≤ S := by
    dsimp only [S, exceptionalReciprocalSum, inverseDegree]
    positivity
  have hnorm := error_sum_sqrt_bound _ _ δ S hδ hS (norm_nonneg _) hpar hfour
    (Finset.sum_nonneg (fun g _ => abs_nonneg _))
  calc
    _ ≤ tv (realProduct 8 μ) (realProduct 8 ν) +
      tv (realProduct 8 ν) (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) := tv_triangle _ _ _
    _ ≤ 2 * δ + (1/2 : ℝ) * (4 * δ + Real.sqrt S) := add_le_add hdist
      (mul_le_mul_of_nonneg_left hnorm (by norm_num))
    _ = _ := by dsimp only [δ, S]; ring

end Thorp.Specht

end

end OAI
