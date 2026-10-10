import OAI.Probability.ThorpShuffle.ExceptionalShapes
import OAI.Probability.ThorpShuffle.BlockEmbedding
import OAI.Probability.ThorpShuffle.Model

namespace OAI

universe uE

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Thorp.Fourier

/-- The first inverse-degree moment yields a `D^(3/8)` orbit bound.
The filter is precisely `degree ≤ D^(1/8)`, written without a root. -/
lemma low_degree_first {H : Type} [Group H] [Fintype H]
    (F : Fourier.Family H) (D : ℕ) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D), (F.degree b : ℝ)^2) ≤
      (D : ℝ) ^ (3 / 8 : ℝ) * ∑ b, (F.degree b : ℝ)⁻¹ := by
  let s := Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D)
  have hp (b : F.Index) : (0 : ℝ) < F.degree b := by exact_mod_cast F.positive b
  have hsmall : ∑ b ∈ s, (F.degree b : ℝ)⁻¹ ≤ ∑ b, (F.degree b : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b _ _ => inv_nonneg.mpr (hp b).le)
  calc
    _ ≤ ∑ b ∈ s, (D : ℝ) ^ (3 / 8 : ℝ) * (F.degree b : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro b hb
      have hbD : (F.degree b : ℝ)^8 ≤ D := by
        exact_mod_cast (Finset.mem_filter.mp hb).2
      apply (le_mul_inv_iff₀ (hp b)).mpr
      calc
        (F.degree b : ℝ)^2 * F.degree b = (F.degree b : ℝ)^3 := by ring
        _ = ((F.degree b : ℝ)^8) ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_natCast_mul (hp b).le]
          norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hbD (by norm_num)
    _ = (D : ℝ) ^ (3 / 8 : ℝ) * ∑ b ∈ s, (F.degree b : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg (Nat.cast_nonneg D) _)

/-- The integrated operator norm bound for an eight-fold block action
with a common probability mass function satisfying all eight coset caps. -/
lemma eight_block_of_cap {G : Type} [Group G] [Fintype G]
    (s : ℕ) (hs : 1 ≤ s)
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ψ : (Fin 8 → Equiv.Perm (Fin s)) →* G)
    (ν : G → ℝ) (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1)
    (hcoset : ∀ (i : Fin 8) g,
      ∑ h : Equiv.Perm (Fin s), ν (g * ψ (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin s)) : ℝ) / Fintype.card G) :
    ‖LinearMap.toContinuousLinearMap (integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ) := by
  let : Nontrivial E := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hD : (0 : ℝ) < Module.finrank ℂ E := by exact_mod_cast (Module.finrank_pos (R:=ℂ) (M:=E))
  let D := Module.finrank ℂ E
  let F := Specht.symmetricFamily s
  have hsum : (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D), (F.degree b : ℝ)^2) ≤
      (D : ℝ) ^ (3 / 8 : ℝ) * C1 := by
    refine (low_degree_first F D).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact reciprocalFirst_le_C1 s hs
  have hconst : 0 ≤ Real.sqrt (32 * C1) * (D : ℝ) ^ (-5 / 16 : ℝ) := by positivity
  have hconst_sq : (Real.sqrt (32 * C1) * (D : ℝ) ^ (-5 / 16 : ℝ))^2 =
      8 * 4 * ((D : ℝ) ^ (3 / 8 : ℝ) * C1) / D := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) C1_nonneg),
      ← Real.rpow_mul_natCast (Nat.cast_nonneg D)]
    rw [show (-5 / 16 : ℝ) * (2 : ℕ) = (3 / 8 : ℝ) - 1 by norm_num,
      Real.rpow_sub hD, Real.rpow_one]
    ring
  apply ContinuousLinearMap.opNorm_le_bound _ hconst
  intro v
  have hb := F.integrated_norm_sq ρ hu (Nat.ne_of_gt Module.finrank_pos) ψ ν 4 hν h1
    (by norm_num) (fun i g => by
      convert hcoset i g using 1
      apply Finset.sum_congr rfl
      intro h _
      congr 3
      funext j
      by_cases hij : j = i <;> simp [hij]) v
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hb
  have hv : ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ^ 2 ≤
      (Real.sqrt (32 * C1) * (D : ℝ) ^ (-5 / 16 : ℝ) * ‖v‖)^2 := by
    rw [mul_pow, hconst_sq]
    exact hb.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num)) hD.le) (sq_nonneg _))
  change ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ≤ _
  nlinarith [norm_nonneg (integrated ρ (fun g => (ν g : ℂ)) v),
    mul_nonneg hconst (norm_nonneg v)]

/-- The integrated operator norm bound for permutations of binary positions
under any equivalence with eight equal blocks. -/
theorem eight_block_fourier_bound
    (d : ℕ) (_hd : 3 ≤ d)
    (e : Position d ≃ Fin 8 × Fin (2 ^ (d - 3)))
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (Equiv.Perm (Position d)) E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ν : Equiv.Perm (Position d) → ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1)
    (hcoset : ∀ (i : Fin 8) (g : Equiv.Perm (Position d)),
      ∑ h : Equiv.Perm (Fin (2 ^ (d - 3))),
          ν (g * Block.embedding e (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin (2 ^ (d - 3)))) : ℝ) /
          Fintype.card (Equiv.Perm (Position d))) :
    ‖LinearMap.toContinuousLinearMap (Fourier.integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ) := by
  exact eight_block_of_cap (2 ^ (d - 3)) (Nat.one_le_pow _ _ (by norm_num)) ρ hu
    (Block.embedding e) ν hν h1 hcoset

end Thorp.Current

end

end OAI
