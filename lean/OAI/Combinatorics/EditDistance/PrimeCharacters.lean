import OAI.Combinatorics.EditDistance.FourierCharacters

namespace OAI

/-!
# Coprime roots and prime-product Fourier multipliers
-/

namespace EditFourier
open scoped BigOperators
open Finset

section CoprimeRoots
variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in

theorem prod_roots_pow (s : Finset J) (p : J → ℕ) (z : J → ℂ)
    (hz : ∀ j ∈ s, z j ^ p j = 1) (q : ℕ) (hq : ∀ j ∈ s, p j ∣ q) :
    (∏ j ∈ s, z j) ^ q = 1 := by
  rw [← prod_pow]
  apply prod_eq_one
  intro j hj
  obtain ⟨m, hm⟩ := hq j hj
  rw [hm, pow_mul, hz j hj, one_pow]

theorem coprime_roots_nontrivial (s : Finset J) (p : J → ℕ) (z : J → ℂ)
    (hcop : (s : Set J).Pairwise (fun i j => (p i).Coprime (p j)))
    (hz : ∀ j ∈ s, z j ^ p j = 1) (i : J) (hi : i ∈ s) (hne : z i ≠ 1) :
    (∏ j ∈ s, z j) ≠ 1 := by
  intro h
  let q := ∏ j ∈ s.erase i, p j
  have hq : ∀ j ∈ s.erase i, p j ∣ q := fun j hj => dvd_prod_of_mem p hj
  have hpow := prod_roots_pow (s.erase i) p z
    (fun j hj => hz j (mem_of_mem_erase hj)) q hq
  have hp : z i ^ q = 1 := by
    have hh := congrArg (fun a : ℂ => a ^ q) h
    rw [← mul_prod_erase s z hi, mul_pow, hpow, mul_one, one_pow] at hh
    exact hh
  have hc : (p i).Coprime q := Nat.Coprime.prod_right fun j hj =>
    hcop hi (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm
  exact hne ((pow_eq_one_iff_of_coprime hc).mp ⟨hz i hi, hp⟩)

theorem coprime_root_separation (s : Finset J) (p : J → ℕ) (z : J → ℂ)
    (hpos : ∀ j ∈ s, 0 < p j)
    (hcop : (s : Set J).Pairwise (fun i j => (p i).Coprime (p j)))
    (hz : ∀ j ∈ s, z j ^ p j = 1) (hnorm : ∀ j ∈ s, ‖z j‖ = 1)
    (i : J) (hi : i ∈ s) (hne : z i ≠ 1) :
    2 ≤ ((∏ j ∈ s, p j : ℕ) : ℝ) * ‖(∏ j ∈ s, z j) - 1‖ := by
  apply root_separation
  · rw [norm_prod]
    exact prod_eq_one hnorm
  · exact coprime_roots_nontrivial s p z hcop hz i hi hne
  · exact prod_pos hpos
  · apply prod_roots_pow s p z hz
    exact fun j hj => dvd_prod_of_mem p hj

end CoprimeRoots
end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset

lemma norm_sub_one_sq_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
  have hh : z.re * z.re + z.im * z.im = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hz
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    simpa only [one_pow] using h
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

lemma character_multiplier_four {R : Type*} [AddCommGroup R] [Finite R]
    (ψ : AddChar R ℂ) (a : R) : ‖ψ a - 1‖ ^ 2 ≤ 4 := by
  have hb : ‖ψ a - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖ψ a‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [ψ.norm_apply, norm_one]; norm_num
  nlinarith [norm_nonneg (ψ a - 1)]

lemma average_character_multiplier {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) :
    (∑ x : R, ‖ψ (a * x) - 1‖ ^ 2) / (Fintype.card R : ℝ) =
      if a = 0 then 0 else 2 := by
  by_cases ha : a = 0
  · simp [ha]
  have hs : ∑ x : R, ψ (a * x) = 0 := by
    simpa only [ha, ite_false, Nat.cast_zero, mul_comm] using AddChar.sum_mulShift a hψ
  have hr : ∑ x : R, (ψ (a * x)).re = 0 := by rw [← Complex.re_sum, hs]; rfl
  simp_rw [norm_sub_one_sq_of_norm_one _ (ψ.norm_apply _)]
  rw [sum_sub_distrib, ← mul_sum, hr, mul_zero, sub_zero]
  simp only [sum_const, card_univ, nsmul_eq_mul, ha, ite_false]
  field_simp

lemma std_character_pow (p : ℕ) [NeZero p] (a : ZMod p) :
    (ZMod.stdAddChar a) ^ p = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  simp

end EditFourier

namespace EditFourier
open scoped BigOperators
open Finset

section PrimeProduct
variable {J : Type*} [Fintype J] [DecidableEq J]
variable (p : J → ℕ) [∀ j, NeZero (p j)]

theorem multiplier_comparison
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (B : ℝ) (hB : 1 ≤ B) (hpB : ∀ j, (p j : ℝ) ≤ B)
    (h : ℕ) (hh : 0 < h) (lam : ∀ j, ZMod (p j)) (i : J) (u : ZMod (p i)) :
    ‖ZMod.stdAddChar (lam i * u) - 1‖ ^ 2 ≤
      B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 +
        (2 / (h : ℝ)) * ∑ j, (if lam j = 0 then (0 : ℝ) else 2) := by
  have hSim : 0 ≤ B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 := by positivity
  have hCoord : 0 ≤ (2 / (h : ℝ)) * ∑ j, (if lam j = 0 then (0 : ℝ) else 2) := by
    apply mul_nonneg (by positivity)
    apply sum_nonneg
    intro j _
    split_ifs <;> norm_num
  by_cases hi : lam i = 0
  · simpa only [hi, zero_mul, AddChar.map_zero_eq_one, sub_self, norm_zero, zero_pow
      (by omega : 2 ≠ 0)] using add_nonneg hSim hCoord
  have hleft := character_multiplier_four (ZMod.stdAddChar (N := p i)) (lam i * u)
  let s : Finset J := univ.filter (fun j => lam j ≠ 0)
  have his : i ∈ s := by simp [s, hi]
  by_cases hs : s.card < h
  · have hroot := coprime_root_separation s p (fun j => ZMod.stdAddChar (lam j))
      (fun j _ => NeZero.pos (p j))
      (fun _ _ _ _ hij => hcop hij)
      (fun j _ => std_character_pow (p j) (lam j))
      (fun j _ => (ZMod.stdAddChar (N := p j)).norm_apply (lam j)) i his
      (by
        intro heq
        apply hi
        exact ZMod.injective_stdAddChar (heq.trans (AddChar.map_zero_eq_one _).symm))
    have heq : (∏ j ∈ s, ZMod.stdAddChar (lam j)) = torusCharacter p lam := by
      change (∏ j ∈ s, ZMod.stdAddChar (lam j)) = ∏ j, ZMod.stdAddChar (lam j)
      apply prod_subset (filter_subset _ _)
      intro j _ hj
      have hjz : lam j = 0 := by simpa [s] using hj
      simp [hjz]
    rw [heq] at hroot
    have hprod : ((∏ j ∈ s, p j : ℕ) : ℝ) ≤ B ^ h := by
      calc
        _ = ∏ j ∈ s, (p j : ℝ) := by norm_cast
        _ ≤ ∏ _j ∈ s, B := prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun j _ => hpB j)
        _ = B ^ s.card := by rw [prod_const]
        _ ≤ B ^ h := pow_le_pow_right₀ hB hs.le
    have htwo : 2 ≤ B ^ h * ‖torusCharacter p lam - 1‖ :=
      hroot.trans (mul_le_mul_of_nonneg_right hprod (norm_nonneg _))
    have hfour : 4 ≤ B ^ (2 * h) * ‖torusCharacter p lam - 1‖ ^ 2 := by
      have hsq : 4 ≤ (B ^ h * ‖torusCharacter p lam - 1‖) ^ 2 := by nlinarith
      simpa only [mul_pow, ← pow_mul, Nat.mul_comm h 2] using hsq
    linarith
  · have hcard : (h : ℝ) ≤ s.card := by exact_mod_cast Nat.le_of_not_gt hs
    have hsum : (∑ j, (if lam j = 0 then (0 : ℝ) else 2)) = (s.card : ℝ) * 2 := by
      calc
        _ = ∑ _j ∈ s, (2 : ℝ) := by simp only [s, sum_filter, ite_not]
        _ = _ := by simp
    rw [hsum]
    have hfour : 4 ≤ 2 / (h : ℝ) * ((s.card : ℝ) * 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (Nat.cast_pos.mpr hh)]
      linarith
    linarith

end PrimeProduct
end EditFourier

end OAI
