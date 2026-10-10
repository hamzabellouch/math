import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorFamilies
import OAI.Combinatorics.MatchingPSD.TypeProbabilities

namespace OAI

/-!
# Survival under balanced labeled partitions

The three category profiles in the survival proof are as balanced as possible.
Their multinomial coefficients are therefore maximal, giving bounds on the
number of prescribed labeled partitions.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Counts differ by at most one across all labeled blocks. -/
def BalancedProfile (t : K → ℕ) : Prop := ∀ i j, t i ≤ t j + 1

private theorem poisson_mass_at_adjacent_mode (q j t : ℕ) (ht : t = q ∨ t = q + 1) :
    ((q + 1 : ℕ) : ℝ) ^ j / j.factorial ≤
      ((q + 1 : ℕ) : ℝ) ^ t / t.factorial := by
  have h := MatchingSmoothing.poisson_mass_le_integer_mode (q + 1) j
  rcases ht with rfl | rfl
  · convert h using 1
    push_cast
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  · exact h

omit [DecidableEq K] in
theorem balanced_multinomial_max [Nonempty K] (t k : K → ℕ)
    (ht : BalancedProfile t) (hsum : ∑ i, k i = ∑ i, t i) :
    Nat.multinomial Finset.univ k ≤ Nat.multinomial Finset.univ t := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ t Finset.univ_nonempty
  have hnear (i : K) : t i = t j ∨ t i = t j + 1 := by
    have hl := hj i (Finset.mem_univ i)
    have hu := ht i j
    omega
  have hmass := Finset.prod_le_prod₀
    (fun i (_ : i ∈ (Finset.univ : Finset K)) =>
      by positivity : ∀ i ∈ (Finset.univ : Finset K),
        0 ≤ (((t j + 1 : ℕ) : ℝ) ^ k i / (k i).factorial))
    (fun i (_ : i ∈ (Finset.univ : Finset K)) =>
      poisson_mass_at_adjacent_mode (t j) (k i) (t i) (hnear i))
  have hprod := mul_le_mul_of_nonneg_left hmass
    (by positivity : (0 : ℝ) ≤ (∑ i, t i).factorial)
  have hk := MatchingSmoothing.multinomial_term_eq Finset.univ k
    (fun _ => ((t j + 1 : ℕ) : ℝ))
  have ht' := MatchingSmoothing.multinomial_term_eq Finset.univ t
    (fun _ => ((t j + 1 : ℕ) : ℝ))
  rw [hsum] at hk
  rw [← hk, ← ht', Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, hsum] at hprod
  have hp : 0 < (((t j + 1 : ℕ) : ℝ) ^ (∑ i, t i)) := by positivity
  exact_mod_cast (mul_le_mul_iff_left₀ hp).mp hprod

/-- A balanced profile receives at least the average multinomial mass.
There are at most `(n+1)^|K|` profiles. -/
theorem balanced_multinomial_lower [Nonempty K] (t : K → ℕ) (n : ℕ)
    (ht : BalancedProfile t) (hsum : ∑ i, t i = n) :
    (Fintype.card K : ℝ) ^ n ≤ (n + 1 : ℝ) ^ Fintype.card K *
      Nat.multinomial Finset.univ t := by
  classical
  have heq : (Fintype.card K : ℝ) ^ n =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset K) n,
        (Nat.multinomial Finset.univ k : ℝ) := by
    simpa using Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset K)
      (fun _ : K => (1 : ℝ)) n
  rw [heq]
  calc
    _ ≤ ∑ _k ∈ Finset.piAntidiag (Finset.univ : Finset K) n,
        (Nat.multinomial Finset.univ t : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      exact_mod_cast balanced_multinomial_max t k ht
        ((Finset.mem_piAntidiag.mp hk).1.trans hsum.symm)
    _ = ((Finset.piAntidiag (Finset.univ : Finset K) n).card : ℝ) *
        Nat.multinomial Finset.univ t := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast MatchingSmoothing.card_piAntidiag_univ_le (ι := K) n)
      (Nat.cast_nonneg _)

private def sigma_fst_fiber_equiv (t : K → ℕ) (i : K) :
    {x : (Σ j, Fin (t j)) // x.1 = i} ≃ Fin (t i) where
  toFun x := x.2 ▸ x.1.2
  invFun x := ⟨⟨i, x⟩, rfl⟩
  left_inv := by rintro ⟨⟨j, x⟩, h⟩; dsimp at h; subst j; rfl
  right_inv := by intro x; rfl

theorem exists_coloring_of_sum (A : Type*) [Fintype A] (t : K → ℕ)
    (ht : ∑ i, t i = Fintype.card A) :
    ∃ f : A → K, MatchingSmoothing.histogram f = t := by
  classical
  let e : A ≃ (Σ i, Fin (t i)) := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using ht.symm)
  refine ⟨fun a => (e a).1, ?_⟩
  funext i
  unfold MatchingSmoothing.histogram
  let e' : {a : A // (e a).1 = i} ≃ {x : (Σ j, Fin (t j)) // x.1 = i} :=
    e.subtypeEquivOfSubtype (p := fun x : (Σ j, Fin (t j)) => x.1 = i)
  exact (Fintype.card_congr (e'.trans (sigma_fst_fiber_equiv t i))).trans
    (Fintype.card_fin (t i))

theorem card_colorings_of_sum (A : Type*) [Fintype A] (t : K → ℕ)
    (ht : ∑ i, t i = Fintype.card A) :
    Fintype.card (MatchingSmoothing.Colorings A K t) = Nat.multinomial Finset.univ t := by
  obtain ⟨f, hf⟩ := exists_coloring_of_sum A t ht
  rw [← hf]
  exact MatchingSmoothing.card_colorings_eq_multinomial f

/-- The domain is the disjoint union of the three categories in the paper. -/
abbrev CategoryDomain (C : Fin 3 → Type*) := Σ a, C a

abbrev PrescribedLabelings (C : Fin 3 → Type*) [∀ a, Fintype (C a)] (q : Fin 3 → K → ℕ) :=
  {f : CategoryDomain C → K // ∀ a,
    MatchingSmoothing.histogram (fun x : C a => f ⟨a, x⟩) = q a}

noncomputable instance prescribedLabelingsFintype (C : Fin 3 → Type*)
    [∀ a, Fintype (C a)] (q : Fin 3 → K → ℕ) : Fintype (PrescribedLabelings C q) :=
  Fintype.ofFinite _

theorem card_prescribedLabelings (C : Fin 3 → Type*) [∀ a, Fintype (C a)]
    (q : Fin 3 → K → ℕ) (hrows : ∀ a, ∑ i, q a i = Fintype.card (C a)) :
    Fintype.card (PrescribedLabelings C q) = ∏ a, Nat.multinomial Finset.univ (q a) := by
  classical
  let e : PrescribedLabelings C q ≃
      ((a : Fin 3) → MatchingSmoothing.Colorings (C a) K (q a)) :=
    { toFun := fun f a => ⟨fun x => f.1 ⟨a, x⟩, f.2 a⟩
      invFun := fun f => ⟨fun x => (f x.1).1 x.2, fun a => (f a).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_pi]
  exact Finset.prod_congr rfl (fun a _ => card_colorings_of_sum (C a) (q a) (hrows a))

omit [Fintype K] in
theorem histogram_categoryDomain (C : Fin 3 → Type*) [∀ a, Fintype (C a)]
    (f : CategoryDomain C → K) (i : K) :
    MatchingSmoothing.histogram f i =
      ∑ a, MatchingSmoothing.histogram (fun x : C a => f ⟨a, x⟩) i := by
  classical
  let e : {x : CategoryDomain C // f x = i} ≃ (Σ a, {x : C a // f ⟨a, x⟩ = i}) :=
    { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold MatchingSmoothing.histogram
  exact (Fintype.card_congr e).trans Fintype.card_sigma

omit [Fintype K] in
theorem prescribedLabelings_fill_blocks (C : Fin 3 → Type*) [∀ a, Fintype (C a)]
    (q : Fin 3 → K → ℕ) (b : ℕ) (hcols : ∀ i, ∑ a, q a i = b)
    (f : PrescribedLabelings C q) : MatchingSmoothing.histogram f.val = fun _ => b := by
  funext i
  rw [histogram_categoryDomain]
  simp_rw [f.property]
  exact hcols i

/-- Exact favorable/total counting formula, before applying the balanced bounds. -/
theorem prescribed_partition_probability_eq
    (C : Fin 3 → Type*) [∀ a, Fintype (C a)] (q : Fin 3 → K → ℕ) (b : ℕ)
    (hrows : ∀ a, ∑ i, q a i = Fintype.card (C a))
    (hcols : ∀ i, ∑ a, q a i = b) :
    finiteUniformProbability
        (fun f : MatchingSmoothing.Colorings (CategoryDomain C) K (fun _ => b) =>
          ∀ a, MatchingSmoothing.histogram (fun x : C a => f.val ⟨a, x⟩) = q a) =
      (∏ a, (Nat.multinomial Finset.univ (q a) : ℝ)) /
        Nat.multinomial (Finset.univ : Finset K) (fun _ => b) := by
  classical
  let Part := MatchingSmoothing.Colorings (CategoryDomain C) K (fun _ => b)
  let P : Part → Prop := fun f =>
    ∀ a, MatchingSmoothing.histogram (fun x : C a => f.val ⟨a, x⟩) = q a
  let : DecidablePred P := fun _ => Classical.propDecidable _
  let e : {f : Part // P f} ≃ PrescribedLabelings C q :=
    { toFun := fun f => ⟨f.1.1, f.2⟩
      invFun := fun f => ⟨⟨f.1, prescribedLabelings_fill_blocks C q b hcols f⟩, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hgood : Fintype.card {f : Part // P f} = Fintype.card (PrescribedLabelings C q) :=
    Fintype.card_congr e
  have hsum : ∑ i : K, b = Fintype.card (CategoryDomain C) := by
    calc
      _ = ∑ i, ∑ a, q a i := Finset.sum_congr rfl (fun i _ => (hcols i).symm)
      _ = ∑ a, ∑ i, q a i := Finset.sum_comm
      _ = _ := by simp only [hrows, Fintype.card_sigma]
  have hpart : Fintype.card Part = Nat.multinomial Finset.univ (fun _ : K => b) :=
    card_colorings_of_sum (CategoryDomain C) (fun _ => b) hsum
  change finiteUniformProbability P = _
  unfold finiteUniformProbability
  rw [hgood, card_prescribedLabelings C q hrows, hpart, Nat.cast_prod]

theorem balanced_category_count_lower [Nonempty K]
    (C : Fin 3 → Type*) [∀ a, Fintype (C a)] (q : Fin 3 → K → ℕ)
    (hrows : ∀ a, ∑ i, q a i = Fintype.card (C a)) (hbal : ∀ a, BalancedProfile (q a)) :
    (Fintype.card K : ℝ) ^ Fintype.card (CategoryDomain C) ≤
      (Fintype.card (CategoryDomain C) + 1 : ℝ) ^ (3 * Fintype.card K) *
        Fintype.card (PrescribedLabelings C q) := by
  classical
  have hsize (a : Fin 3) : Fintype.card (C a) ≤ Fintype.card (CategoryDomain C) := by
    rw [Fintype.card_sigma]
    exact Finset.single_le_sum (f := fun a : Fin 3 => Fintype.card (C a))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hrow (a : Fin 3) : (Fintype.card K : ℝ) ^ Fintype.card (C a) ≤
      (Fintype.card (CategoryDomain C) + 1 : ℝ) ^ Fintype.card K *
        Nat.multinomial Finset.univ (q a) := by
    apply (balanced_multinomial_lower (q a) _ (hbal a) (hrows a)).trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right (hsize a) 1
  have hprod := Finset.prod_le_prod₀
    (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
      by positivity : ∀ a ∈ (Finset.univ : Finset (Fin 3)),
        0 ≤ (Fintype.card K : ℝ) ^ Fintype.card (C a))
    (fun a _ => hrow a)
  rw [Finset.prod_pow_eq_pow_sum, ← Fintype.card_sigma] at hprod
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  rw [← pow_mul, Nat.mul_comm] at hprod
  rw [card_prescribedLabelings C q hrows, Nat.cast_prod]
  exact hprod

/-- Uniform labeled equal-size partitions preserve all three balanced
category prescriptions with the paper's inverse-polynomial probability. -/
theorem balanced_partition_probability [Nonempty K]
    (C : Fin 3 → Type*) [∀ a, Fintype (C a)] (q : Fin 3 → K → ℕ) (b : ℕ)
    (hrows : ∀ a, ∑ i, q a i = Fintype.card (C a))
    (hcols : ∀ i, ∑ a, q a i = b) (hbal : ∀ a, BalancedProfile (q a)) :
    1 / (Fintype.card (CategoryDomain C) + 1 : ℝ) ^ (3 * Fintype.card K) ≤
      finiteUniformProbability
        (fun f : MatchingSmoothing.Colorings (CategoryDomain C) K (fun _ => b) =>
          ∀ a, MatchingSmoothing.histogram (fun x : C a => f.val ⟨a, x⟩) = q a) := by
  classical
  let Part := MatchingSmoothing.Colorings (CategoryDomain C) K (fun _ => b)
  let P : Part → Prop := fun f =>
    ∀ a, MatchingSmoothing.histogram (fun x : C a => f.val ⟨a, x⟩) = q a
  let : DecidablePred P := fun _ => Classical.propDecidable _
  let e : {f : Part // P f} ≃ PrescribedLabelings C q :=
    { toFun := fun f => ⟨f.1.1, f.2⟩
      invFun := fun f => ⟨⟨f.1, prescribedLabelings_fill_blocks C q b hcols f⟩, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hgood : Fintype.card {f : Part // P f} = Fintype.card (PrescribedLabelings C q) :=
    Fintype.card_congr e
  have hpos : 0 < Fintype.card (PrescribedLabelings C q) := by
    rw [card_prescribedLabelings C q hrows]
    exact Finset.prod_pos (fun _ _ => Nat.multinomial_pos _ _)
  have hle : Fintype.card (PrescribedLabelings C q) ≤ Fintype.card Part := by
    rw [← hgood]
    exact Fintype.card_subtype_le P
  have hden : (0 : ℝ) < Fintype.card Part := by exact_mod_cast lt_of_lt_of_le hpos hle
  have hall : (Fintype.card Part : ℝ) ≤
      (Fintype.card K : ℝ) ^ Fintype.card (CategoryDomain C) := by
    have h := Fintype.card_subtype_le
      (fun f : CategoryDomain C → K => MatchingSmoothing.histogram f = fun _ => b)
    rw [Fintype.card_fun] at h
    exact_mod_cast h
  have hbound := hall.trans (balanced_category_count_lower C q hrows hbal)
  change 1 / _ ≤ finiteUniformProbability P
  unfold finiteUniformProbability
  apply (div_le_div_iff₀ (by positivity) hden).mpr
  rw [one_mul]
  rw [hgood]
  simpa only [mul_comm] using hbound

/-- The only two arities used by the algorithm: top blocks (`l=4`) and
local blocks (`l=2`). -/
theorem balanced_partition_probability_two_or_four (l b : ℕ) (hl : l = 2 ∨ l = 4)
    (C : Fin 3 → Type*) [∀ a, Fintype (C a)] (q : Fin 3 → Fin l → ℕ)
    (hrows : ∀ a, ∑ i, q a i = Fintype.card (C a))
    (hcols : ∀ i, ∑ a, q a i = b) (hbal : ∀ a, BalancedProfile (q a)) :
    1 / (Fintype.card (CategoryDomain C) + 1 : ℝ) ^ (3 * l) ≤
      finiteUniformProbability
        (fun f : MatchingSmoothing.Colorings (CategoryDomain C) (Fin l) (fun _ => b) =>
          ∀ a, MatchingSmoothing.histogram (fun x : C a => f.val ⟨a, x⟩) = q a) := by
  have : Nonempty (Fin l) := ⟨⟨0, by omega⟩⟩
  simpa only [Fintype.card_fin] using balanced_partition_probability C q b hrows hcols hbal

/-- A bounded surviving fraction has a polynomially likely substantial value. -/
theorem surviving_fraction_probability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) {p : ℝ} (_hZ0 : ∀ ω, 0 ≤ Z ω) (hZ1 : ∀ ω, Z ω ≤ 1)
    (hp : p ≤ (∑ ω, Z ω) / Fintype.card Ω) :
    p / 2 ≤ finiteUniformProbability (fun ω => p / 2 ≤ Z ω) := by
  classical
  by_cases hp0 : p ≤ 0
  · exact (by linarith : p / 2 ≤ 0).trans (finiteUniformProbability_nonneg _)
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hpoint (ω : Ω) : Z ω ≤ p / 2 + if p / 2 ≤ Z ω then (1 : ℝ) else 0 := by
    split_ifs with h
    · linarith [hZ1 ω]
    · linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hevent : (∑ ω, if p / 2 ≤ Z ω then (1 : ℝ) else 0) =
      (Fintype.card {ω // p / 2 ≤ Z ω} : ℝ) := by
    rw [Fintype.card_subtype]
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hevent] at hsum
  unfold finiteUniformProbability
  apply (le_div_iff₀ hcard).mpr
  have hmean := (le_div_iff₀ hcard).mp hp
  nlinarith

theorem finiteUniformProbability_eq_indicator_mean {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] : finiteUniformProbability P =
      (∑ ω, if P ω then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  unfold finiteUniformProbability
  congr 1
  rw [Fintype.card_subtype]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Pointwise survival gives a likely partition retaining at least half the
expected fraction of an arbitrary finite representative family. -/
theorem surviving_representative_family {Ω R : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype R] [Nonempty R]
    (keeps : Ω → R → Prop) {p : ℝ}
    (hp : ∀ r, p ≤ finiteUniformProbability (fun ω => keeps ω r)) :
    p / 2 ≤ finiteUniformProbability
      (fun ω => p / 2 ≤ finiteUniformProbability (keeps ω)) := by
  classical
  apply surviving_fraction_probability (fun ω => finiteUniformProbability (keeps ω))
    (fun ω => finiteUniformProbability_nonneg (keeps ω))
    (fun ω => finiteUniformProbability_le_one (keeps ω))
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hp r)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have havg : p ≤ (∑ r, finiteUniformProbability (fun ω => keeps ω r)) /
      Fintype.card R := (le_div_iff₀ hcard).mpr (by simpa only [mul_comm] using hsum)
  convert havg using 1
  simp_rw [finiteUniformProbability_eq_indicator_mean]
  rw [← Finset.sum_div, ← Finset.sum_div, div_div, div_div, Finset.sum_comm, mul_comm]

end LowSpaceSubsetSum

end OAI
