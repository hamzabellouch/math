import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Jacobsthal.Primes.PrimeProductOmissions

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.AffinePrimeSieve

open _root_.Finset
open NumberTheoryLean IntervalBoundingSieve SubsetPrimeSieve PrimeProductOmissions

noncomputable def value (a : ℤ) (q i : ℕ) : ℤ := a + (q:ℤ)*i
noncomputable def survivors (N : ℕ) (a : ℤ) (q : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (range N).filter (fun i => ∀ p ∈ P, ¬Int.ModEq (p:ℤ) (value a q i) 0)
noncomputable def primeIndices (N : ℕ) (a : ℤ) (q : ℕ) : Finset ℕ :=
  (range N).filter (fun i => (value a q i).natAbs.Prime ∧ 0 ≤ value a q i)
noncomputable def smallPrimeIndices (N : ℕ) (a : ℤ) (q : ℕ) (u : ℝ) : Finset ℕ :=
  (primeIndices N a q).filter (fun i => ((value a q i).natAbs : ℝ) ≤ u)

theorem exists_coordinate_residues (N : ℕ) (a : ℤ) (q : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, q.Coprime p) :
    ∃ r : ℕ → ℕ, survivors N a q P = residueAvoidingOffsets N (∏ p ∈ P, p) r := by
  classical
  have hc : ∀ p : ℕ, ∃ r : ℕ, p ∈ P → ∀ i : ℕ,
      Int.ModEq (p:ℤ) (value a q i) 0 ↔ Nat.ModEq p i r := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨r,hr⟩ := ProgressionSmallSieve.exists_integer_affine_residue a q 0 (hP p hp) (hcop p hp)
      exact ⟨r,fun _ i => hr i⟩
    · exact ⟨0,fun h => (hp h).elim⟩
  choose r hr using hc
  refine ⟨r,?_⟩
  ext i
  simp only [survivors,residueAvoidingOffsets,mem_filter,Nat.primeFactors_prod hP]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro p hp
  exact not_congr (hr p hp i)

theorem affine_sieve_error (N : ℕ) (a : ℤ) (q : ℕ) (u s J : ℝ) (P : Finset ℕ)
    (hu : 2 ≤ u) (hs : 480024 ≤ s) (hJ : 0 ≤ J) (hNJ : |(N:ℝ)-J| ≤ 1)
    (hP : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p:ℝ) ≤ u)
    (hcop : ∀ p ∈ P, q.Coprime p) :
    |((survivors N a q P).card : ℝ) - J*euler P| ≤
      J*euler P*Real.exp (-s/96) + 2*u^s := by
  obtain ⟨r,hr⟩ := exists_coordinate_residues N a q P hP hcop
  rw [hr]
  exact finite_subset_sieve_bound N u s J P r hu hs hJ hNJ hP hsize

lemma natAbs_cast_of_nonneg {x : ℤ} (hx : 0 ≤ x) : (x.natAbs : ℤ) = x := by
  simpa only [abs_of_nonneg hx] using Int.natCast_natAbs x

theorem prime_above_survives (N : ℕ) (a : ℤ) (q : ℕ) (u : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p:ℝ) ≤ u)
    {i : ℕ} (hi : i ∈ primeIndices N a q) (hbig : u < ((value a q i).natAbs : ℝ)) :
    i ∈ survivors N a q P := by
  obtain ⟨hiN,hprime,hpos⟩ := mem_filter.mp hi
  refine mem_filter.mpr ⟨hiN,?_⟩
  intro p hp hmod
  have hd : (p:ℤ) ∣ value a q i := Int.modEq_zero_iff_dvd.mp hmod
  rw [← natAbs_cast_of_nonneg hpos] at hd
  have hdN : p ∣ (value a q i).natAbs := Int.natCast_dvd_natCast.mp hd
  have heq : p = (value a q i).natAbs := ((hprime.dvd_iff_eq (hP p hp).ne_one).mp hdN).symm
  have hle := hsize p hp
  rw [heq] at hle
  exact (not_lt_of_ge hle) hbig

theorem value_injective (a : ℤ) {q : ℕ} (hq : 0 < q) : Function.Injective (value a q) := by
  intro m n h
  have hq0 : (q:ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have he : (m:ℤ)=(n:ℤ) := mul_left_cancel₀ hq0 (add_left_cancel h)
  exact_mod_cast he

theorem small_prime_count_le (N : ℕ) (a : ℤ) (q : ℕ) (u : ℝ) (hq : 0 < q) (hu : 0 ≤ u) :
    ((smallPrimeIndices N a q u).card : ℝ) ≤ u := by
  classical
  let S := smallPrimeIndices N a q u
  let f := fun i : ℕ => (value a q i).natAbs
  have hinj : Set.InjOn f S := by
    intro m hm n hn hmn
    have hmpos := ((mem_filter.mp (mem_filter.mp hm).1).2).2
    have hnpos := ((mem_filter.mp (mem_filter.mp hn).1).2).2
    apply value_injective a hq
    rw [← natAbs_cast_of_nonneg hmpos,← natAbs_cast_of_nonneg hnpos]
    exact congrArg (fun v : ℕ => (v:ℤ)) hmn
  have hsub : S.image f ⊆ Icc 1 ⌊u⌋₊ := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    obtain ⟨hip,hsmall⟩ := mem_filter.mp hi
    have hprime := (mem_filter.mp hip).2.1
    exact mem_Icc.mpr ⟨hprime.pos,(Nat.le_floor_iff hu).mpr hsmall⟩
  have hc : S.card ≤ ⌊u⌋₊ := by
    calc
      _ = (S.image f).card := (card_image_iff.mpr hinj).symm
      _ ≤ (Icc 1 ⌊u⌋₊).card := card_le_card hsub
      _ = ⌊u⌋₊ := by simp
  exact (show (S.card:ℝ) ≤ (⌊u⌋₊:ℝ) by exact_mod_cast hc).trans (Nat.floor_le hu)

theorem prime_count_le_sifted_add (N : ℕ) (a : ℤ) (q : ℕ) (u : ℝ) (P : Finset ℕ)
    (hq : 0 < q) (hu : 0 ≤ u) (hP : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p:ℝ) ≤ u) :
    ((primeIndices N a q).card : ℝ) ≤ ((survivors N a q P).card : ℝ) + u := by
  classical
  have hsub : primeIndices N a q ⊆ survivors N a q P ∪ smallPrimeIndices N a q u := by
    intro i hi
    by_cases hsmall : ((value a q i).natAbs : ℝ) ≤ u
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hi,hsmall⟩))
    · exact mem_union.mpr (Or.inl (prime_above_survives N a q u P hP hsize hi (lt_of_not_ge hsmall)))
  have hc : (primeIndices N a q).card ≤ (survivors N a q P).card + (smallPrimeIndices N a q u).card :=
    (card_le_card hsub).trans (card_union_le _ _)
  calc
    _ ≤ ((survivors N a q P).card:ℝ) + ((smallPrimeIndices N a q u).card:ℝ) := by exact_mod_cast hc
    _ ≤ _ := add_le_add le_rfl (small_prime_count_le N a q u hq hu)

end ErdosPrimeInputs.AffinePrimeSieve

end

section

namespace ErdosPrimeInputs.SieveScale

open _root_.Filter
open scoped Topology

noncomputable def level : ℝ := 480024
noncomputable def exponent : ℝ := 1 / (2*level)
noncomputable def cutoff (J : ℝ) : ℝ := J ^ exponent

lemma exponent_pos : 0 < exponent := by norm_num [exponent,level]
lemma exponent_le_half : exponent ≤ 1/2 := by norm_num [exponent,level]

lemma cutoff_tendsto : Tendsto cutoff atTop atTop := tendsto_rpow_atTop exponent_pos

lemma cutoff_eventually_ge (u₀ : ℝ) : ∃ J₀ : ℝ, 1 < J₀ ∧ ∀ J : ℝ, J₀ ≤ J → u₀ ≤ cutoff J := by
  obtain ⟨b,hb⟩ := eventually_atTop.mp (cutoff_tendsto.eventually (eventually_ge_atTop u₀))
  refine ⟨max 2 b,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro J hJ
  exact hb J ((le_max_right _ _).trans hJ)

lemma cutoff_power {J : ℝ} (hJ : 0 ≤ J) : cutoff J ^ level = Real.sqrt J := by
  rw [cutoff,← Real.rpow_mul hJ]
  have h : exponent * level = 1/2 := by norm_num [exponent,level]
  rw [h,Real.sqrt_eq_rpow]

lemma log_cutoff {J : ℝ} (hJ : 0 < J) : Real.log (cutoff J) = exponent * Real.log J :=
  Real.log_rpow hJ exponent

lemma cutoff_le_sqrt {J : ℝ} (hJ : 1 ≤ J) : cutoff J ≤ Real.sqrt J := by
  rw [cutoff,Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hJ exponent_le_half

lemma sqrt_le_log_scale {J : ℝ} (hJ : 1 < J) : Real.sqrt J ≤ 2*J/Real.log J := by
  have hJ0 : 0 < J := by linarith
  have hl0 := Real.log_pos hJ
  have hs0 := Real.sqrt_pos.mpr hJ0
  have hs2 := Real.sq_sqrt hJ0.le
  have hlog : Real.log J ≤ 2 * Real.sqrt J := by
    have h := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt hJ0.le] at h
    linarith
  apply (le_div_iff₀ hl0).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog hs0.le]

end ErdosPrimeInputs.SieveScale

end

end Erdos970

end OAI
