import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.FundamentalBlockEstimate
import OAI.NumberTheory.Jacobsthal.Sieve.RealCoprimeResidueCount

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem prime_residue_choices_card (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    [NeZero (∏ p ∈ P,p)] (E : ∀ p : ℕ,Finset (ZMod p)) :
    (Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) => ∀ p ∈ P,(r.val : ZMod p) ∈ E p)).card =
      ∏ p ∈ P,(E p).card := by
  have hcop : Pairwise (fun i j : P => Nat.Coprime i.val j.val) := by
    intro i j hij
    exact (Nat.coprime_primes (hP i i.property) (hP j j.property)).mpr
      (fun he => hij (Subtype.ext he))
  have he : (∏ i : P,(i : ℕ)) = ∏ p ∈ P,p := Finset.prod_coe_sort P (fun p => p)
  let : NeZero (∏ i : P,(i : ℕ)) := ⟨by rw [he];exact NeZero.ne _⟩
  have hc := literal_residue_choices_card (fun i : P => (i : ℕ)) hcop (fun i => E i)
  have hn := (canonical_filter_card (∏ i : P,(i : ℕ))
    (fun n => ∀ i : P,(n : ZMod i.val) ∈ E i.val)).symm.trans hc
  calc
    _ = ((Finset.range (∏ p ∈ P,p)).filter (fun n => ∀ p ∈ P,(n : ZMod p) ∈ E p)).card :=
      canonical_filter_card _ _
    _ = _ := by
      simpa only [he,Finset.prod_coe_sort P (fun p => (E p).card),Subtype.forall] using hn

theorem prime_unit_avoidance_card (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    [NeZero (∏ p ∈ P,p)] (u : ∀ p : ℕ,(ZMod p)ˣ) (c : ∀ p : ℕ,ZMod p) :
    (Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) =>
      ∀ p ∈ P,∀ j ∈ S,(r.val : ZMod p)+(u p : ZMod p)*(j : ZMod p) ≠ c p)).card =
      ∏ p ∈ P,(p-(positionResidues S p).card) := by
  let E (p : ℕ) : Finset (ZMod p) :=
    if hp : p = 0 then ∅ else @allowedClasses S p ⟨hp⟩ (u p) (c p)
  have hmem (p : ℕ) (hp : p ∈ P) (x : ZMod p) :
      x ∈ E p ↔ ∀ j ∈ S,x+(u p : ZMod p)*(j : ZMod p) ≠ c p := by
    have hn := (hP p hp).ne_zero
    let : NeZero p := ⟨hn⟩
    simp only [E,dite_eq_right hn,mem_allowedClasses]
  have hcard (p : ℕ) (hp : p ∈ P) : (E p).card = p-(positionResidues S p).card := by
    have hn := (hP p hp).ne_zero
    let : NeZero p := ⟨hn⟩
    simp only [E,dite_eq_right hn,allowedClasses_card]
  have hf : Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) =>
      ∀ p ∈ P,∀ j ∈ S,(r.val : ZMod p)+(u p : ZMod p)*(j : ZMod p) ≠ c p) =
      Finset.univ.filter (fun r : ZMod (∏ p ∈ P,p) => ∀ p ∈ P,(r.val : ZMod p) ∈ E p) := by
    apply Finset.filter_congr
    intro r _hr
    exact forall_congr' (fun p => forall_congr' (fun hp => (hmem p hp _).symm))
  rw [hf,prime_residue_choices_card P hP E]
  exact Finset.prod_congr rfl hcard

theorem product_allowed_eq_density (P S : Finset ℕ) (hP : ∀ p ∈ P,p.Prime) :
    ((∏ p ∈ P,(p-(positionResidues S p).card) : ℕ) : ℝ) =
      ((∏ p ∈ P,p : ℕ) : ℝ)*jointDensity P S := by
  rw [Nat.cast_prod,Nat.cast_prod,jointDensity,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  let : NeZero p := ⟨(hP p hp).ne_zero⟩
  have hle := positionResidues_le_modulus S p
  rw [Nat.cast_sub hle,positionDensity]
  have hn : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def primeResidueSet (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (E : ∀ p : ℕ,Finset (ZMod p)) : Finset (ZMod (∏ p ∈ P,p)) := by
  letI : NeZero (∏ p ∈ P,p) := ⟨(Finset.prod_pos (fun p hp => (hP p hp).pos)).ne'⟩
  exact Finset.univ.filter (fun r => ∀ p ∈ P,(r.val : ZMod p) ∈ E p)

theorem primeResidueSet_card (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (E : ∀ p : ℕ,Finset (ZMod p)) :
    (primeResidueSet P hP E).card = ∏ p ∈ P,(E p).card := by
  let : NeZero (∏ p ∈ P,p) := ⟨(Finset.prod_pos (fun p hp => (hP p hp).pos)).ne'⟩
  exact prime_residue_choices_card P hP E

theorem cast_int_residue (M t : ℕ) [NeZero M] (htM : t ∣ M) (n : ℤ) :
    (((n : ZMod M).val : ℕ) : ZMod t) = (n : ZMod t) := by
  have hh := congrArg (ZMod.castHom htM (ZMod t)) (ZMod.natCast_zmod_val (n : ZMod M))
  simpa only [map_natCast,map_intCast] using hh

theorem int_mem_primeResidueSet (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (E : ∀ p : ℕ,Finset (ZMod p)) (n : ℤ) :
    (n : ZMod (∏ p ∈ P,p)) ∈ primeResidueSet P hP E ↔ ∀ p ∈ P,(n : ZMod p) ∈ E p := by
  let : NeZero (∏ p ∈ P,p) := ⟨(Finset.prod_pos (fun p hp => (hP p hp).pos)).ne'⟩
  change ((n : ZMod (∏ p ∈ P,p)) ∈ Finset.univ.filter (fun r => ∀ p ∈ P,(r.val : ZMod p) ∈ E p)) ↔ _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact forall_congr' (fun p => forall_congr' (fun hp => by
    rw [cast_int_residue _ p (Finset.dvd_prod_of_mem _ hp) n]))

noncomputable def integerPrimeIntersection (H : ℕ) (P : Finset ℕ)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) : Finset ℤ :=
  (Finset.Ico ⌈b⌉ ⌈c⌉).filter (fun n => H.Coprime n.natAbs ∧ ∀ p ∈ P,(n : ZMod p) ∈ E p)

theorem integerPrimeIntersection_error (H : ℕ) (hH : 0 < H) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime) (hHP : ∀ p ∈ P,H.Coprime p)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) (hbc : b ≤ c) :
    |((integerPrimeIntersection H P E b c).card : ℝ)-
      (c-b)*((H.totient : ℝ)/(H : ℝ))*(∏ p ∈ P,((E p).card : ℝ)/(p : ℝ))| ≤
      2*(H.divisors.card : ℝ)*(∏ p ∈ P,((E p).card : ℝ)) := by
  have hL : 0 < ∏ p ∈ P,p := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hcop : H.Coprime (∏ p ∈ P,p) := Nat.coprime_prod_right_iff.mpr hHP
  have he : integerPrimeIntersection H P E b c =
      ErdosCoprimeResidueInterval.realCoprimeResidues H (∏ p ∈ P,p) (primeResidueSet P hP E) b c := by
    ext n
    simp only [integerPrimeIntersection,Finset.mem_filter,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil,
      ErdosCoprimeResidueInterval.mem_realCoprimeResidues,int_mem_primeResidueSet,and_assoc]
  rw [he]
  have hh := ErdosCoprimeResidueInterval.real_coprime_residue_count H _ hH hL hcop
    (primeResidueSet P hP E) b c hbc
  simpa only [primeResidueSet_card,Nat.cast_prod,Finset.prod_div_distrib] using hh

end ErdosVarianceMoments

end

section

namespace NumberTheoryLean.RealFundamentalSieve

open scoped BigOperators

noncomputable def levelDivisors (P : Finset ℕ) (v s : ℝ) : Finset ℕ := by
  classical
  exact (∏ p ∈ P, p).divisors.filter fun d => (d : ℝ) ≤ v ^ s

theorem floor_level_le (v s : ℝ) (hv : 1 ≤ v) (hs : 0 ≤ s) :
    (((⌊v⌋₊ ^ ⌊s⌋₊ : ℕ) : ℝ)) ≤ v ^ s := by
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  calc
    (⌊v⌋₊ : ℝ) ^ (⌊s⌋₊ : ℝ) ≤ v ^ (⌊s⌋₊ : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (Nat.cast_nonneg _)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hv (Nat.floor_le hs)

theorem fundamental_lemma {α : Type*} (C : Finset α) (weight : α → ℝ)
    (hweight : ∀ x ∈ C, 0 ≤ weight x) (hit : ℕ → α → Prop)
    (v s : ℝ) (P : Finset ℕ) (X : ℝ) (g : ℕ → ℝ)
    (hv : 2 ≤ v) (hs : 480024 ≤ s) (hX : 0 ≤ X)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p : ℝ) ≤ v)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hdim : ∀ p ∈ P, g p ≤ 2 / p)
    (htwo : 2 ∈ P → g 2 ≤ 1 / 2) :
    |(∑ x ∈ C, weight x * BonferroniBlocks.survives P (fun p => hit p x)) -
        X * (∏ p ∈ P, (1 - g p))| ≤
      X * (∏ p ∈ P, (1 - g p)) * Real.exp (-s / 96) +
        ∑ d ∈ levelDivisors P v s, |FundamentalBlockEstimate.integerRemainder C weight hit X g d| := by
  have hv0 : 0 ≤ v := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hV : 2 ≤ ⌊v⌋₊ := (Nat.le_floor_iff hv0).mpr (by exact_mod_cast hv)
  have hS : 240012 ≤ ⌊s⌋₊ := (Nat.le_floor_iff hs0).mpr (by norm_num; linarith)
  have hPsize : ∀ p ∈ P, p ≤ ⌊v⌋₊ := fun p hp => (Nat.le_floor_iff hv0).mpr (hsize p hp)
  have h := FundamentalBlockEstimate.fundamental_integer_parameter C weight hweight hit
    ⌊v⌋₊ ⌊s⌋₊ P X g hV hS hX hprime hPsize hg0 hdim htwo
  apply h.trans
  apply add_le_add
  · have hcap := BonferroniDensity.prime_density_le_two_thirds P g hprime hdim htwo
    have hEuler : 0 ≤ ∏ p ∈ P, (1 - g p) := Finset.prod_nonneg (fun p hp => by linarith [hcap p hp])
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hX hEuler)
    apply Real.exp_le_exp.mpr
    have hfloor := Nat.lt_floor_add_one s
    linarith
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdP, hdL⟩ := Finset.mem_filter.mp hd
      apply Finset.mem_filter.mpr
      refine ⟨hdP, ?_⟩
      have hdLReal : (d : ℝ) ≤ ((⌊v⌋₊ ^ ⌊s⌋₊ : ℕ) : ℝ) := by exact_mod_cast hdL
      exact hdLReal.trans (floor_level_le v s (by linarith) hs0)
    · intro d _ _
      exact abs_nonneg _

end NumberTheoryLean.RealFundamentalSieve

end

section

namespace ErdosVarianceMoments
open NumberTheoryLean
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def unitIntervalIntegers (H : ℕ) (b c : ℝ) : Finset ℤ :=
  (Finset.Ico ⌈b⌉ ⌈c⌉).filter (fun n => H.Coprime n.natAbs)

noncomputable def residueDensity (E : ∀ p : ℕ,Finset (ZMod p)) (p : ℕ) : ℝ :=
  ((E p).card : ℝ)/(p : ℝ)

theorem actual_intersection_mass (H : ℕ) (P : Finset ℕ)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) :
    BonferroniBlocks.intersectionMass (unitIntervalIntegers H b c) (fun _ => 1)
      (fun p n => (n : ZMod p) ∈ E p) P = (integerPrimeIntersection H P E b c).card := by
  have he : integerPrimeIntersection H P E b c =
      (unitIntervalIntegers H b c).filter (fun n => ∀ p ∈ P,(n : ZMod p) ∈ E p) := by
    ext n
    simp only [integerPrimeIntersection,unitIntervalIntegers,Finset.mem_filter,and_assoc]
  rw [he,Finset.card_filter,Nat.cast_sum]
  simp only [BonferroniBlocks.intersectionMass,BonferroniBlocks.intersectionValue,one_mul,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro n _hn
  split_ifs <;> rfl

theorem integerRemainder_bound (H : ℕ) (hH : 0 < H) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime) (hHP : ∀ p ∈ P,H.Coprime p)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) (hbc : b ≤ c)
    (d : ℕ) (hd : d ∣ ∏ p ∈ P,p) :
    |FundamentalBlockEstimate.integerRemainder (unitIntervalIntegers H b c) (fun _ => 1)
      (fun p n => (n : ZMod p) ∈ E p) ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E) d| ≤
      2*(H.divisors.card : ℝ)*(d : ℝ) := by
  have hsq : Squarefree (∏ p ∈ P,p) := IntervalBoundingSieve.squarefree_primeSet_product P hP
  have hdsq := hsq.squarefree_of_dvd hd
  have hsub : d.primeFactors ⊆ P := by
    rw [← Nat.primeFactors_prod hP]
    exact Nat.primeFactors_mono hd hsq.ne_zero
  have hprime (p : ℕ) (hp : p ∈ d.primeFactors) : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have herr := integerPrimeIntersection_error H hH d.primeFactors hprime
    (fun p hp => hHP p (hsub hp)) E b c hbc
  have hcard : (∏ p ∈ d.primeFactors,((E p).card : ℝ)) ≤ d := by
    calc
      _ ≤ ∏ p ∈ d.primeFactors,(p : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro p hp
        let : NeZero p := ⟨(hprime p hp).ne_zero⟩
        have hh := Finset.card_le_univ (E p)
        rw [ZMod.card] at hh
        exact_mod_cast hh
      _ = d := by rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hdsq]
  unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
  rw [actual_intersection_mass]
  exact herr.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

theorem remainder_sum_bound (H : ℕ) (hH : 0 < H) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime) (hHP : ∀ p ∈ P,H.Coprime p)
    (E : ∀ p : ℕ,Finset (ZMod p)) (b c : ℝ) (hbc : b ≤ c)
    (v s : ℝ) (hD : 1 ≤ v^s) :
    (∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
      |FundamentalBlockEstimate.integerRemainder (unitIntervalIntegers H b c) (fun _ => 1)
        (fun p n => (n : ZMod p) ∈ E p) ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E) d|) ≤
      4*(H.divisors.card : ℝ)*(v^s)^2 := by
  let D := v^s
  let F := RealFundamentalSieve.levelDivisors P v s
  have hsize (d : ℕ) (hd : d ∈ F) : (d : ℝ) ≤ D := (Finset.mem_filter.mp hd).2
  have hsub : F ⊆ Finset.range (⌊D⌋₊+1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by dsimp [D];linarith)).mpr (hsize d hd)))
  have hcard : (F.card : ℝ) ≤ 2*D := by
    have hc : (F.card : ℝ) ≤ ((⌊D⌋₊+1 : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    have hf := Nat.floor_le (show 0 ≤ D by dsimp [D];linarith)
    push_cast at hc
    dsimp [D] at *
    linarith
  have hsum : (∑ d ∈ F,
      |FundamentalBlockEstimate.integerRemainder (unitIntervalIntegers H b c) (fun _ => 1)
        (fun p n => (n : ZMod p) ∈ E p) ((c-b)*((H.totient : ℝ)/(H : ℝ))) (residueDensity E) d|) ≤
      (F.card : ℝ)*(2*(H.divisors.card : ℝ)*D) := by
    calc
      _ ≤ ∑ _d ∈ F,2*(H.divisors.card : ℝ)*D := by
        apply Finset.sum_le_sum
        intro d hd
        exact (integerRemainder_bound H hH P hP hHP E b c hbc d
          (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1)).trans
            (mul_le_mul_of_nonneg_left (hsize d hd) (by positivity))
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
  have hnon : 0 ≤ 2*(H.divisors.card : ℝ)*D := by dsimp [D];positivity
  have hh := mul_le_mul_of_nonneg_right hcard hnon
  exact hsum.trans (by dsimp [D] at hh ⊢;nlinarith)

end ErdosVarianceMoments

end

section

namespace NumberTheoryLean.SmallSieveFinite

open scoped BigOperators

noncomputable def smallEuler (z : ℕ) : ℝ :=
  ∏ p ∈ LargePrimeDeletion.cutoffPrimes z, (1 - (p : ℝ)⁻¹)

theorem squarefree_dvd_iff_primeFactors {d x : ℕ} (hd : Squarefree d) :
    d ∣ x ↔ ∀ p ∈ d.primeFactors, p ∣ x := by
  constructor
  · intro h p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    by_cases hx : x = 0
    · simp [hx]
    · rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.prod_primeFactors_dvd_iff hx]
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, h p hp, hx⟩

theorem intersectionValue_divisibility (A i d : ℕ) (hd : Squarefree d) :
    BonferroniBlocks.intersectionValue d.primeFactors (fun p => p ∣ A + i) =
      (if d ∣ A + i then 1 else 0 : ℝ) := by
  classical
  unfold BonferroniBlocks.intersectionValue
  simp only [← squarefree_dvd_iff_primeFactors hd]

theorem reciprocal_primeFactors_product {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, (p : ℝ)⁻¹) = (d : ℝ)⁻¹ := by
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

theorem integerRemainder_eq_interval_rem (A N D : ℕ) (hD : Squarefree D)
    {d : ℕ} (hd : d ∣ D) :
    FundamentalBlockEstimate.integerRemainder (Finset.range N) (fun _ => 1)
      (fun p i => p ∣ A + i) (N : ℝ) (fun p => (p : ℝ)⁻¹) d =
      (IntervalBoundingSieve.intervalSieve A N D hD).rem d := by
  classical
  have hdsq : Squarefree d := hD.squarefree_of_dvd hd
  unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    BonferroniBlocks.intersectionMass
  simp_rw [one_mul, intersectionValue_divisibility A _ d hdsq]
  rw [reciprocal_primeFactors_product hdsq]
  change (∑ i ∈ Finset.range N, if d ∣ A + i then (1 : ℝ) else 0) -
      (N : ℝ) * (d : ℝ)⁻¹ = _
  rw [BoundingSieve.rem, IntervalBoundingSieve.interval_multSum]
  simp only [LargePrimeDeletion.deletionCell, ← Nat.cast_add, Int.natCast_dvd_natCast,
    Finset.sum_boole, IntervalBoundingSieve.intervalSieve, IntervalBoundingSieve.reciprocalDensity_apply]
  ring

theorem integerRemainder_abs_le_two (A N D : ℕ) (hD : Squarefree D)
    {d : ℕ} (hd : d ∣ D) (J : ℝ) (hNJ : |(N : ℝ) - J| ≤ 1) :
    |FundamentalBlockEstimate.integerRemainder (Finset.range N) (fun _ => 1)
      (fun p i => p ∣ A + i) J (fun p => (p : ℝ)⁻¹) d| ≤ 2 := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hD.ne_zero)
  have hdsq : Squarefree d := hD.squarefree_of_dvd hd
  have hEq : FundamentalBlockEstimate.integerRemainder (Finset.range N) (fun _ => 1)
      (fun p i => p ∣ A + i) J (fun p => (p : ℝ)⁻¹) d =
      (IntervalBoundingSieve.intervalSieve A N D hD).rem d + ((N : ℝ) - J) * (d : ℝ)⁻¹ := by
    rw [← integerRemainder_eq_interval_rem A N D hD hd]
    unfold FundamentalBlockEstimate.integerRemainder BonferroniBlocks.intersectionRemainder
    rw [reciprocal_primeFactors_product hdsq]
    ring
  rw [hEq]
  have hInv : (d : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hdpos)
  have hErr : |((N : ℝ) - J) * (d : ℝ)⁻¹| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ)⁻¹ from inv_nonneg.mpr (Nat.cast_nonneg d))]
    simpa only [one_mul] using mul_le_mul hNJ hInv (inv_nonneg.mpr (Nat.cast_nonneg d)) zero_le_one
  exact (abs_add_le _ _).trans (by linarith [IntervalBoundingSieve.interval_rem_abs_le_one A N D hD hdpos])

theorem survives_sum_eq_coprimeOffsets (A N : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ i ∈ Finset.range N, (1 : ℝ) * BonferroniBlocks.survives P (fun p => p ∣ A + i)) =
      ((LargePrimeDeletion.coprimeOffsets N (∏ p ∈ P, p) (A : ℤ)).card : ℝ) := by
  classical
  have hD : Squarefree (∏ p ∈ P, p) := IntervalBoundingSieve.squarefree_primeSet_product P hprime
  have hfac : (∏ p ∈ P, p).primeFactors = P := Nat.primeFactors_prod hprime
  have hpoint : ∀ i : ℕ, BonferroniBlocks.survives P (fun p => p ∣ A + i) =
      if (A + i).Coprime (∏ p ∈ P, p) then 1 else 0 := by
    intro i
    unfold BonferroniBlocks.survives
    have hcop := LargePrimeDeletion.coprime_iff_avoid_primeFactors
      (Nat.pos_of_ne_zero hD.ne_zero) ((A + i : ℕ) : ℤ)
    simp only [hfac, Int.natAbs_natCast, Int.natCast_dvd_natCast] at hcop
    simp only [← hcop]
  simp_rw [one_mul, hpoint]
  simp only [LargePrimeDeletion.coprimeOffsets, ← Nat.cast_add, Int.natAbs_natCast, Finset.sum_boole]

theorem realLevelDivisors_card_le (P : Finset ℕ) (u s : ℝ) (hu : 0 ≤ u) :
    ((RealFundamentalSieve.levelDivisors P u s).card : ℝ) ≤ u ^ s := by
  classical
  have hpow : 0 ≤ u ^ s := Real.rpow_nonneg hu s
  have hsub : RealFundamentalSieve.levelDivisors P u s ⊆ Finset.Icc 1 ⌊u ^ s⌋₊ := by
    intro d hd
    obtain ⟨hdP, hdL⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, (Nat.le_floor_iff hpow).mpr hdL⟩
  have hcard : (RealFundamentalSieve.levelDivisors P u s).card ≤ ⌊u ^ s⌋₊ := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  exact (show ((RealFundamentalSieve.levelDivisors P u s).card : ℝ) ≤ (⌊u ^ s⌋₊ : ℝ) by exact_mod_cast hcard).trans
    (Nat.floor_le hpow)

theorem cutoffSurvivors_eq_residueAvoidingOffsets (N z : ℕ) (residue : ℕ → ℕ) :
    LargePrimeDeletion.cutoffSurvivors N z residue =
      IntervalBoundingSieve.residueAvoidingOffsets N (IntervalBoundingSieve.cutoffProduct z) residue := by
  classical
  ext i
  simp only [LargePrimeDeletion.mem_cutoffSurvivors, IntervalBoundingSieve.residueAvoidingOffsets,
    Finset.mem_filter, Finset.mem_range, IntervalBoundingSieve.cutoffProduct_primeFactors,
    LargePrimeDeletion.mem_cutoffPrimes]
  tauto

theorem finite_small_sieve_bound (N : ℕ) (u s J : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hs : 480024 ≤ s) (hJ : 0 ≤ J) (hNJ : |(N : ℝ) - J| ≤ 1) :
    |((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) - J * smallEuler ⌊u⌋₊| ≤
      J * smallEuler ⌊u⌋₊ * Real.exp (-s / 96) + 2 * u ^ s := by
  classical
  let z := ⌊u⌋₊
  let P := LargePrimeDeletion.cutoffPrimes z
  let D := IntervalBoundingSieve.cutoffProduct z
  have hD : Squarefree D := IntervalBoundingSieve.cutoffProduct_squarefree z
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1
  have hsize : ∀ p ∈ P, (p : ℝ) ≤ u := by
    intro p hp
    have hpz := (LargePrimeDeletion.mem_cutoffPrimes.mp hp).2
    exact (show (p : ℝ) ≤ (z : ℝ) by exact_mod_cast hpz).trans (Nat.floor_le (by linarith))
  obtain ⟨A, hA⟩ := IntervalBoundingSieve.exists_residue_count_translation N D
    (Nat.pos_of_ne_zero hD.ne_zero) residue
  have hcount : (LargePrimeDeletion.cutoffSurvivors N z residue).card =
      (LargePrimeDeletion.coprimeOffsets N D (A : ℤ)).card := by
    rw [cutoffSurvivors_eq_residueAvoidingOffsets, hA]
  have h := RealFundamentalSieve.fundamental_lemma (Finset.range N) (fun _ => (1 : ℝ))
    (fun _ _ => by norm_num) (fun p i => p ∣ A + i) u s P J (fun p => (p : ℝ)⁻¹)
    hu hs hJ hprime hsize (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun p _ => by simpa only [one_div] using
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_nonneg p))
    (fun _ => by norm_num)
  rw [survives_sum_eq_coprimeOffsets A N P hprime] at h
  change |((LargePrimeDeletion.coprimeOffsets N D (A : ℤ)).card : ℝ) - J * smallEuler z| ≤ _ at h
  rw [← hcount] at h
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _d ∈ RealFundamentalSieve.levelDivisors P u s, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact integerRemainder_abs_le_two A N D hD
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) J hNJ
    _ = 2 * ((RealFundamentalSieve.levelDivisors P u s).card : ℝ) := by simp [mul_comm]
    _ ≤ 2 * u ^ s := mul_le_mul_of_nonneg_left (realLevelDivisors_card_le P u s (by linarith)) (by norm_num)

theorem all_integer_euler_product (z : ℕ) (hz : 1 ≤ z) :
    (∏ n ∈ Finset.Icc 2 z, (1 - (n : ℝ)⁻¹)) = (z : ℝ)⁻¹ := by
  induction z, hz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
      rw [Finset.prod_Icc_succ_top (by omega), ih]
      have hz0 : (z : ℝ) ≠ 0 := by exact_mod_cast (show z ≠ 0 by omega)
      have hzs : ((z + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem smallEuler_ge_inv (z : ℕ) (hz : 2 ≤ z) : (z : ℝ)⁻¹ ≤ smallEuler z := by
  have hsubset : LargePrimeDeletion.cutoffPrimes z ⊆ Finset.Icc 2 z := by
    intro p hp
    obtain ⟨hprime, hpz⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.two_le, hpz⟩
  rw [← all_integer_euler_product z (by omega)]
  apply Finset.prod_le_prod_of_subset_of_le_one₀ hsubset
  · intro n hn
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ n by have := (Finset.mem_Icc.mp hn).1; omega))
  · intro n _ _
    have h := inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n)
    linarith

theorem smallEuler_floor_ge_inv (u : ℝ) (hu : 2 ≤ u) : u⁻¹ ≤ smallEuler ⌊u⌋₊ := by
  have hz : 2 ≤ ⌊u⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hu)
  have hzpos : (0 : ℝ) < (⌊u⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊u⌋₊ by omega)
  exact ((inv_le_inv₀ (by linarith) hzpos).mpr (Nat.floor_le (by linarith))).trans (smallEuler_ge_inv _ hz)

end NumberTheoryLean.SmallSieveFinite

end

section

namespace NumberTheoryLean.EulerProductRatio

open scoped BigOperators

theorem restricted_block_union (z K : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ z)
    (hlower : ∀ p ∈ P, 2 ^ (2 ^ K) ≤ p) :
    (Finset.Icc K (PrimeDensityBlocks.lastBlock z)).biUnion (PrimeDensityBlocks.primeBlock P) = P := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, _, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hpj).1
  · intro hp
    have hfull := PrimeDensityBlocks.primeBlock_union z P hprime hsize
    have hpFull : p ∈ (PrimeDensityBlocks.blockIndices z).biUnion (PrimeDensityBlocks.primeBlock P) := by
      simpa only [hfull] using hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hpFull
    have hjJ : j ≤ PrimeDensityBlocks.lastBlock z := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hKj : K ≤ j := by
      by_contra hnot
      have hjK : j + 1 ≤ K := by omega
      have he : 2 ^ (j + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
      have htop : 2 ^ (2 ^ (j + 1)) ≤ 2 ^ (2 ^ K) := Nat.pow_le_pow_right (by norm_num) he
      have hbelow := (PrimeDensityBlocks.mem_geometricPrimes.mp (Finset.mem_inter.mp hpj).2).2.1
      have habove := hlower p hp
      omega
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Icc.mpr ⟨hKj, hjJ⟩, hpj⟩

theorem tail_euler_lower (z h : ℕ) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, p ≤ z)
    (hlower : ∀ p ∈ P, 2 ^ (2 ^ (PrimeDensityBlocks.lastBlock z - h)) ≤ p) :
    Real.exp (-4596 * ((h + 1 : ℕ) : ℝ)) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  let J := PrimeDensityBlocks.lastBlock z
  let B := Finset.Icc (J - h) J
  have hdim : ∀ p ∈ P, (p : ℝ)⁻¹ ≤ 2 / p := by
    intro p _
    simpa only [one_div] using div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_nonneg p)
  have hcap := BonferroniDensity.prime_density_le_two_thirds P (fun p => (p : ℝ)⁻¹)
    hprime hdim (fun _ => by norm_num)
  have heach : ∀ j ∈ B, Real.exp (-4596) ≤
      ∏ p ∈ PrimeDensityBlocks.primeBlock P j, (1 - (p : ℝ)⁻¹) := by
    intro j _
    have hsum := PrimeDensityBlocks.primeBlock_density_sum_le P j (fun p => (p : ℝ)⁻¹) hdim
    have he := BonferroniDensity.exp_neg_three_mul_le_eulerProduct (PrimeDensityBlocks.primeBlock P j)
      (fun p => (p : ℝ)⁻¹) (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
      (fun p hp => hcap p (Finset.mem_inter.mp hp).1) hsum
    norm_num at he
    exact he
  have hcard : B.card ≤ h + 1 := by
    dsimp [B]
    rw [Nat.card_Icc]
    omega
  have hdis : (B : Set ℕ).PairwiseDisjoint (PrimeDensityBlocks.primeBlock P) := by
    intro i _ j _ hij
    exact (PrimeDensityBlocks.geometricPrimes_disjoint hij).mono Finset.inter_subset_right Finset.inter_subset_right
  calc
    Real.exp (-4596 * ((h + 1 : ℕ) : ℝ)) ≤ Real.exp (-4596 * (B.card : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hc : (B.card : ℝ) ≤ ((h + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      linarith
    _ = ∏ _j ∈ B, Real.exp (-4596) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ∏ j ∈ B, ∏ p ∈ PrimeDensityBlocks.primeBlock P j, (1 - (p : ℝ)⁻¹) :=
      Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) heach
    _ = _ := by rw [← Finset.prod_biUnion hdis, restricted_block_union z (J - h) P hprime hsize hlower]

theorem smallEuler_nonneg (z : ℕ) : 0 ≤ SmallSieveFinite.smallEuler z := by
  apply Finset.prod_nonneg
  intro p hp
  apply sub_nonneg.mpr
  have hprime := (LargePrimeDeletion.mem_cutoffPrimes.mp hp).1
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hprime.one_lt.le)

theorem smallEuler_ratio_nat (z t h : ℕ) (htz : t ≤ z)
    (hlower : 2 ^ (2 ^ (PrimeDensityBlocks.lastBlock z - h)) ≤ t) :
    SmallSieveFinite.smallEuler t ≤ Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * SmallSieveFinite.smallEuler z := by
  classical
  let Pz := LargePrimeDeletion.cutoffPrimes z
  let Pt := LargePrimeDeletion.cutoffPrimes t
  let Q := Pz \ Pt
  have hsub : Pt ⊆ Pz := by
    intro p hp
    obtain ⟨hpp, hpt⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
    exact LargePrimeDeletion.mem_cutoffPrimes.mpr ⟨hpp, hpt.trans htz⟩
  have hprime : ∀ p ∈ Q, p.Prime := fun p hp =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp hp).1).1
  have hsize : ∀ p ∈ Q, p ≤ z := fun p hp =>
    (LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp hp).1).2
  have hQlow : ∀ p ∈ Q, 2 ^ (2 ^ (PrimeDensityBlocks.lastBlock z - h)) ≤ p := by
    intro p hp
    have hn := (Finset.mem_sdiff.mp hp).2
    have hpp := hprime p hp
    have htp : t < p := by
      by_contra hnot
      exact hn (LargePrimeDeletion.mem_cutoffPrimes.mpr ⟨hpp, Nat.le_of_not_lt hnot⟩)
    exact hlower.trans htp.le
  have he := tail_euler_lower z h Q hprime hsize hQlow
  have hprod : SmallSieveFinite.smallEuler z =
      SmallSieveFinite.smallEuler t * ∏ p ∈ Q, (1 - (p : ℝ)⁻¹) := by
    unfold SmallSieveFinite.smallEuler
    rw [← Finset.prod_sdiff hsub]
    ring
  have hmul : SmallSieveFinite.smallEuler t * Real.exp (-4596 * ((h + 1 : ℕ) : ℝ)) ≤
      SmallSieveFinite.smallEuler z := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_left he (smallEuler_nonneg t)
  have hfinal := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (4596 * ((h + 1 : ℕ) : ℝ))).le
  have hcancel : Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) *
      (SmallSieveFinite.smallEuler t * Real.exp (-4596 * ((h + 1 : ℕ) : ℝ))) = SmallSieveFinite.smallEuler t := by
    calc
      _ = SmallSieveFinite.smallEuler t *
          (Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * Real.exp (-4596 * ((h + 1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [← Real.exp_add]; simp
  rw [hcancel] at hfinal
  exact hfinal

noncomputable def rootCutoff (u : ℝ) (h : ℕ) : ℝ := u ^ (((2 ^ h : ℕ) : ℝ)⁻¹)

theorem rootExponent_pos (h : ℕ) : (0 : ℝ) < ((2 ^ h : ℕ) : ℝ)⁻¹ := by positivity

theorem rootExponent_le_one (h : ℕ) : ((2 ^ h : ℕ) : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_pow h 2 (by norm_num))

theorem rootCutoff_le (u : ℝ) (h : ℕ) (hu : 1 ≤ u) : rootCutoff u h ≤ u :=
  Real.rpow_le_self_of_one_le hu (rootExponent_le_one h)

theorem rootCutoff_ge_two (u : ℝ) (h : ℕ) (hu : (2 : ℝ) ^ (2 ^ h : ℕ) ≤ u) :
    2 ≤ rootCutoff u h := by
  have hroot := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 ^ h : ℕ)) hu (rootExponent_pos h).le
  rw [Real.pow_rpow_inv_natCast (by norm_num) (pow_ne_zero h (by norm_num : (2 : ℕ) ≠ 0))] at hroot
  exact hroot

theorem geometric_endpoint_le_rootCutoff (u : ℝ) (h : ℕ) (hu : 2 ≤ u) (hw : 2 ≤ rootCutoff u h) :
    ((2 ^ (2 ^ (PrimeDensityBlocks.lastBlock ⌊u⌋₊ - h)) : ℕ) : ℝ) ≤ rootCutoff u h := by
  let z := ⌊u⌋₊
  let J := PrimeDensityBlocks.lastBlock z
  have hz : 2 ≤ z := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hu)
  by_cases hhJ : h ≤ J
  · let n := 2 ^ (2 ^ (J - h))
    have hpow : n ^ (2 ^ h) = 2 ^ (2 ^ J) := by
      dsimp [n]
      have he : 2 ^ (J - h) * 2 ^ h = 2 ^ J := by rw [← pow_add, Nat.sub_add_cancel hhJ]
      rw [← pow_mul, he]
    have hbaseN : n ^ (2 ^ h) ≤ z := hpow ▸ PrimeDensityBlocks.lastBlock_lower_le z hz
    have hbaseR : (n : ℝ) ^ (2 ^ h : ℕ) ≤ u := by
      have hcast : (n : ℝ) ^ (2 ^ h : ℕ) ≤ (z : ℝ) := by exact_mod_cast hbaseN
      exact hcast.trans (Nat.floor_le (by linarith))
    have hroot := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg n) _) hbaseR (rootExponent_pos h).le
    rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg n) (pow_ne_zero h (by norm_num : (2 : ℕ) ≠ 0))] at hroot
    exact hroot
  · have hJh : J ≤ h := by omega
    have hzero : J - h = 0 := Nat.sub_eq_zero_of_le hJh
    change ((2 ^ (2 ^ (J - h)) : ℕ) : ℝ) ≤ _
    simpa only [hzero, pow_zero, pow_one, Nat.cast_ofNat] using hw

theorem smallEuler_ratio_rootCutoff (u : ℝ) (h : ℕ) (hu : 2 ≤ u) (hw : 2 ≤ rootCutoff u h) :
    SmallSieveFinite.smallEuler ⌊rootCutoff u h⌋₊ ≤
      Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  apply smallEuler_ratio_nat
  · exact Nat.floor_mono (rootCutoff_le u h (by linarith))
  · apply (Nat.le_floor_iff (by linarith : 0 ≤ rootCutoff u h)).mpr
    exact geometric_endpoint_le_rootCutoff u h hu hw

end NumberTheoryLean.EulerProductRatio

end

end Erdos970

end OAI
