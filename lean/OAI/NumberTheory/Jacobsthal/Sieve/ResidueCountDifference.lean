import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Sieve.EulerProductRatio

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.ProgressionSieve

open scoped BigOperators

theorem exists_affine_residue {p q : ℕ} (hp : p.Prime) (hqp : q.Coprime p)
    (r c : ℕ) : ∃ b : ℕ, ∀ t : ℕ,
      (r + q * t) % p = c % p ↔ t % p = b % p := by
  obtain ⟨b, _, hb⟩ := Nat.exists_mul_mod_eq_of_coprime (p - r % p + c) hqp hp.ne_zero
  have hsol : Nat.ModEq p (r + q * b) c := by
    have h := (Nat.mod_modEq r p).symm.add (show Nat.ModEq p (q * b) (p - r % p + c) from hb)
    have heq : r % p + (p - r % p + c) = p + c := by
      have := Nat.mod_lt r hp.pos
      omega
    rw [heq] at h
    exact h.trans (show Nat.ModEq p (p + c) c by simp [Nat.ModEq])
  refine ⟨b, ?_⟩
  intro t
  constructor
  · intro h
    have hprod := Nat.ModEq.add_left_cancel' r ((show Nat.ModEq p (r + q * t) c from h).trans hsol.symm)
    exact hprod.cancel_left_of_coprime hqp.symm.gcd_eq_one
  · intro h
    exact ((show Nat.ModEq p t b from h).mul_left q |>.add_left r).trans hsol

theorem exists_progression_residues (z q r : ℕ) (hq : q.Prime) (hzq : z < q)
    (residue : ℕ → ℕ) : ∃ transformed : ℕ → ℕ,
      ∀ p, p.Prime → p ≤ z → ∀ t : ℕ,
        (r + q * t) % p = residue p % p ↔ t % p = transformed p % p := by
  classical
  have hchoice : ∀ p : ℕ, ∃ b : ℕ, p.Prime → p ≤ z → ∀ t : ℕ,
      (r + q * t) % p = residue p % p ↔ t % p = b % p := by
    intro p
    by_cases hp : p.Prime ∧ p ≤ z
    · have hqp : q.Coprime p := (Nat.coprime_primes hq hp.1).mpr (by omega)
      obtain ⟨b, hb⟩ := exists_affine_residue hp.1 hqp r (residue p)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨0, fun hprime hpz => False.elim (hp ⟨hprime, hpz⟩)⟩
  choose transformed htrans using hchoice
  exact ⟨transformed, htrans⟩

theorem divisibilityResidue_lt (a : ℤ) {q : ℕ} (hq : 0 < q) :
    LargePrimeDeletion.divisibilityResidue a q < q := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hr0 : 0 ≤ (-a) % q := Int.emod_nonneg _ (ne_of_gt hqz)
  have hrq : (-a) % q < q := Int.emod_lt_of_pos _ hqz
  exact_mod_cast (show ((LargePrimeDeletion.divisibilityResidue a q : ℕ) : ℤ) < q by
    simpa only [LargePrimeDeletion.divisibilityResidue, Int.toNat_of_nonneg hr0] using hrq)

theorem offset_eq_residue_add_mul_div (a : ℤ) {q i : ℕ} (hq : 0 < q)
    (hdiv : (q : ℤ) ∣ a + i) :
    i = LargePrimeDeletion.divisibilityResidue a q + q * (i / q) := by
  have hmod := (LargePrimeDeletion.divisibility_iff_modEq a hq i).mp hdiv
  have hr := divisibilityResidue_lt a hq
  have hi : i % q = LargePrimeDeletion.divisibilityResidue a q := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using hmod
  have hdecomp := Nat.mod_add_div i q
  rw [hi] at hdecomp
  exact hdecomp.symm

def progressionLength (Y z : ℕ) : ℕ := Y / (z + 1) + 1

theorem exists_deletion_pullback (Y z : ℕ) (residue : ℕ → ℕ) (a : ℤ)
    {q : ℕ} (hq : q.Prime) (hzq : z < q) :
    ∃ transformed : ℕ → ℕ,
      (LargePrimeDeletion.deletionCell (LargePrimeDeletion.cutoffSurvivors Y z residue) a q).card ≤
        (LargePrimeDeletion.cutoffSurvivors (progressionLength Y z) z transformed).card := by
  classical
  let r := LargePrimeDeletion.divisibilityResidue a q
  obtain ⟨transformed, htrans⟩ := exists_progression_residues z q r hq hzq residue
  refine ⟨transformed, ?_⟩
  apply Finset.card_le_card_of_injOn (fun i : ℕ => i / q)
  · intro i hi
    obtain ⟨his, hdiv⟩ := LargePrimeDeletion.mem_deletionCell.mp hi
    obtain ⟨hiY, hav⟩ := LargePrimeDeletion.mem_cutoffSurvivors.mp his
    apply LargePrimeDeletion.mem_cutoffSurvivors.mpr
    refine ⟨?_, ?_⟩
    · have hquot : i / q ≤ Y / (z + 1) :=
        Nat.div_le_div (Nat.le_of_lt hiY) (Nat.succ_le_of_lt hzq) (Nat.succ_ne_zero z)
      exact Nat.lt_succ_of_le hquot
    · intro p hp hpz hbad
      have hdecomp := offset_eq_residue_add_mul_div a hq.pos hdiv
      have hhit := (htrans p hp hpz (i / q)).mpr hbad
      change (r + q * (i / q)) % p = residue p % p at hhit
      rw [← hdecomp] at hhit
      exact hav p hp hpz hhit
  · intro i hi j hj hquot
    obtain ⟨_, hdivi⟩ := LargePrimeDeletion.mem_deletionCell.mp hi
    obtain ⟨_, hdivj⟩ := LargePrimeDeletion.mem_deletionCell.mp hj
    change i / q = j / q at hquot
    rw [offset_eq_residue_add_mul_div a hq.pos hdivi,
      offset_eq_residue_add_mul_div a hq.pos hdivj, hquot]

noncomputable def deletionBudget (Y z : ℕ) : ℝ :=
  255 * (1 + (progressionLength Y z : ℝ) / Real.log (progressionLength Y z))

theorem deletionBudget_nonneg (Y z : ℕ) : 0 ≤ deletionBudget Y z := by
  have hT : 1 ≤ progressionLength Y z := by simp [progressionLength]
  have hlog : 0 ≤ Real.log (progressionLength Y z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hT)
  unfold deletionBudget
  exact mul_nonneg (by norm_num) (add_nonneg zero_le_one
    (div_nonneg (Nat.cast_nonneg _) hlog))

theorem largePrime_deletion_le_log (Y z : ℕ) (residue : ℕ → ℕ) (a : ℤ)
    {q : ℕ} (hq : q.Prime) (hzq : z < q) (hTz : progressionLength Y z ≤ z) :
    ((LargePrimeDeletion.deletionCell
      (LargePrimeDeletion.cutoffSurvivors Y z residue) a q).card : ℝ) ≤ deletionBudget Y z := by
  obtain ⟨transformed, hcard⟩ := exists_deletion_pullback Y z residue a hq hzq
  calc
    _ ≤ ((LargePrimeDeletion.cutoffSurvivors (progressionLength Y z) z transformed).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ _ := SquarefreeHarmonic.cutoffSurvivors_le_uniform_log
      (progressionLength Y z) z transformed hTz

theorem sum_largePrime_deletions_le_log (Y n z k : ℕ)
    (hcard : n.primeFactors.card ≤ k) (residue : ℕ → ℕ) (a : ℤ)
    (hTz : progressionLength Y z ≤ z) :
    (∑ q ∈ LargePrimeDeletion.largePrimeFactors n z,
      ((LargePrimeDeletion.deletionCell
        (LargePrimeDeletion.cutoffSurvivors Y z residue) a q).card : ℝ)) ≤
      (k : ℝ) * deletionBudget Y z := by
  have hlargecard : (LargePrimeDeletion.largePrimeFactors n z).card ≤ k :=
    (Finset.card_filter_le _ _).trans hcard
  calc
    _ ≤ ∑ _q ∈ LargePrimeDeletion.largePrimeFactors n z, deletionBudget Y z := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqn, hqz⟩ := LargePrimeDeletion.mem_largePrimeFactors.mp hq
      exact largePrime_deletion_le_log Y z residue a
        (Nat.mem_primeFactors.mp hqn).1 hqz hTz
    _ = ((LargePrimeDeletion.largePrimeFactors n z).card : ℝ) * deletionBudget Y z := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hlargecard) (deletionBudget_nonneg Y z)

theorem isJacobsthalBound_of_cutoff_lower (Y z k : ℕ)
    (hTz : progressionLength Y z ≤ z) {S : ℝ}
    (hlower : ∀ residue : ℕ → ℕ,
      S ≤ (LargePrimeDeletion.cutoffSurvivors Y z residue).card)
    (hbudget : (k : ℝ) * deletionBudget Y z < S) :
    Targets.IsJacobsthalBound k Y := by
  apply LargePrimeDeletion.isJacobsthalBound_of_cutoff_estimates Y z k
    (deletionBudget_nonneg Y z) hlower
  · intro residue a q hq hqz
    exact largePrime_deletion_le_log Y z residue a hq hqz hTz
  · exact hbudget

end NumberTheoryLean.ProgressionSieve



namespace NumberTheoryLean.SmallSieveRelative

open scoped BigOperators

theorem normalized_remainder_le (u v : ℝ) (hu : 2 ≤ u) (hv : 4 ≤ v) :
    u ^ (v / 2) / (u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊) ≤ Real.exp (-v / 192) := by
  have hu0 : 0 < u := by linarith
  have hJ : 0 < u ^ v := Real.rpow_pos_of_pos hu0 v
  have hEuler := SmallSieveFinite.smallEuler_floor_ge_inv u hu
  have hinv : 0 < u⁻¹ := inv_pos.mpr hu0
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogu : (1 / 2 : ℝ) ≤ Real.log u := hlog2.trans (Real.log_le_log (by norm_num) hu)
  calc
    u ^ (v / 2) / (u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊) ≤
        u ^ (v / 2) / (u ^ v * u⁻¹) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hu0.le _) (mul_pos hJ hinv)
        (mul_le_mul_of_nonneg_left hEuler hJ.le)
    _ = (u ^ (v / 2) / u ^ v) * u := by field_simp
    _ = u ^ (v / 2 - v) * u := by rw [Real.rpow_sub hu0]
    _ = u ^ (1 - v / 2) := by
      have hidx : (v / 2 - v) + 1 = 1 - v / 2 := by ring
      rw [← hidx, Real.rpow_add hu0, Real.rpow_one]
    _ = Real.exp (Real.log u * (1 - v / 2)) := Real.rpow_def_of_pos hu0 _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg (show 0 ≤ v / 2 - 1 by linarith) (sub_nonneg.mpr hlogu)
      nlinarith

theorem relative_bound_rpow (N : ℕ) (u v : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hv : 960048 ≤ v) (hNJ : |(N : ℝ) - u ^ v| ≤ 1) :
    |((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) /
        (u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊) - 1| ≤ 3 * Real.exp (-v / 192) := by
  have hu0 : 0 < u := by linarith
  have hJ : 0 < u ^ v := Real.rpow_pos_of_pos hu0 v
  have hEuler : 0 < SmallSieveFinite.smallEuler ⌊u⌋₊ :=
    (inv_pos.mpr hu0).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv u hu)
  have hDen : 0 < u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊ := mul_pos hJ hEuler
  have h := SmallSieveFinite.finite_small_sieve_bound N u (v / 2) (u ^ v) residue
    hu (by linarith) hJ.le hNJ
  have hparam : -(v / 2) / 96 = -v / 192 := by ring
  rw [hparam] at h
  have hrem := normalized_remainder_le u v hu (by linarith)
  let A : ℝ := (LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card
  let D : ℝ := u ^ v * SmallSieveFinite.smallEuler ⌊u⌋₊
  have hD0 : D ≠ 0 := ne_of_gt hDen
  have hEq : A / D - 1 = (A - D) / D := by field_simp [hD0]
  change |A / D - 1| ≤ _
  rw [hEq, abs_div, abs_of_pos hDen]
  calc
    |A - D| / D ≤ (D * Real.exp (-v / 192) + 2 * u ^ (v / 2)) / D :=
      div_le_div_of_nonneg_right h hDen.le
    _ = Real.exp (-v / 192) + 2 * (u ^ (v / 2) / D) := by field_simp [hD0]
    _ ≤ _ := by change u ^ (v / 2) / D ≤ _ at hrem; linarith

theorem rpow_log_ratio (u J : ℝ) (hu : 1 < u) (hJ : 0 < J) :
    u ^ (Real.log J / Real.log u) = J := by
  have hlu : Real.log u ≠ 0 := ne_of_gt (Real.log_pos hu)
  rw [Real.rpow_def_of_pos (by linarith)]
  have he : Real.log u * (Real.log J / Real.log u) = Real.log J := by field_simp
  rw [he, Real.exp_log hJ]

theorem small_relative (N : ℕ) (u J : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hJ : 0 < J) (hNJ : |(N : ℝ) - J| ≤ 1)
    (hv : 960048 ≤ Real.log J / Real.log u) :
    |((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) /
        (J * SmallSieveFinite.smallEuler ⌊u⌋₊) - 1| ≤
      3 * Real.exp (-(Real.log J / Real.log u) / 192) := by
  have hpow := rpow_log_ratio u J (by linarith) hJ
  have h := relative_bound_rpow N u (Real.log J / Real.log u) residue hu hv (by simpa only [hpow] using hNJ)
  simpa only [hpow] using h

end NumberTheoryLean.SmallSieveRelative



namespace NumberTheoryLean.ProgressionSmallSieve

def progressionHit (a : ℤ) (q : ℕ) (residue : ℕ → ℕ) (p i : ℕ) : Prop :=
  Int.ModEq (p : ℤ) (a + (q : ℤ) * i) (residue p : ℤ)

noncomputable def progressionSurvivors (N z : ℕ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ) : Finset ℕ :=
  SievePartition.survivors (Finset.range N) (LargePrimeDeletion.cutoffPrimes z)
    (progressionHit a q residue)

theorem exists_integer_affine_residue (a : ℤ) (q c : ℕ) {p : ℕ}
    (hp : p.Prime) (hqp : q.Coprime p) : ∃ b : ℕ, ∀ i : ℕ,
      Int.ModEq (p : ℤ) (a + (q : ℤ) * i) (c : ℤ) ↔ Nat.ModEq p i b := by
  let r : ℕ := (a % p).toNat
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hr : (r : ℤ) = a % p := Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hpz))
  have ha : Int.ModEq (p : ℤ) a r := by
    unfold Int.ModEq
    rw [hr, Int.emod_emod]
  obtain ⟨b, hb⟩ := ProgressionSieve.exists_affine_residue hp hqp r c
  refine ⟨b, ?_⟩
  intro i
  have hshift : Int.ModEq (p : ℤ) (a + (q : ℤ) * i) ((r + q * i : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using ha.add_right ((q : ℤ) * i)
  constructor
  · intro h
    have hnat : Nat.ModEq p (r + q * i) c := Int.natCast_modEq_iff.mp (hshift.symm.trans h)
    exact (hb i).mp hnat
  · intro h
    have hnat : Nat.ModEq p (r + q * i) c := (hb i).mpr h
    exact hshift.trans (Int.natCast_modEq_iff.mpr hnat)

theorem exists_coordinate_residues (z : ℕ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ)
    (hcoprime : ∀ p : ℕ, p.Prime → p ≤ z → q.Coprime p) :
    ∃ transformed : ℕ → ℕ, ∀ p, p.Prime → p ≤ z → ∀ i : ℕ,
      progressionHit a q residue p i ↔ SievePartition.residueBad transformed p i := by
  classical
  have hchoice : ∀ p : ℕ, ∃ b : ℕ, p.Prime → p ≤ z → ∀ i : ℕ,
      progressionHit a q residue p i ↔ Nat.ModEq p i b := by
    intro p
    by_cases hp : p.Prime ∧ p ≤ z
    · obtain ⟨b, hb⟩ := exists_integer_affine_residue a q (residue p) hp.1 (hcoprime p hp.1 hp.2)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨0, fun hprime hpz => False.elim (hp ⟨hprime, hpz⟩)⟩
  choose transformed htrans using hchoice
  exact ⟨transformed, htrans⟩

theorem exists_progressionSurvivors_eq (N z : ℕ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ)
    (hcoprime : ∀ p : ℕ, p.Prime → p ≤ z → q.Coprime p) :
    ∃ transformed : ℕ → ℕ,
      progressionSurvivors N z a q residue = LargePrimeDeletion.cutoffSurvivors N z transformed := by
  classical
  obtain ⟨transformed, htrans⟩ := exists_coordinate_residues z a q residue hcoprime
  refine ⟨transformed, ?_⟩
  ext i
  simp only [progressionSurvivors, LargePrimeDeletion.cutoffSurvivors, SievePartition.mem_survivors]
  apply and_congr_right
  intro _
  apply forall₂_congr
  intro p hp
  obtain ⟨hprime, hpz⟩ := LargePrimeDeletion.mem_cutoffPrimes.mp hp
  exact not_congr (htrans p hprime hpz i)

theorem progression_small_relative (N : ℕ) (u J : ℝ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hJ : 0 < J) (hNJ : |(N : ℝ) - J| ≤ 1)
    (hv : 960048 ≤ Real.log J / Real.log u)
    (hcoprime : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ u → q.Coprime p) :
    |((progressionSurvivors N ⌊u⌋₊ a q residue).card : ℝ) /
        (J * SmallSieveFinite.smallEuler ⌊u⌋₊) - 1| ≤
      3 * Real.exp (-(Real.log J / Real.log u) / 192) := by
  have hcop : ∀ p, p.Prime → p ≤ ⌊u⌋₊ → q.Coprime p := by
    intro p hp hpz
    exact hcoprime p hp ((Nat.le_floor_iff (by linarith)).mp hpz)
  obtain ⟨transformed, hEq⟩ := exists_progressionSurvivors_eq N ⌊u⌋₊ a q residue hcop
  rw [hEq]
  exact SmallSieveRelative.small_relative N u J transformed hu hJ hNJ hv

end NumberTheoryLean.ProgressionSmallSieve



namespace ErdosModulusRelative
open ErdosInverseHits ErdosInverseCounts NumberTheoryLean
attribute [local instance] Classical.propDecidable

noncomputable def modulusOffsets (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (d : ℕ) (hd : Squarefree d) : Finset ℕ :=
  (Finset.range (hitLength Y d (primeHitRepresentative d hd a))).filter
    (fun j => ∀ p ∈ small,(primeHitRepresentative d hd a+d*j)%p ≠ a p%p)

theorem modulus_candidates_eq_offsets (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (d : ℕ) (hd : Squarefree d) :
    modulusCandidates Y small a d =
      (modulusOffsets Y small a d hd).image (fun j => primeHitRepresentative d hd a+d*j) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hb := primeHitRepresentative_spec d hd a
  ext n
  rw [mem_modulusCandidates]
  simp only [modulusOffsets,Finset.mem_image,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hn1,hnY,hpr,hsmall⟩
    obtain ⟨j,rfl⟩ := exists_positive_coordinate d _ n hd0 hb.1 hb.2.1 hn1 ((hb.2.2 n).mp hpr)
    exact ⟨j,⟨(lt_hitLength_iff Y d _ j hd0 hb.2.1).mpr hnY,hsmall⟩,rfl⟩
  · rintro ⟨j,⟨hj,hsmall⟩,rfl⟩
    refine ⟨by omega,(lt_hitLength_iff Y d _ j hd0 hb.2.1).mp hj,?_,hsmall⟩
    apply (hb.2.2 _).mpr
    change (_+d*j)%d=_%d
    simp

theorem modulus_count_eq_offsets (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (d : ℕ) (hd : Squarefree d) :
    modulusCount Y small a d = ((modulusOffsets Y small a d hd).card : ℤ) := by
  unfold modulusCount
  rw [modulus_candidates_eq_offsets,Finset.card_image_of_injective]
  intro i j hij
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd.ne_zero) (Nat.add_left_cancel hij)

theorem offsets_eq_progression (Y z : ℕ) (a : ℕ → ℕ) (d : ℕ) (hd : Squarefree d) :
    modulusOffsets Y (LargePrimeDeletion.cutoffPrimes z) a d hd =
      ProgressionSmallSieve.progressionSurvivors (hitLength Y d (primeHitRepresentative d hd a))
        z (primeHitRepresentative d hd a : ℤ) d a := by
  ext j
  simp only [modulusOffsets,ProgressionSmallSieve.progressionSurvivors,SievePartition.mem_survivors,
    Finset.mem_filter,Finset.mem_range,ProgressionSmallSieve.progressionHit]
  apply and_congr_right
  intro _hj
  apply forall_congr'
  intro p
  apply forall_congr'
  intro _hp
  rw [← Nat.cast_mul,← Nat.cast_add,Int.natCast_modEq_iff]
  rfl

theorem large_modulus_coprime_small (w : ℝ) (d : ℕ) (hd : Squarefree d)
    (hlarge : ∀ p ∈ d.primeFactors,w < (p : ℝ)) (p : ℕ) (hp : p.Prime) (hpw : (p : ℝ) ≤ w) :
    d.Coprime p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hpd
  have h := hlarge p (Nat.mem_primeFactors.mpr ⟨hp,hpd,hd.ne_zero⟩)
  linarith

end ErdosModulusRelative



namespace NumberTheoryLean.SmallSieveUpper

theorem cutoffSurvivors_antitone (N z t : ℕ) (htz : t ≤ z) (residue : ℕ → ℕ) :
    LargePrimeDeletion.cutoffSurvivors N z residue ⊆ LargePrimeDeletion.cutoffSurvivors N t residue := by
  intro i hi
  obtain ⟨hiN, hav⟩ := LargePrimeDeletion.mem_cutoffSurvivors.mp hi
  exact LargePrimeDeletion.mem_cutoffSurvivors.mpr ⟨hiN, fun p hp hpt => hav p hp (hpt.trans htz)⟩

theorem count_le_four_of_relative (N : ℕ) (u J : ℝ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hJ : 0 < J) (hNJ : |(N : ℝ) - J| ≤ 1)
    (hv : 960048 ≤ Real.log J / Real.log u) :
    ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
      4 * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  have h := SmallSieveRelative.small_relative N u J residue hu hJ hNJ hv
  have hExp : Real.exp (-(Real.log J / Real.log u) / 192) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  have hEuler : 0 < SmallSieveFinite.smallEuler ⌊u⌋₊ :=
    (inv_pos.mpr (show 0 < u by linarith)).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv u hu)
  have hDen : 0 < J * SmallSieveFinite.smallEuler ⌊u⌋₊ := mul_pos hJ hEuler
  have hRatio := (abs_le.mp h).2
  have hBound : ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
      4 * (J * SmallSieveFinite.smallEuler ⌊u⌋₊) := (div_le_iff₀ hDen).mp (by linarith)
  simpa only [mul_assoc] using hBound

theorem threshold_ge_two (h : ℕ) : (2 : ℝ) ≤ (2 : ℝ) ^ (2 ^ h : ℕ) := by
  have hn : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by norm_num)
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  simpa only [pow_one] using hp

theorem small_upper_explicit (N : ℕ) (u J η : ℝ) (residue : ℕ → ℕ) (h : ℕ)
    (hscale : 960048 ≤ η * ((2 ^ h : ℕ) : ℝ))
    (hu : (2 : ℝ) ^ (2 ^ h : ℕ) ≤ u) (hJlower : u ^ η ≤ J) (hNJ : |(N : ℝ) - J| ≤ 1) :
    ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
      (4 * Real.exp (4596 * ((h + 1 : ℕ) : ℝ))) * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  let w := EulerProductRatio.rootCutoff u h
  have hu2 : 2 ≤ u := (threshold_ge_two h).trans hu
  have hu0 : 0 < u := by linarith
  have hw2 : 2 ≤ w := EulerProductRatio.rootCutoff_ge_two u h hu
  have hwle : w ≤ u := EulerProductRatio.rootCutoff_le u h (by linarith)
  have hJ : 0 < J := (Real.rpow_pos_of_pos hu0 η).trans_le hJlower
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hn : (0 : ℝ) < ((2 ^ h : ℕ) : ℝ) := by positivity
  have hη : 960048 * (((2 ^ h : ℕ) : ℝ)⁻¹) ≤ η := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hn).mpr hscale
  have hlogJ : η * Real.log u ≤ Real.log J := by
    have hlog := Real.log_le_log (Real.rpow_pos_of_pos hu0 η) hJlower
    rwa [Real.log_rpow hu0] at hlog
  have hlogw : Real.log w = (((2 ^ h : ℕ) : ℝ)⁻¹) * Real.log u := Real.log_rpow hu0 _
  have hvw : 960048 ≤ Real.log J / Real.log w := by
    apply (le_div_iff₀ hlw).mpr
    rw [hlogw]
    have hmul := mul_le_mul_of_nonneg_right hη hlu.le
    nlinarith
  have hCount := count_le_four_of_relative N w J residue hw2 hJ hNJ hvw
  have hEuler := EulerProductRatio.smallEuler_ratio_rootCutoff u h hu2 hw2
  have hSubset := cutoffSurvivors_antitone N ⌊u⌋₊ ⌊w⌋₊ (Nat.floor_mono hwle) residue
  calc
    ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
        ((LargePrimeDeletion.cutoffSurvivors N ⌊w⌋₊ residue).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSubset
    _ ≤ 4 * J * SmallSieveFinite.smallEuler ⌊w⌋₊ := hCount
    _ ≤ 4 * J * (Real.exp (4596 * ((h + 1 : ℕ) : ℝ)) * SmallSieveFinite.smallEuler ⌊u⌋₊) :=
      mul_le_mul_of_nonneg_left hEuler (by positivity)
    _ = _ := by ring

theorem small_upper (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℝ, 2 ≤ u₀ ∧
      ∀ (N : ℕ) (u J : ℝ) (residue : ℕ → ℕ), u₀ ≤ u → u ^ η ≤ J →
        |(N : ℝ) - J| ≤ 1 →
        ((LargePrimeDeletion.cutoffSurvivors N ⌊u⌋₊ residue).card : ℝ) ≤
          C * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  obtain ⟨h, hh⟩ := pow_unbounded_of_one_lt (960048 / η) (by norm_num : (1 : ℝ) < 2)
  have hscale : 960048 ≤ η * ((2 ^ h : ℕ) : ℝ) := by
    have hmul := (div_lt_iff₀ hη).mp hh
    push_cast
    nlinarith
  refine ⟨4 * Real.exp (4596 * ((h + 1 : ℕ) : ℝ)), by positivity,
    (2 : ℝ) ^ (2 ^ h : ℕ), threshold_ge_two h, ?_⟩
  intro N u J residue hu hJ hNJ
  exact small_upper_explicit N u J η residue h hscale hu hJ hNJ

theorem progression_small_upper (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ u₀ : ℝ, 2 ≤ u₀ ∧
      ∀ (N : ℕ) (u J : ℝ) (a : ℤ) (q : ℕ) (residue : ℕ → ℕ),
        u₀ ≤ u → u ^ η ≤ J → |(N : ℝ) - J| ≤ 1 →
        (∀ p : ℕ, p.Prime → (p : ℝ) ≤ u → q.Coprime p) →
        ((ProgressionSmallSieve.progressionSurvivors N ⌊u⌋₊ a q residue).card : ℝ) ≤
          C * J * SmallSieveFinite.smallEuler ⌊u⌋₊ := by
  obtain ⟨C, hC, u₀, hu₀, hBound⟩ := small_upper η hη
  refine ⟨C, hC, u₀, hu₀, ?_⟩
  intro N u J a q residue hu hJ hNJ hcop
  have hcopNat : ∀ p : ℕ, p.Prime → p ≤ ⌊u⌋₊ → q.Coprime p := by
    intro p hp hpu
    exact hcop p hp ((Nat.le_floor_iff (by linarith)).mp hpu)
  obtain ⟨transformed, hEq⟩ := ProgressionSmallSieve.exists_progressionSurvivors_eq N ⌊u⌋₊ a q residue hcopNat
  rw [hEq]
  exact hBound N u J transformed hu hJ hNJ

end NumberTheoryLean.SmallSieveUpper



namespace ErdosPrimeInputs.SubsetPrimeSieve

open Finset
open NumberTheoryLean
open SmallSieveFinite IntervalBoundingSieve

noncomputable def euler (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - (p : ℝ)⁻¹)

theorem finite_subset_sieve_bound (N : ℕ) (u s J : ℝ) (P : Finset ℕ) (residue : ℕ → ℕ)
    (hu : 2 ≤ u) (hs : 480024 ≤ s) (hJ : 0 ≤ J) (hNJ : |(N : ℝ) - J| ≤ 1)
    (hprime : ∀ p ∈ P, p.Prime) (hsize : ∀ p ∈ P, (p : ℝ) ≤ u) :
    |((residueAvoidingOffsets N (∏ p ∈ P, p) residue).card : ℝ) - J * euler P| ≤
      J * euler P * Real.exp (-s / 96) + 2 * u ^ s := by
  classical
  let D := ∏ p ∈ P, p
  have hD : Squarefree D := squarefree_primeSet_product P hprime
  obtain ⟨A,hA⟩ := exists_residue_count_translation N D (Nat.pos_of_ne_zero hD.ne_zero) residue
  have h := RealFundamentalSieve.fundamental_lemma (Finset.range N) (fun _ => (1 : ℝ))
    (fun _ _ => by norm_num) (fun p i => p ∣ A+i) u s P J (fun p => (p : ℝ)⁻¹)
    hu hs hJ hprime hsize (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun p _ => by simpa only [one_div] using
      div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) (Nat.cast_nonneg p))
    (fun _ => by norm_num)
  rw [survives_sum_eq_coprimeOffsets A N P hprime] at h
  change |((LargePrimeDeletion.coprimeOffsets N D (A : ℤ)).card : ℝ) - J * euler P| ≤ _ at h
  rw [← hA] at h
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _d ∈ RealFundamentalSieve.levelDivisors P u s, (2:ℝ) := by
      apply sum_le_sum
      intro d hd
      exact integerRemainder_abs_le_two A N D hD
        (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1) J hNJ
    _ = 2 * ((RealFundamentalSieve.levelDivisors P u s).card : ℝ) := by simp [mul_comm]
    _ ≤ 2 * u ^ s := mul_le_mul_of_nonneg_left (realLevelDivisors_card_le P u s (by linarith)) (by norm_num)

theorem euler_pos {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) : 0 < euler P := by
  apply prod_pos
  intro p hp
  have hp1 : (1:ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)

end ErdosPrimeInputs.SubsetPrimeSieve



namespace ErdosModulusRelative
open ErdosInverseHits ErdosInverseCounts NumberTheoryLean

theorem modulus_small_relative (w : ℝ) (Y d : ℕ) (a : ℕ → ℕ)
    (hw : 2 ≤ w) (hY : 0 < Y) (hd : Squarefree d)
    (hlarge : ∀ p ∈ d.primeFactors,w < (p : ℝ))
    (hv : 960048 ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w) :
    |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ)/
      (((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊)-1| ≤
        3*Real.exp (-(Real.log ((Y : ℝ)/(d : ℝ))/Real.log w)/192) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hb := primeHitRepresentative_spec d hd a
  have hJ : 0 < (Y : ℝ)/(d : ℝ) := by positivity
  have hN := hitLength_error Y d (primeHitRepresentative d hd a) hd0 hb.1 hb.2.1
  have hs := ProgressionSmallSieve.progression_small_relative
    (hitLength Y d (primeHitRepresentative d hd a)) w ((Y : ℝ)/(d : ℝ))
    (primeHitRepresentative d hd a : ℤ) d a hw hJ hN hv
    (large_modulus_coprime_small w d hd hlarge)
  rw [modulus_count_eq_offsets Y _ a d hd,offsets_eq_progression,Int.cast_natCast]
  exact hs

theorem uniform_modulus_small_relative (eps : ℝ) (heps : 0 < eps) :
    ∃ K0 w0 : ℝ,1 ≤ K0 ∧ 1 < w0 ∧ ∀ w : ℝ,w0 ≤ w →
      ∀ (Y d : ℕ) (a : ℕ → ℕ),0 < Y → 0 < d → Squarefree d →
        (∀ p ∈ d.primeFactors,w < (p : ℝ)) →
        K0 ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w →
        |(modulusCount Y (LargePrimeDeletion.cutoffPrimes ⌊w⌋₊) a d : ℝ)/
          (((Y : ℝ)/(d : ℝ))*SmallSieveFinite.smallEuler ⌊w⌋₊)-1| ≤ eps := by
  let K0 := max (960048 : ℝ) (-192*Real.log (eps/3))
  have hK : 960048 ≤ K0 := le_max_left _ _
  have hKe : -192*Real.log (eps/3) ≤ K0 := le_max_right _ _
  have hExp : 3*Real.exp (-K0/192) ≤ eps := by
    have hh : -K0/192 ≤ Real.log (eps/3) := by linarith
    have he := Real.exp_le_exp.mpr hh
    rw [Real.exp_log (by positivity : 0 < eps/3)] at he
    linarith
  refine ⟨K0,2,by linarith,by norm_num,?_⟩
  intro w hw Y d a hY _hdpos hd hlarge hv
  calc
    _ ≤ 3*Real.exp (-(Real.log ((Y : ℝ)/(d : ℝ))/Real.log w)/192) :=
      modulus_small_relative w Y d a hw hY hd hlarge (hK.trans hv)
    _ ≤ 3*Real.exp (-K0/192) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ _ := hExp

end ErdosModulusRelative



namespace ErdosInverseTail
open NumberTheoryLean

noncomputable def sieveTail (J N z : ℕ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  SievePartition.survivors (Finset.Ico J N) (LargePrimeDeletion.cutoffPrimes z)
    (ProgressionSmallSieve.progressionHit b step a)

theorem progressionHit_shift (J i t : ℕ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    ProgressionSmallSieve.progressionHit (b+(step : ℤ)*J) step a t i ↔
      ProgressionSmallSieve.progressionHit b step a t (J+i) := by
  unfold ProgressionSmallSieve.progressionHit
  have h : b+(step : ℤ)*J+(step : ℤ)*i = b+(step : ℤ)*(J+i) := by ring
  rw [h]
  simp only [Nat.cast_add]

theorem sieveTail_eq_image (J N z : ℕ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    sieveTail J N z b step a =
      (ProgressionSmallSieve.progressionSurvivors (N-J) z (b+(step : ℤ)*J) step a).image
        (fun i => J+i) := by
  classical
  ext j
  simp only [sieveTail,SievePartition.mem_survivors,Finset.mem_Ico,Finset.mem_image,
    ProgressionSmallSieve.progressionSurvivors,Finset.mem_range,progressionHit_shift]
  constructor
  · rintro ⟨⟨hJj,hjN⟩,ha⟩
    refine ⟨j-J,⟨by omega,?_⟩,Nat.add_sub_of_le hJj⟩
    simpa only [Nat.add_sub_of_le hJj] using ha
  · rintro ⟨i,⟨hi,ha⟩,rfl⟩
    exact ⟨⟨by omega,by omega⟩,ha⟩

theorem sieveTail_card (J N z : ℕ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    (sieveTail J N z b step a).card =
      (ProgressionSmallSieve.progressionSurvivors (N-J) z (b+(step : ℤ)*J) step a).card := by
  rw [sieveTail_eq_image,Finset.card_image_of_injective]
  exact fun _ _ h => Nat.add_left_cancel h

theorem survivor_card_split (J N z : ℕ) (hJN : J ≤ N) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    (ProgressionSmallSieve.progressionSurvivors N z b step a).card =
      (ProgressionSmallSieve.progressionSurvivors J z b step a).card+(sieveTail J N z b step a).card := by
  classical
  have hset : ProgressionSmallSieve.progressionSurvivors N z b step a =
      ProgressionSmallSieve.progressionSurvivors J z b step a ∪ sieveTail J N z b step a := by
    ext j
    simp only [ProgressionSmallSieve.progressionSurvivors,sieveTail,SievePartition.mem_survivors,
      Finset.mem_range,Finset.mem_Ico,Finset.mem_union]
    constructor
    · rintro ⟨hj,ha⟩
      by_cases hh : j < J
      · exact Or.inl ⟨hh,ha⟩
      · exact Or.inr ⟨⟨by omega,hj⟩,ha⟩
    · rintro (⟨hj,ha⟩ | ⟨⟨_,hj⟩,ha⟩)
      · exact ⟨lt_of_lt_of_le hj hJN,ha⟩
      · exact ⟨hj,ha⟩
  have hdis : Disjoint (ProgressionSmallSieve.progressionSurvivors J z b step a) (sieveTail J N z b step a) := by
    apply Finset.disjoint_left.mpr
    intro j hj ht
    have hjJ := Finset.mem_range.mp (SievePartition.mem_survivors.mp hj).1
    have hJj := (Finset.mem_Ico.mp (SievePartition.mem_survivors.mp ht).1).1
    omega
  rw [hset,Finset.card_union_of_disjoint hdis]

end ErdosInverseTail



namespace ErdosInverseTail
open NumberTheoryLean ErdosInverseHits

noncomputable def residueOffset (J u : ℕ) [NeZero u] (e : ZMod u) : ℕ := (e-(J : ZMod u)).val

theorem residueOffset_lt (J u : ℕ) [NeZero u] (e : ZMod u) : residueOffset J u e < u := ZMod.val_lt _

theorem residue_coordinate_exists (J j u : ℕ) [NeZero u] (e : ZMod u)
    (hJj : J ≤ j) (hje : (j : ZMod u) = e) :
    ∃ i : ℕ,j = J+residueOffset J u e+u*i := by
  have hc : ((j-J : ℕ) : ZMod u) = e-(J : ZMod u) := by rw [Nat.cast_sub hJj,hje]
  have hv := congrArg ZMod.val hc
  have hmod : (j-J)%u = residueOffset J u e := by simpa only [ZMod.val_natCast,residueOffset] using hv
  refine ⟨(j-J)/u,?_⟩
  have he := Nat.mod_add_div (j-J) u
  rw [hmod] at he
  omega

theorem residue_coordinate_hit (J u i : ℕ) [NeZero u] (e : ZMod u) :
    ((J+residueOffset J u e+u*i : ℕ) : ZMod u) = e := by
  simp only [Nat.cast_add,Nat.cast_mul,residueOffset,ZMod.natCast_zmod_val,ZMod.natCast_self,
    zero_mul,add_zero]
  ring

theorem progressionHit_stride (A i u t : ℕ) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    ProgressionSmallSieve.progressionHit (b+(step : ℤ)*A) (step*u) a t i ↔
      ProgressionSmallSieve.progressionHit b step a t (A+u*i) := by
  unfold ProgressionSmallSieve.progressionHit
  have he : b+(step : ℤ)*A+((step*u : ℕ) : ℤ)*i = b+(step : ℤ)*(A+u*i) := by push_cast;ring
  rw [he]
  simp only [Nat.cast_add,Nat.cast_mul]

theorem residue_tail_eq_image (J N z u : ℕ) [NeZero u] (e : ZMod u)
    (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    (sieveTail J N z b step a).filter (fun j : ℕ => (j : ZMod u) = e) =
      (ProgressionSmallSieve.progressionSurvivors (hitLength (N-J) u (residueOffset J u e+1)) z
        (b+(step : ℤ)*((J+residueOffset J u e : ℕ) : ℤ)) (step*u) a).image
          (fun i => J+residueOffset J u e+u*i) := by
  classical
  have hu : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  have hr := residueOffset_lt J u e
  have hlen : ∀ i : ℕ,i < hitLength (N-J) u (residueOffset J u e+1) ↔
      residueOffset J u e+u*i < N-J := by
    intro i
    rw [lt_hitLength_iff (N-J) u _ i hu (by omega)]
    omega
  ext j
  simp only [Finset.mem_filter,sieveTail,SievePartition.mem_survivors,Finset.mem_Ico,
    Finset.mem_image,ProgressionSmallSieve.progressionSurvivors,Finset.mem_range,
    progressionHit_stride,hlen]
  constructor
  · rintro ⟨⟨⟨hJj,hjN⟩,ha⟩,hje⟩
    obtain ⟨i,rfl⟩ := residue_coordinate_exists J j u e hJj hje
    exact ⟨i,⟨by omega,ha⟩,rfl⟩
  · rintro ⟨i,⟨hi,ha⟩,rfl⟩
    exact ⟨⟨⟨by omega,by omega⟩,ha⟩,residue_coordinate_hit J u i e⟩

theorem residue_tail_card (J N z u : ℕ) [NeZero u] (e : ZMod u)
    (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    ((sieveTail J N z b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card =
      (ProgressionSmallSieve.progressionSurvivors (hitLength (N-J) u (residueOffset J u e+1)) z
        (b+(step : ℤ)*((J+residueOffset J u e : ℕ) : ℤ)) (step*u) a).card := by
  rw [residue_tail_eq_image,Finset.card_image_of_injective]
  intro i j hij
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne u)) (Nat.add_left_cancel hij)

end ErdosInverseTail



namespace ErdosInverseTail
open NumberTheoryLean

theorem residue_survivor_card_split (J N z u : ℕ) [NeZero u] (hJN : J ≤ N)
    (e : ZMod u) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    ((ProgressionSmallSieve.progressionSurvivors N z b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card =
      ((ProgressionSmallSieve.progressionSurvivors J z b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card+
        ((sieveTail J N z b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card := by
  classical
  have hset : (ProgressionSmallSieve.progressionSurvivors N z b step a).filter (fun j : ℕ => (j : ZMod u) = e) =
      (ProgressionSmallSieve.progressionSurvivors J z b step a).filter (fun j : ℕ => (j : ZMod u) = e) ∪
        (sieveTail J N z b step a).filter (fun j : ℕ => (j : ZMod u) = e) := by
    ext j
    simp only [Finset.mem_filter,ProgressionSmallSieve.progressionSurvivors,sieveTail,
      SievePartition.mem_survivors,Finset.mem_range,Finset.mem_Ico,Finset.mem_union]
    constructor
    · rintro ⟨⟨hj,ha⟩,he⟩
      by_cases hh : j < J
      · exact Or.inl ⟨⟨hh,ha⟩,he⟩
      · exact Or.inr ⟨⟨⟨by omega,hj⟩,ha⟩,he⟩
    · rintro (⟨⟨hj,ha⟩,he⟩ | ⟨⟨⟨_,hj⟩,ha⟩,he⟩)
      · exact ⟨⟨lt_of_lt_of_le hj hJN,ha⟩,he⟩
      · exact ⟨⟨hj,ha⟩,he⟩
  rw [hset,Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro j hj ht
  have hjJ := Finset.mem_range.mp (SievePartition.mem_survivors.mp (Finset.mem_filter.mp hj).1).1
  have hJj := (Finset.mem_Ico.mp (SievePartition.mem_survivors.mp (Finset.mem_filter.mp ht).1).1).1
  omega

theorem residue_count_difference (J N z u : ℕ) [NeZero u] (hJN : J ≤ N)
    (e : ZMod u) (b : ℤ) (step : ℕ) (a : ℕ → ℕ) :
    |(((ProgressionSmallSieve.progressionSurvivors N z b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card : ℝ)-
      (((ProgressionSmallSieve.progressionSurvivors J z b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card : ℝ)| =
      ((sieveTail J N z b step a).filter (fun j : ℕ => (j : ZMod u) = e)).card := by
  rw [residue_survivor_card_split J N z u hJN e b step a,Nat.cast_add,add_sub_cancel_left,
    abs_of_nonneg (Nat.cast_nonneg _)]

end ErdosInverseTail


end Erdos970

end OAI
