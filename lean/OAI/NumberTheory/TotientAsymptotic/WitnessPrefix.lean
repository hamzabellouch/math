import OAI.NumberTheory.TotientAsymptotic.RemainderSplit

namespace OAI

/-! The exact banded, perturbed regions represented by the arithmetic fibers. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def PrefixPrimeBands (x : ℝ) (H : ℕ) (p : Fin (R x H) → ℕ) : Prop :=
  ∀ i, (p i).Prime ∧ (9/10 : ℝ)*bandScale x (i.val+1) ≤ primePrefixCoord p i ∧
    primePrefixCoord p i ≤ (11/10 : ℝ)*bandScale x (i.val+1)

lemma attachTail_prefix_coord {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    (p : Fin (R x H) → ℕ) (η : TailDatum H) (i : Fin (R x H)) :
    remainderCoord x (attachTail x H p η) (i.val+1) = primePrefixCoord p i := by
  simp only [remainderCoord, Nat.add_one_ne_zero, ite_false,
    attachTail_prefix hPH, primePrefixCoord]

lemma attachTail_tail_prime {x s : ℝ} {H i : ℕ} (_hPH : P H < H) (_hHm : H ≤ m x)
    (p : Fin (R x H) → ℕ) {η : TailDatum H} (_hη : IsWitness H s η)
    (hi : i ∈ Finset.Icc (R x H+1) (L x H)) :
    remainderPrime (attachTail x H p η) i = tailPrime η (m x-i) := by
  have hi' := Finset.mem_Icc.mp hi
  have hiL : i ∈ Finset.Icc 1 (L x H) := Finset.mem_Icc.mpr (by omega)
  rw [remainderPrime_attachTail p η hiL, dite_eq_right (by omega)]

lemma attachTail_tail_coord {x s : ℝ} {H i : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (p : Fin (R x H) → ℕ) {η : TailDatum H} (hη : IsWitness H s η)
    (hi : i ∈ Finset.Icc (R x H+1) (L x H)) :
    remainderCoord x (attachTail x H p η) i = tailLog η (m x-i) := by
  have hi' := Finset.mem_Icc.mp hi
  simp only [remainderCoord, ite_eq_right (by omega : i ≠ 0),
    attachTail_tail_prime hPH hHm p hη hi, tailLog]

lemma attachTail_tail_basic {x : ℝ} {H : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (p : Fin (R x H) → ℕ) {η : TailDatum H} (hη : IsWitness H (theta x) η) :
    (∀ i ∈ Finset.Icc (R x H+1) (L x H),
      (remainderPrime (attachTail x H p η) i).Prime ∧
      (9/10 : ℝ)*bandScale x i ≤ remainderCoord x (attachTail x H p η) i ∧
      remainderCoord x (attachTail x H p η) i ≤ (11/10 : ℝ)*bandScale x i) ∧
    (∀ i ∈ Finset.Icc (R x H+1) (L x H),
      (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x (attachTail x H p η) r) ≤
      (if i = L x H then 1 else xi x i)*remainderCoord x (attachTail x H p η) i) := by
  have hh {i : ℕ} (hi : i ∈ Finset.Icc (R x H+1) (L x H)) :
      m x-i ∈ Finset.Ico (P H) H := by
    have hi' := Finset.mem_Icc.mp hi
    apply Finset.mem_Ico.mpr
    unfold R L at hi'
    omega
  have him {i : ℕ} (hi : i ∈ Finset.Icc (R x H+1) (L x H)) : i ≤ m x :=
    (Finset.mem_Icc.mp hi).2.trans (Nat.sub_le _ _)
  constructor
  · intro i hi
    have hp := hη.2.2.1 (m x-i) (hh hi)
    have hb : bandScale x i = alpha (theta x)*(m x-i : ℕ)*(rho^(m x-i))⁻¹ := rfl
    rw [attachTail_tail_prime hPH hHm p hη hi, attachTail_tail_coord hPH hHm p hη hi, hb]
    exact ⟨hp.1, by simpa only [mul_assoc] using hp.2.1,
      by simpa only [mul_assoc] using hp.2.2.1⟩
  · intro i hi
    have ht := hη.2.2.1 (m x-i) (hh hi)
    have he := extractTail_threshold (attachTail x H p η) hHm
      (Finset.mem_Ico.mp (hh hi)).1 (Finset.mem_Ico.mp (hh hi)).2.le
    rw [extract_attachTail hPH hHm p hη, Nat.sub_sub_self (him hi)] at he
    rw [← he, attachTail_tail_coord hPH hHm p hη hi]
    by_cases hiL : i = L x H
    · subst i
      have hP : m x-L x H = P H := by unfold L; omega
      simp only [ite_true, hP, Finset.Ico_self, Finset.sum_empty, one_mul]
      have hp := hη.2.2.1 (P H) (Finset.mem_Ico.mpr ⟨le_rfl, hPH⟩)
      have ha := alpha_pos (theta x)
      have hr := pow_pos rho_pos (P H)
      exact (by positivity : (0 : ℝ) ≤ (9/10 : ℝ)*alpha (theta x)*(P H)*(rho^(P H))⁻¹).trans hp.2.1
    · rw [ite_eq_right hiL]
      exact ht.2.2.2

lemma attachTail_cofactor_basic {x : ℝ} {H : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (p : Fin (R x H) → ℕ) {η : TailDatum H} (hη : IsWitness H (theta x) η) :
    largestPrimeFactor (attachTail x H p η).cofactor ≤
        remainderPrime (attachTail x H p η) (L x H) ∧
      Real.log ((attachTail x H p η).cofactor : ℝ) ≤ Real.exp (2*bandScale x (L x H)) := by
  have hRL : R x H < L x H := by unfold R L; omega
  have hLP : m x-L x H = P H := by unfold L; omega
  have hi : L x H ∈ Finset.Icc (R x H+1) (L x H) := Finset.mem_Icc.mpr (by omega)
  rw [attachTail_tail_prime hPH hHm p hη hi, hLP]
  exact ⟨hη.2.2.2.1, by simpa only [attachTail, bandScale, hLP, mul_assoc] using hη.2.2.2.2⟩

lemma attachTail_prefix_sum {x s : ℝ} {H i : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (p : Fin (R x H) → ℕ) {η : TailDatum H} (hη : IsWitness H s η) (hi : i ≤ R x H) :
    (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x (attachTail x H p η) r) =
      (∑ j : Fin (R x H), if i < j.val+1 then a (j.val+1-i)*primePrefixCoord p j else 0) +
      D (m x-i) η := by
  rw [remainder_sum_prefix_tail _ hPH.le hHm hi, extract_attachTail hPH hHm p hη]
  simp only [attachTail_prefix_coord hPH.le]

theorem basic_attach_iff_region {x : ℝ} {H : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (p : Fin (R x H) → ℕ) {η : TailDatum H} (hη : IsWitness H (theta x) η) :
    IsBasicRemainder x H (attachTail x H p η) ↔
      PrefixPrimeBands x H p ∧ primePrefixCoord p ∈ perturbedTailPrefixRegion x H η := by
  have hRL : R x H < L x H := by unfold R L; omega
  constructor
  · intro hb
    constructor
    · intro i
      have hi : i.val+1 ∈ Finset.Icc 1 (L x H) :=
        Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
      simpa only [attachTail_prefix hPH.le, attachTail_prefix_coord hPH.le] using hb.2.1 _ hi
    · have hh := basic_remainder_mem_perturbed hb hPH hHm
      rw [extract_attachTail hPH hHm p hη] at hh
      have he : (fun i : Fin (R x H) => remainderPrime (attachTail x H p η) (i.val+1)) = p :=
        funext (attachTail_prefix hPH.le p η)
      rwa [he] at hh
  · rintro ⟨hb, hu⟩
    have htail := attachTail_tail_basic hPH hHm p hη
    refine ⟨hη.2.1, ?_, ?_, attachTail_cofactor_basic hPH hHm p hη⟩
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      by_cases hiR : i ≤ R x H
      · let j : Fin (R x H) := ⟨i-1, by omega⟩
        have he : j.val+1 = i := by dsimp [j]; omega
        have hh := hb j
        simpa only [← he, attachTail_prefix hPH.le, attachTail_prefix_coord hPH.le] using hh
      · exact htail.1 i (Finset.mem_Icc.mpr (by omega))
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      by_cases hiR : i ≤ R x H
      · rw [attachTail_prefix_sum hPH hHm p hη hiR,
          ite_eq_right (by omega : i ≠ L x H)]
        by_cases hi0 : i = 0
        · subst i
          simp only [Nat.zero_lt_succ, ite_true, Nat.sub_zero, remainderCoord, ite_true]
          exact le_sub_iff_add_le.mp hu.2
        · let j : Fin (R x H) := ⟨i-1, by omega⟩
          have he : j.val+1 = i := by dsimp [j]; omega
          rw [← he, attachTail_prefix_coord hPH.le]
          have ht := hu.1 j
          rw [prefixLinear_apply] at ht
          have hs : (∑ k : Fin (R x H), if j.val+1 < k.val+1 then
              a (k.val+1-(j.val+1))*primePrefixCoord p k else 0) =
              ∑ k : Fin (R x H), if j < k then a (k.val-j.val)*primePrefixCoord p k else 0 := by
            simp only [Nat.add_lt_add_iff_right, Nat.add_sub_add_right, Fin.lt_def]
          rw [hs]
          nlinarith
      · exact htail.2 i (Finset.mem_Icc.mpr (by omega))

/-- Membership in the arithmetic fiber is precisely the banded union of the
manuscript's perturbed prefix regions. Witness multiplicities disappear. -/
theorem prefixDatum_iff_banded_region {x : ℝ} {H d : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (p : Fin (R x H) → ℕ) :
    IsPrefixDatum x H ⟨p,d⟩ ↔ PrefixPrimeBands x H p ∧
      ∃ η ∈ witnesses H (theta x) d, primePrefixCoord p ∈ perturbedTailPrefixRegion x H η := by
  rw [prefixDatum_iff_attach_witness hPH hHm]
  constructor
  · rintro ⟨η, hη, hb⟩
    have hh := (basic_attach_iff_region hPH hHm p hη.1).mp hb
    exact ⟨hh.1, η, hη, hh.2⟩
  · rintro ⟨hb, η, hη, hu⟩
    exact ⟨η, hη, (basic_attach_iff_region hPH hHm p hη.1).mpr ⟨hb, hu⟩⟩

end TotientAsymptotic

end

end OAI
