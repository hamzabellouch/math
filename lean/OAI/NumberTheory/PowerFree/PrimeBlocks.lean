import OAI.NumberTheory.PowerFree.AdaptiveRanks

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

theorem product_distinct_prime_divisors_le (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (hd : ∀ p ∈ P, (p : ℤ) ∣ a) :
    (∏ p ∈ P, (p : ℝ)) ≤ |(a : ℝ)| := by
  have hn : a.natAbs ≠ 0 := (Int.natAbs_pos.mpr ha).ne'
  have hs : P ⊆ a.natAbs.primeFactors := by
    intro p h
    exact Nat.mem_primeFactors.mpr ⟨hp p h,
      by simpa using Int.natAbs_dvd_natAbs.mpr (hd p h), hn⟩
  have hh := Nat.le_of_dvd (Int.natAbs_pos.mpr ha)
    ((Finset.prod_dvd_prod_of_subset P a.natAbs.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd a.natAbs))
  have he : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [← he, ← Nat.cast_prod]
  exact_mod_cast hh

theorem card_large_prime_divisors_le (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (hd : ∀ p ∈ P, (p : ℤ) ∣ a)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X ^ ζ ≤ (p : ℝ)) (hlarge : |(a : ℝ)| ≤ X ^ B) :
    (P.card : ℝ) ≤ B / ζ := by
  have hx : 0 ≤ X := (zero_lt_one.trans hX).le
  have h : X ^ (ζ * (P.card : ℝ)) ≤ X ^ B := by
    rw [Real.rpow_mul hx, Real.rpow_natCast]
    calc
      (X ^ ζ) ^ P.card = ∏ _p ∈ P, X ^ ζ := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => (Real.rpow_pos_of_pos (zero_lt_one.trans hX) ζ).le) hsmall
      _ ≤ |(a : ℝ)| := product_distinct_prime_divisors_le a ha P hp hd
      _ ≤ X ^ B := hlarge
  rw [le_div_iff₀ hζ]
  simpa [mul_comm] using (Real.rpow_le_rpow_left_iff hX).mp h

theorem card_large_prime_divisors_le_floor (a : ℤ) (ha : a ≠ 0)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (hd : ∀ p ∈ P, (p : ℤ) ∣ a)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X ^ ζ ≤ (p : ℝ)) (hlarge : |(a : ℝ)| ≤ X ^ B) :
    P.card ≤ ⌊B / ζ⌋₊ :=
  Nat.le_floor (card_large_prime_divisors_le a ha P hp hd X ζ B hX hζ hsmall hlarge)

open scoped BigOperators

def cellKernel {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (ev : ι → V →ₗ[K] K) (S : Set ι) : Submodule K V :=
  ⨅ i ∈ S, LinearMap.ker (ev i)

theorem cellKernel_mono {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (ev : ι → V →ₗ[K] K) {S T : Set ι} (h : S ⊆ T) :
    cellKernel ev T ≤ cellKernel ev S := by
  intro v hv
  simp only [cellKernel, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
  exact fun i hi => hv i (h hi)

theorem adaptiveStates_length {K V σ α : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : ℕ → σ → α → Submodule K V) (next : ℕ → σ → Submodule K V → σ)
    (n i : ℕ) (s : σ) (a : α) : (adaptiveStates W next n i s a).length = n+1 := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [adaptiveStates, List.length_cons, ih]

theorem list_minor_product_bound {σ : Type*} (l : List σ) (minor : σ → ℤ)
    (X B : ℝ) (hX : 0 < X)
    (hminor : ∀ s ∈ l, minor s ≠ 0 ∧ |(minor s : ℝ)| ≤ X^B) :
    (l.map minor).prod ≠ 0 ∧ |(((l.map minor).prod : ℤ) : ℝ)| ≤ X^(B*(l.length : ℝ)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hminor x (by simp)
    have ht := ih (fun s hs => hminor s (by simp [hs]))
    constructor
    · simpa only [List.map_cons, List.prod_cons] using mul_ne_zero hx.1 ht.1
    · simp only [List.map_cons, List.prod_cons, Int.cast_mul, abs_mul,
        List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one,
        Real.rpow_add hX]
      exact (mul_le_mul hx.2 ht.2 (abs_nonneg _) (Real.rpow_nonneg hX.le _)).trans_eq (mul_comm _ _)

theorem adaptive_deletion_bound {K V σ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V]
    (W : ℕ → σ → Finset ℕ → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ)
    (hW : ∀ i s A B, A ⊆ B → W i s A ≤ W i s B)
    (minor : σ → ℤ) (n : ℕ) (s : σ)
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime)
    (X ζ B : ℝ) (hX : 1 < X) (hζ : 0 < ζ)
    (hsmall : ∀ p ∈ P, X^ζ ≤ (p : ℝ))
    (hminor : ∀ A ⊆ P, ∀ t ∈ adaptiveStates W next n 0 s A,
      minor t ≠ 0 ∧ |(minor t : ℝ)| ≤ X^B)
    (ell T : ℕ) (hT : 0 < T) (hsize : ell+T < P.card) :
    let bad := fun A => P.filter fun p : ℕ =>
      (p : ℤ) ∣ ((adaptiveStates W next n 0 s A).map minor).prod
    (∑ j ∈ Finset.range T, badFraction P (ell+j+1) bad) / (T : ℝ) ≤
      (((Module.finrank K V+1)^n : ℕ) : ℝ) / T +
      (⌊(B*(n+1:ℕ))/ζ⌋₊ : ℝ) / ((P.card : ℝ) - (ell+T)) := by
  classical
  intro bad
  let R := fun A => adaptiveCode W next n 0 s A
  apply deletion_average_bound P ell T hT hsize R bad
    ((Module.finrank K V+1)^n) ⌊(B*(n+1:ℕ))/ζ⌋₊
  · intro A _
    exact (adaptiveCode_lt W next n 0 s A).le
  · intro A _ q _
    exact (adaptiveCode_mono_stable W next (A.erase q) A
      (fun i s => hW i s _ _ (Finset.erase_subset _ _)) n 0 s).1
  · intro A _ q _ he
    have hs := (adaptiveCode_mono_stable W next (A.erase q) A
      (fun i s => hW i s _ _ (Finset.erase_subset _ _)) n 0 s).2 he
    dsimp [bad]
    rw [hs]
  · intro A hAP
    let l := adaptiveStates W next n 0 s A
    have hb := list_minor_product_bound l minor X B (zero_lt_one.trans hX) (hminor A hAP)
    have hl : l.length = n+1 := adaptiveStates_length W next n 0 s A
    have hin : P ∩ bad A = bad A := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hin]
    apply card_large_prime_divisors_le_floor _ hb.1 _
      (fun p h => hp p (Finset.mem_filter.mp h).1)
      (fun _ h => (Finset.mem_filter.mp h).2) X ζ (B*(n+1:ℕ)) hX hζ
      (fun p h => hsmall p (Finset.mem_filter.mp h).1)
    simpa only [hl] using hb.2

open scoped BigOperators

def BlockSample (P : Finset ℕ) (ell T : ℕ) :=
  Σ j : Fin T, (P.powersetCard (ell+j.val+1))

noncomputable instance (P : Finset ℕ) (ell T : ℕ) : Fintype (BlockSample P ell T) :=
  inferInstanceAs (Fintype (Σ j : Fin T, (P.powersetCard (ell+j.val+1))))

noncomputable def blockWeight (P : Finset ℕ) (ell T : ℕ)
    (a : BlockSample P ell T) : ℝ :=
  ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹

def blockSet {P : Finset ℕ} {ell T : ℕ} (a : BlockSample P ell T) : Finset ℕ :=
  a.2.val

theorem blockSet_spec {P : Finset ℕ} {ell T : ℕ} (a : BlockSample P ell T) :
    blockSet a ⊆ P ∧ (blockSet a).card = ell+a.1.val+1 :=
  Finset.mem_powersetCard.mp a.2.property

theorem blockWeight_nonneg (P : Finset ℕ) (ell T : ℕ)
    (a : BlockSample P ell T) : 0 ≤ blockWeight P ell T a := by
  unfold blockWeight
  positivity

theorem blockWeight_sum (P : Finset ℕ) (ell T : ℕ)
    (hT : 0 < T) (hsize : ell+T ≤ P.card) :
    ∑ a : BlockSample P ell T, blockWeight P ell T a = 1 := by
  classical
  change (∑ a : Σ j : Fin T, (P.powersetCard (ell+j.val+1)),
    ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹) = 1
  rw [Fintype.sum_sigma]
  have he (j : Fin T) :
      (∑ _a : (P.powersetCard (ell+j.val+1)),
        ((T : ℝ) * ((P.powersetCard (ell+j.val+1)).card : ℝ))⁻¹) = (T : ℝ)⁻¹ := by
    have hc : 0 < (P.powersetCard (ell+j.val+1)).card :=
      Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr (by omega))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    field_simp
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hT.ne')

theorem blockWeight_bad_average (P : Finset ℕ) (ell T : ℕ)
    (bad : Finset ℕ → Finset ℕ) :
    (∑ a : BlockSample P ell T, blockWeight P ell T a *
      ((∑ q ∈ blockSet a, if q ∈ bad (blockSet a) then (1 : ℝ) else 0) /
        (blockSet a).card)) =
      (∑ j ∈ Finset.range T, badFraction P (ell+j+1) bad) / T := by
  classical
  change (∑ a : Σ j : Fin T, (P.powersetCard (ell+j.val+1)),
    ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹ *
      ((∑ q ∈ a.2.val, if q ∈ bad a.2.val then (1 : ℝ) else 0) / a.2.val.card)) = _
  rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [badFraction]
  rw [Finset.sum_coe_sort (P.powersetCard (ell+j.val+1))
    (fun S : Finset ℕ => ((T : ℝ) * ((P.powersetCard (ell+j.val+1)).card : ℝ))⁻¹ *
      ((∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) / S.card)),
    Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_powersetCard.mp ha).2]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem independent_average_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1) (i : ι)
    (F : (∀ j, Ω j) → ℝ) (C : ℝ)
    (hF : ∀ x, (∑ a, w i a * F (Function.update x i a)) ≤ C) :
    (∑ x, (∏ j, w j (x j)) * F x) ≤ C := by
  classical
  let E := Equiv.piSplitAt i Ω
  let W : (∀ j : {j // j ≠ i}, Ω j) → ℝ := fun x => ∏ j : {j // j ≠ i}, w j.val (x j)
  have hs : ∑ x, W x = 1 := by
    rw [show (∑ x, W x) = ∑ x : (∀ j : {j // j ≠ i}, Ω j), ∏ j : {j // j ≠ i}, w j.val (x j) from rfl, ← Fintype.prod_sum]
    simp only [hsum, Finset.prod_const_one]
  have hwE (x : ∀ j, Ω j) : (∏ j, w j (x j)) = w i (x i) * W (E x).2 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w j (x j)) (Finset.mem_univ i)]
    congr 1
    exact Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp) (fun j => w j (x j))
  have hE (x : (∀ j : {j // j ≠ i}, Ω j)) (a b : Ω i) :
      Function.update (E.symm (a,x)) i b = E.symm (b,x) := by
    funext j
    by_cases h : j = i
    · subst j; simp [E, Equiv.piSplitAt]
    · simp [E, Equiv.piSplitAt, h]
  have hEq : (∑ x, (∏ j, w j (x j)) * F x) =
      ∑ x, W x * (∑ a, w i a * F (E.symm (a,x))) := by
    rw [Fintype.sum_equiv E _ (fun z => w i z.1 * W z.2 * F (E.symm z))]
    · rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    · intro x
      rw [hwE, E.symm_apply_apply]
      rfl
  rw [hEq]
  have hFin (x : ∀ j : {j // j ≠ i}, Ω j) :
      (∑ a, w i a * F (E.symm (a,x))) ≤ C := by
    by_cases h : Nonempty (Ω i)
    · obtain ⟨a⟩ := h
      simpa only [hE] using hF (E.symm (a,x))
    · have := not_nonempty_iff.mp h
      have hz := hsum i
      simp at hz
  calc
    _ ≤ ∑ x, W x * C := Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_left (hFin x) (Finset.prod_nonneg fun j _ => hw j.val (x j))
    _ = C := by rw [← Finset.sum_mul, hs, one_mul]

theorem exists_many_regular {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1)
    (bad : Ω → ι → Prop) [DecidableRel bad]
    (η : ℝ) (hbad : ∀ z, (∑ a, w a * if bad a z then (1 : ℝ) else 0) ≤ η) :
    ∃ a : Ω, ((Finset.univ.filter fun z => ¬ bad a z).card : ℝ) ≥
      (1-η) * Fintype.card ι := by
  classical
  have havg : (∑ a, w a * ((Finset.univ.filter fun z => bad a z).card : ℝ)) ≤
      η * Fintype.card ι := by
    simp_rw [← Finset.sum_boole, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum fun z _ => hbad z).trans_eq (by simp; ring)
  have hex : ∃ a : Ω, ((Finset.univ.filter fun z => bad a z).card : ℝ) ≤ η * Fintype.card ι := by
    by_contra h
    push Not at h
    have hp : ∃ a, 0 < w a := by
      by_contra h0
      push Not at h0
      have hz : ∀ a, w a = 0 := fun a => le_antisymm (h0 a) (hw a)
      simp [hz] at hsum
    obtain ⟨a,ha⟩ := hp
    have hlt : (∑ b, w b * (η * Fintype.card ι)) <
        ∑ b, w b * ((Finset.univ.filter fun z => bad b z).card : ℝ) := by
      apply Finset.sum_lt_sum
      · intro b _
        exact mul_le_mul_of_nonneg_left (h b).le (hw b)
      · exact ⟨a,Finset.mem_univ _,mul_lt_mul_of_pos_left (h a) ha⟩
    rw [← Finset.sum_mul,hsum,one_mul] at hlt
    linarith
  obtain ⟨a,ha⟩ := hex
  refine ⟨a,?_⟩
  have hc : (Finset.univ.filter fun z => bad a z).card +
      (Finset.univ.filter fun z => ¬ bad a z).card = Fintype.card ι := by
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun z => bad a z)
  have hcr : ((Finset.univ.filter fun z => bad a z).card : ℝ) +
      ((Finset.univ.filter fun z => ¬ bad a z).card : ℝ) = Fintype.card ι := by exact_mod_cast hc
  linarith

theorem bad_blocks_indicator_le {r : ℕ} (b : Fin r → ℝ) (hb : ∀ i, 0 ≤ b i)
    (ξ : ℝ) (hξ : 0 < ξ) :
    (if ∃ i, ξ < b i then (1 : ℝ) else 0) ≤ (∑ i, b i) / ξ := by
  classical
  split_ifs with h
  · obtain ⟨i,hi⟩ := h
    rw [le_div_iff₀ hξ, one_mul]
    exact hi.le.trans (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i))
  · exact div_nonneg (Finset.sum_nonneg fun i _ => hb i) hξ.le

end QuarticPowerFree

end OAI
