import Mathlib
import OAI.Geometry.NilpotentCharts.Main

namespace OAI



 
 

section
 

 

noncomputable section
namespace BooleanRough
open Finset
open scoped BigOperators

variable {α K : Type*} [DecidableEq α]

def Raise [AddCommMonoid K] (f : Finset α → K) (S : Finset α) : K :=
  ∑ i ∈ S, f (S.erase i)

 
lemma sum_raise_rank [AddCommMonoid K] (S : Finset α) (k : ℕ)
    (f : Finset α → K) :
    (∑ T ∈ S.powersetCard (k+1), Raise f T) =
      (S.card-k) • (∑ U ∈ S.powersetCard k, f U) := by
  unfold Raise
  rw [Finset.sum_sigma']
  calc
    _ = ∑ p ∈ (S.powersetCard k).sigma (fun U => S \ U), f p.1 := by
      apply Finset.sum_bij'
        (fun p _ => (⟨p.1.erase p.2, p.2⟩ : (U : Finset α) × α))
        (fun p _ => (⟨insert p.2 p.1, p.2⟩ : (U : Finset α) × α))
      · intro p hp
        obtain ⟨hT, hi⟩ := Finset.mem_sigma.mp hp
        obtain ⟨hTS, hTk⟩ := Finset.mem_powersetCard.mp hT
        apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨(erase_subset _ _).trans hTS, ?_⟩, ?_⟩
        · rw [card_erase_of_mem hi, hTk]; omega
        · exact mem_sdiff.mpr ⟨hTS hi, notMem_erase _ _⟩
      · intro p hp
        obtain ⟨hU, hi⟩ := Finset.mem_sigma.mp hp
        obtain ⟨hUS, hUk⟩ := Finset.mem_powersetCard.mp hU
        obtain ⟨hiS, hiU⟩ := mem_sdiff.mp hi
        apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨insert_subset hiS hUS, ?_⟩, mem_insert_self _ _⟩
        rw [card_insert_of_notMem hiU, hUk]
      · intro p hp
        have hi := (Finset.mem_sigma.mp hp).2
        exact Sigma.ext (insert_erase hi) (heq_of_eq rfl)
      · intro p hp
        have hi := (mem_sdiff.mp (Finset.mem_sigma.mp hp).2).2
        exact Sigma.ext (erase_insert hi) (heq_of_eq rfl)
      · intro p hp
        rfl
    _ = ∑ U ∈ S.powersetCard k, (S.card-k) • f U := by
      rw [← Finset.sum_sigma' (S.powersetCard k) (fun U => S \ U) (fun U (_ : α) => f U)]
      apply sum_congr rfl
      intro U hU
      obtain ⟨hUS, hUk⟩ := mem_powersetCard.mp hU
      rw [sum_const, card_sdiff_of_subset hUS, hUk]
    _ = _ := Finset.smul_sum.symm

lemma sum_raise_rank_zero [Fintype α] [Field K] (k : ℕ)
    (hchar : ∀ j : ℕ, 0 < j → j ≤ Fintype.card α → (j : K) ≠ 0)
    (f : Finset α → K) (hu : ∀ S, Raise f S = 0)
    (S : Finset α) (hS : k < S.card) :
    (∑ T ∈ S.powersetCard k, f T) = 0 := by
  have he := sum_raise_rank S k f
  have hz : (∑ T ∈ S.powersetCard (k+1), Raise f T) = 0 :=
    sum_eq_zero (fun T _ => hu T)
  rw [hz, nsmul_eq_mul] at he
  have hne : ((S.card-k : ℕ) : K) ≠ 0 :=
    hchar _ (Nat.sub_pos_of_lt hS) ((Nat.sub_le _ _).trans (card_le_univ _))
  exact (mul_eq_zero.mp he.symm).resolve_left hne

 
lemma alternating_powerset [Ring K] (S : Finset α) :
    (∑ T ∈ S.powerset, (-1 : K)^T.card) = if S = ∅ then 1 else 0 := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := S)
  have hc := congrArg (Int.castRingHom K) h
  simpa only [map_sum, map_pow, map_neg, map_one, map_zero, apply_ite] using hc

lemma powerset_sdiff_filter [Fintype α] (C : Finset α) :
    (univ \ C).powerset = univ.powerset.filter (fun T : Finset α => Disjoint T C) := by
  ext T
  simp only [mem_powerset, mem_filter, subset_univ, true_and]
  simp only [subset_sdiff, subset_univ, true_and, disjoint_left]

 
lemma complement_mobius [Fintype α] [CommRing K]
    (f : Finset α → K) (A : Finset α) :
    (∑ C ∈ A.powerset, (-1 : K)^C.card * ∑ T ∈ (univ \ C).powerset, f T) =
      ∑ T ∈ univ.powerset, if A ⊆ T then f T else 0 := by
  simp_rw [powerset_sdiff_filter, sum_filter, mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  have he : (∑ C ∈ A.powerset, if Disjoint T C then (-1 : K)^C.card * f T else 0) =
      (∑ C ∈ (A \ T).powerset, (-1 : K)^C.card) * f T := by
    rw [sum_mul, ← sum_filter]
    apply sum_congr
    · ext C
      simp only [mem_filter, mem_powerset, subset_sdiff]
      constructor
      · rintro ⟨hCA, hd⟩
        exact ⟨hCA, hd.symm⟩
      · rintro ⟨hCA, hd⟩
        exact ⟨hCA, hd.symm⟩
    · intro C hC; rfl
  rw [he, alternating_powerset]
  by_cases hAT : A ⊆ T
  · simp [sdiff_eq_empty_iff_subset.mpr hAT, hAT]
  · simp [sdiff_eq_empty_iff_subset, hAT]

 
theorem raise_injective_below_middle [Fintype α] [Field K]
    (k : ℕ) (hk : 2*k < Fintype.card α)
    (hchar : ∀ j : ℕ, 0 < j → j ≤ Fintype.card α → (j : K) ≠ 0)
    (f : Finset α → K) (hf : ∀ S, S.card ≠ k → f S = 0)
    (hu : ∀ S, Raise f S = 0) : f = 0 := by
  funext A
  change f A = 0
  by_cases hAk : A.card = k
  · have hFzero (C : Finset α) (hC : C ⊆ A) :
        (∑ T ∈ (univ \ C).powerset, f T) = 0 := by
      have hCk : C.card ≤ k := hAk ▸ card_le_card hC
      have hlarge : k < (univ \ C).card := by
        rw [card_sdiff_of_subset (subset_univ _), card_univ]
        omega
      have he : (∑ T ∈ (univ \ C).powersetCard k, f T) =
          ∑ T ∈ (univ \ C).powerset, f T := by
        apply sum_subset (fun T hT => mem_powerset.mpr (mem_powersetCard.mp hT).1)
        intro T hT hnot
        apply hf
        intro hTk
        exact hnot (mem_powersetCard.mpr ⟨mem_powerset.mp hT, hTk⟩)
      rw [← he]
      exact sum_raise_rank_zero k hchar f hu _ hlarge
    have hleft : (∑ C ∈ A.powerset,
        (-1 : K)^C.card * ∑ T ∈ (univ \ C).powerset, f T) = 0 := by
      exact sum_eq_zero (fun C hC => by rw [hFzero C (mem_powerset.mp hC), mul_zero])
    rw [complement_mobius] at hleft
    have hright : (∑ T ∈ univ.powerset, if A ⊆ T then f T else 0) = f A := by
      rw [sum_eq_single A]
      · simp
      · intro B hB hBA
        by_cases hAB : A ⊆ B
        · rw [ite_eq_left hAB]
          apply hf
          intro hBk
          have := eq_of_subset_of_card_le hAB (by omega)
          exact hBA this.symm
        · simp [hAB]
      · intro hA
        exact False.elim (hA (mem_powerset.mpr (subset_univ _)))
    rwa [hright] at hleft
  · exact hf A hAk

 
def WeightedRaise [Semiring K] (b : α → K) (f : Finset α → K) (S : Finset α) : K :=
  ∑ i ∈ S, b i * f (S.erase i)

lemma weighted_raise_rescale [Field K] (b : α → K) (hb : ∀ i, b i ≠ 0)
    (f : Finset α → K) (S : Finset α) :
    WeightedRaise b f S = (∏ i ∈ S, b i) *
      Raise (fun T => f T / ∏ i ∈ T, b i) S := by
  unfold WeightedRaise Raise
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [← mul_prod_erase S b hi]
  have hne : (∏ j ∈ S.erase i, b j) ≠ 0 := prod_ne_zero_iff.mpr (fun j _ => hb j)
  field_simp

lemma weighted_raise_injective [Fintype α] [Field K]
    (k : ℕ) (hk : 2*k < Fintype.card α)
    (hchar : ∀ j : ℕ, 0 < j → j ≤ Fintype.card α → (j : K) ≠ 0)
    (b : α → K) (hb : ∀ i, b i ≠ 0)
    (f : Finset α → K) (hf : ∀ S, S.card ≠ k → f S = 0)
    (hu : ∀ S, WeightedRaise b f S = 0) : f = 0 := by
  let g : Finset α → K := fun T => f T / ∏ i ∈ T, b i
  have hg : g = 0 := raise_injective_below_middle k hk hchar g
    (fun S hS => by simp [g, hf S hS]) (fun S => by
      have he := hu S
      rw [weighted_raise_rescale b hb f S] at he
      exact (mul_eq_zero.mp he).resolve_left (prod_ne_zero_iff.mpr (fun i _ => hb i)))
  funext S
  have he := congrFun hg S
  change f S / (∏ i ∈ S, b i) = 0 at he
  exact (div_eq_zero_iff.mp he).resolve_right (prod_ne_zero_iff.mpr (fun i _ => hb i))

 

def LinMul [Semiring K] (a : K) (b : α → K) (f : Finset α → K) (S : Finset α) : K :=
  (a + ∑ i ∈ S, b i) * f S + WeightedRaise b f S

def DegreeLE [Zero K] (d : ℕ) (f : Finset α → K) : Prop :=
  ∀ S, d < S.card → f S = 0

lemma weighted_raise_top [Fintype α] [Field K]
    (d : ℕ) (a : K) (b : α → K) (f : Finset α → K)
    (hf : DegreeLE d f) (hprod : ∀ S, LinMul a b f S = 0) (S : Finset α) :
    WeightedRaise b (fun T => if T.card = d then f T else 0) S = 0 := by
  by_cases hS : S.card = d+1
  · have hzero : f S = 0 := hf S (by omega)
    have he := hprod S
    unfold LinMul at he
    rw [hzero, mul_zero, zero_add] at he
    calc
      _ = WeightedRaise b f S := by
        apply sum_congr rfl
        intro i hi
        have hcard : (S.erase i).card = d := by
          rw [card_erase_of_mem hi, hS]; omega
        simp only [hcard, ite_true]
      _ = 0 := he
  · apply sum_eq_zero
    intro i hi
    have hcard : (S.erase i).card ≠ d := by
      rw [card_erase_of_mem hi]
      have := card_pos.mpr ⟨i, hi⟩
      omega
    simp [hcard]

 

theorem linMul_injective_low_degree [Fintype α] [Field K]
    (d : ℕ) (hd : 2*d < Fintype.card α)
    (hchar : ∀ j : ℕ, 0 < j → j ≤ Fintype.card α → (j : K) ≠ 0)
    (a : K) (b : α → K) (hb : ∀ i, b i ≠ 0)
    (f : Finset α → K) (hf : DegreeLE d f)
    (hprod : ∀ S, LinMul a b f S = 0) : f = 0 := by
  induction d generalizing f with
  | zero =>
    have ht := weighted_raise_injective 0 hd hchar b hb
      (fun S => if S.card = 0 then f S else 0)
      (fun S hS => by simp [hS]) (weighted_raise_top 0 a b f hf hprod)
    funext S
    by_cases he : S.card = 0
    · simpa [he] using congrFun ht S
    · exact hf S (by omega)
  | succ d ih =>
    have ht := weighted_raise_injective (d+1) hd hchar b hb
      (fun S => if S.card = d+1 then f S else 0)
      (fun S hS => by simp [hS]) (weighted_raise_top (d+1) a b f hf hprod)
    apply ih (by omega) f
    intro S hS
    by_cases he : S.card = d+1
    · simpa [he] using congrFun ht S
    · exact hf S (by omega)
    exact hprod

lemma map_linMul {L : Type*} [Semiring K] [Semiring L] (φ : K →+* L)
    (a : K) (b : α → K) (f : Finset α → K) (S : Finset α) :
    φ (LinMul a b f S) = LinMul (φ a) (fun i => φ (b i)) (fun T => φ (f T)) S := by
  simp only [LinMul, WeightedRaise, map_add, map_mul, map_sum]

lemma intCast_linMul [Ring K] (a : ℤ) (b : α → ℤ) (f : Finset α → ℤ)
    (S : Finset α) :
    ((LinMul a b f S : ℤ) : K) = LinMul (a : K) (fun i => (b i : K))
      (fun T => (f T : K)) S := by
  simpa only [Int.coe_castRingHom] using map_linMul (Int.castRingHom K) a b f S

lemma linMul_scalar [CommSemiring K] (c a : K) (b : α → K)
    (f : Finset α → K) (S : Finset α) :
    LinMul a b (fun T => c * f T) S = c * LinMul a b f S := by
  unfold LinMul WeightedRaise
  rw [mul_add, mul_sum]
  congr 1
  · ring
  · apply sum_congr rfl; intro i hi; ring

 
def Clears (D : ℕ) (f : Finset α → ℚ) : Prop :=
  ∀ S, ∃ z : ℤ, (D : ℚ) * f S = z

def IntegralCoeffs (f : Finset α → ℚ) : Prop :=
  ∀ S, ∃ z : ℤ, f S = z

 

lemma clear_divide_prime [Fintype α]
    (d : ℕ) (hd : 2*d < Fintype.card α)
    (a : ℤ) (b : α → ℤ) (f : Finset α → ℚ) (hf : DegreeLE d f)
    (hprod : IntegralCoeffs (LinMul (a : ℚ) (fun i => (b i : ℚ)) f))
    (D p : ℕ) (hp : p.Prime) (hpD : p ∣ D)
    (hlarge : Fintype.card α < p) (hb : ∀ i, ¬ (p : ℤ) ∣ b i)
    (hD : Clears D f) : Clears (D/p) f := by
  classical
  let : Fact (Nat.Prime p) := ⟨hp⟩
  choose c hc using hD
  choose g hg using hprod
  have hcdeg (S : Finset α) (hS : d < S.card) : c S = 0 := by
    have he := hc S
    rw [hf S hS, mul_zero] at he
    exact_mod_cast he.symm
  have hmul (S : Finset α) : LinMul a b c S = (D : ℤ) * g S := by
    apply (Int.cast_injective (α := ℚ))
    push_cast
    rw [intCast_linMul]
    change LinMul (a : ℚ) (fun i => (b i : ℚ)) (fun T => (c T : ℚ)) S = _
    have hfc : (fun T => (c T : ℚ)) = fun T => (D : ℚ) * f T :=
      funext (fun T => (hc T).symm)
    rw [hfc, linMul_scalar, hg S]
  have hchar (j : ℕ) (hj : 0 < j) (hjn : j ≤ Fintype.card α) :
      (j : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hj (hjn.trans_lt hlarge)
  have hbc (i : α) : (b i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hb i
  have hzero : (fun S => (c S : ZMod p)) = 0 := by
    apply linMul_injective_low_degree d hd hchar (a : ZMod p)
      (fun i => (b i : ZMod p)) hbc
    · intro S hS; simp [hcdeg S hS]
    · intro S
      rw [← intCast_linMul, hmul S]
      push_cast
      rw [(ZMod.natCast_eq_zero_iff D p).mpr hpD, zero_mul]
  intro S
  have hpCS : (p : ℤ) ∣ c S :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (c S) p).mp (congrFun hzero S)
  obtain ⟨z, hz⟩ := hpCS
  refine ⟨z, ?_⟩
  have hpn : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ hpn
  have hDC : ((D/p : ℕ) : ℚ) * (p : ℚ) = D := by
    exact_mod_cast Nat.div_mul_cancel hpD
  calc
    (p : ℚ) * (((D/p : ℕ) : ℚ) * f S) =
        (((D/p : ℕ) : ℚ) * (p : ℚ)) * f S := by ring
    _ = (D : ℚ) * f S := by rw [hDC]
    _ = c S := hc S
    _ = (p : ℚ) * z := by exact_mod_cast hz

 
theorem integral_of_linMul_integral [Fintype α]
    (d : ℕ) (hd : 2*d < Fintype.card α)
    (a : ℤ) (b : α → ℤ) (f : Finset α → ℚ) (hf : DegreeLE d f)
    (hprod : IntegralCoeffs (LinMul (a : ℚ) (fun i => (b i : ℚ)) f))
    (D : ℕ) (hDpos : 0 < D) (hD : Clears D f)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ D →
      Fintype.card α < p ∧ ∀ i, ¬ (p : ℤ) ∣ b i) : IntegralCoeffs f := by
  induction D using Nat.strong_induction_on with
  | h D ih =>
    by_cases hD1 : D = 1
    · subst D
      intro S
      obtain ⟨z, hz⟩ := hD S
      exact ⟨z, by simpa using hz⟩
    · obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hD1
      obtain ⟨hlarge, hb⟩ := hrough p hp hpD
      have hDsmall : D/p < D := Nat.div_lt_self hDpos hp.one_lt
      have hDppos : 0 < D/p := Nat.div_pos (Nat.le_of_dvd hDpos hpD) hp.pos
      apply ih (D/p) hDsmall hDppos
        (clear_divide_prime d hd a b f hf hprod D p hp hpD hlarge hb hD)
      intro q hq hqD
      exact hrough q hq (hqD.trans (Nat.div_dvd_of_dvd hpD))

 
def Eval [AddCommMonoid K] (f : Finset α → K) (S : Finset α) : K :=
  ∑ T ∈ S.powerset, f T

lemma eval_weightedRaise [CommSemiring K] (b : α → K)
    (f : Finset α → K) (S : Finset α) :
    Eval (WeightedRaise b f) S =
      ∑ U ∈ S.powerset, (∑ i ∈ S \ U, b i) * f U := by
  unfold Eval WeightedRaise
  rw [Finset.sum_sigma']
  calc
    _ = ∑ p ∈ S.powerset.sigma (fun U => S \ U), b p.2 * f p.1 := by
      apply Finset.sum_bij'
        (fun p _ => (⟨p.1.erase p.2, p.2⟩ : (U : Finset α) × α))
        (fun p _ => (⟨insert p.2 p.1, p.2⟩ : (U : Finset α) × α))
      · intro p hp
        obtain ⟨hT, hi⟩ := Finset.mem_sigma.mp hp
        have hTS := mem_powerset.mp hT
        exact mem_sigma.mpr ⟨mem_powerset.mpr ((erase_subset _ _).trans hTS),
          mem_sdiff.mpr ⟨hTS hi, notMem_erase _ _⟩⟩
      · intro p hp
        obtain ⟨hU, hi⟩ := Finset.mem_sigma.mp hp
        obtain ⟨hiS, hiU⟩ := mem_sdiff.mp hi
        exact mem_sigma.mpr ⟨mem_powerset.mpr (insert_subset hiS (mem_powerset.mp hU)),
          mem_insert_self _ _⟩
      · intro p hp
        exact Sigma.ext (insert_erase (mem_sigma.mp hp).2) (heq_of_eq rfl)
      · intro p hp
        exact Sigma.ext (erase_insert (mem_sdiff.mp (mem_sigma.mp hp).2).2) (heq_of_eq rfl)
      · intro p hp; rfl
    _ = _ := by
      rw [← Finset.sum_sigma' S.powerset (fun U => S \ U) (fun U i => b i * f U)]
      simp_rw [sum_mul]

lemma eval_linMul [CommSemiring K] (a : K) (b : α → K)
    (f : Finset α → K) (S : Finset α) :
    Eval (LinMul a b f) S = (a + ∑ i ∈ S, b i) * Eval f S := by
  change (∑ T ∈ S.powerset, ((a + ∑ i ∈ T, b i) * f T + WeightedRaise b f T)) = _
  rw [sum_add_distrib]
  change _ + Eval (WeightedRaise b f) S = _
  rw [eval_weightedRaise, ← sum_add_distrib]
  unfold Eval
  rw [mul_sum]
  apply sum_congr rfl
  intro T hT
  have he : (∑ i ∈ T, b i) + ∑ i ∈ S \ T, b i = ∑ i ∈ S, b i :=
    by simpa only [add_comm] using (sum_sdiff (f := b) (mem_powerset.mp hT))
  rw [← he]
  ring

omit [DecidableEq α] in
lemma eval_integral_of_coeffs [DecidableEq α] (f : Finset α → ℚ) (hf : IntegralCoeffs f)
    (S : Finset α) : ∃ z : ℤ, Eval f S = z := by
  choose g hg using hf
  refine ⟨∑ T ∈ S.powerset, g T, ?_⟩
  simp only [Eval, hg, Int.cast_sum]

 
lemma integral_coeffs_of_eval (f : Finset α → ℚ)
    (hf : ∀ S, ∃ z : ℤ, Eval f S = z) : IntegralCoeffs f := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain ⟨z, hz⟩ := hf S
    have hi : ∀ T ∈ S.powerset.erase S, ∃ a : ℤ, f T = a := by
      intro T hT
      obtain ⟨hTS, hT⟩ := mem_erase.mp hT
      have hsub := mem_powerset.mp hT
      exact ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hTS⟩)
    choose g hg using hi
    let v : ℤ := ∑ T : {T // T ∈ S.powerset.erase S}, g T.1 T.2
    have hv : (∑ T ∈ S.powerset.erase S, f T) = (v : ℚ) := by
      rw [← sum_attach]
      simp only [attach_eq_univ, v, Int.cast_sum]
      apply sum_congr rfl
      intro T hT
      exact hg T.1 T.2
    refine ⟨z-v, ?_⟩
    have he : f S + ∑ T ∈ S.powerset.erase S, f T = Eval f S := by
      exact add_sum_erase _ _ (mem_powerset.mpr (Subset.refl _))
    rw [hv, hz] at he
    push_cast
    linarith

lemma degree_linMul [Semiring K] (d : ℕ) (a : K) (b : α → K)
    (f : Finset α → K) (hf : DegreeLE d f) : DegreeLE (d+1) (LinMul a b f) := by
  intro S hS
  unfold LinMul WeightedRaise
  rw [hf S (by omega), mul_zero, zero_add]
  apply sum_eq_zero
  intro i hi
  have hcard : d < (S.erase i).card := by rw [card_erase_of_mem hi]; omega
  rw [hf _ hcard, mul_zero]

def LinPow [Semiring K] (a : K) (b : α → K) (f : Finset α → K) : ℕ → Finset α → K
  | 0 => f
  | e+1 => LinMul a b (LinPow a b f e)

lemma eval_linPow [CommSemiring K] (a : K) (b : α → K)
    (f : Finset α → K) (e : ℕ) (S : Finset α) :
    Eval (LinPow a b f e) S = (a + ∑ i ∈ S, b i)^e * Eval f S := by
  induction e with
  | zero => simp [LinPow]
  | succ e ih => rw [LinPow, eval_linMul, ih, pow_succ]; ring

lemma degree_linPow [Semiring K] (d : ℕ) (a : K) (b : α → K)
    (f : Finset α → K) (hf : DegreeLE d f) (e : ℕ) :
    DegreeLE (d+e) (LinPow a b f e) := by
  induction e with
  | zero => exact hf
  | succ e ih => exact degree_linMul (d+e) a b _ ih

lemma clears_linMul (D : ℕ) (a : ℤ) (b : α → ℤ) (f : Finset α → ℚ)
    (hD : Clears D f) : Clears D (LinMul (a : ℚ) (fun i => (b i : ℚ)) f) := by
  choose c hc using hD
  intro S
  refine ⟨LinMul a b c S, ?_⟩
  rw [intCast_linMul, ← linMul_scalar]
  congr 1
  exact funext hc

lemma clears_linPow (D : ℕ) (a : ℤ) (b : α → ℤ) (f : Finset α → ℚ)
    (hD : Clears D f) (e : ℕ) :
    Clears D (LinPow (a : ℚ) (fun i => (b i : ℚ)) f e) := by
  induction e with
  | zero => exact hD
  | succ e ih => exact clears_linMul D a b _ ih

 
theorem integral_of_linPow_integral [Fintype α]
    (d e : ℕ) (hd : 2*(d+e) < Fintype.card α)
    (a : ℤ) (b : α → ℤ) (f : Finset α → ℚ) (hf : DegreeLE d f)
    (hprod : IntegralCoeffs (LinPow (a : ℚ) (fun i => (b i : ℚ)) f e))
    (D : ℕ) (hDpos : 0 < D) (hD : Clears D f)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ D →
      Fintype.card α < p ∧ ∀ i, ¬ (p : ℤ) ∣ b i) : IntegralCoeffs f := by
  induction e with
  | zero => exact hprod
  | succ e ih =>
    have hg := integral_of_linMul_integral (d+e) (by omega) a b
      (LinPow (a : ℚ) (fun i => (b i : ℚ)) f e)
      (degree_linPow d _ _ f hf e) hprod D hDpos (clears_linPow D a b f hD e) hrough
    exact ih (by omega) hg

 
theorem integral_of_power_vertex_integral [Fintype α]
    (d e : ℕ) (hd : 2*(d+e) < Fintype.card α)
    (a : ℤ) (b : α → ℤ) (f : Finset α → ℚ) (hf : DegreeLE d f)
    (hprod : ∀ S, ∃ z : ℤ, ((a : ℚ) + ∑ i ∈ S, (b i : ℚ))^e * Eval f S = z)
    (D : ℕ) (hDpos : 0 < D) (hD : Clears D f)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ D →
      Fintype.card α < p ∧ ∀ i, ¬ (p : ℤ) ∣ b i) : IntegralCoeffs f := by
  apply integral_of_linPow_integral d e hd a b f hf _ D hDpos hD hrough
  apply integral_coeffs_of_eval
  intro S
  rw [eval_linPow]
  exact hprod S

 
lemma sum_subset_incidence [AddCommMonoid K] (S : Finset α)
    (F : Finset α → Finset α → K) :
    (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, F T U) =
      ∑ U ∈ S.powerset, ∑ V ∈ (S \ U).powerset, F (U ∪ V) U := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij'
    (fun p _ => (⟨p.2, p.1 \ p.2⟩ : (U : Finset α) × Finset α))
    (fun p _ => (⟨p.1 ∪ p.2, p.1⟩ : (U : Finset α) × Finset α))
  · intro p hp
    obtain ⟨hT, hU⟩ := mem_sigma.mp hp
    have hTS := mem_powerset.mp hT
    have hUT := mem_powerset.mp hU
    exact mem_sigma.mpr ⟨mem_powerset.mpr (hUT.trans hTS),
      mem_powerset.mpr (sdiff_subset_sdiff_left _ hTS)⟩
  · intro p hp
    obtain ⟨hU, hV⟩ := mem_sigma.mp hp
    have hUS := mem_powerset.mp hU
    have hVsub := mem_powerset.mp hV
    exact mem_sigma.mpr ⟨mem_powerset.mpr (union_subset hUS (hVsub.trans sdiff_subset)),
      mem_powerset.mpr subset_union_left⟩
  · intro p hp
    have hUT := mem_powerset.mp (mem_sigma.mp hp).2
    exact Sigma.ext (union_sdiff_of_subset hUT) (heq_of_eq rfl)
  · intro p hp
    have hV := mem_powerset.mp (mem_sigma.mp hp).2
    have hd : Disjoint p.1 p.2 := by
      apply disjoint_left.mpr
      intro i hiU hiV
      exact (mem_sdiff.mp (hV hiV)).2 hiU
    exact Sigma.ext rfl (heq_of_eq (union_sdiff_cancel_left hd))
  · intro p hp
    have hUT := mem_powerset.mp (mem_sigma.mp hp).2
    rw [union_sdiff_of_subset hUT]

 
def Mobius [Ring K] (g : Finset α → K) (S : Finset α) : K :=
  ∑ T ∈ S.powerset, (-1 : K)^(S \ T).card * g T

lemma eval_mobius [CommRing K] (g : Finset α → K) (S : Finset α) :
    Eval (Mobius g) S = g S := by
  unfold Eval Mobius
  rw [sum_subset_incidence]
  have hs : (∑ U ∈ S.powerset, ∑ V ∈ (S \ U).powerset,
      (-1 : K)^((U ∪ V) \ U).card * g U) =
      ∑ U ∈ S.powerset, (if S \ U = ∅ then 1 else 0) * g U := by
    apply sum_congr rfl
    intro U hU
    calc
      _ = ∑ V ∈ (S \ U).powerset, (-1 : K)^V.card * g U := by
        apply sum_congr rfl
        intro V hV
        have hd : Disjoint U V := by
          apply disjoint_left.mpr
          intro i hiU hiV
          exact (mem_sdiff.mp (mem_powerset.mp hV hiV)).2 hiU
        rw [union_sdiff_cancel_left hd]
      _ = _ := by rw [← sum_mul, alternating_powerset]
  rw [hs, sum_eq_single S]
  · simp
  · intro U hU hUS
    have hne : S \ U ≠ ∅ := by
      intro he
      exact hUS (Subset.antisymm (mem_powerset.mp hU) (sdiff_eq_empty_iff_subset.mp he))
    simp [hne]
  · intro hS
    exact False.elim (hS (mem_powerset.mpr (Subset.refl _)))

lemma eval_injective [AddCancelCommMonoid K] (f g : Finset α → K)
    (h : ∀ S, Eval f S = Eval g S) : f = g := by
  funext S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have he := h S
    have hf : Eval f S = f S + ∑ T ∈ S.powerset.erase S, f T :=
      (add_sum_erase _ _ (mem_powerset.mpr (Subset.refl _))).symm
    have hg : Eval g S = g S + ∑ T ∈ S.powerset.erase S, g T :=
      (add_sum_erase _ _ (mem_powerset.mpr (Subset.refl _))).symm
    rw [hf, hg] at he
    have hs : (∑ T ∈ S.powerset.erase S, f T) = ∑ T ∈ S.powerset.erase S, g T := by
      apply sum_congr rfl
      intro T hT
      obtain ⟨hne, hsub⟩ := mem_erase.mp hT
      exact ih T (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hsub, hne⟩)
    rw [hs] at he
    exact add_right_cancel he

lemma mobius_eval [CommRing K] (f : Finset α → K) (S : Finset α) :
    Mobius (Eval f) S = f S := by
  have he : Mobius (Eval f) = f := eval_injective _ _ (eval_mobius (Eval f))
  exact congrFun he S

 
def Interp [Ring K] (d : ℕ) (g : Finset α → K) (S : Finset α) : K :=
  if S.card ≤ d then Mobius g S else 0

lemma degree_interp [Ring K] (d : ℕ) (g : Finset α → K) : DegreeLE d (Interp d g) := by
  intro S hS
  simp [Interp, Nat.not_le_of_lt hS]

lemma eval_interp_low [CommRing K] (d : ℕ) (g : Finset α → K)
    (S : Finset α) (hS : S.card ≤ d) : Eval (Interp d g) S = g S := by
  rw [← eval_mobius g S]
  apply sum_congr rfl
  intro T hT
  exact ite_eq_left ((card_le_card (mem_powerset.mp hT)).trans hS)

omit [DecidableEq α] in
lemma map_eval [DecidableEq α] {L : Type*} [AddCommMonoid K] [AddCommMonoid L] (φ : K →+ L)
    (f : Finset α → K) (S : Finset α) : φ (Eval f S) = Eval (fun T => φ (f T)) S := by
  simp only [Eval, map_sum]

lemma map_mobius {L : Type*} [Ring K] [Ring L] (φ : K →+* L)
    (f : Finset α → K) (S : Finset α) : φ (Mobius f S) = Mobius (fun T => φ (f T)) S := by
  simp only [Mobius, map_sum, map_mul, map_pow, map_neg, map_one]

lemma map_interp {L : Type*} [Ring K] [Ring L] (φ : K →+* L)
    (d : ℕ) (f : Finset α → K) (S : Finset α) :
    φ (Interp d f S) = Interp d (fun T => φ (f T)) S := by
  by_cases hS : S.card ≤ d <;> simp [Interp, hS, map_mobius]

lemma mobius_scalar [CommRing K] (c : K) (f : Finset α → K) (S : Finset α) :
    Mobius (fun T => c * f T) S = c * Mobius f S := by
  unfold Mobius
  rw [mul_sum]
  apply sum_congr rfl
  intro T hT
  ring

lemma interp_sub [Ring K] (d : ℕ) (f g : Finset α → K) :
    Interp d (fun T => f T - g T) = fun T => Interp d f T - Interp d g T := by
  funext S
  by_cases hS : S.card ≤ d
  · simp only [Interp, hS, ite_true, Mobius, mul_sub, sum_sub_distrib]
  · simp [Interp, hS]

lemma interp_eval_degree [CommRing K] (d : ℕ) (f : Finset α → K) (hf : DegreeLE d f) :
    Interp d (Eval f) = f := by
  funext S
  by_cases hS : S.card ≤ d
  · simp [Interp, hS, mobius_eval]
  · simp [Interp, hS, hf S (by omega)]

lemma clears_interp (D d : ℕ) (f : Finset α → ℚ) (hD : Clears D f) :
    Clears D (Interp d f) := by
  choose c hc using hD
  intro S
  by_cases hS : S.card ≤ d
  · refine ⟨Mobius c S, ?_⟩
    simp only [Interp, hS, ite_true]
    have he := map_mobius (Int.castRingHom ℚ) c S
    simp only [Int.coe_castRingHom] at he
    rw [he, ← mobius_scalar]
    congr 1
    exact funext hc
  · exact ⟨0, by simp [Interp, hS]⟩

lemma abs_mobius_le (g : Finset α → ℝ) (S : Finset α) (δ : ℝ)
    (hg : ∀ T ∈ S.powerset, |g T| ≤ δ) :
    |Mobius g S| ≤ (2 : ℝ)^S.card * δ := by
  unfold Mobius
  calc
    _ ≤ ∑ T ∈ S.powerset, |(-1 : ℝ)^(S \ T).card * g T| := abs_sum_le_sum_abs _ _
    _ = ∑ T ∈ S.powerset, |g T| := by simp
    _ ≤ S.powerset.card • δ := sum_le_card_nsmul _ _ _ hg
    _ = _ := by rw [card_powerset, nsmul_eq_mul]; simp

lemma abs_interp_le [Fintype α] (d : ℕ) (g : Finset α → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hg : ∀ T, T.card ≤ d → |g T| ≤ δ) (S : Finset α) :
    |Interp d g S| ≤ (2 : ℝ)^(Fintype.card α) * δ := by
  by_cases hS : S.card ≤ d
  · rw [Interp, ite_eq_left hS]
    exact (abs_mobius_le g S δ (fun T hT => hg T ((card_le_card (mem_powerset.mp hT)).trans hS))).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (card_le_univ S)) hδ)
  · simp only [Interp, ite_eq_right hS, abs_zero]
    positivity

lemma abs_eval_interp_le [Fintype α] (d : ℕ) (g : Finset α → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hg : ∀ T, T.card ≤ d → |g T| ≤ δ) (S : Finset α) :
    |Eval (Interp d g) S| ≤ ((2 : ℝ)^(Fintype.card α))^2 * δ := by
  unfold Eval
  calc
    _ ≤ ∑ T ∈ S.powerset, |Interp d g T| := abs_sum_le_sum_abs _ _
    _ ≤ S.powerset.card • ((2 : ℝ)^(Fintype.card α) * δ) :=
      sum_le_card_nsmul _ _ _ (fun T _ => abs_interp_le d g δ hδ hg T)
    _ ≤ ((2 : ℝ)^(Fintype.card α))^2 * δ := by
      rw [card_powerset, nsmul_eq_mul]
      push_cast
      calc
        _ ≤ (2 : ℝ)^(Fintype.card α) * ((2 : ℝ)^(Fintype.card α) * δ) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (card_le_univ S)) (by positivity)
        _ = _ := by ring

lemma eval_interp_error [Fintype α] (d : ℕ) (θ : Finset α → ℝ) (hθ : DegreeLE d θ)
    (g : Finset α → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hg : ∀ T, T.card ≤ d → |Eval θ T - g T| ≤ δ) (S : Finset α) :
    |Eval θ S - Eval (Interp d g) S| ≤ ((2 : ℝ)^(Fintype.card α))^2 * δ := by
  have h := abs_eval_interp_le d (fun T => Eval θ T - g T) δ hδ hg S
  rw [interp_sub, interp_eval_degree d θ hθ] at h
  simpa only [Eval, sum_sub_distrib] using h

omit [DecidableEq α] in
lemma clears_eval [DecidableEq α] (D : ℕ) (f : Finset α → ℚ) (hD : Clears D f) :
    Clears D (Eval f) := by
  choose c hc using hD
  intro S
  refine ⟨∑ T ∈ S.powerset, c T, ?_⟩
  simp only [Eval, mul_sum, hc, Int.cast_sum]

lemma denominator_clears_div (D e : ℕ) (t k : ℤ) (ht : 0 < t)
    (hD : t.natAbs^e ∣ D) : ∃ z : ℤ, (D : ℚ) * ((k : ℚ)/(t : ℚ)^e) = z := by
  obtain ⟨c, hc⟩ := hD
  refine ⟨(c : ℤ)*k, ?_⟩
  have hcast : ((t.natAbs : ℕ) : ℚ) = (t : ℚ) := by
    have he := congrArg (Int.castRingHom ℚ) (Int.natAbs_of_nonneg ht.le)
    simpa only [Int.coe_castRingHom, Int.cast_natCast] using he
  have hne : (t : ℚ)^e ≠ 0 := pow_ne_zero _ (by exact_mod_cast ht.ne')
  rw [hc]
  push_cast
  rw [hcast]
  field_simp

lemma rational_exact_of_small (D : ℕ) (hD : 0 < D) (q : ℚ) (z : ℤ)
    (hc : ∃ c : ℤ, (D : ℚ)*q = c)
    (hsmall : (D : ℝ)*|(q : ℝ)-(z : ℝ)| < 1) : q = z := by
  obtain ⟨c, hc⟩ := hc
  have hcr : (D : ℝ)*(q : ℝ) = c := by exact_mod_cast hc
  have hzero : c - (D : ℤ)*z = 0 := by
    apply Int.abs_lt_one_iff.mp
    have he : |((c - (D : ℤ)*z : ℤ) : ℝ)| = (D : ℝ)*|(q : ℝ)-(z : ℝ)| := by
      push_cast
      rw [← hcr, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg D)]
    exact_mod_cast (he ▸ hsmall)
  apply mul_left_cancel₀ (show (D : ℚ) ≠ 0 by exact_mod_cast hD.ne')
  rw [hc]
  exact_mod_cast (sub_eq_zero.mp hzero)

 

theorem rough_rounding_local [Fintype α] (d e M : ℕ) (hdim : 2*(d+e) < Fintype.card α)
    (a : ℤ) (b : α → ℤ) (θ : Finset α → ℝ) (hθ : DegreeLE d θ)
    (htpos : ∀ S : Finset α, 0 < a + ∑ i ∈ S, b i)
    (htbound : ∀ S : Finset α, a + ∑ i ∈ S, b i ≤ (M : ℤ))
    (hrough : ∀ p : ℕ, p.Prime → (∃ S : Finset α, (p : ℤ) ∣ a + ∑ i ∈ S, b i) →
      Fintype.card α < p ∧ ∀ i, ¬ (p : ℤ) ∣ b i)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : (1+(M : ℝ)^e * (2^(Fintype.card α) : ℝ)^2) * ε *
      (M : ℝ)^(e*2^(Fintype.card α)) < 1)
    (δ : Finset α → ℝ) (hδε : ∀ S, δ S ≤ ε)
    (hnear : ∀ S : Finset α, ∃ z : ℤ,
      |((a + ∑ i ∈ S, b i : ℤ) : ℝ)^e * Eval θ S - z| ≤ δ S) :
    ∃ f : Finset α → ℚ, DegreeLE d f ∧ IntegralCoeffs f ∧
      ∀ S, |Eval θ S - ((Eval f S : ℚ) : ℝ)| ≤ δ S / ((a + ∑ i ∈ S, b i : ℤ) : ℝ)^e := by
  classical
  let t : Finset α → ℤ := fun S => a + ∑ i ∈ S, b i
  choose k hk using hnear
  let g : Finset α → ℚ := fun S => (k S : ℚ)/(t S : ℚ)^e
  let f : Finset α → ℚ := Interp d g
  let D : ℕ := ∏ S : Finset α, (t S).natAbs^e
  have ht (S : Finset α) : 0 < t S := htpos S
  have htr (S : Finset α) : 0 < (t S : ℝ) := by exact_mod_cast ht S
  have htt (S : Finset α) : (t S).natAbs ≤ M := by
    have he : ((t S).natAbs : ℤ) ≤ (M : ℤ) :=
      (Int.natAbs_of_nonneg (ht S).le).trans_le (htbound S)
    exact Int.ofNat_le.mp he
  have hDpos : 0 < D := prod_pos (fun S _ => pow_pos (Int.natAbs_pos.mpr (ht S).ne') _)
  have hDbound : D ≤ M^(e*2^(Fintype.card α)) := by
    calc
      D ≤ ∏ S : Finset α, M^e :=
        prod_le_prod (fun S _ => Nat.pow_le_pow_left (htt S) e)
      _ = _ := by rw [prod_const, card_univ, Fintype.card_finset, ← pow_mul]
  have hDg : Clears D g := by
    intro S
    exact denominator_clears_div D e (t S) (k S) (ht S)
      (dvd_prod_of_mem (fun T : Finset α => (t T).natAbs^e) (mem_univ _))
  have hDf : Clears D f := clears_interp D d g hDg
  have hDr : ∀ p : ℕ, p.Prime → p ∣ D →
      Fintype.card α < p ∧ ∀ i, ¬ (p : ℤ) ∣ b i := by
    intro p hp hpD
    obtain ⟨S, _, hpS⟩ := (hp.prime.dvd_finsetProd_iff (fun S : Finset α => (t S).natAbs^e)).mp hpD
    exact hrough p hp ⟨S, Int.natCast_dvd.mpr (hp.dvd_of_dvd_pow hpS)⟩
  have hgnear (S : Finset α) : |Eval θ S - (g S : ℝ)| ≤ ε := by
    have hp1 : (1 : ℝ) ≤ (t S : ℝ)^e := by
      apply one_le_pow₀
      have h1 : (1 : ℤ) ≤ t S := ht S
      exact_mod_cast h1
    have he : (t S : ℝ)^e * (Eval θ S - (g S : ℝ)) =
        (t S : ℝ)^e * Eval θ S - (k S : ℝ) := by
      simp only [g, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow]
      field_simp
    have hh := (hk S).trans (hδε S)
    change |(t S : ℝ)^e * Eval θ S - (k S : ℝ)| ≤ ε at hh
    rw [← he, abs_mul, abs_of_pos (pow_pos (htr S) e)] at hh
    exact (le_mul_of_one_le_left (abs_nonneg _) hp1).trans hh
  have heval (S : Finset α) : ((Eval f S : ℚ) : ℝ) =
      Eval (Interp d (fun T => (g T : ℝ))) S := by
    simp only [Eval, Rat.cast_sum]
    apply sum_congr rfl
    intro T hT
    exact map_interp (Rat.castHom ℝ) d g T
  have herr (S : Finset α) : |Eval θ S - ((Eval f S : ℚ) : ℝ)| ≤
      ((2 : ℝ)^(Fintype.card α))^2 * ε := by
    rw [heval]
    exact eval_interp_error d θ hθ _ ε hε (fun T _ => hgnear T) S
  have hprodnear (S : Finset α) :
      |(t S : ℝ)^e * ((Eval f S : ℚ) : ℝ) - (k S : ℝ)| ≤
        (1+(M : ℝ)^e * (2^(Fintype.card α) : ℝ)^2) * ε := by
    have htpbound : (t S : ℝ)^e ≤ (M : ℝ)^e :=
      pow_le_pow_left₀ (htr S).le (by exact_mod_cast htbound S) e
    calc
      _ = |(t S : ℝ)^e * (((Eval f S : ℚ) : ℝ) - Eval θ S) +
          ((t S : ℝ)^e * Eval θ S - (k S : ℝ))| := by congr 1; ring
      _ ≤ |(t S : ℝ)^e * (((Eval f S : ℚ) : ℝ) - Eval θ S)| +
          |(t S : ℝ)^e * Eval θ S - (k S : ℝ)| := abs_add_le _ _
      _ = (t S : ℝ)^e * |Eval θ S - ((Eval f S : ℚ) : ℝ)| +
          |(t S : ℝ)^e * Eval θ S - (k S : ℝ)| := by
        rw [abs_mul, abs_of_pos (pow_pos (htr S) e), abs_sub_comm]
      _ ≤ (M : ℝ)^e * (((2 : ℝ)^(Fintype.card α))^2 * ε) + ε :=
        add_le_add (mul_le_mul htpbound (herr S) (abs_nonneg _) (by positivity)) ((hk S).trans (hδε S))
      _ = _ := by ring
  have hexact (S : Finset α) : (t S : ℚ)^e * Eval f S = (k S : ℚ) := by
    apply rational_exact_of_small D hDpos
    · obtain ⟨c, hc⟩ := clears_eval D f hDf S
      refine ⟨(t S)^e*c, ?_⟩
      push_cast
      rw [← hc]
      ring
    · push_cast
      calc
        _ ≤ (D : ℝ) * ((1+(M : ℝ)^e * (2^(Fintype.card α) : ℝ)^2) * ε) :=
          mul_le_mul_of_nonneg_left (hprodnear S) (Nat.cast_nonneg D)
        _ ≤ (M : ℝ)^(e*2^(Fintype.card α)) *
            ((1+(M : ℝ)^e * (2^(Fintype.card α) : ℝ)^2) * ε) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hDbound) (by positivity)
        _ = (1+(M : ℝ)^e * (2^(Fintype.card α) : ℝ)^2) * ε *
            (M : ℝ)^(e*2^(Fintype.card α)) := by ring
        _ < 1 := hsmall
  refine ⟨f, degree_interp d g, ?_, ?_⟩
  · apply integral_of_power_vertex_integral d e hdim a b f (degree_interp d g) _ D hDpos hDf hDr
    intro S
    refine ⟨k S, ?_⟩
    simpa only [t, Int.cast_add, Int.cast_sum] using hexact S
  · intro S
    apply (le_div_iff₀ (pow_pos (htr S) e)).mpr
    have hx : (t S : ℝ)^e * ((Eval f S : ℚ) : ℝ) = (k S : ℝ) := by exact_mod_cast hexact S
    calc
      _ = |(t S : ℝ)^e * Eval θ S - (k S : ℝ)| := by
        rw [← hx, ← mul_sub, abs_mul, abs_of_pos (pow_pos (htr S) e)]
        ring
      _ ≤ δ S := hk S

 
theorem rough_rounding [Fintype α] (d e M : ℕ) (hdim : 2*(d+e) < Fintype.card α)
    (a : ℤ) (b : α → ℤ) (θ : Finset α → ℝ) (hθ : DegreeLE d θ)
    (htpos : ∀ S : Finset α, 0 < a + ∑ i ∈ S, b i)
    (htbound : ∀ S : Finset α, a + ∑ i ∈ S, b i ≤ (M : ℤ))
    (hrough : ∀ p : ℕ, p.Prime → (∃ S : Finset α, (p : ℤ) ∣ a + ∑ i ∈ S, b i) →
      Fintype.card α < p ∧ ∀ i, ¬ (p : ℤ) ∣ b i)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : (1+(M : ℝ)^e * (2^(Fintype.card α) : ℝ)^2) * ε *
      (M : ℝ)^(e*2^(Fintype.card α)) < 1)
    (hnear : ∀ S : Finset α, ∃ z : ℤ,
      |((a + ∑ i ∈ S, b i : ℤ) : ℝ)^e * Eval θ S - z| ≤ ε) :
    ∃ f : Finset α → ℚ, DegreeLE d f ∧ IntegralCoeffs f ∧
      ∀ S, |Eval θ S - ((Eval f S : ℚ) : ℝ)| ≤ ε / ((a + ∑ i ∈ S, b i : ℤ) : ℝ)^e := by
  exact rough_rounding_local d e M hdim a b θ hθ htpos htbound hrough ε hε hsmall
    (fun _ => ε) (fun _ => le_rfl) hnear

lemma mobius_sub [Ring K] (f g : Finset α → K) (S : Finset α) :
    Mobius (fun T => f T - g T) S = Mobius f S - Mobius g S := by
  simp only [Mobius, mul_sub, sum_sub_distrib]

lemma eval_constant_coeff [Semiring K] (c : K) (S : Finset α) :
    Eval (fun T : Finset α => if T = ∅ then c else 0) S = c := by
  classical
  simp [Eval]

lemma mobius_const [CommRing K] (c : K) (S : Finset α) :
    Mobius (fun _ => c) S = if S = ∅ then c else 0 := by
  have he : (fun _ : Finset α => c) = Eval (fun T => if T = ∅ then c else 0) :=
    funext (fun T => (eval_constant_coeff c T).symm)
  rw [he, mobius_eval]

 

theorem constant_rounding [Fintype α] (d : ℕ) (θ : Finset α → ℝ) (hθ : DegreeLE d θ)
    (c δ : ℝ) (hδ : 0 ≤ δ) (hsmall : (2 : ℝ)^(Fintype.card α)*δ < 1)
    (hspread : ∀ S : Finset α, |Int.fract (Eval θ S)-c| ≤ δ) :
    ∃ m : Finset α → ℤ, DegreeLE d m ∧ ∀ S, Eval m S = ⌊Eval θ S⌋ := by
  let k : Finset α → ℤ := fun S => ⌊Eval θ S⌋
  refine ⟨Mobius k, ?_, eval_mobius k⟩
  intro S hS
  have hnonempty : S ≠ ∅ := by
    intro he
    simp only [he, card_empty] at hS
    omega
  have hbound := abs_mobius_le (fun T => Int.fract (Eval θ T)-c) S δ
    (fun T _ => hspread T)
  have herr : Mobius (fun T => Int.fract (Eval θ T)-c) S = -((Mobius k S : ℤ) : ℝ) := by
    simp only [Int.fract, mobius_sub, mobius_eval, hθ S hS, mobius_const, ite_eq_right hnonempty]
    have hc := map_mobius (Int.castRingHom ℝ) k S
    simpa only [Int.coe_castRingHom, zero_sub, sub_zero, k] using congrArg Neg.neg hc.symm
  have hsmallS : (2 : ℝ)^S.card*δ < 1 :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (card_le_univ S)) hδ).trans_lt hsmall
  rw [herr, abs_neg] at hbound
  apply Int.abs_lt_one_iff.mp
  exact_mod_cast hbound.trans_lt hsmallS

end BooleanRough

end
end

end OAI
