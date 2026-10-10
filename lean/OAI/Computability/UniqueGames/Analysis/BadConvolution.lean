import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import OAI.Computability.UniqueGames.Analysis.AntecedentCountLemmas
import OAI.Computability.UniqueGames.Analysis.DegreeCover
import OAI.Computability.UniqueGames.Analysis.DyadicError
import OAI.Computability.UniqueGames.Analysis.SubspaceCountingLemmas

namespace OAI

section

/-! The signed bad-convolution term of Appendix A.1.  The selector here is
the weak image/kernel selector, prior to its separate A.4 decomposition. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.BadConvolution
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

def Incidence (A : Submodule F2 V) (B : Submodule F2 W) (Y : W →ₗ[F2] V) : Prop :=
  A ≤ Y.range ∧ Y.ker ≤ B

def Bad (X Y : W →ₗ[F2] V) : Prop :=
  (X.range ⊓ Y.range) ⊓ (X+Y).range ≠ ⊥ ∨
    (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≠ ⊤

def filteredCoefficient (A : Submodule F2 V) (B : Submodule F2 W)
    (a : (W →ₗ[F2] V) → ℝ) (Y : W →ₗ[F2] V) : ℝ :=
  if Incidence A B Y then a Y else 0

def mobius (i : ℕ) : ℝ := (-1:ℝ)^i * 2^(i.choose 2)

def pairDimension (p : Submodule F2 V × Submodule F2 W) : ℕ :=
  finrank F2 p.1 + finrank F2 (W ⧸ p.2)

def pairWeight (p : Submodule F2 V × Submodule F2 W) : ℝ :=
  mobius (finrank F2 p.1) * mobius (finrank F2 (W ⧸ p.2))

def signedWeight (p : Submodule F2 V × Submodule F2 W) : ℝ :=
  if p = (⊥,⊤) then 0 else -pairWeight p

section FiniteSums
variable [Fintype (W →ₗ[F2] V)]

def pieceConvolution (A : Submodule F2 V) (B : Submodule F2 W)
    (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) : ℝ :=
  ∑ Y, filteredCoefficient A B a Y * filteredCoefficient A B a (X+Y)

def badConvolution (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) : ℝ :=
  ∑ Y, if Bad X Y then a Y * a (X+Y) else 0
end FiniteSums

private theorem sum_masked_eq_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] (f : α → M) :
    (∑ a, if p a then f a else 0) = ∑ a : {a // p a}, f a.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro a; simp) f

variable [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

omit [Finite W] [Finite V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
theorem pairDimension_eq_zero_iff (p : Submodule F2 V × Submodule F2 W) :
    pairDimension p = 0 ↔ p = (⊥,⊤) := by
  rw [pairDimension, Nat.add_eq_zero_iff]
  rw [Submodule.finrank_eq_zero, UpperMobius.quotient_finrank_zero_iff]
  constructor
  · rintro ⟨hA,hB⟩
    exact Prod.ext hA hB
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

omit [Finite W] [Finite V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
theorem pairDimension_pos_iff (p : Submodule F2 V × Submodule F2 W) :
    0 < pairDimension p ↔ p ≠ (⊥,⊤) := by
  rw [Nat.pos_iff_ne_zero, ne_eq, pairDimension_eq_zero_iff]

theorem lower_mobius_sum (I : Submodule F2 V) :
    (∑ A : Submodule F2 V, if A ≤ I then mobius (finrank F2 A) else 0) =
      if I = ⊥ then 1 else 0 := by
  let := Fintype.ofFinite {A : Submodule F2 V // A ≤ I}
  rw [sum_masked_eq_subtype]
  have h := SubmoduleInterval.binary_lower_interval_mobius I
  unfold SubmoduleInterval.lowerWeightedTotal at h
  unfold mobius
  exact_mod_cast h

theorem upper_mobius_sum (K : Submodule F2 W) :
    (∑ B : Submodule F2 W, if K ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) =
      if K = ⊤ then 1 else 0 := by
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  rw [sum_masked_eq_subtype]
  have h := UpperMobius.binary_upper_interval_mobius K
  unfold UpperMobius.upperWeightedTotal at h
  unfold mobius
  exact_mod_cast h

omit [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
    [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
private theorem triple_incidence_iff (p : Submodule F2 V × Submodule F2 W)
    (X Y : W →ₗ[F2] V) :
    (Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)) ↔
      p.1 ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range ∧
        (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ p.2 := by
  simp only [Incidence, le_inf_iff, sup_le_iff]
  tauto

theorem triple_mobius_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then pairWeight p else 0) = if Bad X Y then 0 else 1 := by
  simp_rw [triple_incidence_iff]
  calc
    _ = (∑ A : Submodule F2 V,
        if A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range then mobius (finrank F2 A) else 0) *
        (∑ B : Submodule F2 W,
        if (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hA : A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range <;>
        by_cases hB : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B <;>
        simp [pairWeight, hA, hB]
    _ = _ := by
      rw [lower_mobius_sum, upper_mobius_sum]
      by_cases hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥ <;>
        by_cases hk : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker = ⊤ <;>
        simp [Bad, hi, hk]

theorem signed_triple_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then signedWeight p else 0) = if Bad X Y then 1 else 0 := by
  have htop : finrank F2 (W ⧸ (⊤ : Submodule F2 W)) = 0 :=
    (UpperMobius.quotient_finrank_zero_iff ⊤).mpr rfl
  have hterm (p : Submodule F2 V × Submodule F2 W) :
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then pairWeight p else 0) +
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then signedWeight p else 0) = if p = (⊥,⊤) then 1 else 0 := by
    by_cases hp : p = (⊥,⊤)
    · subst p
      simp [Incidence, pairWeight, signedWeight, mobius, htop]
    · by_cases h : Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      all_goals simp [signedWeight, hp, h]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun p _ => hterm p)
  rw [Finset.sum_add_distrib, triple_mobius_sum] at hs
  have hdelta : (∑ p : Submodule F2 V × Submodule F2 W,
      if p = (⊥,⊤) then (1:ℝ) else 0) = 1 := by simp
  rw [hdelta] at hs
  by_cases hbad : Bad X Y <;> simp [hbad] at hs ⊢ <;> linarith

variable [Fintype (W →ₗ[F2] V)]

/-- Exact Möbius expansion; no degree or positivity assumption is used. -/
theorem badConvolution_expansion (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) :
    badConvolution a X =
      ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p * pieceConvolution p.1 p.2 a X else 0 := by
  calc
    _ = ∑ Y, (if Bad X Y then (1:ℝ) else 0) * (a Y * a (X+Y)) := by
      unfold badConvolution
      apply Finset.sum_congr rfl
      intro Y _
      by_cases h : Bad X Y <;> simp [h]
    _ = ∑ Y, ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p *
          (filteredCoefficient p.1 p.2 a Y * filteredCoefficient p.1 p.2 a (X+Y)) else 0 := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← signed_triple_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X <;>
        by_cases hY : Incidence p.1 p.2 Y <;>
        by_cases hZ : Incidence p.1 p.2 (X+Y) <;>
        simp [filteredCoefficient, hX, hY, hZ]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X
      · simp only [hX, ite_true, pieceConvolution, Finset.mul_sum]
      · simp [hX]

omit [Fintype (Submodule F2 V)] in
theorem card_lower_rank_le (I : Submodule F2 V) (n i : ℕ)
    (hn : finrank F2 I ≤ n) :
    Nat.card {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i} ≤ 2^(n*i) := by
  let : Finite (Submodule F2 I) :=
    Finite.of_injective (fun S : Submodule F2 I => (S : Set I)) SetLike.coe_injective
  let e := SubmoduleInterval.lowerIntervalEquiv I
  let code (A : {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i}) :
      {S : Submodule F2 I // finrank F2 S = i} :=
    ⟨e ⟨A.1, A.2.1⟩,
      (SubmoduleInterval.lowerInterval_finrank I ⟨A.1, A.2.1⟩).trans A.2.2⟩
  have hi : Function.Injective code := by
    intro A B h
    have he : e ⟨A.1, A.2.1⟩ = e ⟨B.1, B.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {A : Submodule F2 V // A ≤ I} => z.val) (e.injective he)
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n i hn)

omit [Finite W] [Fintype (Submodule F2 W)] in
theorem card_upper_codim_le (K : Submodule F2 W) (n j : ℕ)
    (hn : finrank F2 (W ⧸ K) ≤ n) :
    Nat.card {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j} ≤ 2^(n*j) := by
  let D := Module.Dual F2 (W ⧸ K)
  let : Finite D := Finite.of_injective (Module.finBasis F2 D).equivFun
    (Module.finBasis F2 D).equivFun.injective
  let : Finite (Submodule F2 D) :=
    Finite.of_injective (fun S : Submodule F2 D => (S : Set D)) SetLike.coe_injective
  let e := UpperMobius.upperDualSubspaceEquiv K
  let code (B : {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j}) :
      {S : Submodule F2 D // finrank F2 S = j} :=
    ⟨e ⟨B.1, B.2.1⟩,
      (UpperMobius.upperDualSubspaceEquiv_codim K ⟨B.1, B.2.1⟩).symm.trans B.2.2⟩
  have hi : Function.Injective code := by
    intro B C h
    have he : e ⟨B.1, B.2.1⟩ = e ⟨C.1, C.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {B : Submodule F2 W // K ≤ B} => z.val) (e.injective he)
  have hdim : finrank F2 D ≤ n := by
    simpa only [D, Subspace.dual_finrank_eq] using hn
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n j hdim)

private theorem finite_pair_level_sum {α : Type*} (s : Finset α)
    (i j : α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hbound : ∀ a ∈ s, i a ≤ d ∧ j a ≤ d)
    (hzero : ∀ a ∈ s, ¬(i a=0 ∧ j a=0))
    (hcount : ∀ u v, (s.filter (fun a => i a=u ∧ j a=v)).card ≤ 2^(2*d*(u+v))) :
    (∑ a ∈ s, (1/2:ℝ)^(5*d*(i a+j a))) ≤ 1 := by
  classical
  have hmap : ∀ a ∈ s, (i a,j a) ∈ Finset.range (d+1) ×ˢ Finset.range (d+1) := by
    intro a ha
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).1),
       Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).2)⟩
  have hcancel (a b : ℕ) :
      (2:ℝ)^a * (1/2:ℝ)^(a+b) = (1/2:ℝ)^b := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  calc
    _ = ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(i a+j a)) := by
      have h := Finset.sum_fiberwise_of_maps_to (g := fun a => (i a,j a)) hmap
        (fun a => (1/2:ℝ)^(5*d*(i a+j a)))
      simpa only [Finset.sum_product, Prod.mk.injEq] using h.symm
    _ ≤ ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        if u=0 ∧ v=0 then 0 else (1/2:ℝ)^(3*d*(u+v)) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      by_cases hz : u=0 ∧ v=0
      · rw [ite_eq_left hz]
        have hempty : s.filter (fun a => i a=u ∧ j a=v) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro a ha
          have ham := Finset.mem_filter.mp ha
          exact hzero a ham.1 ⟨ham.2.1.trans hz.1, ham.2.2.trans hz.2⟩
        rw [hempty, Finset.sum_empty]
      · rw [ite_eq_right hz]
        have hc : ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) ≤
            (2:ℝ)^(2*d*(u+v)) := by exact_mod_cast hcount u v
        calc
          _ = ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) *
              (1/2:ℝ)^(5*d*(u+v)) := by
            calc
              _ = ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(u+v)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [(Finset.mem_filter.mp ha).2.1, (Finset.mem_filter.mp ha).2.2]
              _ = _ := by simp
          _ ≤ (2:ℝ)^(2*d*(u+v)) * (1/2:ℝ)^(5*d*(u+v)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
          _ = _ := by
            have he : 5*d*(u+v)=2*d*(u+v)+3*d*(u+v) := by ring
            rw [he, hcancel]
    _ ≤ 1 := DyadicError.finite_dyadic_error_le_one d hd

omit [Finite W] [Fintype (W →ₗ[F2] V)] in
theorem incident_pair_weight_le_one (X : W →ₗ[F2] V) (d : ℕ)
    (hd : 1 ≤ d) (hX : finrank F2 X.range ≤ 2*d) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
          finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
      then (1/2:ℝ)^(5*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) else 0) ≤ 1 := by
  let i (p : Submodule F2 V × Submodule F2 W) := finrank F2 p.1
  let j (p : Submodule F2 V × Submodule F2 W) := finrank F2 (W ⧸ p.2)
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧ i p ≤ d ∧ j p ≤ d
  let s := Finset.univ.filter good
  have hs (p) (hp : p ∈ s) : good p := (Finset.mem_filter.mp hp).2
  have hbound : ∀ p ∈ s, i p ≤ d ∧ j p ≤ d := by
    intro p hp
    exact (hs p hp).2.2.2
  have hzero : ∀ p ∈ s, ¬(i p=0 ∧ j p=0) := by
    intro p hp hz
    apply (hs p hp).1
    apply (pairDimension_eq_zero_iff p).mp
    exact Nat.add_eq_zero_iff.mpr hz
  have hquot : finrank F2 (W ⧸ X.ker) ≤ 2*d := by
    have hq := X.ker.finrank_quotient_add_finrank
    have hr := X.finrank_range_add_finrank_ker
    omega
  have hcount (u v : ℕ) : (s.filter (fun p => i p=u ∧ j p=v)).card ≤ 2^(2*d*(u+v)) := by
    let t := s.filter (fun p => i p=u ∧ j p=v)
    let LA := {A : Submodule F2 V // A ≤ X.range ∧ finrank F2 A=u}
    let LB := {B : Submodule F2 W // X.ker ≤ B ∧ finrank F2 (W ⧸ B)=v}
    let code (p : ↥t) : LA × LB := by
      have hp := Finset.mem_filter.mp p.property
      have hg := hs p.val hp.1
      exact (⟨p.val.1, hg.2.1, hp.2.1⟩, ⟨p.val.2, hg.2.2.1, hp.2.2⟩)
    have hi : Function.Injective code := by
      intro p q h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : LA × LB => z.1.val) h
      · exact congrArg (fun z : LA × LB => z.2.val) h
    have hc : t.card ≤ Nat.card (LA × LB) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Nat.card_le_card_of_injective code hi
    calc
      _ ≤ Nat.card (LA × LB) := hc
      _ = Nat.card LA * Nat.card LB := Nat.card_prod _ _
      _ ≤ 2^((2*d)*u) * 2^((2*d)*v) := Nat.mul_le_mul
        (card_lower_rank_le X.range (2*d) u hX)
        (card_upper_codim_le X.ker (2*d) v hquot)
      _ = _ := by rw [← pow_add]; congr 1; ring
  simpa only [s, Finset.sum_filter, good, i, j] using
    finite_pair_level_sum s i j d hd hbound hzero hcount

theorem mobius_sq (i : ℕ) : (mobius i)^2 = (2:ℝ)^(2*i.choose 2) := by
  have hs : ((-1:ℝ)^i)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm i 2, pow_mul]
    norm_num
  unfold mobius
  rw [mul_pow, hs, one_mul, ← pow_mul, Nat.mul_comm]

private theorem twice_choose_two_le_square (i : ℕ) : 2*i.choose 2 ≤ i*i := by
  induction i with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

theorem mobius_pair_sq_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 ≤ (2:ℝ)^(d*(i+j)) := by
  have he : 2*i.choose 2 + 2*j.choose 2 ≤ d*(i+j) := by
    calc
      _ ≤ i*i+j*j := Nat.add_le_add (twice_choose_two_le_square i)
        (twice_choose_two_le_square j)
      _ ≤ d*i+d*j := Nat.add_le_add (Nat.mul_le_mul_right i hi) (Nat.mul_le_mul_right j hj)
      _ = _ := (Nat.mul_add d i j).symm
  have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
  rw [mul_pow, mobius_sq, mobius_sq, ← pow_add]
  exact_mod_cast hn

theorem mobius_pair_weight_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 * (1/2:ℝ)^(6*d*(i+j)) ≤ (1/2:ℝ)^(5*d*(i+j)) := by
  calc
    _ ≤ (2:ℝ)^(d*(i+j)) * (1/2:ℝ)^(6*d*(i+j)) :=
      mul_le_mul_of_nonneg_right (mobius_pair_sq_le d i j hi hj) (by positivity)
    _ = _ := by
      have he : 6*d*(i+j) = d*(i+j)+5*d*(i+j) := by ring
      rw [he, pow_add, ← mul_assoc, ← mul_pow]
      norm_num

private theorem exists_nonzero_term {α : Type*} [Fintype α] (f : α → ℝ)
    (h : (∑ x, f x) ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro x _
  by_contra hx
  exact hn ⟨x,hx⟩

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem filteredCoefficient_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (Y : W →ₗ[F2] V)
    (h : filteredCoefficient A B a Y ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  have hi : Incidence A B Y := by
    by_contra hn
    exact h (by simp [filteredCoefficient, hn])
  have hay : a Y ≠ 0 := by
    simpa only [filteredCoefficient, ite_eq_left hi] using h
  have hr : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hay (ha Y (Nat.lt_of_not_ge hn))
  have hA := Submodule.finrank_mono hi.1
  have hB := Submodule.finrank_mono hi.2
  have hq := B.finrank_quotient_add_finrank
  have hY := Y.finrank_range_add_finrank_ker
  constructor <;> omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] in
theorem pieceConvolution_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (X : W →ₗ[F2] V)
    (h : pieceConvolution A B a X ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  obtain ⟨Y,hY⟩ := exists_nonzero_term _ h
  apply filteredCoefficient_nonzero_dimensions a d ha A B Y
  intro hz
  apply hY
  rw [hz, zero_mul]

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem rank_add_le (Y Z : W →ₗ[F2] V) :
    finrank F2 (Y+Z).range ≤ finrank F2 Y.range + finrank F2 Z.range := by
  have hle := Submodule.finrank_mono (LinearMap.range_add_le Y Z)
  have heq := Submodule.finrank_sup_add_finrank_inf_eq Y.range Z.range
  omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] in
theorem badConvolution_eq_zero_of_large_rank
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : 2*d < finrank F2 X.range) : badConvolution a X = 0 := by
  by_contra h
  obtain ⟨Y,hY⟩ := exists_nonzero_term _ h
  have hy : a Y ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hz : a (X+Y) ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hry : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hy (ha Y (Nat.lt_of_not_ge hn))
  have hrz : finrank F2 (X+Y).range ≤ d := by
    by_contra hn
    exact hz (ha (X+Y) (Nat.lt_of_not_ge hn))
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  have hr := rank_add_le Y (X+Y)
  rw [hc] at hr
  omega

private theorem scaled_product (c q : ℝ) (n : ℕ) :
    (c * (1/2:ℝ)^n) * ((2:ℝ)^n * q) = c*q := by
  have hc : (1/2:ℝ)^n * (2:ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = c * (((1/2:ℝ)^n * (2:ℝ)^n) * q) := by ring
    _ = _ := by rw [hc, one_mul]

theorem badConvolution_sq_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : finrank F2 X.range ≤ 2*d) :
    badConvolution a X ^ 2 ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
      finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
  let s := Finset.univ.filter good
  let u (p : Submodule F2 V × Submodule F2 W) :=
    signedWeight p * (1/2:ℝ)^(3*d*pairDimension p)
  let v (p : Submodule F2 V × Submodule F2 W) :=
    (2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X
  have heq : badConvolution a X = ∑ p ∈ s, u p * v p := by
    rw [badConvolution_expansion, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg]
      rw [ite_eq_left (show Incidence p.1 p.2 X from ⟨hg.2.1,hg.2.2.1⟩)]
      exact (scaled_product (signedWeight p) (pieceConvolution p.1 p.2 a X)
        (3*d*pairDimension p)).symm
    · rw [ite_eq_right hg]
      by_cases hi : Incidence p.1 p.2 X
      · rw [ite_eq_left hi]
        by_cases hp : p = (⊥,⊤)
        · simp [signedWeight,hp]
        · by_cases hq : pieceConvolution p.1 p.2 a X = 0
          · rw [hq,mul_zero]
          · exact False.elim (hg ⟨hp,hi.1,hi.2,
              pieceConvolution_nonzero_dimensions a d ha p.1 p.2 X hq⟩)
      · rw [ite_eq_right hi]
  have hu : (∑ p ∈ s, u p ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ s, (1/2:ℝ)^(5*d*pairDimension p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hg : good p := (Finset.mem_filter.mp hp).2
        have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
        change (signedWeight p * (1/2:ℝ)^(3*d*pairDimension p))^2 ≤ _
        rw [signedWeight, ite_eq_right hg.1, mul_pow, neg_sq, ← pow_mul, he]
        exact mobius_pair_weight_le d _ _ hg.2.2.2.1 hg.2.2.2.2
      _ ≤ 1 := by
        simpa only [s,Finset.sum_filter,good,pairDimension] using
          incident_pair_weight_le_one X d hd hX
  have hv0 : 0 ≤ ∑ p ∈ s, v p ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : (∑ p ∈ s, v p ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg, ite_eq_left hg.1]
      have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
      change ((2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X)^2 ≤ _
      rw [mul_pow, ← pow_mul, he]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hn : 6*d*pairDimension p ≤ 7*d*pairDimension p :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (by decide : 6 ≤ 7))
      exact_mod_cast Nat.pow_le_pow_right (n := 2) (by decide) hn
    · rw [ite_eq_right hg]
      split_ifs <;> positivity
  calc
    _ = (∑ p ∈ s, u p * v p)^2 := congrArg (fun x : ℝ => x^2) heq
    _ ≤ (∑ p ∈ s, u p^2) * ∑ p ∈ s, v p^2 := Finset.sum_mul_sq_le_sq_mul_sq s u v
    _ ≤ 1 * ∑ p ∈ s, v p^2 := mul_le_mul_of_nonneg_right hu hv0
    _ = ∑ p ∈ s, v p^2 := one_mul _
    _ ≤ _ := hv

/-- The actual signed bad-convolution estimate of A.1. -/
theorem badConvolution_sq_sum_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ X, badConvolution a X ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) *
          (∑ X, pieceConvolution p.1 p.2 a X ^ 2) else 0 := by
  calc
    _ ≤ ∑ X, ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hX : finrank F2 X.range ≤ 2*d
      · exact badConvolution_sq_le a d hd ha X hX
      · rw [badConvolution_eq_zero_of_large_rank a d ha X (Nat.lt_of_not_ge hX), zero_pow (by decide)]
        apply Finset.sum_nonneg
        intro p _
        split_ifs <;> positivity
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p = (⊥,⊤)
      · simp [hp]
      · simp [hp,pairDimension,Finset.mul_sum]

end UniqueGamesTheorem.Appendix.BadConvolution

end

end

end OAI
