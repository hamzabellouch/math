import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Small
import OAI.Combinatorics.IndependentSets.Reduction.SubchainView

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

def swapOccurrence {C : Type*} {n : ℕ} (h : Fin n) :
    ((Fin n → C) × C) → ((Fin n → C) × C) :=
  fun p => (Function.update p.1 h p.2, p.1 h)

lemma swapOccurrence_involutive {C : Type*} {n : ℕ} (h : Fin n) :
    Function.Involutive (swapOccurrence (C:=C) h) := by
  intro p
  apply Prod.ext
  · funext k
    by_cases hk : k = h <;> simp [swapOccurrence, hk]
  · simp [swapOccurrence]

lemma expect_update {C : Type*} [Fintype C] [Nonempty C] {n : ℕ} (h : Fin n)
    (f : (Fin n → C) → ℝ) :
    (𝔼 background, 𝔼 c, f (Function.update background h c)) = 𝔼 chain, f chain := by
  have he := Fintype.expect_equiv ((swapOccurrence_involutive h).toPerm (swapOccurrence h))
    (fun p : (Fin n → C) × C => f (Function.update p.1 h p.2)) (fun p => f p.1) (fun p => rfl)
  simpa only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const] using he

lemma expect_indicator {C : Type*} [Fintype C] (P : C → Prop) :
    (𝔼 c, if P c then (1:ℝ) else 0) =
      ((Finset.univ.filter P).card : ℝ) / Fintype.card C := by
  simp [Finset.expect_eq_sum_div_card, div_eq_mul_inv]

theorem separated_lists_probability {U V L R C : Type*}
    [Fintype C] [Nonempty C] [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {σ : ℝ} (hsound : lc.Sound σ)
    {n : ℕ} (h : Fin n) (I J : Finset (Fin (n+1)))
    (hI : ∀ i ∈ I, i.val ≤ h.val) (hJ : ∀ j ∈ J, h.val < j.val) (d : ℕ)
    (ruleI : SubchainView U V L R n I → Finset (SubchainCoord L R n I))
    (ruleJ : SubchainView U V L R n J → Finset (SubchainCoord L R n J))
    (hcardI : ∀ v, (ruleI v).card ≤ d) (hcardJ : ∀ v, (ruleJ v).card ≤ d) :
    (𝔼 chain : Fin n → C, if ¬ Disjoint
      (terminalList lc chain I (ruleI (chainView lc chain I)))
      (terminalList lc chain J (ruleJ (chainView lc chain J))) then (1:ℝ) else 0) ≤
      (d:ℝ)^2*σ := by
  rw [← expect_update h]
  apply Finset.expect_le Finset.univ_nonempty
  intro background _
  have hc := separated_lists_conditioned lc hsound background h I J hI hJ d ruleI ruleJ hcardI hcardJ
  have hh := (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0:ℝ) < Fintype.card C)).mpr hc
  simpa only [Finset.expect_eq_sum_div_card, Finset.sum_boole, Finset.card_univ] using hh

def ListsSeparated {r s : ℕ} {M : Type*} (A : Finset (Fin r) → Finset M) : Prop :=
  ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J)

lemma all_separated_probability {C M : Type*} [Fintype C] {r s : ℕ}
    (A : C → Finset (Fin r) → Finset M) {b : ℝ} (hb : 0 ≤ b)
    (hpair : ∀ I J, Small s I → Small s J → Separated I J →
      (𝔼 c, if ¬Disjoint (A c I) (A c J) then (1:ℝ) else 0) ≤ b) :
    (𝔼 c, if ¬ListsSeparated (s:=s) (A c) then (1:ℝ) else 0) ≤ 4^r*b := by
  let bad (c : C) (p : Finset (Fin r) × Finset (Fin r)) : ℝ :=
    if Small s p.1 ∧ Small s p.2 ∧ Separated p.1 p.2 ∧ ¬Disjoint (A c p.1) (A c p.2) then 1 else 0
  have hbad (c : C) (p) : 0 ≤ bad c p := by unfold bad; split_ifs <;> norm_num
  have hcover (c : C) : (if ¬ListsSeparated (s:=s) (A c) then (1:ℝ) else 0) ≤ ∑ p, bad c p := by
    by_cases hc : ListsSeparated (s:=s) (A c)
    · simp only [hc, not_true_eq_false, ite_false]
      exact Finset.sum_nonneg (fun p _ => hbad c p)
    · simp only [hc, not_false_eq_true, ite_true]
      simp only [ListsSeparated, not_forall] at hc
      obtain ⟨I,J,hI,hJ,hsep,hi⟩ := hc
      have hs := Finset.single_le_sum (fun p _ => hbad c p) (Finset.mem_univ (I,J))
      simpa [bad, hI, hJ, hsep, hi] using hs
  calc
    _ ≤ 𝔼 c, ∑ p, bad c p := Finset.expect_le_expect (fun c _ => hcover c)
    _ = ∑ p, 𝔼 c, bad c p := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _p : Finset (Fin r) × Finset (Fin r), b := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : Small s p.1 ∧ Small s p.2 ∧ Separated p.1 p.2
      · have he : (fun c => bad c p) = fun c => if ¬Disjoint (A c p.1) (A c p.2) then (1:ℝ) else 0 := by
          funext c; simp only [bad,hp.1,hp.2.1,hp.2.2,true_and]
        rw [he]
        exact hpair _ _ hp.1 hp.2.1 hp.2.2
      · have he : ∀ c, bad c p = 0 := by intro c; simp [bad, show ¬(Small s p.1 ∧ Small s p.2 ∧ Separated p.1 p.2 ∧ ¬Disjoint (A c p.1) (A c p.2)) by tauto]
        simp only [he, Finset.expect_const_zero]
        exact hb
    _ = 4^r*b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      rw [←mul_pow]; norm_num

lemma LayerLaw.badMass_le_one {r s : ℕ} (μ : LayerLaw r s) {M : Type}
    (A : Finset (Fin r) → Finset M) : (μ.badMass A : ℝ) ≤ 1 := by
  have h : μ.badMass A ≤ ∑ B, μ.weight B := by
    apply Finset.sum_le_sum
    intro B _; split_ifs; exact μ.nonneg B; exact le_rfl
  rw [μ.total] at h
  exact_mod_cast h

lemma good_pair_probability {C M : Type} [Fintype C] [Nonempty C]
    {r s d : ℕ} (μ : LayerLaw r s) {η σ : ℝ} (hη : 0 ≤ η) (hσ : 0 ≤ σ)
    (hμ : ∀ (A : Finset (Fin r) → Finset M),
      (∀ I, Small s I → (A I).card ≤ d) → ListsSeparated (s:=s) A → (μ.badMass A : ℝ) ≤ η)
    (A : C → Finset (Fin r) → Finset M)
    (hcard : ∀ c I, Small s I → (A c I).card ≤ d)
    (hpair : ∀ I J, Small s I → Small s J → Separated I J →
      (𝔼 c, if ¬Disjoint (A c I) (A c J) then (1:ℝ) else 0) ≤ (d:ℝ)^2*σ) :
    (𝔼 c, (μ.badMass (A c) : ℝ)) ≤ η + 4^r*(d:ℝ)^2*σ := by
  have hsep := all_separated_probability A (mul_nonneg (sq_nonneg _) hσ) hpair
  have hpoint (c : C) : (μ.badMass (A c) : ℝ) ≤ η + if ¬ListsSeparated (s:=s) (A c) then 1 else 0 := by
    by_cases hc : ListsSeparated (s:=s) (A c)
    · simpa only [hc, not_true_eq_false, ite_false, add_zero] using hμ _ (hcard c) hc
    · simpa only [hc, not_false_eq_true, ite_true] using (μ.badMass_le_one (A c)).trans (by linarith)
  calc
    _ ≤ (𝔼 c : C, (η + (if ¬ListsSeparated (s:=s) (A c) then 1 else 0))) :=
      Finset.expect_le_expect (fun c _ => hpoint c)
    _ = η + (𝔼 c, if ¬ListsSeparated (s:=s) (A c) then 1 else 0) := by
      rw [Finset.expect_add_distrib, Fintype.expect_const]
    _ ≤ η + 4^r*((d:ℝ)^2*σ) := add_le_add_right hsep _
    _ = _ := by ring

lemma separated_cut {n : ℕ} {I J : Finset (Fin (n+1))}
    (hI : I.Nonempty) (hJ : J.Nonempty) (hsep : Separated I J) :
    ∃ h : Fin n, (∀ i ∈ I, i.val ≤ h.val) ∧ (∀ j ∈ J, h.val < j.val) := by
  let i := I.max' hI
  have hi : i ∈ I := I.max'_mem hI
  obtain ⟨j,hj⟩ := hJ
  have hij := hsep i hi j hj
  have hn : i.val < n := by have := j.isLt; change i.val < j.val at hij; omega
  refine ⟨⟨i.val,hn⟩,?_,?_⟩
  · intro k hk; exact I.le_max' k hk
  · intro k hk; exact hsep i hi k hk

theorem source_lists_probability {U V L R C : Type} [Fintype C] [Nonempty C]
    [Nonempty L] [Nonempty R] (lc : LabelCoverData U V L R C)
    {σ : ℝ} (hsound : lc.Sound σ) {n s d : ℕ}
    (rule : ∀ I : Finset (Fin (n+1)), SubchainView U V L R n I → Finset (SubchainCoord L R n I))
    (hcard : ∀ I, Small s I → ∀ v, (rule I v).card ≤ d)
    (I J : Finset (Fin (n+1))) (hI : Small s I) (hJ : Small s J) (hsep : Separated I J) :
    (𝔼 chain : Fin n → C, if ¬Disjoint
      (terminalList lc chain I (rule I (chainView lc chain I)))
      (terminalList lc chain J (rule J (chainView lc chain J))) then (1:ℝ) else 0) ≤ (d:ℝ)^2*σ := by
  obtain ⟨h,hi,hj⟩ := separated_cut hI.1 hJ.1 hsep
  exact separated_lists_probability lc hsound h I J hi hj d (rule I) (rule J) (hcard I hI) (hcard J hJ)

end LargeIndependentSets

end OAI
