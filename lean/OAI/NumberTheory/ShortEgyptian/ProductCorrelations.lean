import OAI.NumberTheory.ShortEgyptian.BilinearProducts

namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def sampleProduct {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (I : J → Bool) (f : (J × Bool) → A) : ℕ := ∏ j, p (f (j,I j))

lemma pair_exposure_identity {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (u l : ℕ) [NeZero u] (I K : J → Bool)
    (L R : Finset J) (hdis : Disjoint L R)
    (hdiffL : ∀ j ∈ L, I j ≠ K j) (hdiffR : ∀ j ∈ R, I j ≠ K j) (a0 : A) :
    (𝔼 f : (J × Bool) → A,
      ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))) =
    𝔼 b : J → A, 𝔼 z : ((L∪R)ᶜ : Finset J) → A, 𝔼 x : L → A, 𝔼 y : R → A,
      ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K
        (fun jb => if jb.2 = I jb.1 then mergeSamples L R z (fun _ => a0) (fun _ => a0) jb.1 else b jb.1):ℕ):ZMod u)) := by
  let normed (x y : J → A) (jb : J × Bool) := if jb.2 = I jb.1 then x jb.1 else y jb.1
  let second (z : ((L∪R)ᶜ : Finset J) → A) (b : J → A) :=
    sampleProduct p K (normed (mergeSamples L R z (fun _ => a0) (fun _ => a0)) b)
  let C (f : (J × Bool) → A) : ℂ :=
    ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))
  let F (b : J → A) (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) : ℂ :=
    ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*second z b:ℕ):ZMod u))
  have hpoint b z x y : C (normed (mergeSamples L R z x y) b) = F b z x y := by
    have hI : sampleProduct p I (normed (mergeSamples L R z x y) b) =
        (∏ j,p (z j))*(∏ j,p (x j))*(∏ j,p (y j)) := by
      simp only [sampleProduct,normed,ite_eq_left rfl]
      exact prod_mergeSamples L R hdis z x y p
    have hK : sampleProduct p K (normed (mergeSamples L R z x y) b) = second z b := by
      apply prod_congr rfl
      intro j _
      by_cases h : K j = I j
      · have hl' : j ∉ L := fun hj => hdiffL j hj h.symm
        have hr' : j ∉ R := fun hj => hdiffR j hj h.symm
        simp [normed,mergeSamples,h,hl',hr']
      · simp [normed,h]
    dsimp only [C,F]
    rw [hI,hK]
    congr 3
    ring
  have hfull : (𝔼 f, C f) = 𝔼 b : J → A, 𝔼 z : ((L∪R)ᶜ : Finset J) → A,
      𝔼 x : L → A, 𝔼 y : R → A, F b z x y := by
    rw [expect_normalize I,expect_comm]
    apply expect_congr rfl
    intro b _
    rw [expect_partition L R hdis]
    apply expect_congr rfl
    intro z _
    apply expect_congr rfl
    intro x _
    apply expect_congr rfl
    intro y _
    exact hpoint b z x y
  exact hfull

lemma pair_correlation_bound {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u l : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l) (I K : J → Bool)
    (L R : Finset J) (hdis : Disjoint L R) (hcard : R.card = L.card)
    (hdiffL : ∀ j ∈ L, I j ≠ K j) (hdiffR : ∀ j ∈ R, I j ≠ K j)
    (Q G B M a : ℝ) (hG : 0 < G) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hscale : (l:ℝ)*G*Q ≤ u)
    (hprod : ∀ f : L → A, (∏ j, p (f j):ℕ) < Q)
    (hprodR : ∀ f : R → A, (∏ j, p (f j):ℕ) < Q)
    (hatom : (L.card:ℝ)^L.card/(Fintype.card A:ℝ)^L.card ≤ B)
    (hMoment : (𝔼 z : ((L∪R)ᶜ : Finset J) → A, (Nat.gcd (∏ j,p (z j)) u:ℝ)^a) ≤ M) :
    ‖𝔼 f : (J × Bool) → A,
      ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))‖ ≤
        M/G^a+Real.sqrt u*B := by
  let a0 : A := Classical.choice ‹Nonempty A›
  let normed (x y : J → A) (jb : J × Bool) := if jb.2 = I jb.1 then x jb.1 else y jb.1
  let second (z : ((L∪R)ᶜ : Finset J) → A) (b : J → A) :=
    sampleProduct p K (normed (mergeSamples L R z (fun _ => a0) (fun _ => a0)) b)
  let C (f : (J × Bool) → A) : ℂ :=
    ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))
  let F (b : J → A) (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) : ℂ :=
    ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)*
      (starRingEnd ℂ) (ZMod.stdAddChar ((l*second z b:ℕ):ZMod u))
  have hfull : (𝔼 f, C f) = 𝔼 b : J → A, 𝔼 z : ((L∪R)ᶜ : Finset J) → A,
      𝔼 x : L → A, 𝔼 y : R → A, F b z x y :=
    pair_exposure_identity p u l I K L R hdis hdiffL hdiffR a0
  have hfresh (b : J → A) (z : ((L∪R)ᶜ : Finset J) → A) :
      ‖𝔼 x : L → A, 𝔼 y : R → A, F b z x y‖ ≤
        (if G ≤ (Nat.gcd (∏ j,p (z j)) u:ℝ) then 1 else 0)+Real.sqrt u*B := by
    have heq : ‖𝔼 x : L → A, 𝔼 y : R → A, F b z x y‖ =
        ‖𝔼 x : L → A, 𝔼 y : R → A,
          ZMod.stdAddChar (((l*(∏ j,p (z j)))*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)‖ := by
      dsimp only [F]
      simp only [← expect_mul,norm_mul,Complex.norm_conj,stdAddChar_norm,mul_one]
    rw [heq]
    split_ifs with h
    · apply le_trans (b := (1:ℝ))
      · apply (RCLike.norm_expect_le (K := ℂ)).trans
        apply expect_le univ_nonempty
        intro x _
        exact (RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun y _ => by simp))
      · exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg u) hB)
    · rw [zero_add]
      exact finset_fixed_bilinear p hp hinj u l _ hu hl L R hcard Q G B hG hB
        (le_of_not_ge h) hscale hprod hprodR hatom
  have hbad : (𝔼 z : ((L∪R)ᶜ : Finset J) → A,
      if G ≤ (Nat.gcd (∏ j,p (z j)) u:ℝ) then (1:ℝ) else 0) ≤ M/G^a := by
    calc
      _ ≤ 𝔼 z : ((L∪R)ᶜ : Finset J) → A,
        if G^a ≤ (Nat.gcd (∏ j,p (z j)) u:ℝ)^a then (1:ℝ) else 0 := by
        apply expect_le_expect
        intro z _
        split_ifs with h h'
        · rfl
        · exact False.elim (h' (Real.rpow_le_rpow hG.le h ha))
        · positivity
        · rfl
      _ ≤ (𝔼 z : ((L∪R)ᶜ : Finset J) → A, (Nat.gcd (∏ j,p (z j)) u:ℝ)^a)/G^a :=
        finite_markov _ (fun _ => by positivity) _ (Real.rpow_pos_of_pos hG _)
      _ ≤ _ := div_le_div_of_nonneg_right hMoment (Real.rpow_nonneg hG.le _)
  change ‖𝔼 f, C f‖ ≤ _
  rw [hfull]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro b _
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply (expect_le_expect (fun z _ => hfresh b z)).trans
  rw [expect_add_distrib,Fintype.expect_const]
  linarith

lemma disjoint_subsets_card {J : Type uJ} [Fintype J] (D : Finset J) (s : ℕ) (hs : 2*s ≤ D.card) :
    ∃ L R : Finset J, L ⊆ D ∧ R ⊆ D ∧ Disjoint L R ∧ L.card = s ∧ R.card = s := by
  obtain ⟨L,hLD,hLs⟩ := exists_subset_card_eq (show s ≤ D.card by omega)
  have hcard : s ≤ (D\L).card := by
    rw [card_sdiff_of_subset hLD,hLs]
    omega
  obtain ⟨R,hRD,hRs⟩ := exists_subset_card_eq hcard
  refine ⟨L,R,hLD,(fun j hj => (mem_sdiff.mp (hRD hj)).1),?_,hLs,hRs⟩
  exact disjoint_left.mpr (fun j hjL hjR => (mem_sdiff.mp (hRD hjR)).2 hjL)

lemma mean_square_correlation_exp {A : Type uA} {J : Type uJ} [Fintype A] [Nonempty A] [Fintype J]
    (F : (J → Bool) → A → ℂ) (hnorm : ∀ I a, ‖F I a‖ ≤ 1)
    (k : ℕ) (hk : 4*k ≤ Fintype.card J) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hcorr : ∀ I K, k ≤ hammingDistance I K →
      ‖𝔼 a, F I a*(starRingEnd ℂ) (F K a)‖ ≤ epsilon) :
    (𝔼 a, ‖𝔼 I : J → Bool, F I a‖^2) ≤
      Real.exp (-(Fintype.card J:ℝ)/16)+epsilon := by
  have hbound : (2:ℝ)^k*(3/4:ℝ)^Fintype.card J ≤ Real.exp (-(Fintype.card J:ℝ)/16) := by
    have hL : Real.log (3/4:ℝ) ≤ -(1/4:ℝ) := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3/4)
      linarith
    have h2 : Real.log (2:ℝ) ≤ 3/4 := by linarith [Real.log_two_lt_d9]
    have hkR : 4*(k:ℝ) ≤ Fintype.card J := by exact_mod_cast hk
    rw [← Real.exp_log (by positivity : (0:ℝ)<(2:ℝ)^k*(3/4:ℝ)^Fintype.card J)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    have h1 := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg (Fintype.card J))
    have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
    nlinarith only [h1,h3,hkR]
  exact (mean_square_correlation_bound F hnorm k epsilon heps hcorr).trans (add_le_add hbound le_rfl)

end ShortEgyptian

end OAI
