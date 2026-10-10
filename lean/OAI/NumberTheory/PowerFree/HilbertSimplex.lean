import OAI.NumberTheory.PowerFree.ResidueRelations

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators

theorem extend_independent_finset {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (S A : Finset ι)
    (hAS : A ⊆ S) (hA : LinearIndepOn K v (A : Set ι)) (m : ℕ)
    (hAm : A.card ≤ m) (hm : m ≤ Module.finrank K (Submodule.span K (v '' (S : Set ι)))) :
    ∃ B : Finset ι, A ⊆ B ∧ B ⊆ S ∧ B.card = m ∧ LinearIndepOn K v (B : Set ι) := by
  classical
  have hsub : (A : Set ι) ⊆ (S : Set ι) := hAS
  let T := hA.extend hsub
  have hTs : T ⊆ (S : Set ι) := hA.extend_subset hsub
  have hfin : T.Finite := S.finite_toSet.subset hTs
  let B := hfin.toFinset
  have hli : LinearIndepOn K v (B : Set ι) := by
    simpa only [B, Set.Finite.coe_toFinset] using hA.linearIndepOn_extend hsub
  have hspan : Submodule.span K (v '' (B : Set ι)) =
      Submodule.span K (v '' (S : Set ι)) := by
    simpa only [B, Set.Finite.coe_toFinset] using hA.span_image_extend_eq_span_image hsub
  have hcard : Module.finrank K (Submodule.span K (v '' (B : Set ι))) = B.card := by
    have hh := finrank_span_eq_card (hli.linearIndependent_restrict)
    change Module.finrank K (Submodule.span K (Set.range (fun a : B => v a))) = _ at hh
    have hr : Set.range (fun a : B => v a) = v '' (B : Set ι) := by
      ext x
      constructor
      · rintro ⟨a,rfl⟩; exact ⟨a,a.property,rfl⟩
      · rintro ⟨a,ha,rfl⟩; exact ⟨⟨a,ha⟩,rfl⟩
    rw [hr] at hh
    simpa using hh
  have hAB : A ⊆ B := fun a ha => hfin.mem_toFinset.mpr (hA.subset_extend hsub ha)
  have hBS : B ⊆ S := fun a ha => hTs (hfin.mem_toFinset.mp ha)
  have hmB : m ≤ B.card := by rw [← hcard,hspan]; exact hm
  obtain ⟨C,hAC,hCB,hC⟩ := Finset.exists_subsuperset_card_eq hAB hAm hmB
  exact ⟨C,hAC,hCB.trans hBS,hC,hli.mono hCB⟩

theorem hilbert_simplex_shift (h : ℕ) (hh : 0 < h) (δ c : ℝ)
    (hδ : 0 < δ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℕ,
      ((t+h).choose h : ℝ) ≤ (δ*t+C)^h / ((h.factorial : ℝ)*δ^h) -
        c*(δ*t+C)^(h-1) := by
  let a : ℝ := (h.factorial : ℝ)*c*δ^(h-1) + 1/δ
  let C : ℝ := δ*((h : ℝ)+a)
  have hf : (0 : ℝ) < h.factorial := by exact_mod_cast h.factorial_pos
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hC : 1 ≤ C := by
    dsimp [C,a]
    rw [mul_add, mul_add, div_eq_mul_inv, one_mul, mul_inv_cancel₀ hδ.ne']
    have hN : 0 ≤ δ*(h:ℝ)+δ*((h.factorial:ℝ)*c*δ^(h-1)) := by positivity
    linarith
  refine ⟨C,hC,fun t => ?_⟩
  let x : ℝ := (t+h : ℕ)+a
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hlow : ((t+h : ℕ) : ℝ) ≤ x := by dsimp [x]; linarith
  have hT : δ*t+C = δ*x := by dsimp [C,x]; push_cast; ring
  have hpow : x^h = x^(h-1)*x := by rw [← pow_succ,Nat.sub_add_cancel hh]
  have hnum : ((t+h : ℕ) : ℝ)^h ≤ x^h - (h.factorial : ℝ)*c*δ^(h-1)*x^(h-1) := by
    have hq : ((t+h : ℕ) : ℝ)^(h-1) ≤ x^(h-1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hlow _
    have hb : ((t+h : ℕ) : ℝ) ≤ x - (h.factorial : ℝ)*c*δ^(h-1) := by
      dsimp [x,a]
      linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 1) hδ.le]
    calc
      _ = ((t+h : ℕ) : ℝ)^(h-1)*((t+h : ℕ) : ℝ) := by
        rw [← pow_succ,Nat.sub_add_cancel hh]
      _ ≤ x^(h-1)*(x-(h.factorial : ℝ)*c*δ^(h-1)) :=
        mul_le_mul hq hb (Nat.cast_nonneg _) (pow_nonneg hx _)
      _ = _ := by rw [hpow]; ring
  have hb := (Nat.choose_le_pow_div h (t+h) : ((t+h).choose h : ℝ) ≤
      ((t+h : ℕ) : ℝ)^h / (h.factorial : ℝ))
  apply hb.trans
  rw [hT,mul_pow,mul_pow]
  have he : δ^h*x^h / ((h.factorial:ℝ)*δ^h) - c*(δ^(h-1)*x^(h-1)) =
      (x^h-(h.factorial:ℝ)*c*δ^(h-1)*x^(h-1))/(h.factorial:ℝ) := by
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hnum hf.le

theorem simplex_order_step (h t : ℕ) :
    h*((t+1+h).choose (h+1)) + (t+1)*((t+h).choose h) =
      h*((t+h).choose (h+1)) + (t+1)*((t+1+h).choose h) := by
  have h₁ := Nat.choose_succ_succ (t+h) h
  have h₂ := Nat.choose_mul_succ_eq (t+h) h
  rw [show t+h+1-h = t+1 by omega] at h₂
  rw [show t+1+h = t+h+1 by omega]
  nlinarith

theorem independent_weighted_simplex {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (S : ℕ → Finset ι)
    (hS : ∀ t, S t ⊆ S (t+1)) (w : ι → ℝ) (δ C : ℝ)
    (hweight : ∀ t a, a ∈ S t → w a ≤ δ*t+C)
    (h : ℕ) (hrank : ∀ t, (t+h).choose h ≤
      Module.finrank K (Submodule.span K (v '' (S t : Set ι)))) (t : ℕ) :
    ∃ A : Finset ι, A ⊆ S t ∧ A.card = (t+h).choose h ∧
      LinearIndepOn K v (A : Set ι) ∧
      ∑ a ∈ A, w a ≤ δ*(h*((t+h).choose (h+1)) : ℕ) + C*((t+h).choose h) := by
  classical
  induction t with
  | zero =>
    obtain ⟨A,_,hA,hcard,hli⟩ := extend_independent_finset v (S 0) ∅
      (Finset.empty_subset _) (by simp)
      ((0+h).choose h) (by simp) (hrank 0)
    refine ⟨A,hA,hcard,hli,?_⟩
    have hb := Finset.sum_le_sum (s := A) (fun a ha => hweight 0 a (hA ha))
    simpa only [Nat.cast_zero,mul_zero,zero_add,Finset.sum_const, nsmul_eq_mul,
      hcard,Nat.choose_self,Nat.cast_one,mul_one,one_mul,Nat.choose_eq_zero_of_lt (Nat.lt_succ_self h),
      Nat.mul_zero] using hb
  | succ t ih =>
    obtain ⟨A,hA,hcard,hli,hsum⟩ := ih
    have hcount : A.card ≤ (t+1+h).choose h := by
      rw [hcard]
      exact Nat.choose_le_choose h (by omega)
    obtain ⟨B,hAB,hB,hBcard,hlB⟩ := extend_independent_finset v (S (t+1)) A
      (hA.trans (hS t)) hli ((t+1+h).choose h) hcount (hrank (t+1))
    refine ⟨B,hB,hBcard,hlB,?_⟩
    have hnew : ∑ a ∈ B \ A, w a ≤ ((B \ A).card : ℝ)*(δ*(t+1)+C) := by
      calc
        _ ≤ ∑ _a ∈ B \ A, (δ*(t+1)+C) := by
          apply Finset.sum_le_sum
          intro a ha
          have haW := hweight (t+1) a (hB (Finset.mem_sdiff.mp ha).1)
          simpa only [Nat.cast_add,Nat.cast_one] using haW
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
    have hsplit : (∑ a ∈ B \ A, w a) + (∑ a ∈ A, w a) = ∑ a ∈ B, w a :=
      Finset.sum_sdiff hAB
    have hcarddiff : ((B \ A).card : ℝ) = (B.card : ℝ)-(A.card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hAB,Nat.cast_sub (Finset.card_le_card hAB)]
    have hstep : (h*((t+1+h).choose (h+1)) : ℕ) +
        ((t+1)*((t+h).choose h) : ℕ) =
      (h*((t+h).choose (h+1)) : ℕ) + ((t+1)*((t+1+h).choose h) : ℕ) :=
      simplex_order_step h t
    have hstepR : (h*((t+1+h).choose (h+1)) : ℝ) +
        ((t:ℝ)+1)*((t+h).choose h) =
      (h*((t+h).choose (h+1)) : ℝ) + ((t:ℝ)+1)*((t+1+h).choose h) := by
      exact_mod_cast hstep
    rw [hcarddiff,hcard,hBcard] at hnew
    push_cast at hsum ⊢
    have he : (δ*(t+1)+C)*(((t+1+h).choose h : ℝ)-((t+h).choose h : ℝ)) +
        (δ*(h:ℝ)*((t+h).choose (h+1))) + C*((t+h).choose h) =
      δ*(h:ℝ)*((t+1+h).choose (h+1)) + C*((t+1+h).choose h) := by
      nlinarith [congrArg (fun x : ℝ => δ*x) hstepR]
    rw [← hsplit]
    calc
      _ ≤ (( (t+1+h).choose h : ℝ)-((t+h).choose h : ℝ))*(δ*(t+1)+C) +
          (δ*((h:ℝ)*((t+h).choose (h+1))) + C*((t+h).choose h)) := add_le_add hnew hsum
      _ = _ := by nlinarith [he]

open scoped BigOperators
open MvPolynomial

noncomputable def monomialWeight {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (a : σ →₀ ℕ) : ℝ := ∑ i, ω i*(a i : ℝ)

theorem monomialWeight_nonneg {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 ≤ ω i) (a : σ →₀ ℕ) : 0 ≤ monomialWeight ω a :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hω i) (Nat.cast_nonneg _))

noncomputable def weightedExponentBound {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => ⌊T/ω i⌋₊)

noncomputable def weightedMonomials {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : Finset (σ →₀ ℕ) := by
  classical
  exact (Finset.Iic (weightedExponentBound ω T)).filter fun a => monomialWeight ω a ≤ T

theorem mem_weightedMonomials {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ) :
    a ∈ weightedMonomials ω T ↔ monomialWeight ω a ≤ T := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ?_,ha⟩
    intro i
    change a i ≤ ⌊T/ω i⌋₊
    apply Nat.le_floor
    apply (le_div_iff₀ (hω i)).mpr
    have hi := Finset.single_le_sum
      (fun j _ => mul_nonneg (hω j).le (Nat.cast_nonneg (a j))) (Finset.mem_univ i)
    simpa only [mul_comm (a i : ℝ)] using hi.trans ha

theorem weightedMonomials_mono {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) {S T : ℝ} (h : S ≤ T) :
    weightedMonomials ω S ⊆ weightedMonomials ω T := by
  intro a ha
  exact (mem_weightedMonomials ω hω T a).mpr
    (((mem_weightedMonomials ω hω S a).mp ha).trans h)

noncomputable def weightedDegreeBound {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : ℕ := ∑ i, ⌊T/ω i⌋₊

theorem weighted_monomial_degree_bound {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (hω : ∀ i, 0 < ω i) (T : ℝ) (a : σ →₀ ℕ)
    (ha : monomialWeight ω a ≤ T) : a.sum (fun _ e => e) ≤ weightedDegreeBound ω T := by
  classical
  have hs := (Finset.mem_filter.mp ((mem_weightedMonomials ω hω T a).mpr ha)).1
  have hb : a ≤ weightedExponentBound ω T := Finset.mem_Iic.mp hs
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_le_sum (fun i _ => hb i)

noncomputable def weightedFunctions {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  Submodule.span K ((fun a => Ideal.Quotient.mk I (monomial a (1:K))) ''
    (weightedMonomials ω T : Set (σ →₀ ℕ)))

instance weightedFunctions_finite {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) :
    Module.Finite K (weightedFunctions I ω T) := by
  classical
  exact Module.Finite.span_of_finite K ((weightedMonomials ω T).finite_toSet.image _)

noncomputable def weightedHilbert {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) : ℕ :=
  Module.finrank K (weightedFunctions I ω T)

theorem integer_monomial_abs_le {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (C X : ℝ) (hC : 1 ≤ C) (hX : 0 < X)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ C * X^(ω i)) (a : σ →₀ ℕ)
    (D : ℕ) (hD : a.sum (fun _ e => e) ≤ D) :
    |((eval z (monomial a (1:ℤ)) : ℤ) : ℝ)| ≤ C^D * X^(monomialWeight ω a) := by
  classical
  have hprod : |((eval z (monomial a (1:ℤ)) : ℤ) : ℝ)| = ∏ i, |(z i : ℝ)|^(a i) := by
    rw [eval_monomial,one_mul,Finsupp.prod_fintype _ _ (by simp)]
    simp only [Int.cast_prod,Int.cast_pow,Finset.abs_prod,abs_pow]
  have hexp : (∏ i, (X^(ω i))^(a i)) = X^(monomialWeight ω a) := by
    simp_rw [← Real.rpow_mul_natCast hX.le]
    rw [← Real.rpow_sum_of_pos hX]
    rfl
  calc
    _ = ∏ i, |(z i : ℝ)|^(a i) := hprod
    _ ≤ ∏ i, (C*X^(ω i))^(a i) := Finset.prod_le_prod₀
      (fun i _ => pow_nonneg (abs_nonneg _) _) (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hz i) _)
    _ = C^(a.sum (fun _ e => e)) * X^(monomialWeight ω a) := by
      simp_rw [mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hexp]
      rw [Finsupp.sum_fintype _ _ (by simp)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hD) (Real.rpow_nonneg hX.le _)

end

open scoped BigOperators
open MvPolynomial

theorem select_weighted_monomials {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (hω : ∀ i, 0 < ω i)
    (h : ℕ) (hh : 0 < h) (δ c : ℝ) (hδ : 0 < δ) (hc : 0 ≤ c)
    (hH : ∀ T : ℝ, 1 ≤ T → T^h / ((h.factorial : ℝ)*δ^h)-c*T^(h-1) ≤
      weightedHilbert I ω T) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℕ, ∃ A : Finset (σ →₀ ℕ),
      A.card = (t+h).choose h ∧
      LinearIndepOn K (fun a => Ideal.Quotient.mk I (monomial a (1:K))) (A : Set _) ∧
      (∀ a ∈ A, monomialWeight ω a ≤ δ*t+C) ∧
      (∀ a ∈ A, a.sum (fun _ e => e) ≤ weightedDegreeBound ω (δ*t+C)) ∧
      ∑ a ∈ A, monomialWeight ω a ≤ δ*(h*((t+h).choose (h+1)) : ℕ)+C*((t+h).choose h) := by
  obtain ⟨C,hC,hshift⟩ := hilbert_simplex_shift h hh δ c hδ hc
  refine ⟨C,hC,?_⟩
  intro t
  let S := fun t : ℕ => weightedMonomials ω (δ*t+C)
  have hS : ∀ t, S t ⊆ S (t+1) := by
    intro t
    apply weightedMonomials_mono ω hω
    push_cast
    linarith
  have hw : ∀ t a, a ∈ S t → monomialWeight ω a ≤ δ*t+C := by
    intro t a ha
    exact (mem_weightedMonomials ω hω _ a).mp ha
  have hr : ∀ t, (t+h).choose h ≤ Module.finrank K
      (Submodule.span K ((fun a => Ideal.Quotient.mk I (monomial a (1:K))) '' (S t : Set _))) := by
    intro t
    have hT : 1 ≤ δ*(t:ℝ)+C := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg t)]
    have hb := (hshift t).trans (hH _ hT)
    exact_mod_cast hb
  obtain ⟨A,hA,hcard,hli,hsum⟩ := independent_weighted_simplex
    (fun a => Ideal.Quotient.mk I (monomial a (1:K))) S hS (monomialWeight ω) δ C hw h hr t
  refine ⟨A,hcard,hli,fun a ha => hw t a (hA ha),?_,hsum⟩
  exact fun a ha => weighted_monomial_degree_bound ω hω _ a (hw t a (hA ha))

theorem exists_simplex_margin (h : ℕ) (hh : 0 < h) (ν C : ℝ) (hν : 0 < ν) :
    ∃ t : ℕ, 0 < (t+h).choose h ∧
      (C+1)*((t+h).choose h : ℝ) ≤ ν*(h*((t+h).choose (h+1)) : ℕ) := by
  obtain ⟨t,ht⟩ := exists_nat_gt (((C+1)*((h:ℝ)+1))/(ν*h))
  have hp : 0 < ν*(h:ℝ) := mul_pos hν (by exact_mod_cast hh)
  have ht' := (div_lt_iff₀ hp).mp ht
  have hchoose : (h+1)*((t+h).choose (h+1)) = t*((t+h).choose h) := by
    have hc := Nat.add_one_mul_choose_eq (t+h) h
    rw [Nat.choose_succ_succ] at hc
    nlinarith
  have hr : ((h:ℝ)+1)*((t+h).choose (h+1) : ℝ) = (t:ℝ)*((t+h).choose h) := by
    exact_mod_cast hchoose
  have hL : 0 < (t+h).choose h := Nat.choose_pos (by omega)
  refine ⟨t,hL,?_⟩
  have hb := mul_le_mul_of_nonneg_right ht'.le (show (0:ℝ) ≤ (t+h).choose h by positivity)
  push_cast
  nlinarith

end QuarticPowerFree

end OAI
