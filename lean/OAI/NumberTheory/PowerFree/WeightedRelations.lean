import OAI.NumberTheory.PowerFree.HilbertSimplex

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators
open MvPolynomial

theorem weighted_row_product_lt {α : Type*} [Fintype α]
    (w : α → ℝ) (C X δ ν c Q : ℝ) (D m : ℕ)
    (hX : 1 < X)
    (hlarge : (Fintype.card α).factorial * (C^D)^(Fintype.card α) < X)
    (hL : 0 < Fintype.card α)
    (hsum : ∑ a, w a ≤ δ*(m:ℝ)+c*(Fintype.card α))
    (hmargin : (c+1)*(Fintype.card α : ℝ) ≤ ν*(m:ℝ))
    (hQ : X^(δ+ν) ≤ Q) :
    (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, (C^D * X^(w a)) < Q^m := by
  classical
  have hpos : 0 < X := lt_trans zero_lt_one hX
  have hprod : (∏ a, (C^D * X^(w a))) = (C^D)^(Fintype.card α)*X^(∑ a, w a) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Real.rpow_sum_of_pos hpos]
  have hweight : (∑ a, w a)+1 ≤ (δ+ν)*(m:ℝ) := by
    have hcL : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast hL
    nlinarith
  calc
    _ = ((Fintype.card α).factorial * (C^D)^(Fintype.card α))*X^(∑ a, w a) := by rw [hprod]; ring
    _ < X*X^(∑ a, w a) := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hpos _)
    _ = X^((∑ a, w a)+1) := by rw [Real.rpow_add hpos,Real.rpow_one,mul_comm]
    _ ≤ X^((δ+ν)*(m:ℝ)) := Real.rpow_le_rpow_of_exponent_le hX.le hweight
    _ = (X^(δ+ν))^m := Real.rpow_mul_natCast hpos.le _ m
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) hQ m

theorem independent_monomial_relation_proper {σ α K : Type*}
    [Fintype α] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial σ K)) (a : α → (σ →₀ ℕ))
    (hli : LinearIndependent K (fun i => Ideal.Quotient.mk I (monomial (a i) (1:K))))
    (c : α → ℚ) (hc : c ≠ 0) :
    MvPolynomial.map (algebraMap ℚ K) (∑ i, monomial (a i) (c i)) ∉ I := by
  intro hp
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have he (i : α) : monomial (a i) (algebraMap ℚ K (c i)) =
      (algebraMap ℚ K (c i)) • monomial (a i) (1:K) := by
    simp only [smul_monomial,smul_eq_mul,mul_one]
  simp only [map_sum,MvPolynomial.map_monomial,he] at hz
  change ∑ i, (Ideal.Quotient.mkₐ K I) ((algebraMap ℚ K (c i)) • monomial (a i) (1:K)) = 0 at hz
  simp only [map_smul] at hz
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) (fun i => algebraMap ℚ K (c i)) hz
  apply hc
  funext i
  change c i = 0
  exact (algebraMap ℚ K).injective (by simpa only [map_zero] using hcoeff i)

theorem monomial_relation_degree {σ α : Type*} [Fintype α]
    (a : α → (σ →₀ ℕ)) (c : α → ℚ) (D : ℕ)
    (hD : ∀ i, (a i).sum (fun _ e => e) ≤ D) :
    (∑ i, monomial (a i) (c i)).totalDegree ≤ D := by
  exact totalDegree_finsetSum_le (fun i _ => (totalDegree_monomial_le _ _).trans (hD i))

theorem monomial_relation_eval {σ α : Type*} [Fintype α]
    (a : α → (σ →₀ ℕ)) (c : α → ℚ) (z : σ → ℤ)
    (hz : ∑ i, c i * (eval z (monomial (a i) (1:ℤ)) : ℚ) = 0) :
    eval (fun i => (z i : ℚ)) (∑ i, monomial (a i) (c i)) = 0 := by
  rw [map_sum]
  convert hz using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [eval_monomial,one_mul,Finsupp.prod,Int.cast_prod,Int.cast_pow]

theorem weighted_residue_proper_cut {ι κ β K : Type*}
    [Fintype ι] [Fintype κ] [Fintype β] [DecidableEq κ] [Field K] [CharZero K]
    (ω : (ι ⊕ κ) → ℝ) (hω : ∀ i, 0 < ω i)
    (hh : 0 < Fintype.card ι) (δ ν c Cbox : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hc : 0 ≤ c) (hboxC : 1 ≤ Cbox) :
    ∃ D : ℕ, ∃ X₀ : ℝ, ∀ (X : ℝ), X₀ < X →
      ∀ I : Ideal (MvPolynomial (ι ⊕ κ) K),
      (∀ T : ℝ, 1 ≤ T → T^(Fintype.card ι) /
        (((Fintype.card ι).factorial : ℝ)*δ^(Fintype.card ι)) - c*T^(Fintype.card ι-1) ≤
          weightedHilbert I ω T) →
      ∀ (G : κ → MvPolynomial (ι ⊕ κ) ℤ) (z : (ι ⊕ κ) → ℤ),
      (∀ j, eval z (G j) = 0) →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ¬ (p:ℤ) ∣ (Matrix.of (fun j a => eval z (pderiv (Sum.inr a) (G j)))).det) →
      X^(δ+ν) ≤ ∏ p ∈ Q, (p:ℝ) →
      ∀ w : β → (ι ⊕ κ) → ℤ,
      (∀ p ∈ Q, ∀ b i, (p:ℤ) ∣ w b i-z i) →
      (∀ b j, eval (w b) (G j) = 0) →
      (∀ b i, |(w b i : ℝ)| ≤ Cbox*X^(ω i)) →
      ∃ P : MvPolynomial (ι ⊕ κ) ℚ, P.totalDegree ≤ D ∧
        MvPolynomial.map (algebraMap ℚ K) P ∉ I ∧
        ∀ b, eval (fun i => (w b i : ℚ)) P = 0 := by
  classical
  let h := Fintype.card ι
  obtain ⟨C,hC,hshift⟩ := hilbert_simplex_shift h hh δ c hδ hc
  obtain ⟨t,hL,hmargin⟩ := exists_simplex_margin h hh ν C hν
  let D := weightedDegreeBound ω (δ*t+C)
  let L := (t+h).choose h
  let m := h*((t+h).choose (h+1))
  refine ⟨D,max 1 ((L.factorial : ℝ)*(Cbox^D)^L),?_⟩
  intro X hX I hH G z hz Q hprime hgood hQ w hw hroot hbox
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hlarge : (L.factorial : ℝ)*(Cbox^D)^L < X := lt_of_le_of_lt (le_max_right _ _) hX
  let S := fun t : ℕ => weightedMonomials ω (δ*t+C)
  have hS : ∀ t, S t ⊆ S (t+1) := by
    intro t
    apply weightedMonomials_mono ω hω
    push_cast
    linarith
  have hweight : ∀ t a, a ∈ S t → monomialWeight ω a ≤ δ*t+C := by
    intro t a ha
    exact (mem_weightedMonomials ω hω _ a).mp ha
  have hr : ∀ t, (t+h).choose h ≤ Module.finrank K
      (Submodule.span K ((fun a => Ideal.Quotient.mk I (monomial a (1:K))) '' (S t : Set _))) := by
    intro t
    have hT : 1 ≤ δ*(t:ℝ)+C := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg t)]
    exact_mod_cast (hshift t).trans (hH _ hT)
  obtain ⟨A,hA,hcard,hli,hsum⟩ := independent_weighted_simplex
    (fun a => Ideal.Quotient.mk I (monomial a (1:K))) S hS (monomialWeight ω) δ C hweight h hr t
  have hcard' : Fintype.card A = L := by simpa only [Fintype.card_coe] using hcard
  have hD : ∀ a : A, a.val.sum (fun _ e => e) ≤ D := fun a =>
    weighted_monomial_degree_bound ω hω _ a.val (hweight t a.val (hA a.property))
  have hsum' : ∑ a : A, monomialWeight ω a.val ≤ δ*(m:ℝ)+C*(Fintype.card A) := by
    rw [hcard',Finset.sum_coe_sort]
    exact hsum
  have hmargin' : (C+1)*(Fintype.card A : ℝ) ≤ ν*(m:ℝ) := by
    rw [hcard']; exact hmargin
  have hlt : (Fintype.card A).factorial * ∏ a : A, (Cbox^D*X^(monomialWeight ω a.val)) <
      (∏ p ∈ Q, (p:ℝ))^m := weighted_row_product_lt
        (fun a : A => monomialWeight ω a.val) Cbox X δ ν C _ D m hX1
        (by rwa [hcard']) (by rwa [hcard']) hsum' hmargin' hQ
  obtain ⟨c,hc,hrel⟩ := simultaneous_residue_relation G z hz Q hprime hgood m
    (fun a : A => monomial a.val (1:ℤ)) w hw hroot
    (fun r hr => monomial_order_simplex_bound r hr t (by rw [hcard']))
    (fun a : A => Cbox^D*X^(monomialWeight ω a.val))
    (fun a b => integer_monomial_abs_le ω Cbox X hboxC (lt_trans zero_lt_one hX1)
      (w b) (hbox b) a.val D (hD a)) hlt
  refine ⟨∑ a : A, monomial a.val (c a),monomial_relation_degree _ _ D hD,
    independent_monomial_relation_proper I _ hli.linearIndependent_restrict c hc,?_⟩
  exact fun b => monomial_relation_eval _ _ (w b) (hrel b)

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem IntegerPatch.eval_chart {n : ℕ} (P : IntegerPatch n) (z : Fin n → ℤ)
    (p : MvPolynomial (Fin n) ℤ) :
    eval (fun i => z ((Equiv.Set.sumCompl P.free) i))
      (rename (Equiv.Set.sumCompl P.free).symm p) = eval z p := by
  rw [eval_rename]
  simp [Function.comp_def]

theorem IntegerPatch.minor_chart {n : ℕ} (P : IntegerPatch n) (z : Fin n → ℤ) :
    (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z ((Equiv.Set.sumCompl P.free) a))
        (pderiv (Sum.inr j) (rename (Equiv.Set.sumCompl P.free).symm (P.equations i))))).det =
      eval z P.minor := by
  classical
  let e := Equiv.Set.sumCompl P.free
  have he (j : ↥(P.freeᶜ)) : e.symm j.val = Sum.inr j := by
    apply e.injective
    simp [e]
  have hm : (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))))) =
      Matrix.of (fun i j : ↥(P.freeᶜ) => eval z (pderiv j.val (P.equations i))) := by
    ext i j
    change eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))) = _
    rw [← he j,pderiv_rename e.symm.injective]
    exact P.eval_chart z _
  change (Matrix.of (fun i j : ↥(P.freeᶜ) =>
      eval (fun a => z (e a)) (pderiv (Sum.inr j) (rename e.symm (P.equations i))))).det = _
  rw [hm]
  exact ((eval z).map_det (fun i j : ↥(P.freeᶜ) => pderiv j.val (P.equations i))).symm

theorem IntegerPatch.residue_relation {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (P : IntegerPatch n) (z : Fin n → ℤ) (hz : ∀ j, eval z (P.equations j) = 0)
    (Q : Finset ℕ) (hprime : ∀ p ∈ Q, p.Prime)
    (hgood : ∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z P.minor)
    (m : ℕ) (R : α → MvPolynomial (Fin n) ℤ) (w : β → Fin n → ℤ)
    (hw : ∀ p ∈ Q, ∀ b j, (p:ℤ) ∣ w b j-z j)
    (hroot : ∀ b j, eval (w b) (P.equations j) = 0)
    (hm : ∀ r : α → (P.free →₀ ℕ), Function.Injective r → m ≤ ∑ a, (r a).sum (fun _ e => e))
    (B : α → ℝ) (hB : ∀ a b, |(eval (w b) (R a) : ℝ)| ≤ B a)
    (hlt : (Nat.factorial (Fintype.card α) : ℝ) * ∏ a, B a < (∏ p ∈ Q, (p:ℝ))^m) :
    ∃ c : α → ℚ, c ≠ 0 ∧ ∀ b, ∑ a, c a * (eval (w b) (R a) : ℚ) = 0 := by
  classical
  let e := Equiv.Set.sumCompl P.free
  have hc := simultaneous_residue_relation
    (fun j => rename e.symm (P.equations j)) (fun j => z (e j))
    (fun j => (P.eval_chart z _).trans (hz j)) Q hprime
    (fun p hp => by rw [P.minor_chart z]; exact hgood p hp) m
    (fun a => rename e.symm (R a)) (fun b j => w b (e j))
    (fun p hp b j => hw p hp b (e j))
    (fun b j => (P.eval_chart (w b) _).trans (hroot b j)) hm B
    (fun a b => by rw [P.eval_chart]; exact hB a b) hlt
  simpa only [eval_rename,Function.comp_def,Equiv.apply_symm_apply] using hc

theorem weighted_integer_patch_cut {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i)
    (h : ℕ) (hh : 0 < h) (δ ν c Cbox : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hc : 0 ≤ c) (hboxC : 1 ≤ Cbox) :
    ∃ D : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ < X →
      ∀ I : Ideal (MvPolynomial (Fin n) ℂ),
      (∀ T : ℝ, 1 ≤ T → T^h / ((h.factorial : ℝ)*δ^h) - c*T^(h-1) ≤
        weightedHilbert I ω T) →
      ∀ P : IntegerPatch n, Nat.card P.free = h →
      ∀ z : Fin n → ℤ, (∀ j, eval z (P.equations j) = 0) →
      ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z P.minor) → X^(δ+ν) ≤ ∏ p ∈ Q, (p:ℝ) →
      ∀ S : Finset (Fin n → ℤ),
      (∀ p ∈ Q, ∀ w ∈ S, ∀ j, (p:ℤ) ∣ w j-z j) →
      (∀ w ∈ S, ∀ j, eval w (P.equations j) = 0) →
      (∀ w ∈ S, ∀ j, |(w j : ℝ)| ≤ Cbox*X^(ω j)) →
      ∃ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D ∧ p ∉ I ∧
        ∀ w ∈ S, eval (fun i => (w i : ℂ)) p = 0 := by
  classical
  obtain ⟨C,hC,hshift⟩ := hilbert_simplex_shift h hh δ c hδ hc
  obtain ⟨t,hL,hmargin⟩ := exists_simplex_margin h hh ν C hν
  let D := weightedDegreeBound ω (δ*t+C)
  let L := (t+h).choose h
  let m := h*((t+h).choose (h+1))
  refine ⟨D,max 1 ((L.factorial : ℝ)*(Cbox^D)^L),?_⟩
  intro X hX I hH P hfree z hz Q hprime hgood hQ S hw hroot hbox
  have hX1 : 1 < X := lt_of_le_of_lt (le_max_left _ _) hX
  have hlarge : (L.factorial : ℝ)*(Cbox^D)^L < X := lt_of_le_of_lt (le_max_right _ _) hX
  let U := fun t : ℕ => weightedMonomials ω (δ*t+C)
  have hU : ∀ t, U t ⊆ U (t+1) := by
    intro t
    apply weightedMonomials_mono ω hω
    push_cast
    linarith
  have hweight : ∀ t a, a ∈ U t → monomialWeight ω a ≤ δ*t+C := by
    intro t a ha
    exact (mem_weightedMonomials ω hω _ a).mp ha
  have hr : ∀ t, (t+h).choose h ≤ Module.finrank ℂ
      (Submodule.span ℂ ((fun a => Ideal.Quotient.mk I (monomial a (1:ℂ))) '' (U t : Set _))) := by
    intro t
    have hT : 1 ≤ δ*(t:ℝ)+C := by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg t)]
    exact_mod_cast (hshift t).trans (hH _ hT)
  obtain ⟨A,hA,hcard,hli,hsum⟩ := independent_weighted_simplex
    (fun a => Ideal.Quotient.mk I (monomial a (1:ℂ))) U hU (monomialWeight ω) δ C hweight h hr t
  have hcard' : Fintype.card A = L := by simpa only [Fintype.card_coe] using hcard
  have hD : ∀ a : A, a.val.sum (fun _ e => e) ≤ D := fun a =>
    weighted_monomial_degree_bound ω hω _ a.val (hweight t a.val (hA a.property))
  have hsum' : ∑ a : A, monomialWeight ω a.val ≤ δ*(m:ℝ)+C*(Fintype.card A) := by
    rw [hcard',Finset.sum_coe_sort]
    exact hsum
  have hmargin' : (C+1)*(Fintype.card A : ℝ) ≤ ν*(m:ℝ) := by
    rw [hcard']; exact hmargin
  have hlt : (Fintype.card A).factorial * ∏ a : A, (Cbox^D*X^(monomialWeight ω a.val)) <
      (∏ p ∈ Q, (p:ℝ))^m := weighted_row_product_lt
        (fun a : A => monomialWeight ω a.val) Cbox X δ ν C _ D m hX1
        (by rwa [hcard']) (by rwa [hcard']) hsum' hmargin' hQ
  have hf : Fintype.card P.free = h := by simpa only [Nat.card_eq_fintype_card] using hfree
  obtain ⟨c,hc,hrel⟩ := P.residue_relation z hz Q hprime hgood m
    (fun a : A => monomial a.val (1:ℤ)) (fun w : S => w.val)
    (fun p hp w j => hw p hp w.val w.property j)
    (fun w j => hroot w.val w.property j)
    (fun r hr => by
      have hm := monomial_order_simplex_bound r hr t (by rw [hf]; exact hcard'.symm.le)
      simpa only [hf,monomialOrder] using hm)
    (fun a : A => Cbox^D*X^(monomialWeight ω a.val))
    (fun a w => integer_monomial_abs_le ω Cbox X hboxC (lt_trans zero_lt_one hX1)
      w.val (hbox w.val w.property) a.val D (hD a)) hlt
  have hp := independent_monomial_relation_proper I _ hli.linearIndependent_restrict c hc
  let p : MvPolynomial (Fin n) ℚ := ∑ a : A, monomial a.val (c a)
  have hpdeg : (MvPolynomial.map (algebraMap ℚ ℂ) p).totalDegree = p.totalDegree := by
    simp only [totalDegree,support_map_of_injective p (f := algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective]
  refine ⟨MvPolynomial.map (algebraMap ℚ ℂ) p,
    hpdeg.le.trans (monomial_relation_degree _ _ D hD),hp,?_⟩
  intro w hw
  have he := congrArg (algebraMap ℚ ℂ) (monomial_relation_eval _ _ w (hrel ⟨w,hw⟩))
  rw [MvPolynomial.eval_map]
  simpa only [MvPolynomial.eval₂_comp,map_zero,Function.comp_def,map_intCast] using he

end

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

theorem IntegerPatch.equation_vanishes {n : ℕ} {K : Type*} [Field K] [CharZero K]
    {P : IntegerPatch n} {I : Ideal (MvPolynomial (Fin n) K)}
    (hP : P.On I) {z : Fin n → ℤ} (hz : PointOn I z) (j : ↥(P.freeᶜ)) :
    eval z (P.equations j) = 0 := by
  apply Int.cast_injective (α := K)
  rw [Int.cast_zero,← eval_int_map]
  exact hz _ (hP.2.1 j)

theorem physical_weighted_descent {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (q : ℕ) (hq : 0 < q) (δ ν c Cbox : ℝ)
    (hδ : 0 < δ) (hν : 0 < ν) (hc : 0 ≤ c) (hCbox : 1 ≤ Cbox) :
    ∃ D : ℕ, ∃ X₀ : ℝ, ∀ X : ℝ, X₀ < X →
      ∀ (r E : ℕ) (G : KernelGeometry n) (d : ℕ → ℕ) (A h e i : ℕ),
      D ≤ d i → d i ≤ E →
      (∀ w ∈ G.points, ∀ j, |(w j : ℝ)| ≤ Cbox*X^(ω j)) →
      ∀ (z : Fin n → ℤ), z ∈ G.points →
      ∀ s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n,
      PhysicalState G h (pathDegreeBudget n d A h e i) z s →
      affineDimension s.1 = q →
      (∀ T : ℝ, 1 ≤ T → T^q / ((q.factorial : ℝ)*δ^q) - c*T^(q-1) ≤
        weightedHilbert s.1 ω T) →
      ∀ B : Fin r → Finset ℕ, ∀ Q : Finset ℕ,
      Q ⊆ cumulativeBlockPrimes B i → (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ¬ (p:ℤ) ∣ eval z s.2.minor) → X^(δ+ν) ≤ ∏ p ∈ Q, (p:ℝ) →
      affineDimension (physicalNext G d A h e z i s (physicalKernel (E := E) G d z i s B)).1 <
        affineDimension s.1 := by
  classical
  obtain ⟨D,X₀,hcut⟩ := weighted_integer_patch_cut ω hω q hq δ ν c Cbox hδ hν hc hCbox
  refine ⟨D,X₀,?_⟩
  intro X hX r E G d A h e i hD hE hbox z hz s hs hdim hH B Q hQ hprime hgood hprod
  let S := evaluationCell G.points s.1 z (cumulativeBlockPrimes B i)
  obtain ⟨p,hpD,hpI,hpS⟩ := hcut X hX s.1 hH s.2 (hs.2.1.1.trans hdim) z
    (fun j => IntegerPatch.equation_vanishes hs.2.1 hs.2.2.2.1 j) Q hprime hgood hprod S
    (fun p hp w hw j => (Finset.mem_filter.mp hw).2.2 p (hQ hp) j)
    (fun w hw j => IntegerPatch.equation_vanishes hs.2.1 (Finset.mem_filter.mp hw).2.1 j)
    (fun w hw j => hbox w (Finset.mem_filter.mp hw).1 j)
  apply (physical_step (E := E) G d A h e z hz i s hs B).2.2.2.2.2
  intro hsub
  apply hpI
  apply hsub
  exact (mem_stagedKernelPolynomials hE S p).mpr ⟨hpD.trans hD,hpS⟩

theorem PointOn.eq_of_zeroDim {n : ℕ} {K : Type*} [Field K] [CharZero K]
    {I : Ideal (MvPolynomial (Fin n) K)} [I.IsPrime]
    (hd : affineDimension I = 0) {z w : Fin n → ℤ}
    (hz : PointOn I z) (hw : PointOn I w) : z = w := by
  have hI := zeroDim_eq_point I hd (fun j => (z j : K)) hz
  funext j
  apply Int.cast_injective (α := K)
  have hmem : X j - C (z j : K) ∈ I := by
    rw [hI,RingHom.mem_ker]
    simp
  have he : (w j : K) - (z j : K) = 0 := by simpa using hw _ hmem
  exact (sub_eq_zero.mp he).symm

theorem physical_zeroDim_fiber {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : ∀ z, PhysicalState G h e z.val (start z)) (B : Fin r → Finset ℕ)
    (i : ℕ) (z : G.points) (S : Finset G.points)
    (hd : affineDimension (physicalStateAt (E := E) G d A h e start B i z).1 = 0) :
    (S.filter fun w => physicalNode (E := E) G d A h e start B i w =
      physicalNode (E := E) G d A h e start B i z).card ≤ 1 := by
  classical
  let I := (physicalStateAt (E := E) G d A h e start B i z).1
  have hz := physicalStateAt_good (E := E) G d A h e start hs B i z
  let : I.IsPrime := hz.1.1
  apply (Finset.card_le_card (t := {z}) ?_).trans (by simp)
  intro w hw
  have he := congrArg (fun x => x.1) (Finset.mem_filter.mp hw).2
  change physicalStateAt (E := E) G d A h e start B i w =
    physicalStateAt (E := E) G d A h e start B i z at he
  have hw := (physicalStateAt_good (E := E) G d A h e start hs B i w).2.2.2.1
  rw [he] at hw
  exact Finset.mem_singleton.mpr (Subtype.ext (PointOn.eq_of_zeroDim hd hw hz.2.2.2.1))

end QuarticPowerFree

end OAI
