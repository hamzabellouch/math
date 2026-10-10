import OAI.Combinatorics.ListHadwiger.FractionalSampling

namespace OAI

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq ι] [DecidableEq V]

noncomputable def remainder (E : ι → Finset V) (I : Ω → Finset V)
    (x : ι → Ω) : Finset V :=
  Finset.univ \ Finset.univ.biUnion (fun j => I (x j) ∩ E j)

lemma mem_remainder {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V] [DecidableEq ι] [DecidableEq V] (E : ι → Finset V) (I : Ω → Finset V) (x : ι → Ω) (v : V) :
    v ∈ remainder E I x ↔ ∀ j, v ∈ E j → v ∉ I (x j) := by
  classical
  simp only [remainder,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_biUnion,Finset.mem_inter]
  push Not
  constructor
  · intro h j he hi
    exact h j hi he
  · intro h j hi he
    exact h j he hi

lemma probability_not {μ : Ω → ℝ} (hs : ∑ ω, μ ω = 1) (A : Ω → Prop) :
    probability μ (fun ω => ¬ A ω) = 1 - probability μ A := by
  classical
  have he : probability μ (fun ω => ¬ A ω) + probability μ A = ∑ ω, μ ω := by
    unfold probability
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : A ω <;> simp [h]
  linarith

lemma remainder_survival_eq {μ : ι → Ω → ℝ} (hs : ∀ j, ∑ ω, μ j ω = 1)
    (E : ι → Finset V) (I : Ω → Finset V) (v : V) :
    probability (productMass μ) (fun x => v ∈ remainder E I x) =
      ∏ j, if v ∈ E j then 1 - probability (μ j) (fun ω => v ∈ I ω) else 1 := by
  classical
  let f : ι → Ω → ℝ := fun j ω => if v ∈ E j ∧ v ∈ I ω then 0 else 1
  have hprod (x : ι → Ω) :
      (if v ∈ remainder E I x then (1 : ℝ) else 0) = ∏ j, f j (x j) := by
    by_cases hv : v ∈ remainder E I x
    · rw [ite_eq_left hv]
      symm
      apply Finset.prod_eq_one
      intro j _
      simp only [f]
      exact ite_eq_right (fun hh => (mem_remainder E I x v).mp hv j hh.1 hh.2)
    · rw [ite_eq_right hv]
      have hnot : ¬ ∀ j, v ∈ E j → v ∉ I (x j) := mt (mem_remainder E I x v).mpr hv
      push Not at hnot
      obtain ⟨j,hE,hI⟩ := hnot
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [f,hE,hI]
  rw [probability_eq_expectation]
  simp_rw [hprod]
  rw [expectation_product]
  apply Finset.prod_congr rfl
  intro j _
  by_cases he : v ∈ E j
  · simp only [ite_eq_left he]
    have hf : f j = fun ω => if v ∉ I ω then 1 else 0 := by
      funext ω
      by_cases hi : v ∈ I ω <;> simp [f,he,hi]
    rw [hf,← probability_eq_expectation,probability_not (hs j)]
  · simp only [ite_eq_right he]
    have hf : f j = fun _ => 1 := by funext ω; simp [f,he]
    rw [hf,expectation_const (hs j)]

lemma remainder_survival_power {μ : ι → Ω → ℝ} (hs : ∀ j, ∑ ω, μ j ω = 1)
    (E : ι → Finset V) (I : Ω → Finset V) {p : ℝ}
    (hmarg : ∀ j v, probability (μ j) (fun ω => v ∈ I ω) = p) (v : V) :
    probability (productMass μ) (fun x => v ∈ remainder E I x) =
      (1 - p) ^ (Finset.univ.filter (fun j => v ∈ E j)).card := by
  classical
  rw [remainder_survival_eq hs E I v]
  simp_rw [hmarg]
  rw [← Finset.prod_filter]
  simp

theorem remainder_survival_bound {μ : ι → Ω → ℝ} (hs : ∀ j, ∑ ω, μ j ω = 1)
    (E : ι → Finset V) (I : Ω → Finset V) {r : ℝ} (hr : 1 ≤ r)
    (hmarg : ∀ j v, probability (μ j) (fun ω => v ∈ I ω) = 1 / (2*r))
    (hE : ∀ v, (Fintype.card ι : ℝ)/2 ≤ (Finset.univ.filter (fun j => v ∈ E j)).card)
    (v : V) :
    probability (productMass μ) (fun x => v ∈ remainder E I x) ≤
      Real.exp (-(Fintype.card ι : ℝ)/(4*r)) := by
  classical
  rw [remainder_survival_power hs E I hmarg v]
  have hp : 0 ≤ 1 - 1/(2*r) := by
    have hh : 1/(2*r) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hex : 1 - 1/(2*r) ≤ Real.exp (-(1/(2*r))) := by
    have h := Real.add_one_le_exp (-(1/(2*r)))
    linarith
  calc
    _ ≤ (Real.exp (-(1/(2*r)))) ^ (Finset.univ.filter (fun j => v ∈ E j)).card :=
      pow_le_pow_left₀ hp hex _
    _ = Real.exp (-((Finset.univ.filter (fun j => v ∈ E j)).card : ℝ)/(2*r)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := hE v
      have hpos : 0 < 2*r := by linarith
      apply (div_le_div_iff₀ hpos (by linarith : 0 < 4*r)).mpr
      nlinarith

lemma remainder_sdiff_subset (E : ι → Finset V) (I : Ω → Finset V)
    {i : ι} {x y : ι → Ω} (hxy : ∀ j, j ≠ i → x j = y j) :
    remainder E I x \ remainder E I y ⊆ I (y i) := by
  classical
  intro v hv
  obtain ⟨hx,hy⟩ := Finset.mem_sdiff.mp hv
  by_contra hn
  apply hy
  apply (mem_remainder E I y v).mpr
  intro j he
  by_cases hj : j = i
  · simpa [hj] using hn
  · rw [← hxy j hj]
    exact (mem_remainder E I x v).mp hx j he

lemma inter_sdiff_subset_left {V : Type} [Fintype V] [DecidableEq V] (A S T : Finset V) :
    (A ∩ S) \ (A ∩ T) ⊆ S \ T := by
  intro v hv
  simp only [Finset.mem_sdiff,Finset.mem_inter] at hv ⊢
  tauto

lemma inter_remainder_difference_bound (E : ι → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V)
    {i : ι} {x y : ι → Ω} (hxy : ∀ j, j ≠ i → x j = y j) :
    (((A ∩ remainder E I x) \ (A ∩ remainder E I y)).card : ℝ) +
      ((A ∩ remainder E I y) \ (A ∩ remainder E I x)).card ≤ 2 * (M : ℝ) := by
  have h₁ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (remainder_sdiff_subset E I hxy))).trans (hI (y i))
  have h₂ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (remainder_sdiff_subset E I (fun j hj => (hxy j hj).symm)))).trans (hI (x i))
  exact_mod_cast (by omega : ((A ∩ remainder E I x) \ (A ∩ remainder E I y)).card +
    ((A ∩ remainder E I y) \ (A ∩ remainder E I x)).card ≤ 2*M)

lemma card_abs_sub_le_differences {V : Type} [Fintype V] [DecidableEq V] (S T : Finset V) :
    |(S.card : ℝ)-T.card| ≤ (S \ T).card + (T \ S).card := by
  have hS := Finset.card_sdiff_add_card_inter S T
  have hT := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hT
  have hSr : ((S \ T).card : ℝ) + (S ∩ T).card = S.card := by exact_mod_cast hS
  have hTr : ((T \ S).card : ℝ) + (S ∩ T).card = T.card := by exact_mod_cast hT
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (S \ T).card,
    Nat.cast_nonneg (α := ℝ) (T \ S).card]

lemma remainder_card_bounded_changes {N : ℕ} (E : Fin N → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V) :
    FiniteConcentration.BoundedChanges (fun x => ((A ∩ remainder E I x).card : ℝ)) (2*M) := by
  intro i x y hxy
  exact (card_abs_sub_le_differences _ _).trans (inter_remainder_difference_bound E I hI A hxy)

lemma remainder_fractional_bounded_changes {N : ℕ} (G : SimpleGraph V)
    (E : Fin N → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V) :
    FiniteConcentration.BoundedChanges
      (fun x => Fractional.number (G.induce (↑(A ∩ remainder E I x) : Set V))) (2*M) := by
  intro i x y hxy
  exact (Fractional.induced_number_abs_sub_le G _ _).trans
    (inter_remainder_difference_bound E I hI A hxy)

theorem remainder_fractional_concentration {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (G : SimpleGraph V) (μ : Fin N → Ω → ℝ) (hμ : ∀ j ω, 0 ≤ μ j ω)
    (hs : ∀ j, ∑ ω, μ j ω = 1) (E : Fin N → Finset V) (I : Ω → Finset V)
    (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V) {u : ℝ} (hu : 0 < u) :
    probability (productMass μ)
      (fun x => u ≤ |Fractional.number (G.induce (↑(A ∩ remainder E I x) : Set V)) -
        expectation (productMass μ) (fun y => Fractional.number
          (G.induce (↑(A ∩ remainder E I y) : Set V)))|) ≤
      2 * Real.exp (-u^2/(2*N*(2*(M : ℝ))^2)) := by
  have hb : 0 < 2*(M : ℝ) := by exact_mod_cast (by omega : 0 < 2*M)
  exact FiniteConcentration.bounded_differences hN μ hμ hs _ hb hu
    (remainder_fractional_bounded_changes G E I hI A)

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

theorem bounded_differences_general (hn : 1 ≤ Fintype.card ι)
    (μ : ι → Ω → ℝ) (hμ : ∀ i ω, 0 ≤ μ i ω) (hs : ∀ i, ∑ ω, μ i ω = 1)
    (f : (ι → Ω) → ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u)
    (hf : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x-f y| ≤ b) :
    probability (productMass μ) (fun x => u ≤ |f x-expectation (productMass μ) f|) ≤
      2 * Real.exp (-u^2/(2*Fintype.card ι*b^2)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (Fin (Fintype.card ι) → Ω) ≃ (ι → Ω) := Equiv.arrowCongr e (Equiv.refl Ω)
  let μ' : Fin (Fintype.card ι) → Ω → ℝ := fun i => μ (e i)
  have hm (x : Fin (Fintype.card ι) → Ω) :
      productMass μ' x = productMass μ (E x) := by
    apply Fintype.prod_equiv e
    intro i
    simp [μ',E,Equiv.arrowCongr]
  have he : expectation (productMass μ) f =
      expectation (productMass μ') (fun x => f (E x)) := by
    unfold expectation
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    rw [hm]
  have hc : FiniteConcentration.BoundedChanges (fun x => f (E x)) b := by
    intro i x y hxy
    apply hf (e i)
    intro j hj
    change x (e.symm j) = y (e.symm j)
    apply hxy
    intro heq
    apply hj
    rw [← e.apply_symm_apply j,heq]
  have hh := FiniteConcentration.bounded_differences hn μ' (fun i => hμ (e i))
    (fun i => hs (e i)) (fun x => f (E x)) hb hu hc
  change probability (productMass μ')
    (fun x => u ≤ |f (E x) - expectation (productMass μ') (fun y => f (E y))|) ≤ _ at hh
  rw [← he] at hh
  convert hh using 1
  unfold probability
  rw [← E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [hm]

variable {κ V : Type} [Fintype κ] [Fintype V] [DecidableEq κ] [DecidableEq V]

noncomputable def unionRemainders (E : ι → Finset V) (I : Ω → Finset V)
    (x : κ × ι → Ω) : Finset V :=
  Finset.univ.biUnion (fun k => remainder E I (fun i => x (k,i)))

lemma unionRemainders_sdiff_subset (E : ι → Finset V) (I : Ω → Finset V)
    {k : κ × ι} {x y : κ × ι → Ω} (hxy : ∀ j, j ≠ k → x j = y j) :
    unionRemainders E I x \ unionRemainders E I y ⊆ I (y k) := by
  classical
  intro v hv
  obtain ⟨hx,hy⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨c,_,hvc⟩ := Finset.mem_biUnion.mp hx
  have hn : v ∉ remainder E I (fun i => y (c,i)) := by
    intro h
    exact hy (Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,h⟩)
  have hck : c = k.1 := by
    by_contra hne
    apply hn
    have he : (fun i => y (c,i)) = (fun i => x (c,i)) := by
      funext i
      exact (hxy (c,i) (fun h => hne (congrArg Prod.fst h))).symm
    rw [he]
    exact hvc
  subst c
  have hdiff := remainder_sdiff_subset E I
    (i := k.2) (x := fun i => x (k.1,i)) (y := fun i => y (k.1,i))
    (fun j hj => hxy (k.1,j) (fun h => hj (congrArg Prod.snd h)))
  exact hdiff (Finset.mem_sdiff.mpr ⟨hvc,hn⟩)

lemma unionRemainders_card_bounded_changes (E : ι → Finset V) (I : Ω → Finset V)
    {M : ℕ} (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V)
    {k : κ × ι} {x y : κ × ι → Ω} (hxy : ∀ j, j ≠ k → x j = y j) :
    |((A ∩ unionRemainders E I x).card : ℝ) - (A ∩ unionRemainders E I y).card| ≤ 2*M := by
  have h₁ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (unionRemainders_sdiff_subset E I hxy))).trans (hI (y k))
  have h₂ := (Finset.card_le_card ((inter_sdiff_subset_left A _ _).trans
    (unionRemainders_sdiff_subset E I (fun j hj => (hxy j hj).symm)))).trans (hI (x k))
  apply (card_abs_sub_le_differences _ _).trans
  exact_mod_cast (by omega : ((A ∩ unionRemainders E I x) \ (A ∩ unionRemainders E I y)).card +
    ((A ∩ unionRemainders E I y) \ (A ∩ unionRemainders E I x)).card ≤ 2*M)

theorem unionRemainders_concentration (hn : 1 ≤ Fintype.card ι) (hq : 1 ≤ Fintype.card κ)
    {M : ℕ} (hM : 1 ≤ M) (μ : κ × ι → Ω → ℝ) (hμ : ∀ j ω, 0 ≤ μ j ω)
    (hs : ∀ j, ∑ ω, μ j ω = 1) (E : ι → Finset V) (I : Ω → Finset V)
    (hI : ∀ ω, (I ω).card ≤ M) (A : Finset V) {u : ℝ} (hu : 0 < u) :
    probability (productMass μ)
      (fun x => u ≤ |((A ∩ unionRemainders E I x).card : ℝ) -
        expectation (productMass μ) (fun y => ((A ∩ unionRemainders E I y).card : ℝ))|) ≤
      2 * Real.exp (-u^2/(2*(Fintype.card κ * Fintype.card ι : ℕ)*(2*(M : ℝ))^2)) := by
  have hb : 0 < 2*(M : ℝ) := by exact_mod_cast (by omega : 0 < 2*M)
  have hqn : 1 ≤ Fintype.card (κ × ι) := by
    rw [Fintype.card_prod]
    have := Nat.mul_pos (by omega : 0 < Fintype.card κ) (by omega : 0 < Fintype.card ι)
    omega
  have hh := bounded_differences_general hqn μ hμ hs
    (fun x => ((A ∩ unionRemainders E I x).card : ℝ)) hb hu
    (fun k x y hxy => unionRemainders_card_bounded_changes E I hI A hxy)
  simpa only [Fintype.card_prod] using hh

end LinearListHadwiger.Sampling

end OAI
