import OAI.NumberTheory.ShortEgyptian.DeterministicLists

namespace OAI

universe uI uΩ uJ uA uE uD uU

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical

noncomputable def phaseAverage {I : Type uI} [Fintype I]
    (t : I → ℕ) (Q u l : ℕ) : ℂ :=
  (∑ i, phase ((l:ℝ)*Q*t i/u))/(Fintype.card I:ℂ)

noncomputable def FourierBad {I : Type uI} [Fintype I]
    (t : I → ℕ) (Q u : ℕ) (δ : ℝ) : Prop :=
  ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage t Q u l‖

lemma frequency_bad_probability {Ω : Type uΩ} [Fintype Ω]
    (F : Ω → ℕ → ℂ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊,
      (𝔼 ω, ‖F ω l‖^2) ≤ E) :
    (𝔼 ω, if ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^10 := by
  classical
  let H := Icc 1 ⌊1/δ^4⌋₊
  have hl (l : H) :
      (𝔼 ω, if δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^6 := by
    have hh := finite_markov (fun ω => ‖F ω l‖^2)
      (fun _ => sq_nonneg _) (δ^6) (pow_pos hδ 6)
    apply le_trans (b := (𝔼 ω, if δ^6 ≤ ‖F ω l‖^2 then (1:ℝ) else 0))
    · apply expect_le_expect
      intro ω _
      split_ifs with h h'
      all_goals try norm_num
      exfalso
      apply h'
      have hd : 0 ≤ δ^3 := pow_nonneg hδ.le _
      nlinarith [sq_nonneg (‖F ω l‖-δ^3)]
    · exact hh.trans (div_le_div_of_nonneg_right (hmoment l l.property) (by positivity))
  have heq (ω : Ω) : (∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖) ↔
      (∃ l : H, δ^3 < ‖F ω l‖) := by
    constructor
    · rintro ⟨l,hl,hf⟩
      exact ⟨⟨l,hl⟩,hf⟩
    · rintro ⟨l,hf⟩
      exact ⟨l,l.property,hf⟩
  simp_rw [heq]
  have hs := finite_union_bound (fun l : H => fun ω => δ^3 < ‖F ω l‖)
  apply hs.trans
  calc
    _ ≤ ∑ _l : H, E/δ^6 := sum_le_sum (fun l _ => hl l)
    _ = (⌊1/δ^4⌋₊:ℝ)*(E/δ^6) := by simp [H,Nat.card_Icc]
    _ ≤ (1/δ^4)*(E/δ^6) := by
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (div_nonneg hE (by positivity))
    _ = _ := by field_simp

lemma fourierBad_probability {I : Type uI} {Ω : Type uΩ} [Fintype I] [Fintype Ω]
    (t : Ω → I → ℕ) (Q u : ℕ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊,
      (𝔼 ω, ‖phaseAverage (t ω) Q u l‖^2) ≤ E) :
    (𝔼 ω, if FourierBad (t ω) Q u δ then (1:ℝ) else 0) ≤ E/δ^10 :=
by
  have hh := frequency_bad_probability (fun ω l => phaseAverage (t ω) Q u l) δ E hδ hE hmoment
  apply le_trans _ hh
  apply expect_le_expect
  intro ω _
  by_cases h : FourierBad (t ω) Q u δ
  · have h' : ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage (t ω) Q u l‖ := h
    simp only [ite_eq_left h,ite_eq_left h',le_refl]
  · have h' : ¬∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖phaseAverage (t ω) Q u l‖ := h
    simp only [ite_eq_right h,ite_eq_right h',le_refl]

lemma frequency_bad_sum {Ω : Type uΩ} [Fintype Ω]
    (F : Ω → ℕ → ℂ) (δ E : ℝ) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hmoment : ∀ l ∈ Icc 1 ⌊1/δ^4⌋₊, (∑ ω, ‖F ω l‖^2) ≤ E) :
    (∑ ω, if ∃ l ∈ Icc 1 ⌊1/δ^4⌋₊, δ^3 < ‖F ω l‖ then (1:ℝ) else 0) ≤ E/δ^10 := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h => simp only [univ_eq_empty, sum_empty]; positivity
  | inr h =>
    have hN : (0:ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
    have hh := frequency_bad_probability F δ (E/Fintype.card Ω) hδ (by positivity) (by
      intro l hl
      rw [Fintype.expect_eq_sum_div_card]
      exact div_le_div_of_nonneg_right (hmoment l hl) hN.le)
    rw [Fintype.expect_eq_sum_div_card] at hh
    have heq : (E/(Fintype.card Ω:ℝ))/δ^10 = (E/δ^10)/Fintype.card Ω := by ring
    rw [heq] at hh
    exact (div_le_div_iff_of_pos_right hN).mp hh

lemma phaseAverage_sample {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (f : (J × Bool) → A) (u l : ℕ) [NeZero u] :
    phaseAverage (fun I => sampleProduct p I f) 1 u l =
      𝔼 I : J → Bool, ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u) := by
  rw [Fintype.expect_eq_sum_div_card]
  unfold phaseAverage
  congr 1
  apply sum_congr rfl
  intro I _
  rw [stdAddChar_nat_phase]
  push_cast
  simp

lemma random_fourier_failure {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S v : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊)
    (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u : ℕ) (hu : 0 < u) (hV : 100000*Real.log S ≤ Real.log u) (hVS : Real.log u ≤ S)
    (hv : 0 ≤ v) (hvw : (99/100:ℝ)*v ≤ min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)) :
    (𝔼 f : (J × Bool) → A,
      if FourierBad (fun I => sampleProduct p I f) 1 u (Real.exp (-(1/10000:ℝ)*v)) then (1:ℝ) else 0) ≤
        Real.exp (-(1/200:ℝ)*v) := by
  let : NeZero u := ⟨hu.ne'⟩
  let δ := Real.exp (-(1/10000:ℝ)*v)
  let w := min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : 1/δ^4 = Real.exp ((1/2500:ℝ)*v) := by
    dsimp [δ]
    rw [←Real.exp_nat_mul,one_div,←Real.exp_neg]
    congr 1
    norm_num
    ring
  have hh := fourierBad_probability (fun f : (J × Bool) → A => fun I : J → Bool => sampleProduct p I f) 1 u δ
    (Real.exp (-(1/100:ℝ)*w)) hδ (Real.exp_nonneg _) (by
      intro l hl
      simp_rw [phaseAverage_sample]
      apply random_product_second_moment S hcard hlog hS p hp hinj hmax hP u l hu (mem_Icc.mp hl).1
        hV hVS
      have hlf : (l:ℝ) ≤ 1/δ^4 :=
        (Nat.cast_le.mpr (mem_Icc.mp hl).2).trans (Nat.floor_le (by positivity))
      rw [hinv] at hlf
      exact hlf.trans (Real.exp_le_exp.mpr (by nlinarith)))
  apply hh.trans
  dsimp [δ,w]
  rw [←Real.exp_nat_mul,←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  norm_num
  nlinarith

lemma expect_eval_function {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A] [Nonempty A]
    [AddCommMonoid E] [Module ℚ≥0 E] (j : J) (f : A → E) :
    (𝔼 g : J → A, f (g j)) = 𝔼 a : A, f a := by
  have hh := expect_restrict_injective (fun _ : Unit => j)
    (fun _ _ _ => Subsingleton.elim _ _) (fun g => f (g ()))
  change (𝔼 g : J → A, f (g j)) = _ at hh
  rw [hh]
  let e : (Unit → A) ≃ A := Equiv.funUnique Unit A
  convert Fintype.expect_equiv e (fun g => f (g ())) f (fun _ => rfl) using 1
  exact expect_congr (by ext; simp) (fun _ _ => rfl)

lemma simultaneous_finite_selection {Ω : Type uΩ} {J : Type uJ} {D : Type uD} {U : Type uU}
    [Fintype Ω] [Nonempty Ω] [Fintype J] [Fintype D] [Fintype U]
    (j₀ : J) (B : D → Ω → ℝ) (c ε : D → ℝ) (P : U → Ω → Prop) (r : U → ℝ)
    (hB : ∀ d ω, 0 ≤ B d ω) (hc : ∀ d, 0 < c d)
    (hmean : ∀ d, (𝔼 ω, B d ω) ≤ c d*ε d)
    (hprob : ∀ u, (𝔼 ω, if P u ω then (1:ℝ) else 0) ≤ r u)
    (hsmall : (∑ d, ε d)+(∑ u, r u^Fintype.card J) < 1) :
    ∃ f : J → Ω, (∀ d, B d (f j₀) < c d) ∧ (∀ u, ∃ j, ¬P u (f j)) := by
  classical
  let cost (f : J → Ω) :=
    (∑ d, B d (f j₀)/c d)+(∑ u, ∏ j, if P u (f j) then (1:ℝ) else 0)
  have hcost : (𝔼 f, cost f) < 1 := by
    apply lt_of_le_of_lt (b := (∑ d, ε d)+(∑ u, r u^Fintype.card J)) _ hsmall
    dsimp [cost]
    rw [expect_add_distrib, expect_sum_comm, expect_sum_comm]
    apply add_le_add
    · apply sum_le_sum
      intro d _
      rw [←expect_div, expect_eval_function]
      exact (div_le_iff₀ (hc d)).mpr (by simpa [mul_comm] using hmean d)
    · apply sum_le_sum
      intro u _
      have heq := expect_prod_pi (fun _j : J => fun ω : Ω => if P u ω then (1:ℝ) else 0)
      rw [heq]
      calc
        _ ≤ ∏ _j : J, r u := prod_le_prod₀ (fun _ _ => expect_nonneg (fun _ _ => by positivity)) (fun _ _ => hprob u)
        _ = _ := by simp
  obtain ⟨f,_,hf⟩ := exists_lt_of_expect_lt univ_nonempty hcost
  have hfirst (d : D) : B d (f j₀)/c d ≤ cost f := by
    exact (single_le_sum (fun e _ => div_nonneg (hB e _) (hc e).le) (mem_univ d)).trans
      (le_add_of_nonneg_right (sum_nonneg (fun _ _ => prod_nonneg (fun _ _ => by positivity))))
  refine ⟨f, ?_, ?_⟩
  · intro d
    exact (div_lt_iff₀ (hc d)).mp ((hfirst d).trans_lt hf) |>.trans_eq (one_mul _)
  · intro u
    by_contra hbad
    push Not at hbad
    have h1 : (1:ℝ) ≤ cost f := by
      have hp : (∏ j, if P u (f j) then (1:ℝ) else 0) = 1 := by simp [hbad]
      rw [←hp]
      have hn (v : U) : 0 ≤ ∏ j : J, if P v (f j) then (1:ℝ) else 0 :=
        prod_nonneg (fun _ _ => by positivity)
      exact (single_le_sum (fun v _ => hn v) (mem_univ u)).trans
        (le_add_of_nonneg_left (sum_nonneg (fun d _ => div_nonneg (hB d (f j₀)) (hc d).le)))
    linarith

lemma fourier_good_residues {I : Type uI} [Fintype I] [Nonempty I]
    (t : I → ℕ) (Q u : ℕ) (hQ : 0 < Q) (hu : 0 < u) (ht : ∀ i, 0 < t i)
    (δ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/256) (hgood : ¬FourierBad t Q u δ) :
    δ*Fintype.card I/2 ≤
      ((univ.filter fun i => (residue (Q*t i) u (quotient (Q*t i) u):ℝ) < δ*u).card:ℝ) := by
  apply residue_list_discrepancy t Q u hQ hu ht δ hδ hsmall
  intro l hl hlH
  exact le_of_not_gt (fun h => hgood ⟨l,mem_Icc.mpr ⟨hl,hlH⟩,h⟩)

end ShortEgyptian

end OAI
