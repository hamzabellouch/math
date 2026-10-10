import OAI.Combinatorics.Hamiltonian.PairPhases

namespace OAI

/-! First nonzero coefficients of paired-state polynomials. -/

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

theorem common_phase_sum_ne_zero {D : Type*} (s : Finset D) (hs : s.Nonempty)
    (c : D → ℕ) (p : D → ℂ[X]) (a : D → ℝ)
    (ha : ∀ d ∈ s, 0 < a d)
    (hp : ∀ d ∈ s, (p d).coeff 0 = (a d : ℂ)) :
    (∑ d ∈ s, C ((-Complex.I) ^ c d) * (X ^ c d * p d)) ≠ 0 := by
  classical
  obtain ⟨d₀, hd₀, hmin⟩ := s.exists_min_image c hs
  let m := c d₀
  let t := s.filter (fun d => c d = m)
  have ht : t.Nonempty := ⟨d₀, Finset.mem_filter.mpr ⟨hd₀, rfl⟩⟩
  have hpos : 0 < ∑ d ∈ t, a d := by
    exact Finset.sum_pos (fun d hd => ha d (Finset.mem_filter.mp hd).1) ht
  have hterm (d : D) (hd : d ∈ s) :
      (C ((-Complex.I) ^ c d) * (X ^ c d * p d)).coeff m =
        if c d = m then (-Complex.I) ^ m * (a d : ℂ) else 0 := by
    rw [coeff_C_mul, coeff_X_pow_mul']
    by_cases heq : c d = m
    · simp only [heq, le_refl, ite_true, Nat.sub_self, hp d hd]
    · have hlt : m < c d := lt_of_le_of_ne (hmin d hd) (Ne.symm heq)
      simp only [heq, not_le.mpr hlt, ite_false, mul_zero]
  have hcoeff :
      (∑ d ∈ s, C ((-Complex.I) ^ c d) * (X ^ c d * p d)).coeff m =
        (-Complex.I) ^ m * (∑ d ∈ t, a d : ℝ) := by
    rw [finsetSum_coeff]
    calc
      _ = ∑ d ∈ s, if c d = m then (-Complex.I) ^ m * (a d : ℂ) else 0 :=
        Finset.sum_congr rfl hterm
      _ = _ := by
        simp only [t, Finset.sum_filter, Complex.ofReal_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> simp only [Complex.ofReal_zero, mul_zero]
  intro hz
  have hnz : (-Complex.I) ^ m * ((∑ d ∈ t, a d : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (by exact_mod_cast ne_of_gt hpos)
  apply hnz
  rw [← hcoeff, hz, coeff_zero]

noncomputable def linearProduct {A R : Type*} [CommRing R] (s : Finset A) (a : A → R) : R[X] :=
  ∏ t ∈ s, (1 + C (a t) * X)

@[simp] theorem linearProduct_coeff_zero {A R : Type*} [CommRing R]
    (s : Finset A) (a : A → R) : (linearProduct s a).coeff 0 = 1 := by
  simp [linearProduct, coeff_zero_prod]

theorem linearProduct_coeff_one {A R : Type*} [CommRing R]
    (s : Finset A) (a : A → R) : (linearProduct s a).coeff 1 = ∑ t ∈ s, a t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linearProduct, coeff_one]
  | @insert t s ht ih =>
    rw [linearProduct, Finset.prod_insert ht, mul_coeff_one]
    change (1 + C (a t) * X).coeff 0 * (linearProduct s a).coeff 1 +
      (1 + C (a t) * X).coeff 1 * (linearProduct s a).coeff 0 = _
    simp [ih, Finset.sum_insert ht, add_comm, coeff_one]

theorem cycle_difference_divX_coeff_zero {A R : Type*} [CommRing R]
    (s : Finset A) (a b : A → R) :
    (divX (linearProduct s a - linearProduct s b)).coeff 0 =
      (∑ t ∈ s, a t) - ∑ t ∈ s, b t := by
  rw [coeff_divX, zero_add, coeff_sub, linearProduct_coeff_one, linearProduct_coeff_one]

theorem cycle_difference_eq_X_mul_divX {A R : Type*} [CommRing R]
    (s : Finset A) (a b : A → R) :
    linearProduct s a - linearProduct s b =
      X * divX (linearProduct s a - linearProduct s b) := by
  have h := X_mul_divX_add (linearProduct s a - linearProduct s b)
  simpa using h.symm

theorem cycle_group_polynomials_ne_zero {D A : Type*}
    (s : Finset D) (hs : s.Nonempty) (cycles : D → Finset A)
    (q : D → A → ℂ[X]) (a : D → A → ℝ)
    (ha : ∀ d ∈ s, ∀ t ∈ cycles d, 0 < a d t)
    (hq : ∀ d ∈ s, ∀ t ∈ cycles d, (q d t).coeff 0 = (a d t : ℂ)) :
    (∑ d ∈ s, ∏ t ∈ cycles d, C (-Complex.I) * (X * q d t)) ≠ 0 := by
  have h := common_phase_sum_ne_zero s hs (fun d => (cycles d).card)
    (fun d => ∏ t ∈ cycles d, q d t) (fun d => ∏ t ∈ cycles d, a d t)
    (fun d hd => Finset.prod_pos (ha d hd)) (by
      intro d hd
      rw [coeff_zero_prod, Complex.ofReal_prod]
      exact Finset.prod_congr rfl (hq d hd))
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finset.prod_mul_distrib, Finset.prod_const, ← map_pow]

end Barnette

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

theorem phase_sum {K : Type*} (s : Finset K) (a : K → ℤ)
    (ha : ∀ k ∈ s, 3 ∣ a k) : phase (∑ k ∈ s, a k) = ∏ k ∈ s, phase (a k) := by
  classical
  unfold phase
  rw [Int.sum_div ha]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, zpow_add₀ Complex.I_ne_zero]
    congr 1
    exact ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))

@[simp] theorem phase_three : phase 3 = Complex.I := by norm_num [phase]
@[simp] theorem phase_neg_three : phase (-3) = -Complex.I := by norm_num [phase, Complex.inv_I]

theorem phase_neg_of_disk {n : ℤ} (hn : n = 3 ∨ n = -3) : phase (-n) = -phase n := by
  rcases hn with rfl | rfl <;> norm_num

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def cycleFaces (P : @Pair A V T X) (c : CycleClass P.next) : Finset A := by
  classical
  exact Finset.univ.filter (fun t => classOf P.next t = c)

@[simp] theorem mem_cycleFaces (P : @Pair A V T X) (c : CycleClass P.next) (t : A) :
    t ∈ P.cycleFaces c ↔ classOf P.next t = c := by
  classical
  simp [cycleFaces]

noncomputable def cycleDelta (P : @Pair A V T X) (c : CycleClass P.next) : ℤ :=
  ∑ t ∈ P.cycleFaces c, indexDelta (P.left.val t) (P.right.val t)

omit [Fintype A] in
@[simp] theorem orient_left_val (P : @Pair A V T X) (b : CycleClass P.next → Bool) (t : A) :
    (P.orient b).val.left.val t =
      if b (classOf P.next t) then P.right.val t else P.left.val t := rfl

omit [Fintype A] in
@[simp] theorem orient_right_val (P : @Pair A V T X) (b : CycleClass P.next → Bool) (t : A) :
    (P.orient b).val.right.val t =
      if b (classOf P.next t) then P.left.val t else P.right.val t := rfl

theorem orient_delta_sum (P : @Pair A V T X) (b : CycleClass P.next → Bool)
    (c : CycleClass P.next) :
    (∑ t ∈ P.cycleFaces c, indexDelta ((P.orient b).val.left.val t)
        ((P.orient b).val.right.val t)) =
      if b c then -P.cycleDelta c else P.cycleDelta c := by
  classical
  rw [cycleDelta]
  cases hb : b c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro t ht
    rw [orient_left_val, orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl
  · simp only [↓reduceIte, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [orient_left_val, orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    exact indexDelta_antisymm _ _

theorem orient_rawIndexSum (P : @Pair A V T X) (b : CycleClass P.next → Bool) :
    rawIndexSum (P.orient b).val.left (P.orient b).val.right =
      ∑ c, if b c then -P.cycleDelta c else P.cycleDelta c := by
  classical
  unfold rawIndexSum
  rw [← Finset.sum_fiberwise Finset.univ (classOf P.next)]
  apply Finset.sum_congr rfl
  intro c _
  exact P.orient_delta_sum b c

theorem orient_phase (P : @Pair A V T X)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3)
    (b : CycleClass P.next → Bool) :
    phase (rawIndexSum (P.orient b).val.left (P.orient b).val.right) =
      ∏ c, if b c then -phase (P.cycleDelta c) else phase (P.cycleDelta c) := by
  classical
  rw [P.orient_rawIndexSum b, phase_sum]
  · apply Finset.prod_congr rfl
    intro c _
    cases hb : b c <;> simp [phase_neg_of_disk (hdisk c)]
  · intro c _
    rcases hdisk c with h | h <;> cases b c <;> simp [h]

noncomputable def stateWeight (w : A → Fin 3 → ℝ) (s : T.State X) : ℂ[X] :=
  linearProduct Finset.univ (fun t => (w t (s.val t) : ℂ))

noncomputable def cycleLeftWeight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℂ[X] :=
  linearProduct (P.cycleFaces c) (fun t => (w t (P.left.val t) : ℂ))

noncomputable def cycleRightWeight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℂ[X] :=
  linearProduct (P.cycleFaces c) (fun t => (w t (P.right.val t) : ℂ))

theorem orient_weight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (b : CycleClass P.next → Bool) : stateWeight w (P.orient b).val.right =
      ∏ c, if b c then P.cycleLeftWeight w c else P.cycleRightWeight w c := by
  classical
  unfold stateWeight linearProduct
  rw [← Finset.prod_fiberwise Finset.univ (classOf P.next)]
  apply Finset.prod_congr rfl
  intro c _
  change (∏ t ∈ P.cycleFaces c, _) = _
  cases hb : b c
  · simp only [Bool.false_eq_true, ↓reduceIte, cycleRightWeight, linearProduct]
    apply Finset.prod_congr rfl
    intro t ht
    rw [orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl
  · simp only [↓reduceIte, cycleLeftWeight, linearProduct]
    apply Finset.prod_congr rfl
    intro t ht
    rw [orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl

noncomputable def term (w : A → Fin 3 → ℝ) (P : @Pair A V T X) : ℂ[X] :=
  C (phase (rawIndexSum P.left P.right)) * stateWeight w P.right

theorem orient_term (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3)
    (b : CycleClass P.next → Bool) : term w (P.orient b).val =
      ∏ c, if b c then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
        else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c := by
  classical
  rw [term, P.orient_phase hdisk, P.orient_weight, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  cases b c <;> simp

theorem group_sum_product (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3) :
    (∑ Q : P.Group, term w Q.val) =
      ∏ c, C (phase (P.cycleDelta c)) *
        (P.cycleRightWeight w c - P.cycleLeftWeight w c) := by
  classical
  rw [← Fintype.sum_equiv P.groupEquiv _ (fun Q : P.Group => term w Q.val)
    (fun _ => rfl)]
  calc
    _ = ∑ b : CycleClass P.next → Bool,
        ∏ c, if b c then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c := by
      apply Finset.sum_congr rfl
      intro b _
      exact P.orient_term w hdisk b
    _ = ∏ c, ∑ b : Bool, if b then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c :=
      (Fintype.prod_sum (ι := CycleClass P.next) (κ := fun _ => Bool)
        (fun c b => if b then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro c _
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.false_eq_true]
      ring

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def cycleSlope (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℝ :=
  (∑ t ∈ P.cycleFaces c, w t (P.right.val t)) -
    ∑ t ∈ P.cycleFaces c, w t (P.left.val t)

theorem cycle_diff_coeff_one (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) :
    (divX (P.cycleRightWeight w c - P.cycleLeftWeight w c)).coeff 0 =
      (P.cycleSlope w c : ℂ) := by
  rw [cycleRightWeight, cycleLeftWeight, cycle_difference_divX_coeff_zero]
  simp only [cycleSlope, Complex.ofReal_sub, Complex.ofReal_sum]

theorem cycle_factor_witness (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next)
    (hsign : (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    ∃ (q : ℂ[X]) (a : ℝ), 0 < a ∧ q.coeff 0 = (a : ℂ) ∧
      C (phase (P.cycleDelta c)) * (P.cycleRightWeight w c - P.cycleLeftWeight w c) =
        C (-Complex.I) * (Polynomial.X * q) := by
  rcases hsign with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · refine ⟨divX (P.cycleRightWeight w c - P.cycleLeftWeight w c),
      P.cycleSlope w c, hs, P.cycle_diff_coeff_one w c, ?_⟩
    rw [hd, phase_neg_three]
    congr 1
    exact cycle_difference_eq_X_mul_divX _ _ _
  · refine ⟨-divX (P.cycleRightWeight w c - P.cycleLeftWeight w c),
      -P.cycleSlope w c, neg_pos.mpr hs, ?_, ?_⟩
    · rw [coeff_neg, P.cycle_diff_coeff_one, Complex.ofReal_neg]
    · rw [hd, phase_three]
      have heq : P.cycleRightWeight w c - P.cycleLeftWeight w c =
          Polynomial.X * divX (P.cycleRightWeight w c - P.cycleLeftWeight w c) :=
        cycle_difference_eq_X_mul_divX _ _ _
      calc
        _ = C Complex.I * (Polynomial.X *
            divX (P.cycleRightWeight w c - P.cycleLeftWeight w c)) := congrArg _ heq
        _ = _ := by simp only [map_neg, mul_neg, neg_mul, neg_neg]

def GroupIndex : Type _ := Set.range (@third A V T X)

noncomputable instance : Fintype (@GroupIndex A V T X) :=
  Fintype.ofFinite (Set.range (@third A V T X))

noncomputable def GroupIndex.representative (d : @GroupIndex A V T X) : @Pair A V T X :=
  Classical.choose d.property

omit [Fintype A] in
theorem GroupIndex.representative_third (d : @GroupIndex A V T X) : d.representative.third = d.val :=
  Classical.choose_spec d.property

def groupIndex (P : @Pair A V T X) : @GroupIndex A V T X := ⟨P.third, P, rfl⟩

noncomputable def GroupIndex.fiberEquivGroup (d : @GroupIndex A V T X) :
    {P : @Pair A V T X // P.groupIndex = d} ≃ d.representative.Group :=
  Equiv.subtypeEquivRight (fun P => by
    constructor
    · intro h
      have hh := congrArg Subtype.val h
      change P.third = d.val at hh
      exact hh.trans d.representative_third.symm
    · intro h
      apply Subtype.ext
      exact h.trans d.representative_third)

theorem sum_groups (w : A → Fin 3 → ℝ) :
    (∑ P : @Pair A V T X, term w P) =
      ∑ d : @GroupIndex A V T X, ∑ Q : d.representative.Group, term w Q.val := by
  classical
  rw [← Fintype.sum_fiberwise groupIndex (term w)]
  apply Finset.sum_congr rfl
  intro d _
  exact Fintype.sum_equiv d.fiberEquivGroup _ _ (fun _ => rfl)

theorem total_sum_ne_zero (hex : Nonempty (@Pair A V T X)) (w : A → Fin 3 → ℝ)
    (hsign : ∀ (P : @Pair A V T X) c,
      (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    (∑ P : @Pair A V T X, term w P) ≠ 0 := by
  classical
  let D := @GroupIndex A V T X
  have hnonempty : (Finset.univ : Finset D).Nonempty :=
    ⟨hex.some.groupIndex, Finset.mem_univ _⟩
  have hw : ∀ d : D, ∀ c : CycleClass d.representative.next,
      ∃ (q : ℂ[X]) (a : ℝ), 0 < a ∧ q.coeff 0 = (a : ℂ) ∧
        C (phase (d.representative.cycleDelta c)) *
          (d.representative.cycleRightWeight w c - d.representative.cycleLeftWeight w c) =
            C (-Complex.I) * (Polynomial.X * q) := by
    intro d c
    exact d.representative.cycle_factor_witness w c (hsign d.representative c)
  choose q a ha hq hf using hw
  have h := common_phase_sum_ne_zero Finset.univ hnonempty
    (fun d : D => Fintype.card (CycleClass d.representative.next))
    (fun d => ∏ c, q d c) (fun d => ∏ c, a d c)
    (fun d _ => Finset.prod_pos (fun c _ => ha d c)) (by
      intro d _
      rw [coeff_zero_prod, Complex.ofReal_prod]
      exact Finset.prod_congr rfl (fun c _ => hq d c))
  rw [sum_groups]
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  rw [d.representative.group_sum_product w (fun c => by
    rcases hsign d.representative c with ⟨hd, _⟩ | ⟨hd, _⟩
    · exact Or.inr hd
    · exact Or.inl hd)]
  calc
    _ = ∏ c, C (-Complex.I) * (Polynomial.X * q d c) :=
      Finset.prod_congr rfl (fun c _ => hf d c)
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← map_pow]

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def secondFiberEquiv (s : T.State X) :
    {P : @Pair A V T X // P.right = s} ≃ T.Partners s where
  toFun P := ⟨P.val.left,
    Eq.mp (congrArg (fun z => T.Partner P.val.left z) P.property) P.val.partner⟩
  invFun r := ⟨⟨(r.val, s), r.property⟩, rfl⟩
  left_inv P := by
    apply Subtype.ext
    apply Pair.ext
    · rfl
    · exact P.property.symm
  right_inv _ := rfl

theorem sum_second_states (w : A → Fin 3 → ℝ) :
    (∑ P : @Pair A V T X, term w P) =
      ∑ s : T.State X, ∑ r : T.Partners s,
        C (phase (rawIndexSum r.val s)) * stateWeight w s := by
  classical
  rw [← Fintype.sum_fiberwise right (term w)]
  apply Finset.sum_congr rfl
  intro s _
  apply Fintype.sum_equiv (secondFiberEquiv s)
  intro P
  change C (phase (rawIndexSum P.val.left P.val.right)) * stateWeight w P.val.right = _
  rw [P.property]
  rfl

theorem forest_pair_of_disk_circulation (hex : Nonempty (@Pair A V T X))
    (hdisk : ∀ (s : T.State X) (C : T.OppositeCycle s) (r : T.Partners s),
      C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (w : A → Fin 3 → ℝ)
    (hsign : ∀ (P : @Pair A V T X) c,
      (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    ∃ P : @Pair A V T X, (T.oppositeGraph P.right).IsAcyclic := by
  classical
  by_contra hforest
  have hcyclic (P : @Pair A V T X) : ¬(T.oppositeGraph P.right).IsAcyclic :=
    fun h => hforest ⟨P, h⟩
  apply total_sum_ne_zero hex w hsign
  rw [sum_second_states]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hp : Nonempty (T.Partners s)
  · let P : @Pair A V T X := ⟨(hp.some.val, s), hp.some.property⟩
    obtain ⟨C⟩ := T.oppositeCycle_nonempty s (hcyclic P)
    simpa only [Polynomial.smul_eq_C_mul] using
      C.fixed_second_state_cancels (hdisk s C) (stateWeight w s)
  · have : IsEmpty (T.Partners s) := not_nonempty_iff.mp hp
    exact Finset.sum_eq_zero (fun r _ => isEmptyElim r)

end TriangleSystem.Pair
end Barnette

end OAI
