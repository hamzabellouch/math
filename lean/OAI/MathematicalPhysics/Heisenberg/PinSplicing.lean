import OAI.MathematicalPhysics.Heisenberg.PermutationSymbols

namespace OAI

noncomputable section

open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

open scoped Classical
namespace Heisenberg.Pin

section

variable {V : Type*} [Fintype V] [DecidableEq V]

def spliceVariables : Option V ⊕ Option V → Option (V ⊕ V)
  | Sum.inl none => none
  | Sum.inr none => none
  | Sum.inl (some i) => some (Sum.inl i)
  | Sum.inr (some i) => some (Sum.inr i)

def eraseNone {σ : Type*} : MvPolynomial (Option σ) ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.aeval (fun j => j.elim 0 MvPolynomial.X)

def splice (p : MvPolynomial (Option V ⊕ Option V) ℂ) : MvPolynomial (V ⊕ V) ℂ :=
  eraseNone (MvPolynomial.pderiv none (MvPolynomial.rename spliceVariables p))

lemma eraseNone_rename_some {σ : Type*} (p : MvPolynomial σ ℂ) :
    eraseNone (MvPolynomial.rename some p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [eraseNone]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    simp [eraseNone]

lemma pderiv_none_rename_some {σ : Type*} (p : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv none (MvPolynomial.rename some p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

lemma eraseNone_X_none {σ : Type*} :
    eraseNone (MvPolynomial.X (none : Option σ)) = 0 := by simp [eraseNone]

lemma eraseNone_X_some {σ : Type*} (i : σ) :
    eraseNone (MvPolynomial.X (some i)) = MvPolynomial.X i := by simp [eraseNone]

omit [DecidableEq V] in
lemma renamed_symbol_fixed (π : Equiv.Perm (Option V)) (h : π none = none) :
    MvPolynomial.rename spliceVariables (permutationSymbol π) =
      (2 * MvPolynomial.X none) *
        MvPolynomial.rename some (permutationSymbol (Equiv.removeNone π)) := by
  have hs (i : V) : π (some i) = some (Equiv.removeNone π i) := by
    apply Eq.symm
    apply Equiv.removeNone_some
    cases he : π (some i) with
    | none => exact False.elim (Option.some_ne_none i (π.injective (he.trans h.symm)))
    | some j => exact ⟨j, rfl⟩
  simp only [permutationSymbol, map_prod, Fintype.prod_option, map_mul, map_add,
    MvPolynomial.rename_X, h, spliceVariables, hs]
  congr 1
  ring

theorem splice_permutationSymbol_fixed (π : Equiv.Perm (Option V)) (h : π none = none) :
    splice (permutationSymbol π) = 2 * permutationSymbol (Equiv.removeNone π) := by
  have hd : MvPolynomial.pderiv none (2 : MvPolynomial (Option (V ⊕ V)) ℂ) = 0 :=
    (MvPolynomial.pderiv none).map_natCast 2
  rw [splice, renamed_symbol_fixed π h, MvPolynomial.pderiv_mul]
  simp [hd, pderiv_none_rename_some, eraseNone_rename_some, map_ofNat]

omit [Fintype V] [DecidableEq V] in
lemma removeNone_at_predecessor (π : Equiv.Perm (Option V)) (a b : V)
    (ha : π (some a) = none) (hb : π none = some b) : Equiv.removeNone π a = b := by
  exact Option.some.inj ((Equiv.removeNone_none π ha).trans hb)

omit [Fintype V] [DecidableEq V] in
lemma removeNone_off_predecessor (π : Equiv.Perm (Option V)) (a i : V)
    (ha : π (some a) = none) (hi : i ≠ a) :
    π (some i) = some (Equiv.removeNone π i) := by
  apply Eq.symm
  apply Equiv.removeNone_some
  cases he : π (some i) with
  | none => exact False.elim (hi (Option.some.inj (π.injective (he.trans ha.symm))))
  | some j => exact ⟨j, rfl⟩

lemma renamed_symbol_spliced (π : Equiv.Perm (Option V)) (a b : V)
    (ha : π (some a) = none) (hb : π none = some b) :
    MvPolynomial.rename spliceVariables (permutationSymbol π) =
      (MvPolynomial.X none + MvPolynomial.X (some (Sum.inr b))) *
      (MvPolynomial.X (some (Sum.inl a)) + MvPolynomial.X none) *
      MvPolynomial.rename some
        (∏ i ∈ Finset.univ.erase a,
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (Equiv.removeNone π i)))) := by
  rw [permutationSymbol, Fintype.prod_option]
  rw [← Finset.mul_prod_erase Finset.univ (fun i : V =>
    MvPolynomial.X (Sum.inl (some i)) + MvPolynomial.X (Sum.inr (π (some i))))
    (Finset.mem_univ a)]
  simp only [map_mul, map_add, map_prod, MvPolynomial.rename_X, ha, hb,
    spliceVariables, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [removeNone_off_predecessor π a i ha (Finset.mem_erase.mp hi).1]

theorem splice_permutationSymbol_nonfixed (π : Equiv.Perm (Option V))
    (h : π none ≠ none) :
    splice (permutationSymbol π) = permutationSymbol (Equiv.removeNone π) := by
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h
  have hi : π.symm none ≠ none := by simpa using h
  obtain ⟨a, ha'⟩ := Option.ne_none_iff_exists'.mp hi
  have ha : π (some a) = none := by rw [← ha']; exact π.apply_symm_apply none
  rw [splice, renamed_symbol_spliced π a b ha hb, MvPolynomial.pderiv_mul]
  simp only [pderiv_none_rename_some, mul_zero, add_zero, MvPolynomial.pderiv_mul,
    map_add, MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne (Option.some_ne_none _),
    add_zero, zero_add, one_mul, mul_one, map_mul, eraseNone_X_none,
    eraseNone_X_some, eraseNone_rename_some]
  rw [permutationSymbol, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
  rw [removeNone_at_predecessor π a b ha hb]

end

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

lemma eraseNone_eq_boundarySection {σ : Type*} (p : MvPolynomial (Option σ) ℂ) :
    eraseNone p = boundarySection p id (fun _ => 0) := by
  simp only [eraseNone, boundarySection, MvPolynomial.aeval_def]
  congr 1
  funext j
  cases j <;> simp

omit [DecidableEq V] in

theorem stable_splice {p : MvPolynomial (Option V ⊕ Option V) ℂ}
    (hp : Stable p) (hn : splice p ≠ 0) : Stable (splice p) := by
  have hr : Stable (MvPolynomial.rename spliceVariables p) := by
    intro z hz
    rw [MvPolynomial.eval_rename]
    exact hp (z ∘ spliceVariables) (fun i => hz (spliceVariables i))
  obtain hz | hd := stable_pderiv hr none
  · exact False.elim (hn (by simp [splice, hz]))
  rw [splice, eraseNone_eq_boundarySection] at hn ⊢
  exact stable_boundarySection hd id (fun _ => 0) hn

omit [Fintype V] [DecidableEq V] in
lemma splice_add (p q : MvPolynomial (Option V ⊕ Option V) ℂ) :
    splice (p + q) = splice p + splice q := by simp [splice]

omit [Fintype V] [DecidableEq V] in
lemma splice_C_mul (c : ℂ) (p : MvPolynomial (Option V ⊕ Option V) ℂ) :
    splice (MvPolynomial.C c * p) = MvPolynomial.C c * splice p := by
  simp only [splice, map_mul, MvPolynomial.rename_C, MvPolynomial.pderiv_C_mul]
  congr 1
  simp [eraseNone]

omit [Fintype V] [DecidableEq V] in
lemma splice_sum (p : Ω → MvPolynomial (Option V ⊕ Option V) ℂ) :
    splice (∑ ω, p ω) = ∑ ω, splice (p ω) := by simp [splice]

def spliceWeight (π : Equiv.Perm (Option V)) : ℝ := if π none = none then 2 else 1

omit [Fintype V] [DecidableEq V] in
lemma spliceWeight_ge_one (π : Equiv.Perm (Option V)) : 1 ≤ spliceWeight π := by
  unfold spliceWeight
  split_ifs <;> norm_num

lemma splice_permutationSymbol (π : Equiv.Perm (Option V)) :
    splice (permutationSymbol π) =
      MvPolynomial.C (spliceWeight π : ℂ) * permutationSymbol (Equiv.removeNone π) := by
  by_cases h : π none = none
  · rw [splice_permutationSymbol_fixed π h]
    norm_num [spliceWeight, h, map_ofNat]
  · rw [splice_permutationSymbol_nonfixed π h]
    simp [spliceWeight, h]

lemma splice_lawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm (Option V)) :
    splice (lawSymbol μ π) =
      lawSymbol (fun ω => μ ω * spliceWeight (π ω)) (fun ω => Equiv.removeNone (π ω)) := by
  simp only [lawSymbol, splice_sum, splice_C_mul, splice_permutationSymbol,
    Complex.ofReal_mul, map_mul, mul_assoc]

omit [DecidableEq V] in
lemma lawSymbol_eval_one_general (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) :
    MvPolynomial.eval (fun _ => 1) (lawSymbol μ π) =
      ((∑ ω, μ ω : ℝ) : ℂ) * 2 ^ Fintype.card V := by
  simp only [lawSymbol, permutationSymbol, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, map_add, MvPolynomial.eval_X, one_add_one_eq_two,
    Finset.prod_const, Finset.card_univ]
  rw [← Finset.sum_mul, Complex.ofReal_sum]

omit [DecidableEq V] in
lemma lawSymbol_ne_zero_general (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω ≠ 0) : lawSymbol μ π ≠ 0 := by
  intro hzero
  have he := lawSymbol_eval_one_general μ π
  rw [hzero, map_zero] at he
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ) (pow_ne_zero _ (by norm_num)) he.symm

theorem stable_spliced_law (μ : Ω → ℝ) (π : Ω → Equiv.Perm (Option V))
    (hμ : ∀ ω, 0 ≤ μ ω) (hpos : 0 < ∑ ω, μ ω) (hs : Stable (lawSymbol μ π)) :
    Stable (lawSymbol (fun ω => μ ω * spliceWeight (π ω))
      (fun ω => Equiv.removeNone (π ω))) := by
  rw [← splice_lawSymbol]
  apply stable_splice hs
  rw [splice_lawSymbol]
  apply lawSymbol_ne_zero_general
  apply ne_of_gt
  apply hpos.trans_le
  apply Finset.sum_le_sum
  intro ω _
  exact le_mul_of_one_le_right (hμ ω) (spliceWeight_ge_one (π ω))

end Heisenberg.Pin

namespace Heisenberg.Cycle

open Equiv

variable {V : Type*}

def projection (π : Perm (Option V)) : Option V → Option (Classes (removeNone π))
  | some i => some (classOf (removeNone π) i)
  | none => (π none).map (classOf (removeNone π))

lemma projection_apply (π : Perm (Option V)) (i : Option V) :
    projection π (π i) = projection π i := by
  cases i with
  | none =>
    cases h : π none <;> simp [projection, h]
  | some i =>
    cases h : π (some i) with
    | none =>
      have he := removeNone_none π h
      change (π none).map (classOf (removeNone π)) = _
      rw [← he]
      simp [projection]
    | some j =>
      have he := removeNone_some π ⟨j, h⟩
      have he' : removeNone π i = j := Option.some.inj (he.trans h)
      simp only [projection]
      rw [← he', classOf_apply]

lemma projection_pow (π : Perm (Option V)) (n : ℕ) (i : Option V) :
    projection π ((π ^ n) i) = projection π i := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', Perm.mul_apply, projection_apply, hn]

variable [Fintype V]

lemma sameCycle_removeNone_iff (π : Perm (Option V)) (i j : V) :
    Perm.SameCycle (removeNone π) i j ↔ π.SameCycle (some i) (some j) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hstep (k : V) : π.SameCycle (some k) (some (removeNone π k)) := by
      cases he : π (some k) with
      | none =>
        rw [removeNone_none π he]
        have h1 : π.SameCycle (some k) none := by
          rw [← he]
          exact (Perm.SameCycle.refl π _).apply_right
        exact h1.apply_right
      | some l =>
        rw [removeNone_some π ⟨l, he⟩]
        exact (Perm.SameCycle.refl π _).apply_right
    have hall (m : ℕ) : π.SameCycle (some i) (some ((removeNone π ^ m) i)) := by
      induction m with
      | zero => exact Perm.SameCycle.refl _ _
      | succ m hm =>
        rw [pow_succ', Perm.mul_apply]
        exact hm.trans (hstep _)
    simpa [hn] using hall n
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have he := projection_pow π n (some i)
    rw [hn] at he
    exact (classOf_eq_iff _ _ _).mp (Option.some.inj he).symm

def classInclusion (π : Perm (Option V)) : Classes (removeNone π) → Classes π :=
  Quotient.map some (fun i j h => (sameCycle_removeNone_iff π i j).mp h)

@[simp] lemma classInclusion_mk (π : Perm (Option V)) (i : V) :
    classInclusion π (classOf (removeNone π) i) = classOf π (some i) := rfl

lemma classInclusion_injective (π : Perm (Option V)) :
    Function.Injective (classInclusion π) := by
  intro a b h
  induction a using Quotient.inductionOn with | _ i =>
    induction b using Quotient.inductionOn with | _ j =>
      exact (classOf_eq_iff _ _ _).mpr
        ((sameCycle_removeNone_iff π i j).mpr ((classOf_eq_iff _ _ _).mp h))

lemma classInclusion_surjective (π : Perm (Option V)) (hn : π none ≠ none) :
    Function.Surjective (classInclusion π) := by
  intro c
  induction c using Quotient.inductionOn with | _ i =>
    cases i with
    | some i => exact ⟨classOf (removeNone π) i, rfl⟩
    | none =>
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hn
      refine ⟨classOf (removeNone π) i, ?_⟩
      simp only [classInclusion_mk]
      rw [← hi, classOf_apply]
      rfl

lemma classInclusion_range_fixed (π : Perm (Option V)) (hfix : π none = none) :
    Set.range (classInclusion π) = {c | c ≠ classOf π none} := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩ h
    induction a using Quotient.inductionOn with | _ i =>
      have hs := (classOf_eq_iff π (some i) none).mp h
      exact Option.some_ne_none i (hs.eq_of_right hfix)
  · intro h
    induction c using Quotient.inductionOn with | _ i =>
      cases i with
      | none => exact False.elim (h rfl)
      | some i => exact ⟨classOf (removeNone π) i, rfl⟩

lemma missingInclusion_condition (π : Perm (Option V)) (P : Set V)
    (c : Classes (removeNone π)) :
    (∀ i ∈ some '' P, classInclusion π c ≠ classOf π i) ↔
      ∀ i ∈ P, c ≠ classOf (removeNone π) i := by
  constructor
  · intro h i hi he
    apply h (some i) ⟨i, hi, rfl⟩
    rw [he, classInclusion_mk]
  · rintro h _ ⟨i, hi, rfl⟩ he
    exact h i hi (classInclusion_injective π he)

def missingInclusion (π : Perm (Option V)) (P : Set V) :
    MissingClasses (removeNone π) P → MissingClasses π (some '' P) :=
  fun c => ⟨classInclusion π c.val, (missingInclusion_condition π P c.val).mpr c.property⟩

lemma missingInclusion_injective (π : Perm (Option V)) (P : Set V) :
    Function.Injective (missingInclusion π P) := by
  intro a b h
  apply Subtype.ext
  exact classInclusion_injective π (congrArg Subtype.val h)

lemma missingInclusion_surjective (π : Perm (Option V)) (P : Set V)
    (hn : π none ≠ none) : Function.Surjective (missingInclusion π P) := by
  intro c
  obtain ⟨a, ha⟩ := classInclusion_surjective π hn c.val
  refine ⟨⟨a, (missingInclusion_condition π P a).mp (by simpa [ha] using c.property)⟩, ?_⟩
  exact Subtype.ext ha

lemma missingCount_nonfixed (π : Perm (Option V)) (P : Set V) (hn : π none ≠ none) :
    missingCount π (some '' P) = missingCount (removeNone π) P := by
  unfold missingCount
  exact (Nat.card_congr (Equiv.ofBijective (missingInclusion π P)
    ⟨missingInclusion_injective π P, missingInclusion_surjective π P hn⟩)).symm

omit [Fintype V] in
lemma none_missing (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    ∀ i ∈ some '' P, classOf π none ≠ classOf π i := by
  rintro _ ⟨i, _, rfl⟩ he
  have hs := (classOf_eq_iff π none (some i)).mp he
  exact Option.some_ne_none i (hs.eq_of_left hf).symm

def missingOption (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    Option (MissingClasses (removeNone π) P) → MissingClasses π (some '' P)
  | none => ⟨classOf π none, none_missing π P hf⟩
  | some c => missingInclusion π P c

lemma missingOption_injective (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    Function.Injective (missingOption π P hf) := by
  intro a b he
  have hv := congrArg Subtype.val he
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      have hb : classInclusion π b.val ≠ classOf π none := by
        have hr : classInclusion π b.val ∈ Set.range (classInclusion π) := ⟨b.val, rfl⟩
        rw [classInclusion_range_fixed π hf] at hr
        exact hr
      exact False.elim (hb hv.symm)
  | some a =>
    cases b with
    | none =>
      have ha : classInclusion π a.val ≠ classOf π none := by
        have hr : classInclusion π a.val ∈ Set.range (classInclusion π) := ⟨a.val, rfl⟩
        rw [classInclusion_range_fixed π hf] at hr
        exact hr
      exact False.elim (ha hv)
    | some b => exact congrArg some (missingInclusion_injective π P he)

lemma missingOption_surjective (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    Function.Surjective (missingOption π P hf) := by
  classical
  intro c
  by_cases hc : c.val = classOf π none
  · exact ⟨none, Subtype.ext hc.symm⟩
  · have hr : c.val ∈ Set.range (classInclusion π) := by
      rw [classInclusion_range_fixed π hf]
      exact hc
    obtain ⟨a, ha⟩ := hr
    refine ⟨some ⟨a, (missingInclusion_condition π P a).mp ?_⟩, Subtype.ext ha⟩
    simpa [ha] using c.property

lemma missingCount_fixed (π : Perm (Option V)) (P : Set V) (hf : π none = none) :
    missingCount π (some '' P) = missingCount (removeNone π) P + 1 := by
  unfold missingCount
  have he := Nat.card_congr (Equiv.ofBijective (missingOption π P hf)
    ⟨missingOption_injective π P hf, missingOption_surjective π P hf⟩)
  let _ : Fintype (MissingClasses (removeNone π) P) := Fintype.ofFinite _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option] using he.symm

theorem cycle_weight_splice (π : Perm (Option V)) (P : Set V) :
    (2 : ℝ) ^ missingCount π (some '' P) =
      (if π none = none then 2 else 1) * (2 : ℝ) ^ missingCount (removeNone π) P := by
  classical
  by_cases hf : π none = none
  · rw [ite_eq_left hf, missingCount_fixed π P hf, pow_succ, mul_comm]
  · rw [ite_eq_right hf, missingCount_nonfixed π P hf, one_mul]

end Heisenberg.Cycle

end

end OAI
