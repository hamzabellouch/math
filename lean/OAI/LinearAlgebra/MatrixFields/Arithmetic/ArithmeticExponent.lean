import Mathlib
import OAI.LinearAlgebra.MatrixFields.Arithmetic.RecursiveBlockPrograms

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic
section

namespace Program

variable {F Input : Type*}

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => simp [registerCost, cost]
  | step p g ih => simp [registerCost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Field F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert i
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      change g.cost = 0 at hi
      cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hi
      | sub a b => simp [Gate.cost] at hi
      | mul a b => simp [Gate.cost] at hi
    · intro hi
      simpa only [eval_step_succ] using ih j hi

end Program

section ElementaryMatrices

variable {F : Type*} [Field F] {a b c : ℕ}

def elementaryLeft (i : Fin a) (j : Fin b) : Matrix (Fin a) (Fin b) F :=
  fun x y => if x = i then if y = j then 1 else 0 else 0

def elementaryRight (j : Fin b) (k : Fin c) : Matrix (Fin b) (Fin c) F :=
  fun y z => if z = k then if y = j then 1 else 0 else 0

theorem elementaryProduct (i x : Fin a) (j : Fin b) (k z : Fin c) :
    (elementaryLeft (F := F) i j * elementaryRight (F := F) j k) x z =
      if (x, z) = (i, k) then 1 else 0 := by
  by_cases hi : x = i <;> by_cases hk : z = k <;>
    simp [Matrix.mul_apply, elementaryLeft, elementaryRight, hi, hk]

end ElementaryMatrices

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem output_injective (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : Function.Injective (fun o : Fin a × Fin c => P.output o.1 o.2) := by
  classical
  intro x y hxy
  change P.output x.1 x.2 = P.output y.1 y.2 at hxy
  let j : Fin b := ⟨0, by omega⟩
  let A := elementaryLeft (F := F) x.1 j
  let B := elementaryRight (F := F) j x.2
  have hx := congrFun (congrFun (hP A B) x.1) x.2
  have hy := congrFun (congrFun (hP A B) y.1) y.2
  have heq : (A * B) x.1 x.2 = (A * B) y.1 y.2 := by
    rw [← hx, ← hy]
    change P.program.eval (matrixInputs A B) (P.output x.1 x.2) =
      P.program.eval (matrixInputs A B) (P.output y.1 y.2)
    rw [hxy]
  simp only [A, B, elementaryProduct, Prod.eta, ite_true] at heq
  by_contra hne
  have hyx : y ≠ x := Ne.symm hne
  simp [hyx] at heq

theorem one_le_output_registerCost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    1 ≤ P.program.registerCost (P.output i k) := by
  by_contra hn
  have hzero : P.program.registerCost (P.output i k) = 0 := by omega
  let j : Fin b := ⟨0, by omega⟩
  have hentry (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
      P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun (congrFun (hP A B) i) k
  rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
      (P.output i k) hzero with ⟨z, hz⟩ | ⟨u, hu⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry (elementaryLeft i j) (elementaryRight j k)
      rw [hz] at h
      simpa only [elementaryProduct, ite_true] using h
    exact (zero_ne_one : (0 : F) ≠ 1) (hz0.symm.trans hz1)
  · rcases u with ⟨x, y⟩ | ⟨y, z⟩
    · have h := hentry (fun _ _ => 1) 0
      rw [hu] at h
      change (1 : F) = ∑ _ : Fin b, (1 : F) * 0 at h
      simp at h
    · have h := hentry 0 (fun _ _ => 1)
      rw [hu] at h
      change (1 : F) = ∑ _ : Fin b, (0 : F) * 1 at h
      simp at h

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  classical
  let f : Fin a × Fin c → Fin P.registers := fun o => P.output o.1 o.2
  have hf : Function.Injective f := P.output_injective hb hP
  calc
    a * c = ∑ _o : Fin a × Fin c, (1 : ℕ) := by simp
    _ ≤ ∑ o : Fin a × Fin c, P.program.registerCost (f o) := by
      apply Finset.sum_le_sum
      intro o ho
      exact P.one_le_output_registerCost hb hP o.1 o.2
    _ = ∑ r ∈ Finset.univ.image f, P.program.registerCost r := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑ r, P.program.registerCost r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = P.cost := P.program.sum_registerCost

end MatrixAlgorithm

theorem rectangularAdmissibleExponent_two_le {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : 2 ≤ τ := by
  by_contra hneg
  have hτlt : τ < 2 := lt_of_not_ge hneg
  let ε : ℝ := (2 - τ) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hlower : (n : ℝ) ^ (2 : ℕ) ≤ P.cost := by
    have h : n ^ 2 ≤ P.cost := by
      simpa [pow_two] using P.output_size_le_cost (one_le_innerSize hn1 k) hP
    exact_mod_cast h
  have hstrict : (n : ℝ) ^ (2 : ℕ) < (n : ℝ) ^ (2 : ℕ) := calc
    (n : ℝ) ^ (2 : ℕ) ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hnpos]
      have he : ε + (τ + ε) = 2 := by dsimp [ε]; ring
      rw [he]
      norm_num
  exact (lt_irrefl _ hstrict)

theorem rectangularAdmissibleExponent_bddBelow (F : Type*) [Field F] (k : ℝ) :
    BddBelow {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2, fun _ h => rectangularAdmissibleExponent_two_le h⟩

theorem rectangularOmega_le_of_admissibleExponent {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : rectangularOmega F k ≤ τ :=
  csInf_le (rectangularAdmissibleExponent_bddBelow F k) hτ

theorem admissibleExponent_iff_rectangular_one (F : Type*) [Field F] (τ : ℝ) :
    AdmissibleExponent F τ ↔ RectangularAdmissibleExponent F 1 τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    rw [innerSize_one]
    exact hbound n hn
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hnBound := hbound n hn
    rw [innerSize_one] at hnBound
    exact hnBound

theorem admissibleExponent_two_le {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ :=
  rectangularAdmissibleExponent_two_le ((admissibleExponent_iff_rectangular_one F τ).mp hτ)

theorem admissibleExponent_bddBelow (F : Type*) [Field F] :
    BddBelow {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨2, fun _ h => admissibleExponent_two_le h⟩

theorem omega_le_of_admissibleExponent {F : Type*} [Field F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : omega F ≤ τ :=
  csInf_le (admissibleExponent_bddBelow F) hτ

@[simp] theorem rectangularOmega_one (F : Type*) [Field F] :
    rectangularOmega F 1 = omega F := by
  unfold rectangularOmega omega
  congr 1
  ext τ
  exact (admissibleExponent_iff_rectangular_one F τ).symm

end

variable {F : Type*} [Field F]

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

theorem sumFin_eval {n : ℕ} (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, eval]
  | succ n ih => simp [sumFin, eval, ih, Fin.sum_univ_succ]

theorem sumFin_cost {n : ℕ} (f : Fin n → Expression F Input) :
    (sumFin f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, cost]
  | succ n ih =>
    simp only [sumFin, cost, ih, Fin.sum_univ_succ]
    omega

end Expression

def naiveEntry {a b c : ℕ} (i : Fin a) (k : Fin c) : Expression F (MatrixInput a b c) :=
  Expression.sumFin fun j : Fin b =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

theorem naiveEntry_eval {a b c : ℕ} (i : Fin a) (k : Fin c)
    (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
    (naiveEntry i k).eval (matrixInputs A B) = ∑ j, A i j * B j k := by
  simp [naiveEntry, Expression.sumFin_eval, Expression.eval, matrixInputs]

@[simp] theorem naiveEntry_cost {a b c : ℕ} (i : Fin a) (k : Fin c) :
    (naiveEntry (F := F) (b := b) i k).cost = 2 * b := by
  simp [naiveEntry, Expression.sumFin_cost, Expression.cost, two_mul]

def naiveAlgorithm (a b c : ℕ) : MatrixAlgorithm F a b c :=
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (b := b) ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

theorem naiveAlgorithm_correct (a b c : ℕ) : (naiveAlgorithm (F := F) a b c).Correct := by
  apply (MatrixAlgorithm.correct_iff_entries _).2
  intro A B i k
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.eval (matrixInputs A B) (p.output (i, k)) = _
  rw [p.correct]
  exact naiveEntry_eval i k A B

@[simp] theorem naiveAlgorithm_cost (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost = 2 * a * b * c := by
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (F := F) (b := b) ik.1 ik.2)
  change p.program.cost = _
  rw [p.cost_eq]
  simp only [naiveEntry_cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem naiveAlgorithm_cost_le (a b c : ℕ) :
    (naiveAlgorithm (F := F) a b c).cost ≤ 2 * a * b * c :=
  (naiveAlgorithm_cost a b c).le

theorem admissibleExponent_three : AdmissibleExponent F 3 := by
  intro ε hε
  refine ⟨2, by norm_num, ?_⟩
  intro n hn
  refine ⟨naiveAlgorithm n n n, naiveAlgorithm_correct n n n, ?_⟩
  rw [naiveAlgorithm_cost]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (le_add_of_nonneg_right hε.le)
  calc
    ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℝ) := by
      calc
        ((2 * n * n * n : ℕ) : ℝ) = 2 * (n : ℝ) ^ (3 : ℕ) := by
          push_cast
          ring
        _ = 2 * (n : ℝ) ^ (3 : ℝ) :=
          congrArg (fun t : ℝ => 2 * t) (Real.rpow_natCast (n : ℝ) 3).symm
    _ ≤ 2 * (n : ℝ) ^ (3 + ε) := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem admissibleExponent_nonempty : Set.Nonempty {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨3, admissibleExponent_three⟩

end MatrixMultiplication.Arithmetic

end

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem AdmissibleExponent.mono {τ σ : ℝ} (hτ : AdmissibleExponent F τ)
    (hτσ : τ ≤ σ) : AdmissibleExponent F σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add hτσ le_rfl)

theorem omega_two_le : 2 ≤ omega F :=
  le_csInf admissibleExponent_nonempty (fun _ hτ => admissibleExponent_two_le hτ)

theorem omega_nonneg : 0 ≤ omega F := le_trans (by norm_num) omega_two_le

theorem omega_le_three : omega F ≤ 3 :=
  omega_le_of_admissibleExponent admissibleExponent_three

theorem omega_admissibleExponent : AdmissibleExponent F (omega F) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt admissibleExponent_nonempty
    (show sInf {σ : ℝ | AdmissibleExponent F σ} < omega F + ε / 2 from
      lt_add_of_pos_right (omega F) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem admissibleExponent_iff_omega_le {τ : ℝ} :
    AdmissibleExponent F τ ↔ omega F ≤ τ :=
  ⟨omega_le_of_admissibleExponent, omega_admissibleExponent.mono⟩

theorem RectangularAdmissibleExponent.mono {k τ σ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) (hτσ : τ ≤ σ) :
    RectangularAdmissibleExponent F k σ := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (add_le_add hτσ le_rfl)

theorem rectangularAdmissibleExponent_of_uniform_costs {k τ C : ℝ} (hC : 0 < C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    (le_add_of_nonneg_right hε.le)

theorem rectangularAdmissibleExponent_naive (k : ℝ) :
    RectangularAdmissibleExponent F k (2 + max k 0) := by
  apply rectangularAdmissibleExponent_of_uniform_costs (C := 4) (by norm_num)
  intro n hn
  refine ⟨naiveAlgorithm n (innerSize n k) n,
    naiveAlgorithm_correct n (innerSize n k) n, ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hinner : (innerSize n k : ℝ) ≤ 2 * (n : ℝ) ^ max k 0 :=
    (Nat.cast_le.mpr (innerSize_mono hn (le_max_left k 0))).trans
      (innerSize_cast_le hn (le_max_right k 0))
  rw [naiveAlgorithm_cost]
  push_cast
  calc
    2 * (n : ℝ) * innerSize n k * n = 2 * (n : ℝ) ^ 2 * innerSize n k := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * (2 * (n : ℝ) ^ max k 0) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * (n : ℝ) ^ (2 + max k 0) := by
      rw [Real.rpow_add hnpos]
      norm_num
      ring

theorem rectangularAdmissibleExponent_nonempty (k : ℝ) :
    Set.Nonempty {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2 + max k 0, rectangularAdmissibleExponent_naive k⟩

theorem rectangularOmega_two_le (k : ℝ) : 2 ≤ rectangularOmega F k :=
  le_csInf (rectangularAdmissibleExponent_nonempty k)
    (fun _ hτ => rectangularAdmissibleExponent_two_le hτ)

theorem rectangularOmega_admissibleExponent (k : ℝ) :
    RectangularAdmissibleExponent F k (rectangularOmega F k) := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨τ, hτ, hclose⟩ := exists_lt_of_csInf_lt (rectangularAdmissibleExponent_nonempty k)
    (show sInf {σ : ℝ | RectangularAdmissibleExponent F k σ} <
        rectangularOmega F k + ε / 2 from lt_add_of_pos_right (rectangularOmega F k) hhalf)
  obtain ⟨C, hC, hbound⟩ := hτ (ε / 2) hhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨P, hP, hcost⟩ := hbound n hn
  refine ⟨P, hP, hcost.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

theorem rectangularAdmissibleExponent_iff_omega_le {k τ : ℝ} :
    RectangularAdmissibleExponent F k τ ↔ rectangularOmega F k ≤ τ :=
  ⟨rectangularOmega_le_of_admissibleExponent, (rectangularOmega_admissibleExponent k).mono⟩

theorem rectangularOmega_mono {k l : ℝ} (hkl : k ≤ l) :
    rectangularOmega F k ≤ rectangularOmega F l :=
  rectangularOmega_le_of_admissibleExponent
    ((rectangularOmega_admissibleExponent l).mono_aspect hkl)

@[simp] theorem rectangularOmega_zero : rectangularOmega F 0 = 2 := by
  apply le_antisymm _ (rectangularOmega_two_le 0)
  apply rectangularOmega_le_of_admissibleExponent
  simpa using (rectangularAdmissibleExponent_naive (F := F) 0)

theorem complexAlpha_set_nonempty :
    Set.Nonempty {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨0, ⟨by norm_num, by norm_num⟩, rectangularOmega_zero⟩

theorem complexAlpha_set_bddAbove :
    BddAbove {k : ℝ | k ∈ Set.Icc 0 1 ∧ rectangularOmega ℂ k = 2} :=
  ⟨1, fun _ h => h.1.2⟩

theorem le_complexAlpha {k : ℝ} (hk : k ∈ Set.Icc 0 1)
    (hω : rectangularOmega ℂ k = 2) : k ≤ complexAlpha :=
  le_csSup complexAlpha_set_bddAbove ⟨hk, hω⟩

theorem complexAlpha_le_one : complexAlpha ≤ 1 :=
  csSup_le complexAlpha_set_nonempty (fun _ h => h.1.2)

theorem complexAlpha_nonneg : 0 ≤ complexAlpha :=
  le_complexAlpha ⟨le_refl 0, by norm_num⟩ rectangularOmega_zero

end MatrixMultiplication.Arithmetic

end

end MatrixAllFields

end OAI
