import OAI.Analysis.Steinitz.Energy

namespace OAI

/-! Symmetric contraction updates and filtered matrix states. -/

namespace EuclideanSteinitz.Filter
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

structure Step (ι κ : Type*) where
  C : Matrix ι ι ℝ
  b : ι → ℝ
  j : κ

noncomputable def insert (b : ι → ℝ) (j : κ) : Matrix ι κ ℝ :=
  fun i k => if k = j then b i else 0

noncomputable def Step.apply (p : Step ι κ) (R : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  p.C * R + insert p.b p.j

noncomputable def Step.move (p : Step ι κ) (q : κ → ℝ) : Move ι :=
  ⟨p.C, q p.j • vecMulVec p.b p.b⟩

def Step.Good (p : Step ι κ) : Prop :=
  IsUnit p.C ∧ p.C * p.C.transpose + vecMulVec p.b p.b = 1

noncomputable def run (R : Matrix ι κ ℝ) : List (Step ι κ) → Matrix ι κ ℝ
  | [] => R
  | p :: ps => run (p.apply R) ps

noncomputable def product : List (Step ι κ) → Matrix ι ι ℝ
  | [] => 1
  | p :: ps => product ps * p.C

noncomputable def state (q : κ → ℝ) (R : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  R * diagonal q * R.transpose

def Fresh (R : Matrix ι κ ℝ) (ps : List (Step ι κ)) : Prop :=
  ∀ p ∈ ps, ∀ i, R i p.j = 0

omit [Fintype ι] [DecidableEq ι] in
lemma insert_mul_transpose (b : ι → ℝ) (j : κ) :
    insert b j * (insert b j).transpose = vecMulVec b b := by
  ext i k
  simp [Matrix.mul_apply, insert, Matrix.transpose_apply, vecMulVec_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma mul_insert_transpose (R : Matrix ι κ ℝ) (b : ι → ℝ) (j : κ) :
    R * (insert b j).transpose = vecMulVec (fun i => R i j) b := by
  ext i k
  simp [Matrix.mul_apply, insert, Matrix.transpose_apply, vecMulVec_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma insert_mul_transpose_zero (R : Matrix ι κ ℝ) (b : ι → ℝ) (j : κ)
    (hR : ∀ i, R i j = 0) : insert b j * R.transpose = 0 := by
  apply Matrix.transpose_injective
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    mul_insert_transpose]
  ext i k
  simp only [vecMulVec_apply, hR, zero_mul, Matrix.zero_apply]

omit [Fintype κ] [DecidableEq ι] in
lemma step_apply_column (p : Step ι κ) (R : Matrix ι κ ℝ) {j : κ}
    (hj : j ≠ p.j) (hR : ∀ i, R i j = 0) : ∀ i, p.apply R i j = 0 := by
  intro i
  simp [Step.apply, Matrix.mul_apply, insert, hj, hR]

lemma Step.coisometry {p : Step ι κ} (hp : p.Good) {R : Matrix ι κ ℝ}
    (hR : R * R.transpose = 1) (hf : ∀ i, R i p.j = 0) :
    p.apply R * (p.apply R).transpose = 1 := by
  have hz : R * (insert p.b p.j).transpose = 0 := by
    rw [mul_insert_transpose]
    ext i k
    simp [vecMulVec_apply, hf]
  have hz' := insert_mul_transpose_zero R p.b p.j hf
  have h₁ : p.C * R * (p.C * R).transpose = p.C * p.C.transpose := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc p.C R, ← Matrix.mul_assoc R, hR, Matrix.one_mul]
  have h₂ : p.C * R * (insert p.b p.j).transpose = 0 := by
    rw [Matrix.mul_assoc, hz, Matrix.mul_zero]
  have h₃ : insert p.b p.j * (p.C * R).transpose = 0 := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hz', Matrix.zero_mul]
  simpa only [Step.apply, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    h₁, h₂, h₃, insert_mul_transpose, add_zero, zero_add] using hp.2

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
lemma rankOne_psd (b : ι → ℝ) : (vecMulVec b b).PosSemidef := by
  have h := Matrix.PosSemidef.one.mul_mul_conjTranspose_same (insert (κ := Unit) b ())
  simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_one, insert_mul_transpose] using h

omit [Fintype κ] [DecidableEq κ] in
lemma Step.contract {p : Step ι κ} (hp : p.Good) : p.C * p.C.transpose ≤ 1 := by
  rw [← hp.2]
  exact le_add_of_nonneg_right (rankOne_psd p.b).nonneg

omit [Fintype κ] [DecidableEq κ] in
lemma Step.admissible {p : Step ι κ} (hp : p.Good) {q : κ → ℝ} (hq : ∀ j, 0 ≤ q j) :
    (p.move q).Admissible :=
  ⟨Step.contract hp, (rankOne_psd p.b).smul (hq p.j)⟩

omit [Fintype κ] [DecidableEq ι] in
lemma Step.fresh_tail {p : Step ι κ} {ps : List (Step ι κ)} {R : Matrix ι κ ℝ}
    (hf : Fresh R (p :: ps)) (hd : ∀ r ∈ ps, p.j ≠ r.j) : Fresh (p.apply R) ps := by
  intro r hr
  exact step_apply_column p R (Ne.symm (hd r hr)) (hf r (List.mem_cons_of_mem p hr))

lemma run_coisometry {R : Matrix ι κ ℝ} (hR : R * R.transpose = 1)
    {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) (hf : Fresh R ps)
    (hd : (ps.map Step.j).Nodup) : run R ps * (run R ps).transpose = 1 := by
  induction ps generalizing R with
  | nil => exact hR
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    have htail : ∀ r ∈ ps, p.j ≠ r.j := by
      intro r hr he
      apply hd'.1
      exact List.mem_map.mpr ⟨r, hr, he.symm⟩
    exact ih (Step.coisometry (hp p (List.mem_cons_self ..)) hR (hf p (List.mem_cons_self ..)))
      (fun r hr => hp r (List.mem_cons_of_mem p hr)) (Step.fresh_tail hf htail) hd'.2

omit [Fintype κ] [DecidableEq κ] in
lemma product_contract {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) :
    product ps * (product ps).transpose ≤ 1 := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    have hp₀ := Step.contract (hp p (List.mem_cons_self ..))
    have hps := ih (fun r hr => hp r (List.mem_cons_of_mem p hr))
    have hh := Gain.congruence_mono hp₀ (product ps)
    simp only [Matrix.mul_one] at hh
    have he : product (p :: ps) * (product (p :: ps)).transpose ≤
        product ps * (product ps).transpose := by
      simpa only [product, Matrix.transpose_mul, Matrix.mul_assoc] using hh
    exact he.trans hps

omit [Fintype κ] [DecidableEq κ] in
lemma product_unit {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) : IsUnit (product ps) := by
  induction ps with
  | nil => exact isUnit_one
  | cons p ps ih =>
    exact (ih (fun r hr => hp r (List.mem_cons_of_mem p hr))).mul (hp p (List.mem_cons_self ..)).1

lemma state_posDef {R : Matrix ι κ ℝ} (hR : R * R.transpose = 1)
    {q : κ → ℝ} (hq : ∀ j, 0 < q j) : (state q R).PosDef := by
  have hi : Function.Injective R.vecMul := by
    intro x y hxy
    have hh := congrArg (fun v => R.transpose.vecMul v) hxy
    simpa only [Matrix.vecMul_vecMul, hR, Matrix.vecMul_one] using hh
  simpa only [state, conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosDef.diagonal hq).mul_mul_conjTranspose_same hi

omit [Fintype ι] [DecidableEq ι] in
lemma insert_diagonal (b : ι → ℝ) (j : κ) (q : κ → ℝ) :
    insert b j * diagonal q = q j • insert b j := by
  ext i k
  simp only [Matrix.mul_diagonal, insert, Matrix.smul_apply, smul_eq_mul]
  by_cases h : k = j
  · simp [h, mul_comm]
  · simp [h]

omit [DecidableEq ι] in
lemma Step.state_next {R : Matrix ι κ ℝ} (p : Step ι κ) (q : κ → ℝ)
    (hf : ∀ i, R i p.j = 0) : state q (p.apply R) = (p.move q).next (state q R) := by
  have hz : R * diagonal q * (insert p.b p.j).transpose = 0 := by
    rw [mul_insert_transpose]
    ext i k
    simp [vecMulVec_apply, Matrix.mul_diagonal, hf]
  have hz' : insert p.b p.j * diagonal q * R.transpose = 0 := by
    rw [insert_diagonal, Matrix.smul_mul, insert_mul_transpose_zero R p.b p.j hf, smul_zero]
  have h₁ : p.C * R * diagonal q * (p.C * R).transpose =
      p.C * state q R * p.C.transpose := by
    simp only [state, Matrix.transpose_mul, Matrix.mul_assoc]
  have h₂ : p.C * R * diagonal q * (insert p.b p.j).transpose = 0 := by
    simpa only [Matrix.mul_assoc, Matrix.mul_zero] using congrArg (fun M => p.C * M) hz
  have h₃ : insert p.b p.j * diagonal q * (p.C * R).transpose = 0 := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hz', Matrix.zero_mul]
  have h₄ : insert p.b p.j * diagonal q * (insert p.b p.j).transpose =
      q p.j • vecMulVec p.b p.b := by
    rw [insert_diagonal, Matrix.smul_mul, insert_mul_transpose]
  simp only [state, Step.apply, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
    h₁, h₂, h₃, h₄, add_zero, zero_add]
  rfl

omit [DecidableEq ι] in
lemma run_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (q : κ → ℝ)
    (hf : Fresh R ps) (hd : (ps.map Step.j).Nodup) :
    state q (run R ps) = finish (state q R) (ps.map (fun p => p.move q)) := by
  induction ps generalizing R with
  | nil => rfl
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    have htail : ∀ r ∈ ps, p.j ≠ r.j := by
      intro r hr he
      exact hd'.1 (List.mem_map.mpr ⟨r, hr, he.symm⟩)
    simp only [run, List.map_cons, finish]
    rw [ih (Step.fresh_tail hf htail) hd'.2,
      Step.state_next p q (hf p (List.mem_cons_self ..))]

omit [Fintype κ] [DecidableEq κ] in
lemma follow_old (Z V : Matrix ι ι ℝ) (ps : List (Step ι κ)) (q : κ → ℝ) :
    (follow Z V (ps.map (fun p => p.move q))).1 = product ps * Z * (product ps).transpose := by
  induction ps generalizing Z V with
  | nil => simp [follow, product]
  | cons p ps ih =>
    change (follow ((p.move q).old Z) ((p.move q).next V)
      (ps.map (fun p => p.move q))).1 = _
    rw [ih]
    simp only [product, Step.move, Move.old, Matrix.transpose_mul, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
lemma insert_mul_zero {μ : Type*} (b : ι → ℝ) (j : κ) (B : Matrix κ μ ℝ)
    (hz : ∀ l, B j l = 0) : insert b j * B = 0 := by
  ext i l
  simp [Matrix.mul_apply, insert, hz]

lemma run_mul {μ : Type*} (R : Matrix ι κ ℝ) (ps : List (Step ι κ)) (B : Matrix κ μ ℝ)
    (hz : ∀ p ∈ ps, ∀ l, B p.j l = 0) : run R ps * B = product ps * R * B := by
  induction ps generalizing R with
  | nil => simp [run, product]
  | cons p ps ih =>
    simp only [run]
    rw [ih _ (fun r hr => hz r (List.mem_cons_of_mem p hr))]
    simp only [Step.apply, product, Matrix.mul_add, Matrix.add_mul]
    rw [Matrix.mul_assoc (product ps) (insert p.b p.j),
      insert_mul_zero _ _ _ (hz p (List.mem_cons_self ..)), Matrix.mul_zero, add_zero]
    simp only [Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def newSet (ps : List (Step ι κ)) : Finset κ := (ps.map Step.j).toFinset

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
lemma mem_newSet {p : Step ι κ} {ps : List (Step ι κ)} (hp : p ∈ ps) : p.j ∈ newSet ps := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)

noncomputable def oldMask (J : Finset κ) : Matrix κ κ ℝ := diagonal (fun j => if j ∈ J then 0 else 1)
noncomputable def oldQ (J : Finset κ) (q : κ → ℝ) : Matrix κ κ ℝ :=
  diagonal (fun j => if j ∈ J then 0 else q j)
noncomputable def newQ (J : Finset κ) (q : κ → ℝ) : Matrix κ κ ℝ :=
  diagonal (fun j => if j ∈ J then q j else 0)

lemma oldQ_eq (J : Finset κ) (q : κ → ℝ) :
    oldQ J q = oldMask J * diagonal q * (oldMask J).transpose := by
  simp only [oldQ, oldMask, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split <;> simp_all

omit [Fintype κ] in
lemma oldQ_add_newQ (J : Finset κ) (q : κ → ℝ) : oldQ J q + newQ J q = diagonal q := by
  rw [oldQ, newQ, Matrix.diagonal_add]
  congr 1
  funext j
  split <;> simp_all

omit [Fintype κ] in
lemma oldQ_psd (J : Finset κ) {q : κ → ℝ} (hq : ∀ j, 0 ≤ q j) : (oldQ J q).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp only
  split <;> simp_all

omit [Fintype κ] in
lemma newQ_psd (J : Finset κ) {q : κ → ℝ} (hq : ∀ j, 0 ≤ q j) : (newQ J q).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp only
  split <;> simp_all

omit [Fintype ι] [DecidableEq ι] in
lemma oldQ_sandwich (A B : Matrix ι κ ℝ) (J : Finset κ) (q : κ → ℝ) :
    A * oldQ J q * B.transpose =
      (A * oldMask J) * diagonal q * (B * oldMask J).transpose := by
  rw [oldQ_eq, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_oldMask {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps) :
    R * oldMask (newSet ps) = R := by
  ext i j
  simp only [oldMask, Matrix.mul_diagonal]
  by_cases hj : j ∈ newSet ps
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    simp only [ite_eq_left hj, mul_zero, hf p hp i]
  · simp [hj]

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_newQ {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps) (q : κ → ℝ) :
    R * newQ (newSet ps) q = 0 := by
  ext i j
  simp only [newQ, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hj : j ∈ newSet ps
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    simp only [ite_eq_left hj, hf p hp i, zero_mul]
  · simp [hj]

lemma run_oldMask {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps) :
    run R ps * oldMask (newSet ps) = product ps * R := by
  rw [run_mul]
  · rw [Matrix.mul_assoc, fresh_oldMask hf]
  · intro p hp l
    simp only [oldMask, Matrix.diagonal_apply]
    by_cases h : p.j = l
    · subst l
      simp [mem_newSet hp]
    · simp [h]

lemma run_cross {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps)
    (hR : R * R.transpose = 1) : run R ps * R.transpose = product ps := by
  rw [run_mul R ps R.transpose (fun p hp l => hf p hp l), Matrix.mul_assoc, hR, Matrix.mul_one]

omit [Fintype ι] [DecidableEq ι] in
lemma old_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    R * oldQ (newSet ps) q * R.transpose = state q R := by
  rw [oldQ_sandwich, fresh_oldMask hf]
  rfl

lemma run_old_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    run R ps * oldQ (newSet ps) q * (run R ps).transpose =
      product ps * state q R * (product ps).transpose := by
  rw [oldQ_sandwich, run_oldMask hf]
  simp only [state, Matrix.transpose_mul, Matrix.mul_assoc]

lemma run_old_cross {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    run R ps * oldQ (newSet ps) q * R.transpose = product ps * state q R := by
  rw [oldQ_sandwich, run_oldMask hf, fresh_oldMask hf]
  simp only [state, Matrix.mul_assoc]

lemma run_new_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    run R ps * newQ (newSet ps) q * (run R ps).transpose =
      state q (run R ps) - product ps * state q R * (product ps).transpose := by
  have he : run R ps * oldQ (newSet ps) q * (run R ps).transpose +
      run R ps * newQ (newSet ps) q * (run R ps).transpose = state q (run R ps) := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, oldQ_add_newQ]
    rfl
  rw [run_old_state hf] at he
  exact eq_sub_of_add_eq' he

omit [DecidableEq ι] in
lemma fresh_lift_new_zero {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) (A : Matrix ι ι ℝ) :
    Coefficient.lift R A * newQ (newSet ps) q = 0 := by
  rw [Coefficient.lift, Matrix.mul_assoc, fresh_newQ hf q, Matrix.mul_zero]

lemma weighted_increment {R : Matrix ι κ ℝ} (hR : R * R.transpose = 1)
    {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) (hf : Fresh R ps)
    (hd : (ps.map Step.j).Nodup) {q : κ → ℝ} (hq : ∀ j, 0 < q j)
    {E : ℝ} (hCost : cost (state q R) (ps.map (fun p => p.move q)) ≤ E)
    (hSmall : E ≤ 1 / (16 * gainConstant)) :
    Coefficient.weightedSq
      (Coefficient.lift (run R ps) (cfc cutoff (state q (run R ps))) -
        Coefficient.lift R (cfc cutoff (state q R))) (1 + diagonal q) ≤
      incrementConstant * (1 + (cfc sizeWeight (state q (run R ps))).trace) *
        E ^ (1 / exponent) := by
  have hT := run_coisometry hR hp hf hd
  have hY := state_posDef hR hq
  have hX := state_posDef hT hq
  have hC := product_unit hp
  have hZ : (product ps * state q R * (product ps).transpose).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hY.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hC)
  have hMoves : ∀ p ∈ ps.map (fun p => p.move q), p.Admissible := by
    intro p hp'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp'
    exact Step.admissible (hp r hr) (fun j => (hq j).le)
  have he := Coefficient.weighted_increment hX hY hZ hC (product_contract hp) rfl
    (run R ps) R hT hR (oldQ (newSet ps) q) (newQ (newSet ps) q)
    (oldQ_psd _ (fun j => (hq j).le)) (newQ_psd _ (fun j => (hq j).le))
    (old_state hf q) (run_old_state hf q) (run_cross hf hR) (run_old_cross hf q)
    (run_new_state hf q) (fresh_lift_new_zero hf q _) _ hMoves
    (run_state q hf hd) (follow_old _ _ _ _).symm hCost hSmall
  simpa only [add_assoc, oldQ_add_newQ] using he

end EuclideanSteinitz.Filter

end OAI
