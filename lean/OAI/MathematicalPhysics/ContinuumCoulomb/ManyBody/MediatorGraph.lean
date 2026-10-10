import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorParameters
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! Explicit ordinary-spin coordinates for a simultaneous mediator stage.
The new sites are the two actual members of every fresh pair. -/

noncomputable section
namespace ContinuumCoulomb.MediatorGraph
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem submatrix_sum {ι κ α β γ : Type*} [Fintype γ]
    (M : γ → Matrix ι κ ℂ) (f : α → ι) (g : β → κ) :
    (∑ e, M e).submatrix f g = ∑ e, (M e).submatrix f g := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]

theorem submatrix_add_apply {ι κ α β : Type*} (M N : Matrix ι κ ℂ) (f : α → ι) (g : β → κ) :
    (M + N).submatrix f g = M.submatrix f g + N.submatrix f g := rfl

theorem submatrix_smul_apply {ι κ α β : Type*} (c : ℂ) (M : Matrix ι κ ℂ)
    (f : α → ι) (g : β → κ) : (c • M).submatrix f g = c • M.submatrix f g := rfl

theorem sum_kronecker {ι κ α β γ : Type*} [Fintype γ]
    (M : γ → Matrix ι κ ℂ) (N : Matrix α β ℂ) :
    (∑ e, M e) ⊗ₖ N = ∑ e, M e ⊗ₖ N := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

theorem kronecker_sum {ι κ α β γ : Type*} [Fintype γ]
    (M : Matrix ι κ ℂ) (N : γ → Matrix α β ℂ) :
    M ⊗ₖ (∑ e, N e) = ∑ e, M ⊗ₖ N e := by
  ext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

def vertexEquiv (n r : ℕ) : Fin n ⊕ (Fin r × Fin 2) ≃ Fin (n + r * 2) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def old (n r : ℕ) (i : Fin n) : Fin (n + r * 2) := vertexEquiv n r (Sum.inl i)

def fresh (n r : ℕ) (e : Fin r) (member : Fin 2) : Fin (n + r * 2) :=
  vertexEquiv n r (Sum.inr (e, member))

def pairEquiv : (Fin 2 → Fin 2) ≃ Fin 4 :=
  (finTwoArrowEquiv (Fin 2)).trans finProdFinEquiv

def basisEquiv (n r : ℕ) : MediatedSpinBasis n r ≃ SourceSpinBasis (n + r * 2) where
  toFun p k := Sum.elim p.1 (fun a => pairEquiv.symm (p.2 a.1) a.2)
    ((vertexEquiv n r).symm k)
  invFun s := (fun i => s (old n r i),
    fun e => pairEquiv (fun member => s (fresh n r e member)))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp [old]
    · funext e
      simp [fresh]
  right_inv s := by
    funext k
    obtain ⟨i, rfl⟩ := (vertexEquiv n r).surjective k
    cases i with
    | inl i => simp [old]
    | inr a => simp [fresh]

@[simp] theorem basisEquiv_old (n r : ℕ) (p : MediatedSpinBasis n r) (i : Fin n) :
    basisEquiv n r p (old n r i) = p.1 i := by
  simp [basisEquiv, old]

@[simp] theorem basisEquiv_fresh (n r : ℕ) (p : MediatedSpinBasis n r)
    (e : Fin r) (member : Fin 2) :
    basisEquiv n r p (fresh n r e member) = pairEquiv.symm (p.2 e) member := by
  simp [basisEquiv, fresh]

theorem old_ne_fresh (n r : ℕ) (i : Fin n) (e : Fin r) (member : Fin 2) :
    old n r i ≠ fresh n r e member := by
  intro h
  have := (vertexEquiv n r).injective h
  cases this

theorem fresh_injective (n r : ℕ) : Function.Injective (fun a : Fin r × Fin 2 =>
    fresh n r a.1 a.2) := by
  intro a b h
  exact Sum.inr.inj ((vertexEquiv n r).injective h)

theorem old_injective (n r : ℕ) : Function.Injective (old n r) := by
  intro a b h
  exact Sum.inl.inj ((vertexEquiv n r).injective h)

theorem pairTensor_entry (A B : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 4) :
    twoSpinTensor A B a b =
      A (pairEquiv.symm a 0) (pairEquiv.symm b 0) *
        B (pairEquiv.symm a 1) (pairEquiv.symm b 1) := by
  fin_cases a <;> fin_cases b <;> rfl

def joinedMatrices (n r : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (B : Fin r → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin (n + r * 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  Sum.elim A (fun a => B a.1 a.2) ((vertexEquiv n r).symm k)

/-- Splitting the ordinary spin tensor into old spins and actual two-spin
mediator pairs is an exact basis permutation. -/
theorem sourceTensor_joined (n r : ℕ) (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (B : Fin r → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) :
    (sourceTensor (n + r * 2) (joinedMatrices n r A B)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        sourceTensor n A ⊗ₖ mediatorTensor r (fun e => twoSpinTensor (B e 0) (B e 1)) := by
  ext p q
  change (∏ k, joinedMatrices n r A B k (basisEquiv n r p k) (basisEquiv n r q k)) = _
  rw [← (vertexEquiv n r).prod_comp]
  simp only [joinedMatrices, Equiv.symm_apply_apply]
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Sum.elim_inl, Sum.elim_inr, basisEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  change (∏ i, A i (p.1 i) (q.1 i)) *
      (∏ e, ∏ σ, B e σ (pairEquiv.symm (p.2 e) σ) (pairEquiv.symm (q.2 e) σ)) =
    (∏ i, A i (p.1 i) (q.1 i)) * (∏ e, twoSpinTensor (B e 0) (B e 1) (p.2 e) (q.2 e))
  simp only [Fin.prod_univ_two, pairTensor_entry]

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def normalizedBottom (H : Matrix ι ι ℂ) : ℝ :=
  sInf {e | ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ e = ⟪x, spinMatrixOperator H x⟫_ℝ}

theorem reindex_operator_apply (e : ι ≃ κ) (H : Matrix κ κ ℂ) (x : EuclideanSpace ℂ ι) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (spinMatrixOperator (H.submatrix e e) x) =
      spinMatrixOperator H (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x) := by
  ext k
  change (∑ j, H (e (e.symm k)) (e j) * x j) = ∑ j, H k j * x (e.symm j)
  simp only [Equiv.apply_symm_apply]
  simpa only [Equiv.symm_apply_apply] using
    e.sum_comp (fun j => H k j * x (e.symm j))

theorem reindex_form (e : ι ≃ κ) (H : Matrix κ κ ℂ) (x : EuclideanSpace ℂ ι) :
    ⟪x, spinMatrixOperator (H.submatrix e e) x⟫_ℝ =
      ⟪LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x,
        spinMatrixOperator H (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x)⟫_ℝ := by
  rw [← reindex_operator_apply]
  rw [HubbardGlobal.euclidean_real_inner, HubbardGlobal.euclidean_real_inner]
  exact congrArg Complex.re
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).inner_map_map x
      (spinMatrixOperator (H.submatrix e e) x)).symm

theorem normalizedBottom_reindex (e : ι ≃ κ) (H : Matrix κ κ ℂ) :
    normalizedBottom (H.submatrix e e) = normalizedBottom H := by
  unfold normalizedBottom
  congr 1
  ext a
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨U x, (U.norm_map x).trans hx, reindex_form e H x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U.symm x, (U.symm.norm_map x).trans hx, ?_⟩
    rw [reindex_form]
    change ⟪x, spinMatrixOperator H x⟫_ℝ = ⟪U (U.symm x), spinMatrixOperator H (U (U.symm x))⟫_ℝ
    rw [U.apply_symm_apply]

theorem reindex_operator_norm (e : ι ≃ κ) (H : Matrix κ κ ℂ) :
    ‖spinMatrixOperator (H.submatrix e e)‖ = ‖spinMatrixOperator H‖ := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (spinMatrixOperator H).le_opNorm (U x)
    rw [← reindex_operator_apply] at h
    change ‖U (spinMatrixOperator (H.submatrix e e) x)‖ ≤ ‖spinMatrixOperator H‖ * ‖U x‖ at h
    rw [U.norm_map, U.norm_map] at h
    exact h
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (spinMatrixOperator (H.submatrix e e)).le_opNorm (U.symm x)
    have hn : ‖spinMatrixOperator (H.submatrix e e) (U.symm x)‖ =
        ‖spinMatrixOperator H x‖ := by
      rw [← U.norm_map (spinMatrixOperator (H.submatrix e e) (U.symm x))]
      rw [reindex_operator_apply]
      change ‖spinMatrixOperator H (U (U.symm x))‖ = _
      rw [U.apply_symm_apply]
    rw [hn, U.symm.norm_map] at h
    exact h

theorem matrixForm_smul (H : Matrix ι ι ℂ) (a : ℝ) (x : EuclideanSpace ℂ ι) :
    ⟪a • x, spinMatrixOperator H (a • x)⟫_ℝ = a ^ 2 * ⟪x, spinMatrixOperator H x⟫_ℝ := by
  change ⟪a • x, (spinMatrixOperator H).restrictScalars ℝ (a • x)⟫_ℝ = _
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  change a * (a * ⟪x, spinMatrixOperator H x⟫_ℝ) = _
  ring

theorem normalizedBottom_eq_rayleigh (H : Matrix ι ι ℂ) :
    normalizedBottom H = sInf {e | ∃ x : EuclideanSpace ℂ ι,
      0 < ‖x‖ ^ 2 ∧ e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2} := by
  unfold normalizedBottom
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by rw [hx]; norm_num, by rw [hx]; simp⟩
  · rintro ⟨x, hx, rfl⟩
    have hnx : ‖x‖ ≠ 0 := by intro h; simp [h] at hx
    refine ⟨(‖x‖⁻¹ : ℝ) • x, norm_smul_inv_norm (norm_ne_zero_iff.mp hnx), ?_⟩
    rw [matrixForm_smul]
    field_simp

end Reindex

theorem sourceMatrixBottom_eq_mediator (n r : ℕ)
    (H : Matrix (SourceSpinBasis (n + r * 2)) (SourceSpinBasis (n + r * 2)) ℂ) :
    sourceMatrixBottom (n + r * 2) H =
      mediatorFullBottom n r (H.submatrix (basisEquiv n r) (basisEquiv n r)) := by
  change normalizedBottom H = _
  rw [← normalizedBottom_reindex (basisEquiv n r) H, normalizedBottom_eq_rayleigh]
  rfl

theorem twoSpinTensor_one : twoSpinTensor (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [twoSpinTensor, Matrix.one_apply]

theorem localPauli_old (n r : ℕ) (i : Fin n) (μ : Fin 3) :
    (sourceLocalPauli (n + r * 2) (old n r i) μ).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        sourceLocalPauli n i μ ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  have hfun : (fun k => if k = old n r i then pauli μ else 1) =
      joinedMatrices n r (fun j => if j = i then pauli μ else 1) (fun _ _ => 1) := by
    funext k
    obtain ⟨a, rfl⟩ := (vertexEquiv n r).surjective k
    cases a with
    | inl j => simp [old, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
    | inr a => simp [old, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
  unfold sourceLocalPauli
  rw [hfun, sourceTensor_joined]
  simp only [twoSpinTensor_one, mediatorTensor_one]

theorem pairPauli (member : Fin 2) (μ : Fin 3) :
    twoSpinTensor (if (0 : Fin 2) = member then pauli μ else 1)
      (if (1 : Fin 2) = member then pauli μ else 1) = physicalMemberPauli member μ := by
  fin_cases member <;> simp [physicalMemberPauli, firstPauli, secondPauli]

theorem localPauli_fresh (n r : ℕ) (e : Fin r) (member : Fin 2) (μ : Fin 3) :
    (sourceLocalPauli (n + r * 2) (fresh n r e member) μ).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ
          mediatorLocal r e (physicalMemberPauli member μ) := by
  have hfun : (fun k => if k = fresh n r e member then pauli μ else 1) =
      joinedMatrices n r (fun _ => 1)
        (fun f σ => if f = e ∧ σ = member then pauli μ else 1) := by
    funext k
    obtain ⟨a, rfl⟩ := (vertexEquiv n r).surjective k
    cases a with
    | inl j => simp [fresh, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
    | inr a =>
      rcases a with ⟨f, σ⟩
      simp [fresh, joinedMatrices, (vertexEquiv n r).injective.eq_iff]
  unfold sourceLocalPauli
  rw [hfun, sourceTensor_joined, sourceTensor_one]
  congr 1
  unfold mediatorLocal
  congr 1
  funext f
  by_cases hf : f = e
  · simp only [hf, true_and, ite_true]
    exact pairPauli member μ
  · simp [hf, twoSpinTensor_one]

theorem heisenberg_old (n r : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (sourceHeisenbergMatrix (n + r * 2) (old n r i) (old n r j)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        sourceHeisenbergMatrix n i j ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  rw [← sourceLocalPauli_sum _ _ _ (fun h => hij (old_injective n r h))]
  simp only [submatrix_sum, ← Matrix.submatrix_mul_equiv _ _ _ (basisEquiv n r) _,
    localPauli_old, ← Matrix.mul_kronecker_mul, one_mul]
  rw [← sum_kronecker, sourceLocalPauli_sum n i j hij]

theorem heisenberg_spoke (n r : ℕ) (i : Fin n) (e : Fin r) (member : Fin 2) :
    (sourceHeisenbergMatrix (n + r * 2) (old n r i) (fresh n r e member)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        ∑ μ : Fin 3, sourceLocalPauli n i μ ⊗ₖ
          mediatorLocal r e (physicalMemberPauli member μ) := by
  rw [← sourceLocalPauli_sum _ _ _ (old_ne_fresh n r i e member)]
  simp only [submatrix_sum, ← Matrix.submatrix_mul_equiv _ _ _ (basisEquiv n r) _,
    localPauli_old, localPauli_fresh, ← Matrix.mul_kronecker_mul, mul_one, one_mul]

theorem heisenberg_central (n r : ℕ) (e : Fin r) :
    (sourceHeisenbergMatrix (n + r * 2) (fresh n r e 0) (fresh n r e 1)).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ
          mediatorLocal r e heisenberg := by
  have hne : fresh n r e 0 ≠ fresh n r e 1 := by
    intro h
    have := fresh_injective n r (a₁ := (e, 0)) (a₂ := (e, 1)) h
    have := congrArg Prod.snd this
    norm_num at this
  rw [← sourceLocalPauli_sum _ _ _ hne]
  simp only [submatrix_sum, ← Matrix.submatrix_mul_equiv _ _ _ (basisEquiv n r) _,
    localPauli_fresh, ← Matrix.mul_kronecker_mul, one_mul]
  simp only [physicalMemberPauli, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    mediatorLocal_mul_same]
  rw [← kronecker_sum]
  congr 1
  ext a b
  simp only [Matrix.sum_apply, mediatorLocal_apply, ← Finset.sum_mul]
  rw [← Matrix.sum_apply, sum_first_second_pauli]

abbrev EdgeIndex (q r : ℕ) := Fin q ⊕ (Fin r ⊕ (Fin r × Fin 2))

def edgeEquiv (q r : ℕ) : EdgeIndex q r ≃ Fin (q + (r + r * 2)) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv

def stageLeft (n q r : ℕ) (keepLeft : Fin q → Fin n) (left right : Fin r → Fin n)
    (a : Fin (q + (r + r * 2))) : Fin (n + r * 2) :=
  match (edgeEquiv q r).symm a with
  | .inl e => old n r (keepLeft e)
  | .inr (.inl e) => fresh n r e 0
  | .inr (.inr (e, side)) => old n r (if side = 0 then left e else right e)

def stageRight (n q r : ℕ) (keepRight : Fin q → Fin n) (member : Fin r → Fin 2)
    (a : Fin (q + (r + r * 2))) : Fin (n + r * 2) :=
  match (edgeEquiv q r).symm a with
  | .inl e => old n r (keepRight e)
  | .inr (.inl e) => fresh n r e 1
  | .inr (.inr (e, side)) => fresh n r e (if side = 0 then 0 else member e)

def stageWeight (q r : ℕ) (keepWeight : Fin q → ℚ) (Delta : ℚ) (amplitude : Fin r → ℚ)
    (a : Fin (q + (r + r * 2))) : ℚ :=
  match (edgeEquiv q r).symm a with
  | .inl e => keepWeight e
  | .inr (.inl _) => Delta
  | .inr (.inr (e, _)) => amplitude e

def stageMatrix (n q r : ℕ) (keepLeft keepRight : Fin q → Fin n) (keepWeight : Fin q → ℚ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (Delta : ℚ)
    (amplitude : Fin r → ℚ) :
    Matrix (SourceSpinBasis (n + r * 2)) (SourceSpinBasis (n + r * 2)) ℂ :=
  sourceGraphMatrix (n + r * 2) (q + (r + r * 2))
    (stageLeft n q r keepLeft left right) (stageRight n q r keepRight member)
    (fun a => (stageWeight q r keepWeight Delta amplitude a : ℝ))

theorem stage_no_loops (n q r : ℕ) (keepLeft keepRight : Fin q → Fin n)
    (hkeep : ∀ e, keepLeft e ≠ keepRight e) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) : ∀ a,
    stageLeft n q r keepLeft left right a ≠ stageRight n q r keepRight member a := by
  intro a
  obtain ⟨b, rfl⟩ := (edgeEquiv q r).surjective a
  cases b with
  | inl e =>
    simpa only [stageLeft, stageRight, Equiv.symm_apply_apply] using
      (fun h => hkeep e (old_injective n r h))
  | inr b =>
    cases b with
    | inl e =>
      simp only [stageLeft, stageRight, Equiv.symm_apply_apply]
      intro h
      have := congrArg Prod.snd (fresh_injective n r (a₁ := (e, 0)) (a₂ := (e, 1)) h)
      norm_num at this
    | inr b =>
      simp only [stageLeft, stageRight, Equiv.symm_apply_apply]
      exact old_ne_fresh n r _ _ _

theorem stage_positive (q r : ℕ) (keepWeight : Fin q → ℚ) (hkeep : ∀ e, 0 < keepWeight e)
    {Delta : ℚ} (hDelta : 0 < Delta) (amplitude : Fin r → ℚ) (ha : ∀ e, 0 < amplitude e) :
    ∀ a, 0 < stageWeight q r keepWeight Delta amplitude a := by
  intro a
  obtain ⟨b, rfl⟩ := (edgeEquiv q r).surjective a
  cases b with
  | inl e => simpa [stageWeight] using hkeep e
  | inr b =>
    cases b with
    | inl e => simpa [stageWeight] using hDelta
    | inr b => simpa [stageWeight] using ha b.1

/-- The emitted ordinary graph has exactly the physical central and
spoke matrices used in the proved simultaneous-mediator estimate. -/
theorem stageMatrix_physical (n q r : ℕ) (keepLeft keepRight : Fin q → Fin n)
    (hkeep : ∀ e, keepLeft e ≠ keepRight e) (keepWeight : Fin q → ℚ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (Delta : ℚ)
    (amplitude : Fin r → ℚ) :
    (stageMatrix n q r keepLeft keepRight keepWeight left right member Delta amplitude).submatrix
      (basisEquiv n r) (basisEquiv n r) =
        physicalRawMediatorHamiltonian n r (Delta : ℝ)
          (sourceGraphMatrix n q keepLeft keepRight (fun e => (keepWeight e : ℝ)))
          left right member (fun e => (amplitude e : ℝ)) := by
  unfold stageMatrix sourceGraphMatrix
  rw [← (edgeEquiv q r).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    stageLeft, stageRight, stageWeight, Equiv.symm_apply_apply, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false, submatrix_add_apply, submatrix_sum,
    submatrix_smul_apply, heisenberg_old n r _ _ (hkeep _), heisenberg_central,
    heisenberg_spoke]
  unfold physicalRawMediatorHamiltonian physicalTotalMediatorSpokes physicalMediatorEdgeSpoke
  simp only [sum_kronecker, kronecker_sum, Matrix.smul_kronecker,
    Matrix.kronecker_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  push_cast
  abel

theorem oldGraph_matrix (n q r : ℕ) (left right : Fin q → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin q → ℝ) :
    (sourceGraphMatrix (n + r * 2) q (fun e => old n r (left e))
      (fun e => old n r (right e)) J).submatrix (basisEquiv n r) (basisEquiv n r) =
        sourceGraphMatrix n q left right J ⊗ₖ
          (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) := by
  unfold sourceGraphMatrix
  simp only [submatrix_sum, submatrix_smul_apply, heisenberg_old n r _ _ (hneq _),
    Matrix.smul_kronecker, sum_kronecker]

theorem oldGraph_operator_norm (n q r : ℕ) (left right : Fin q → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin q → ℝ) :
    ‖spinMatrixOperator (sourceGraphMatrix n q left right J ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 3 * ∑ e, |J e| := by
  rw [← oldGraph_matrix n q r left right hneq J, reindex_operator_norm]
  exact sourceGraphMatrix_operator_norm _ q _ _
    (fun e h => hneq e (old_injective n r h)) J

theorem graph_star (n q : ℕ) (left right : Fin q → Fin n)
    (hneq : ∀ e, left e ≠ right e) (J : Fin q → ℝ) :
    (sourceGraphMatrix n q left right J).conjTranspose = sourceGraphMatrix n q left right J := by
  unfold sourceGraphMatrix
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, sourceHeisenbergMatrix_star n _ _ (hneq _)]

/-- One ordinary, fully enumerated positive graph stage, with explicit
scales and rational spoke outputs. The only bounds concern entering
weights, unreplaced weights and the entering inverse precision. -/
theorem stage_bottom (n q r : ℕ) {W G : ℕ} (hW : 0 < W) (hG : 0 < G)
    (keepLeft keepRight : Fin q → Fin n) (hkeep : ∀ e, keepLeft e ≠ keepRight e)
    (keepWeight : Fin q → ℚ) (hkeepWeight : 3 * ∑ e, |(keepWeight e : ℝ)| ≤ W)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J : Fin r → ℚ) (hJ : ∀ e, |(J e : ℝ)| ≤ W)
    (hJlower : ∀ e, 1 / (W : ℝ) ≤ |(J e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2)
        (stageMatrix n q r keepLeft keepRight keepWeight left right
          (fun e => signedMediatorMember (J e)) (MediatorParameters.delta r W G)
          (fun e => MediatorParameters.spoke r W G (J e))) +
      3 * r * MediatorParameters.delta r W G + 3 * ∑ e, |(J e : ℝ)| -
        sourceMatrixBottom n (sourceGraphMatrix n q keepLeft keepRight
          (fun e => (keepWeight e : ℝ)) + sourceGraphMatrix n r left right (fun e => (J e : ℝ)))| ≤
          1 / (512 * (G : ℝ)) := by
  have h := (MediatorParameters.rational_bottom n r hW hG
    (sourceGraphMatrix n q keepLeft keepRight (fun e => (keepWeight e : ℝ)))
    (graph_star n q keepLeft keepRight hkeep _) left right hneq J hJ hJlower
    ((oldGraph_operator_norm n q r keepLeft keepRight hkeep _).trans hkeepWeight)).2
  rw [sourceMatrixBottom_eq_mediator, stageMatrix_physical n q r keepLeft keepRight hkeep]
  simpa only [Rat.cast_natCast, Complex.ofReal_ratCast, sourceGraphMatrix] using h

end ContinuumCoulomb.MediatorGraph

end

end OAI
