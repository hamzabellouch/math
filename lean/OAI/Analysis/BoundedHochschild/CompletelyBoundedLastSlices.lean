import OAI.Analysis.BoundedHochschild.RightModuleProjection
import OAI.Analysis.BoundedHochschild.Cochains

namespace OAI

/-! Uniformly completely bounded last slices and their module-averaged
primitive. Only the last variable needs a complete bound for this step. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def LastSliceEstimate {n : ℕ} (f : Cochain M (n + 1)) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ v : Fin n → M,
    CompletelyBoundedEstimate (f.curryRight v) (C * ∏ i, ‖v i‖)

def cbCurryRight {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hf : LastSliceEstimate f C) :
    MultilinearMap ℂ (fun _ : Fin n => M) (CompletelyBoundedMap M) :=
  f.curryRight.toMultilinearMap.codRestrict completelyBoundedSubmodule
    (fun v => ⟨C * ∏ i, ‖v i‖, hf.2 v⟩)

@[simp] lemma cbCurryRight_val {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hf : LastSliceEstimate f C) (v : Fin n → M) :
    (cbCurryRight f hf v).val = f.curryRight v := rfl

@[simp] lemma cbCurryRight_apply {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ}
    (hf : LastSliceEstimate f C) (v : Fin n → M) (u : M) :
    (cbCurryRight f hf v).val u = f (Fin.snoc v u) := rfl

@[simp] lemma cbLeftSandwich_apply (a b : M) (T : CompletelyBoundedMap M) (u : M) :
    (cbLeftSandwich a b T).val u = a * T.val (b * u) := rfl

def averagedLastMultilinear (P : RightModuleAveragingProjection (M := M))
    {n : ℕ} (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) :
    MultilinearMap ℂ (fun _ : Fin n => M) M :=
  ((ContinuousLinearMap.apply ℂ M (1 : M)).toLinearMap.comp P.map).compMultilinearMap
    (cbCurryRight f hf)

@[simp] lemma averagedLastMultilinear_apply
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) (v : Fin n → M) :
    averagedLastMultilinear P f hf v = P.map (cbCurryRight f hf v) 1 := rfl

lemma averagedLastMultilinear_bound [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) (v : Fin n → M) :
    ‖averagedLastMultilinear P f hf v‖ ≤ C * ∏ i, ‖v i‖ := by
  rw [averagedLastMultilinear_apply]
  calc
    _ ≤ ‖P.map (cbCurryRight f hf v)‖ * ‖(1 : M)‖ := (P.map _).le_opNorm _
    _ = ‖P.map (cbCurryRight f hf v)‖ := by rw [norm_one, mul_one]
    _ ≤ _ := P.bound _ _ (hf.2 v)

def averagedLastCochain [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) : Cochain M n :=
  (averagedLastMultilinear P f hf).mkContinuous C (averagedLastMultilinear_bound P f hf)

@[simp] lemma averagedLastCochain_apply [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) (v : Fin n → M) :
    averagedLastCochain P f hf v = P.map (cbCurryRight f hf v) 1 := rfl

lemma averagedLastCochain_norm [Nontrivial M]
    (P : RightModuleAveragingProjection (M := M)) {n : ℕ}
    (f : Cochain M (n + 1)) {C : ℝ} (hf : LastSliceEstimate f C) :
    ‖averagedLastCochain P f hf‖ ≤ C :=
  MultilinearMap.mkContinuous_norm_le _ hf.1 _

lemma completelyBounded_id :
    CompletelyBoundedEstimate (ContinuousLinearMap.id ℂ M) 1 := by
  refine ⟨zero_le_one, fun n A => ?_⟩
  have h : A.map (ContinuousLinearMap.id ℂ M) = A := by ext i j; rfl
  rw [h, one_mul]

def cbIdentity : CompletelyBoundedMap M :=
  ⟨ContinuousLinearMap.id ℂ M, 1, completelyBounded_id⟩

def cbLeftMul (a : M) : CompletelyBoundedMap M := cbLeftSandwich a 1 cbIdentity

@[simp] lemma cbLeftMul_apply (a x : M) : (cbLeftMul a).val x = a * x := by
  simp [cbLeftMul, cbLeftSandwich, cbIdentity, leftSandwichMap]

lemma moduleProjection_leftMul (P : RightModuleAveragingProjection (M := M))
    (a : M) : P.map (cbLeftMul a) = (cbLeftMul a).val := by
  apply P.fixes
  intro x y
  simp only [cbLeftMul_apply, mul_assoc]

end BoundedHochschild.KadisonRingrose

end

end OAI
