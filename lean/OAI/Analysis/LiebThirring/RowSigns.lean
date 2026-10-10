import OAI.Analysis.LiebThirring.Continuation

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

namespace SharpLiebThirring.ContinuationGap
open Matrix Set

abbrev LowerSpace (N : ℕ) :=
  {C : Matrix (Fin N) (Fin N) ℝ // ∀ i j, i < j → C i j = 0}

def rowSign {N : ℕ} (s : Fin N → ℝ) (C : LowerSpace N) : LowerSpace N :=
  ⟨fun i j ↦ s i * C.val i j, by
    intro i j hij
    change s i * C.val i j = 0
    rw [C.prop i j hij, mul_zero]⟩

def signConjugate {N : ℕ} (s : Fin N → ℝ) (Z : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j ↦ s i * Z i j * s j

def NonzeroRows {N : ℕ} (C : LowerSpace N) : Prop := ∀ i, ∃ j, C.val i j ≠ 0

end SharpLiebThirring.ContinuationGap
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

abbrev LowerIndex (N : ℕ) := {a : Fin N × Fin N // a.2 ≤ a.1}
abbrev lowerDim (N : ℕ) := Fintype.card (LowerIndex N)
noncomputable def indexEquiv (N : ℕ) : LowerIndex N ≃ Fin (lowerDim N) := Fintype.equivFin _

def diagonalIndex {N : ℕ} (i : Fin N) : Fin (lowerDim N) := indexEquiv N ⟨(i,i),le_refl _⟩
def rowIndex {N : ℕ} (a : Fin (lowerDim N)) : Fin N := ((indexEquiv N).symm a).val.1
def colIndex {N : ℕ} (a : Fin (lowerDim N)) : Fin N := ((indexEquiv N).symm a).val.2

@[simp] lemma rowIndex_diagonal {N : ℕ} (i : Fin N) : rowIndex (diagonalIndex i) = i := by
  simp [rowIndex,diagonalIndex]
@[simp] lemma colIndex_diagonal {N : ℕ} (i : Fin N) : colIndex (diagonalIndex i) = i := by
  simp [colIndex,diagonalIndex]
lemma colIndex_le_rowIndex {N : ℕ} (a : Fin (lowerDim N)) : colIndex a ≤ rowIndex a :=
  ((indexEquiv N).symm a).prop

/-- Exact linear coordinates on the entire lower-triangular coefficient space;
no nonvanishing or invertibility restriction is imposed. -/
def lowerOfCoords {N : ℕ} (x : Fin (lowerDim N) → ℝ) : LowerSpace N :=
  ⟨fun i j ↦ if h : j ≤ i then x (indexEquiv N ⟨(i,j),h⟩) else 0,
    by intro i j hij; simp only [not_le.mpr hij,↓reduceDIte]⟩
def lowerCoords {N : ℕ} (C : LowerSpace N) : Fin (lowerDim N) → ℝ :=
  fun a ↦ C.val (rowIndex a) (colIndex a)

@[simp] lemma lowerCoords_lowerOfCoords {N : ℕ} (x : Fin (lowerDim N) → ℝ) :
    lowerCoords (lowerOfCoords x) = x := by
  funext a
  have he : (⟨(rowIndex a,colIndex a),colIndex_le_rowIndex a⟩ : LowerIndex N) = (indexEquiv N).symm a := rfl
  simp only [lowerCoords,lowerOfCoords,colIndex_le_rowIndex,↓reduceDIte,he,Equiv.apply_symm_apply]

@[simp] lemma lowerOfCoords_lowerCoords {N : ℕ} (C : LowerSpace N) :
    lowerOfCoords (lowerCoords C) = C := by
  apply Subtype.ext
  funext i j
  dsimp [lowerOfCoords]
  split_ifs with h
  · simp [lowerCoords,rowIndex,colIndex]
  · exact (C.prop i j (lt_of_not_ge h)).symm

lemma continuous_lowerCoords {N : ℕ} : Continuous (lowerCoords (N := N)) := by
  apply continuous_pi
  intro a
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)
lemma continuous_lowerOfCoords {N : ℕ} : Continuous (lowerOfCoords (N := N)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : j ≤ i
  · simpa only [lowerOfCoords,h,↓reduceDIte] using (continuous_apply (indexEquiv N ⟨(i,j),h⟩))
  · simpa only [lowerOfCoords,h,↓reduceDIte] using (continuous_const : Continuous (fun _ : Fin (lowerDim N) → ℝ ↦ (0 : ℝ)))

def lowerHomeomorph (N : ℕ) : (Fin (lowerDim N) → ℝ) ≃ₜ LowerSpace N where
  toFun := lowerOfCoords
  invFun := lowerCoords
  left_inv := lowerCoords_lowerOfCoords
  right_inv := lowerOfCoords_lowerCoords
  continuous_toFun := continuous_lowerOfCoords
  continuous_invFun := continuous_lowerCoords

/-- Coordinate reflections that flip whole rows and fix the homotopy time. -/
def rowSubgroup (N : ℕ) : Subgroup (Signs (lowerDim N + 1)) where
  carrier := {s | s.val (Fin.last (lowerDim N)) = false ∧
    ∀ a : Fin (lowerDim N), s.val a.castSucc = s.val (diagonalIndex (rowIndex a)).castSucc}
  one_mem' := ⟨rfl,fun _ ↦ rfl⟩
  mul_mem' hs ht := ⟨by simp only [Signs.mul_val,hs.1,ht.1,Bool.false_xor],
    fun a ↦ by simp only [Signs.mul_val,hs.2 a,ht.2 a]⟩
  inv_mem' hs := hs

def rowBool {N : ℕ} (s : rowSubgroup N) (i : Fin N) : Bool :=
  s.val.val (diagonalIndex i).castSucc
lemma rowSubgroup_time {N : ℕ} (s : rowSubgroup N) : s.val.val (Fin.last (lowerDim N)) = false := s.prop.1
lemma rowSubgroup_coord {N : ℕ} (s : rowSubgroup N) (a : Fin (lowerDim N)) :
    s.val.val a.castSucc = rowBool s (rowIndex a) := s.prop.2 a

@[simp] lemma rowBool_one {N : ℕ} (i : Fin N) : rowBool (1 : rowSubgroup N) i = false := rfl
@[simp] lemma rowBool_mul {N : ℕ} (s t : rowSubgroup N) (i : Fin N) :
    rowBool (s*t) i = xor (rowBool s i) (rowBool t i) := rfl

lemma rowBool_injective {N : ℕ} : Function.Injective (rowBool (N := N)) := by
  intro s t h
  apply Subtype.ext
  apply Signs.ext
  funext a
  refine Fin.lastCases ?_ (fun b ↦ ?_) a
  · rw [rowSubgroup_time,rowSubgroup_time]
  · rw [rowSubgroup_coord,rowSubgroup_coord,h]

def rowElement {N : ℕ} (s : Fin N → Bool) : rowSubgroup N :=
  ⟨⟨Fin.snoc (fun a ↦ s (rowIndex a)) false⟩,by
    constructor
    · simp only [Fin.snoc_last]
    · intro a
      simp only [Fin.snoc_castSucc,rowIndex_diagonal]⟩
@[simp] lemma rowBool_rowElement {N : ℕ} (s : Fin N → Bool) : rowBool (rowElement s) = s := by
  funext i
  simp only [rowBool,rowElement,Fin.snoc_castSucc,rowIndex_diagonal]

def signValue (b : Bool) : ℝ := if b then -1 else 1
@[simp] lemma signValue_false : signValue false = 1 := rfl
@[simp] lemma signValue_true : signValue true = -1 := rfl
lemma signValue_cases (b : Bool) : signValue b = 1 ∨ signValue b = -1 := by cases b <;> simp [signValue]
lemma signValue_xor (b c : Bool) : signValue (xor b c) = signValue b * signValue c := by
  cases b <;> cases c <;> norm_num [signValue]
lemma signValue_smul (b : Bool) (x : ℝ) : (if b then -x else x) = signValue b * x := by
  cases b <;> simp [signValue]

def conjugateSigns {N : ℕ} (s : rowSubgroup N) : Signs (lowerDim N) :=
  ⟨fun a ↦ xor (rowBool s (rowIndex a)) (rowBool s (colIndex a))⟩

def conjugateRepresentation (N : ℕ) : rowSubgroup N →* ((Fin (lowerDim N) → ℝ) ≃ₗ[ℝ] (Fin (lowerDim N) → ℝ)) where
  toFun s := (conjugateSigns s).linearIsometry.toLinearEquiv
  map_one' := by
    ext x a
    simp only [conjugateSigns,Signs.linearIsometry,rowBool_one,Bool.false_xor,Bool.false_eq_true,↓reduceIte]
    rfl
  map_mul' s t := by
    ext x a
    change (if xor (rowBool (s*t) (rowIndex a)) (rowBool (s*t) (colIndex a)) then -x a else x a) =
      if xor (rowBool s (rowIndex a)) (rowBool s (colIndex a)) then
        -(if xor (rowBool t (rowIndex a)) (rowBool t (colIndex a)) then -x a else x a) else
        if xor (rowBool t (rowIndex a)) (rowBool t (colIndex a)) then -x a else x a
    simp only [rowBool_mul]
    rcases Bool.eq_false_or_eq_true (rowBool s (rowIndex a)) with h₁ | h₁ <;>
      rcases Bool.eq_false_or_eq_true (rowBool s (colIndex a)) with h₂ | h₂ <;>
      rcases Bool.eq_false_or_eq_true (rowBool t (rowIndex a)) with h₃ | h₃ <;>
      rcases Bool.eq_false_or_eq_true (rowBool t (colIndex a)) with h₄ | h₄ <;> simp [h₁,h₂,h₃,h₄]

lemma conjugateRepresentation_norm {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N) → ℝ) :
    ‖conjugateRepresentation N s x‖ = ‖x‖ := (conjugateSigns s).linearIsometry.norm_map x
lemma conjugateRepresentation_apply {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N) → ℝ)
    (a : Fin (lowerDim N)) :
    conjugateRepresentation N s x a = signValue (rowBool s (rowIndex a)) * x a * signValue (rowBool s (colIndex a)) := by
  change (if xor (rowBool s (rowIndex a)) (rowBool s (colIndex a)) then -x a else x a) = _
  rw [signValue_smul,signValue_xor]
  ring

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

/-- Lower-coordinate restriction is faithful on symmetric matrices. -/
def matrixCoords {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Fin (lowerDim N) → ℝ :=
  fun a ↦ A (rowIndex a) (colIndex a)
lemma continuous_matrixCoords {N : ℕ} : Continuous (matrixCoords (N := N)) := by
  apply continuous_pi
  intro a
  exact (continuous_apply _).comp (continuous_apply _)
lemma matrixCoords_eq_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (h : matrixCoords A = 0) : A = 0 := by
  have hl (i j : Fin N) (hji : j ≤ i) : A i j = 0 := by
    have he := congrFun h (indexEquiv N ⟨(i,j),hji⟩)
    simpa [matrixCoords,rowIndex,colIndex] using he
  ext i j
  rcases le_total j i with hj | hi
  · exact hl i j hj
  · have hs : A j i = A i j := by simpa using congrArg (fun B ↦ B i j) hA
    exact hs.symm.trans (hl j i hi)

def diagonalLower {N : ℕ} (c : Fin N → ℝ) : LowerSpace N :=
  ⟨diagonal c,fun _i _j hij ↦ diagonal_apply_ne c (ne_of_lt hij)⟩
def diagonalPoint {N : ℕ} (c : Fin N → ℝ) : Fin (lowerDim N) → ℝ := lowerCoords (diagonalLower c)
@[simp] lemma lowerOfCoords_diagonalPoint {N : ℕ} (c : Fin N → ℝ) :
    lowerOfCoords (diagonalPoint c) = diagonalLower c := lowerOfCoords_lowerCoords _

def lowerEntry {N : ℕ} (i j : Fin N) : (Fin (lowerDim N) → ℝ) →L[ℝ] ℝ :=
  if h : j ≤ i then ContinuousLinearMap.proj (indexEquiv N ⟨(i,j),h⟩) else 0
lemma lowerEntry_apply {N : ℕ} (i j : Fin N) (x : Fin (lowerDim N) → ℝ) :
    lowerEntry i j x = (lowerOfCoords x).val i j := by
  dsimp [lowerEntry,lowerOfCoords]
  split_ifs <;> rfl
lemma lowerEntry_diagonal {N : ℕ} (i j : Fin N) (c : Fin N → ℝ) :
    lowerEntry i j (diagonalPoint c) = diagonal c i j := by
  rw [lowerEntry_apply,lowerOfCoords_diagonalPoint]
  rfl

def initialMap {N : ℕ} (β : ℝ) (k : Fin N → ℝ) (x : Fin (lowerDim N) → ℝ) : Fin (lowerDim N) → ℝ :=
  matrixCoords (2 • diagonal k - β • ((lowerOfCoords x).val * (lowerOfCoords x).val.transpose))

def jacobianWeight {N : ℕ} (β : ℝ) (c : Fin N → ℝ) (a : Fin (lowerDim N)) : ℝ :=
  -β * (c (colIndex a) + if rowIndex a = colIndex a then c (rowIndex a) else 0)
lemma jacobianWeight_ne_zero {N : ℕ} {β : ℝ} (hβ : β ≠ 0) (c : Fin N → ℝ)
    (hc : ∀ i, 0 < c i) (a : Fin (lowerDim N)) : jacobianWeight β c a ≠ 0 := by
  unfold jacobianWeight
  apply mul_ne_zero (neg_ne_zero.mpr hβ)
  apply ne_of_gt
  split_ifs
  · exact add_pos (hc _) (hc _)
  · simpa using hc (colIndex a)

def initialLinearEquiv {N : ℕ} (β : ℝ) (hβ : β ≠ 0) (c : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    (Fin (lowerDim N) → ℝ) ≃ₗ[ℝ] (Fin (lowerDim N) → ℝ) :=
  LinearEquiv.piCongrRight (fun a ↦ LinearEquiv.smulOfNeZero ℝ ℝ (jacobianWeight β c a) (jacobianWeight_ne_zero hβ c hc a))

lemma initialLinearEquiv_apply {N : ℕ} (β : ℝ) (hβ : β ≠ 0) (c : Fin N → ℝ) (hc : ∀ i, 0 < c i)
    (x : Fin (lowerDim N) → ℝ) (a : Fin (lowerDim N)) :
    initialLinearEquiv β hβ c hc x a = jacobianWeight β c a * x a := rfl

lemma initialMap_hasFDerivAt {N : ℕ} (β : ℝ) (hβ : β ≠ 0) (k c : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    HasFDerivAt (initialMap β k)
      (initialLinearEquiv β hβ c hc).toContinuousLinearEquiv.toContinuousLinearMap (diagonalPoint c) := by
  classical
  let p := diagonalPoint c
  let D := fun a : Fin (lowerDim N) ↦ -(β • ∑ m : Fin N,
    ((lowerEntry (rowIndex a) m p) • lowerEntry (colIndex a) m +
      (lowerEntry (colIndex a) m p) • lowerEntry (rowIndex a) m))
  have hd : HasFDerivAt (initialMap β k) (ContinuousLinearMap.pi D) p := by
    apply hasFDerivAt_pi.mpr
    intro a
    have hsum := HasFDerivAt.fun_sum (x := p) (u := Finset.univ) (fun m _ ↦
      (lowerEntry (rowIndex a) m).hasFDerivAt.mul (lowerEntry (colIndex a) m).hasFDerivAt)
    convert (hsum.const_mul β).const_sub ((2 • diagonal k) (rowIndex a) (colIndex a)) using 1
    · funext x
      simp only [initialMap,matrixCoords,Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,
        transpose_apply,smul_eq_mul,Pi.mul_apply,lowerEntry_apply]
  have hD : ContinuousLinearMap.pi D =
      (initialLinearEquiv β hβ c hc).toContinuousLinearEquiv.toContinuousLinearMap := by
    ext x a
    simp only [ContinuousLinearMap.pi_apply,ContinuousLinearEquiv.coe_coe]
    change D a x = jacobianWeight β c a * x a
    dsimp [D,p]
    simp only [_root_.neg_apply,_root_.smul_apply,_root_.sum_apply,
      _root_.add_apply,smul_eq_mul,lowerEntry_diagonal,Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (rowIndex a),Finset.sum_eq_single (colIndex a)]
    · simp only [diagonal_apply_eq,lowerEntry_apply]
      have ha : (lowerOfCoords x).val (rowIndex a) (colIndex a) = x a :=
        congrFun (lowerCoords_lowerOfCoords x) a
      rw [ha]
      by_cases he : rowIndex a = colIndex a
      · rw [he] at ha ⊢
        rw [ha]
        simp only [jacobianWeight,he,↓reduceIte]
        ring
      · have hlt : colIndex a < rowIndex a := lt_of_le_of_ne (colIndex_le_rowIndex a) (Ne.symm he)
        rw [(lowerOfCoords x).prop _ _ hlt]
        simp only [jacobianWeight,he,↓reduceIte]
        ring
    · intro m _ hm
      rw [diagonal_apply_ne _ hm.symm,zero_mul]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
    · intro m _ hm
      rw [diagonal_apply_ne _ hm.symm,zero_mul]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  rwa [hD] at hd

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

def spaceTimeHomeomorph (N : ℕ) : (Fin (lowerDim N + 1) → ℝ) ≃ₜ (LowerSpace N × ℝ) where
  toFun x := (lowerOfCoords (spatial x),x (Fin.last (lowerDim N)))
  invFun z := Fin.snoc (lowerCoords z.1) z.2
  left_inv x := by
    simp only [lowerCoords_lowerOfCoords]
    exact Fin.snoc_init_self x
  right_inv z := by
    change (lowerOfCoords (Fin.init (Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) (lowerCoords z.1) z.2)),
      Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) (lowerCoords z.1) z.2 (Fin.last (lowerDim N))) = z
    simp only [Fin.init_snoc,Fin.snoc_last,lowerOfCoords_lowerCoords]
  continuous_toFun := (continuous_lowerOfCoords.comp spatial.continuous_of_finiteDimensional).prodMk (continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · simpa only [Fin.snoc_last] using (continuous_snd : Continuous (fun z : LowerSpace N × ℝ ↦ z.2))
    · simpa only [Fin.snoc_castSucc,Function.comp_def] using ((continuous_apply b).comp (continuous_lowerCoords.comp continuous_fst))

def clampTime (t : ℝ) : ℝ := max 0 (min t 1)
lemma continuous_clampTime : Continuous clampTime := continuous_const.max (continuous_id.min continuous_const)
lemma clampTime_mem (t : ℝ) : clampTime t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_right _ _)⟩
lemma clampTime_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clampTime t = t := by
  rw [clampTime,min_eq_left ht.2,max_eq_right ht.1]
@[simp] lemma clampTime_zero : clampTime 0 = 0 := clampTime_eq ⟨le_refl _,zero_le_one⟩
@[simp] lemma clampTime_one : clampTime 1 = 1 := clampTime_eq ⟨zero_le_one,le_refl _⟩

def homotopyCoords {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (x : Fin (lowerDim N + 1) → ℝ) : Fin (lowerDim N) → ℝ :=
  matrixCoords (Φ (clampTime (x (Fin.last (lowerDim N)))) (lowerOfCoords (spatial x)))
lemma continuous_homotopyCoords {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hΦ : ContinuousOn (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1) (Set.univ ×ˢ Set.Icc 0 1)) :
    Continuous (homotopyCoords Φ) := by
  apply continuous_matrixCoords.comp
  exact hΦ.comp_continuous
    ((continuous_lowerOfCoords.comp spatial.continuous_of_finiteDimensional).prodMk
      (continuous_clampTime.comp (continuous_apply _)))
    (fun x ↦ ⟨Set.mem_univ _,clampTime_mem _⟩)

lemma lowerOfCoords_smul {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N + 1) → ℝ) :
    lowerOfCoords (spatial (s • x)) = rowSign (fun i ↦ signValue (rowBool s i)) (lowerOfCoords (spatial x)) := by
  apply Subtype.ext
  funext i j
  by_cases hji : j ≤ i
  · change (if h : j ≤ i then spatial (s • x) (indexEquiv N ⟨(i,j),h⟩) else 0) = _
    simp only [hji,↓reduceDIte]
    change (s.val • x) (indexEquiv N ⟨(i,j),hji⟩).castSucc =
      signValue (rowBool s i) * (if h : j ≤ i then spatial x (indexEquiv N ⟨(i,j),h⟩) else 0)
    rw [Signs.smul_real,rowSubgroup_coord]
    have hr : rowIndex (indexEquiv N ⟨(i,j),hji⟩) = i := by simp [rowIndex]
    rw [hr,signValue_smul]
    simp only [hji,↓reduceDIte]
    rfl
  · change (if h : j ≤ i then spatial (s • x) (indexEquiv N ⟨(i,j),h⟩) else 0) = _
    simp only [hji,↓reduceDIte,rowSign,lowerOfCoords,mul_zero]

lemma time_smul {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N + 1) → ℝ) :
    (s • x) (Fin.last (lowerDim N)) = x (Fin.last (lowerDim N)) := by
  change (s.val • x) _ = _
  rw [Signs.smul_real,rowSubgroup_time]
  rfl

lemma homotopyCoords_equivariant {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (he : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, ∀ s : Fin N → ℝ,
      (∀ i, s i = 1 ∨ s i = -1) → Φ θ (rowSign s C) = signConjugate s (Φ θ C))
    (s : rowSubgroup N) (x : Fin (lowerDim N + 1) → ℝ) :
    homotopyCoords Φ (s • x) = conjugateRepresentation N s (homotopyCoords Φ x) := by
  unfold homotopyCoords
  rw [time_smul,lowerOfCoords_smul,he _ (clampTime_mem _) _ _ (fun _ ↦ signValue_cases _)]
  ext a
  rw [conjugateRepresentation_apply]
  rfl

lemma homotopyCoords_eq_zero {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    {x : Fin (lowerDim N + 1) → ℝ} (ht : x (Fin.last (lowerDim N)) ∈ Set.Icc (0 : ℝ) 1) :
    homotopyCoords Φ x = 0 ↔ Φ (x (Fin.last (lowerDim N))) (lowerOfCoords (spatial x)) = 0 := by
  rw [homotopyCoords,clampTime_eq ht]
  constructor
  · exact matrixCoords_eq_zero (hs _ ht _)
  · intro h
    rw [h]
    rfl

lemma compact_homotopyCoords_zeros {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    (hK : IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0}) :
    IsCompact {x : Fin (lowerDim N + 1) → ℝ | x (Fin.last (lowerDim N)) ∈ Set.Icc (0 : ℝ) 1 ∧ homotopyCoords Φ x = 0} := by
  have hh := (spaceTimeHomeomorph N).isCompact_preimage.mpr hK
  convert hh using 1
  ext x
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨ht,hx⟩
    exact ⟨ht,(homotopyCoords_eq_zero Φ hs ht).mp hx⟩
  · rintro ⟨ht,hx⟩
    exact ⟨ht,(homotopyCoords_eq_zero Φ hs ht).mpr hx⟩

lemma rowAction_free {N : ℕ} (x : Fin (lowerDim N + 1) → ℝ)
    (hx : NonzeroRows (lowerOfCoords (spatial x)))
    (s : rowSubgroup N) (he : s • x = x) : s = 1 := by
  apply rowBool_injective
  funext i
  rw [rowBool_one]
  obtain ⟨j,hj⟩ := hx i
  have heC := congrArg (fun y ↦ (lowerOfCoords (spatial y)).val i j) he
  rw [lowerOfCoords_smul] at heC
  change signValue (rowBool s i) * (lowerOfCoords (spatial x)).val i j = (lowerOfCoords (spatial x)).val i j at heC
  rcases Bool.eq_false_or_eq_true (rowBool s i) with hb | hb
  · rw [hb,signValue_true,neg_one_mul] at heC
    exact False.elim (hj (by linarith))
  · exact hb

lemma homotopyCoords_initial {N : ℕ} (ε : ℝ) (k : Fin N → ℝ)
    (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (h0 : ∀ C, Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose))
    (u : Fin (lowerDim N) → ℝ) :
    homotopyCoords Φ (embedSpatial u) = initialMap ε⁻¹ k u := by
  unfold homotopyCoords
  have ht : embedSpatial u (Fin.last (lowerDim N)) = 0 := by
    change Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) u 0 (Fin.last (lowerDim N)) = 0
    exact Fin.snoc_last _ _
  rw [ht,clampTime_zero,spatial_embed,h0]
  rfl

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

lemma initial_matrix_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) :
    2 • diagonal k - ε⁻¹ • ((diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))).val *
      (diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))).val.transpose) = 0 := by
  change 2 • diagonal k - ε⁻¹ • (diagonal (fun i ↦ Real.sqrt (2*ε*k i)) *
    (diagonal (fun i ↦ Real.sqrt (2*ε*k i))).transpose) = 0
  rw [diagonal_transpose,diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply,Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul,Matrix.zero_apply]
    rw [← sq,Real.sq_sqrt (le_of_lt (mul_pos (mul_pos (by norm_num) hε) (hk i)))]
    field_simp [ne_of_gt hε]
    ring
  · simp only [Matrix.sub_apply,Matrix.smul_apply,diagonal_apply_ne _ hij,smul_eq_mul,smul_zero,mul_zero,sub_self,Matrix.zero_apply]

lemma gram_of_initial_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (C : LowerSpace N)
    (h : 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose) = 0) :
    C.val * C.val.transpose = diagonal (fun i ↦ 2*ε*k i) := by
  have he : ε • (2 • diagonal k) = C.val * C.val.transpose := by
    have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ ε • A) (sub_eq_zero.mp h)
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt hε),one_smul] using he
  rw [← he]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul]
    ring
  · simp only [Matrix.smul_apply,diagonal_apply_ne _ hij,smul_eq_mul,smul_zero,mul_zero]

lemma homotopyCoords_initial_orbit {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    (h0 : ∀ C, Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose))
    (x : Fin (lowerDim N + 1) → ℝ) (ht : x (Fin.last (lowerDim N)) = 0)
    (hx : homotopyCoords Φ x = 0) :
    ∃ s : rowSubgroup N, s • embedSpatial (diagonalPoint (fun i ↦ Real.sqrt (2*ε*k i))) = x := by
  classical
  let C := lowerOfCoords (spatial x)
  have hΦ : Φ 0 C = 0 := by
    have hh := (homotopyCoords_eq_zero Φ hs (by rw [ht]; exact ⟨le_refl _,zero_le_one⟩)).mp hx
    simpa only [ht] using hh
  rw [h0] at hΦ
  obtain ⟨s,hsign,hC⟩ := PathProof.lower_gram_initial_orbit hε k hk C.prop (gram_of_initial_zero hε k C hΦ)
  let b : Fin N → Bool := fun i ↦ decide (s i = -1)
  have hb (i : Fin N) : signValue (b i) = s i := by
    rcases hsign i with hi | hi
    · norm_num [b,hi,signValue]
    · norm_num [b,hi,signValue]
  have hrow : rowSign (fun i ↦ signValue (rowBool (rowElement b) i))
      (diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))) = C := by
    apply Subtype.ext
    change (fun i j ↦ signValue (rowBool (rowElement b) i) * diagonal (fun i ↦ Real.sqrt (2*ε*k i)) i j) = C.val
    rw [hC]
    ext i j
    rw [rowBool_rowElement,hb]
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
    · simp only [diagonal_apply_ne _ hij,mul_zero]
  refine ⟨rowElement b,?_⟩
  apply (spaceTimeHomeomorph N).injective
  apply Prod.ext
  · change lowerOfCoords (spatial ((rowElement b) • embedSpatial (diagonalPoint _))) = C
    rw [lowerOfCoords_smul,spatial_embed,lowerOfCoords_diagonalPoint,hrow]
  · change ((rowElement b) • embedSpatial (diagonalPoint (fun i ↦ Real.sqrt (2*ε*k i)))) (Fin.last (lowerDim N)) = x (Fin.last (lowerDim N))
    rw [time_smul,ht]
    change Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) _ 0 (Fin.last (lowerDim N)) = 0
    exact Fin.snoc_last _ _

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

/-- Row-sign continuation. Rank
deficiency is allowed throughout; only zero rows at matching solutions are excluded. -/
theorem equivariant_continuation (N : ℕ) (ε : ℝ) (k : Fin N → ℝ)
    (hε : 0 < ε) (hk : ∀ i, 0 < k i)
    (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hΦ : ContinuousOn (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1) (Set.univ ×ˢ Set.Icc 0 1))
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    (he : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, ∀ s : Fin N → ℝ,
      (∀ i, s i = 1 ∨ s i = -1) → Φ θ (rowSign s C) = signConjugate s (Φ θ C))
    (h0 : ∀ C, Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose))
    (hK : IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0})
    (hn : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, Φ θ C = 0 → NonzeroRows C) :
    ∃ C, Φ 1 C = 0 := by
  let c := fun i ↦ Real.sqrt (2*ε*k i)
  have hc (i : Fin N) : 0 < c i := Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) hε) (hk i))
  have hβ : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
  let L := initialLinearEquiv ε⁻¹ hβ c hc
  let p := diagonalPoint c
  let f := homotopyCoords Φ
  have hp0 : f (embedSpatial p) = 0 := by
    change homotopyCoords Φ (embedSpatial p) = 0
    rw [homotopyCoords_initial ε k Φ h0]
    dsimp only [initialMap, p]
    rw [lowerOfCoords_diagonalPoint]
    rw [initial_matrix_zero hε k hk]
    rfl
  have hd : HasFDerivAt (fun u ↦ f (embedSpatial u)) L.toContinuousLinearEquiv.toContinuousLinearMap p := by
    have hh : (fun u ↦ f (embedSpatial u)) = initialMap ε⁻¹ k :=
      funext (homotopyCoords_initial ε k Φ h0)
    rw [hh]
    exact initialMap_hasFDerivAt ε⁻¹ hβ k c hc
  obtain ⟨x,ht,hx⟩ := exists_terminal_zero_simple (rowSubgroup N) rowSubgroup_time
    (conjugateRepresentation N) L conjugateRepresentation_norm p f
    (continuous_homotopyCoords Φ hΦ) (homotopyCoords_equivariant Φ he) hp0 hd
    (homotopyCoords_initial_orbit hε k hk Φ hs h0)
    (compact_homotopyCoords_zeros Φ hs hK)
    (fun x ht hx ↦ rowAction_free x
      (hn _ ht _ ((homotopyCoords_eq_zero Φ hs ht).mp hx)))
  refine ⟨lowerOfCoords (spatial x),?_⟩
  have hh := (homotopyCoords_eq_zero Φ hs (by rw [ht]; exact ⟨zero_le_one,le_refl _⟩)).mp hx
  simpa only [ht] using hh

end SharpLiebThirring.PathTopology

end
end
end

end OAI
