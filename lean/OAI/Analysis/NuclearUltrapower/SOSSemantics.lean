import OAI.Analysis.NuclearUltrapower.SOSResidual

namespace OAI

section

namespace NuclearUltrapower.SOS
section BucketSemantics
variable {α A β γ : Type*} [DecidableEq α] [AddCommGroup A]

omit [DecidableEq α] in
@[simp] theorem eval_append (f : α → A) (p q : Poly α) :
    eval f (p ++ q) = eval f p + eval f q := by
  simp only [eval, List.map_append, List.sum_append]

omit [DecidableEq α] in
@[simp] theorem eval_flatMap (f : α → A) (xs : List β) (p : β → Poly α) :
    eval f (xs.flatMap p) = (xs.map (fun x => eval f (p x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, eval_append, ih, List.map_cons, List.sum_cons]

omit [DecidableEq α] in
@[simp] theorem eval_flatten (f : α → A) (xs : List (Poly α)) :
    eval f xs.flatten = (xs.map (eval f)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatten_cons, eval_append, ih, List.map_cons, List.sum_cons]

omit [DecidableEq α] in
theorem list_sum_comm (x : List β) (y : List γ) (f : β → γ → A) :
    (x.map (fun i => (y.map (fun j => f i j)).sum)).sum =
      (y.map (fun j => (x.map (fun i => f i j)).sum)).sum := by
  induction x with
  | nil => simp
  | cons a x ih => simp [List.sum_map_add, ih]

omit [DecidableEq α] in
theorem sum_getD (N : ℕ) (p : List A) (h : p.length ≤ N) :
    ((List.range N).map (fun i => p.getD i 0)).sum = p.sum := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    simp [hp]
  | succ N ih =>
    cases p with
    | nil => simp
    | cons a p =>
      simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
        List.getD_cons_zero, List.getD_cons_succ, List.sum_cons]
      rw [ih p (by simpa using h)]

theorem eval_buckets (n : ℕ) (rs : List (List (Poly α)))
    (h : ∀ r ∈ rs, r.length ≤ n) (f : α → A) (le : α → α → Bool) :
    eval f ((List.range n).flatMap (fun b => normalize le (rs.flatMap (fun r => r.getD b [])))) =
      eval f (rs.flatMap List.flatten) := by
  simp only [eval_flatMap, eval_normalize]
  rw [list_sum_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hg (i : ℕ) : eval f (r.getD i []) = (r.map (eval f)).getD i 0 := by
    simpa only [eval_nil] using (List.getD_map r [] (n := i) (eval f)).symm
  simp only [hg]
  rw [sum_getD n _ (by simpa only [List.length_map] using h r hr), eval_flatten]

end BucketSemantics
end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

theorem support_addHead_iff (p : α × ℤ) (ps : Poly α) (g : α) :
    g ∈ (addHead p ps).map Prod.fst ↔ g = p.1 ∨ g ∈ ps.map Prod.fst := by
  cases ps with
  | nil => simp [addHead]
  | cons q qs =>
    simp only [addHead]
    split_ifs with h <;> simp_all

theorem support_compress_iff (ps : Poly α) (g : α) :
    g ∈ (compress ps).map Prod.fst ↔ g ∈ ps.map Prod.fst := by
  induction ps with
  | nil => simp [compress]
  | cons p ps ih => simp only [compress, support_addHead_iff, ih, List.map_cons, List.mem_cons]

theorem support_normalize_iff (le : α → α → Bool) (ps : Poly α) (g : α) :
    g ∈ (normalize le ps).map Prod.fst ↔ g ∈ ps.map Prod.fst := by
  rw [normalize, support_compress_iff]
  exact ((List.perm_insertionSort _ ps).map Prod.fst).mem_iff

section EvalOperations
variable [Ring A]
omit [DecidableEq α] in
theorem eval_scale (f : α → A) (ps : Poly α) (k : ℤ) :
    eval f (ps.map (fun p => (p.1, k*p.2))) = k • eval f ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, eval_cons, smul_add, ih, mul_smul]

omit [DecidableEq α] in
theorem eval_mul (f : α → A) (μ : α → α → α) (ps qs : Poly α)
    (h : ∀ p ∈ ps, ∀ q ∈ qs, f (μ p.1 q.1) = f p.1 * f q.1) :
    eval f (ps.flatMap (fun p => qs.map (fun q => (μ p.1 q.1, p.2*q.2)))) =
      eval f ps * eval f qs := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hrow : eval f (qs.map (fun q => (μ p.1 q.1, p.2*q.2))) =
        (p.2 • f p.1) * eval f qs := by
      have hp := h p (by simp)
      clear h ih
      induction qs with
      | nil => simp
      | cons q qs ihq =>
        have hq := hp q (by simp)
        have hi := ihq (fun t ht => hp t (by simp [ht]))
        simp only [List.map_cons, eval_cons, hq, hi, mul_add]
        congr 1
        simp only [zsmul_eq_mul, Int.cast_mul, mul_assoc]
        rw [← mul_assoc (f p.1) (q.2 : A) (f q.1),
          ← (Int.cast_commute q.2 (f p.1)).eq, mul_assoc]
    simp only [List.flatMap_cons, eval_append, eval_cons, add_mul, hrow,
      ih (fun t ht q hq => h t (by simp [ht]) q hq)]
end EvalOperations
end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS
def toMatrix (a : Mat3) : Matrix (Fin 3) (Fin 3) ℤ := fun i j => entry a i j

theorem toMatrix_one : toMatrix matOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem toMatrix_mul (a b : Mat3) : toMatrix (matMul a b) = toMatrix a * toMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, matMul, entry, Matrix.mul_apply, Fin.sum_univ_succ, List.range_succ, add_assoc]

theorem toMatrix_inv (a : Mat3) : toMatrix (matInv a) = (toMatrix a).adjugate := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, matInv, entry, List.range_succ] <;> ring

abbrev SL := Matrix.SpecialLinearGroup (Fin 3) ℤ

/-- Total interpretation of a label; the certificate will establish det=1 at every label used. -/
def interpret (m : Mat3) : SL :=
  if h : (toMatrix m).det = 1 then ⟨toMatrix m,h⟩ else 1

theorem interpret_coe (m : Mat3) (h : (toMatrix m).det = 1) :
    (interpret m : Matrix (Fin 3) (Fin 3) ℤ) = toMatrix m := by
  simp [interpret, h]

theorem interpret_one : interpret matOne = 1 := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_one, Matrix.det_one]), toMatrix_one]
  rfl

theorem interpret_mul (a b : Mat3) (ha : (toMatrix a).det = 1) (hb : (toMatrix b).det = 1) :
    interpret (matMul a b) = interpret a * interpret b := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_mul, Matrix.det_mul, ha, hb, one_mul]),
    Matrix.SpecialLinearGroup.coe_mul, interpret_coe _ ha, interpret_coe _ hb, toMatrix_mul]

theorem interpret_inv (a : Mat3) (ha : (toMatrix a).det = 1) :
    interpret (matInv a) = (interpret a)⁻¹ := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_inv, Matrix.det_adjugate, ha, one_pow]),
    Matrix.SpecialLinearGroup.coe_inv, interpret_coe _ ha, toMatrix_inv]

end NuclearUltrapower.SOS

namespace NuclearUltrapower.SOS
variable {A : Type*} [AddCommGroup A]

theorem intL1_flatten {α : Type*} (rs : List (Poly α)) :
    intL1 rs.flatten = (rs.map intL1).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [intL1, List.map_append, List.sum_append, List.flatten_cons, List.map_cons, List.sum_cons] at *
    exact congrArg (fun t : ℤ => intL1 r + t) ih

def augmentation {α : Type*} (p : Poly α) : ℤ := (p.map Prod.snd).sum

theorem augmentation_flatten {α : Type*} (rs : List (Poly α)) :
    augmentation rs.flatten = (rs.map augmentation).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [augmentation, List.map_append, List.sum_append, List.flatten_cons, List.map_cons, List.sum_cons] at *
    exact congrArg (fun t : ℤ => augmentation r + t) ih

def residual : Poly Mat3 := [residualBucket 0, residualBucket 1, residualBucket 2, residualBucket 3, residualBucket 4, residualBucket 5, residualBucket 6, residualBucket 7, residualBucket 8, residualBucket 9, residualBucket 10, residualBucket 11, residualBucket 12, residualBucket 13, residualBucket 14, residualBucket 15, residualBucket 16, residualBucket 17, residualBucket 18, residualBucket 19, residualBucket 20, residualBucket 21, residualBucket 22, residualBucket 23, residualBucket 24, residualBucket 25, residualBucket 26, residualBucket 27, residualBucket 28, residualBucket 29, residualBucket 30, residualBucket 31, residualBucket 32, residualBucket 33, residualBucket 34, residualBucket 35, residualBucket 36, residualBucket 37, residualBucket 38, residualBucket 39, residualBucket 40, residualBucket 41, residualBucket 42, residualBucket 43, residualBucket 44, residualBucket 45, residualBucket 46, residualBucket 47, residualBucket 48, residualBucket 49, residualBucket 50, residualBucket 51, residualBucket 52, residualBucket 53, residualBucket 54, residualBucket 55, residualBucket 56, residualBucket 57, residualBucket 58, residualBucket 59, residualBucket 60, residualBucket 61, residualBucket 62, residualBucket 63, residualBucket 64, residualBucket 65, residualBucket 66, residualBucket 67, residualBucket 68, residualBucket 69, residualBucket 70, residualBucket 71, residualBucket 72, residualBucket 73, residualBucket 74, residualBucket 75, residualBucket 76, residualBucket 77, residualBucket 78, residualBucket 79, residualBucket 80, residualBucket 81, residualBucket 82, residualBucket 83, residualBucket 84, residualBucket 85, residualBucket 86, residualBucket 87, residualBucket 88, residualBucket 89, residualBucket 90, residualBucket 91, residualBucket 92, residualBucket 93, residualBucket 94, residualBucket 95, residualBucket 96, residualBucket 97, residualBucket 98, residualBucket 99, residualBucket 100, residualBucket 101, residualBucket 102, residualBucket 103, residualBucket 104, residualBucket 105, residualBucket 106, residualBucket 107, residualBucket 108, residualBucket 109, residualBucket 110, residualBucket 111, residualBucket 112, residualBucket 113, residualBucket 114, residualBucket 115, residualBucket 116, residualBucket 117, residualBucket 118, residualBucket 119, residualBucket 120, residualBucket 121, residualBucket 122, residualBucket 123, residualBucket 124, residualBucket 125, residualBucket 126, residualBucket 127].flatten

theorem row_lengths : allRowBuckets.map List.length = List.replicate 123 128 := by
  simp only [allRowBuckets, List.map_cons, List.map_nil, row_length_0, row_length_1, row_length_2, row_length_3, row_length_4, row_length_5, row_length_6, row_length_7, row_length_8, row_length_9, row_length_10, row_length_11, row_length_12, row_length_13, row_length_14, row_length_15, row_length_16, row_length_17, row_length_18, row_length_19, row_length_20, row_length_21, row_length_22, row_length_23, row_length_24, row_length_25, row_length_26, row_length_27, row_length_28, row_length_29, row_length_30, row_length_31, row_length_32, row_length_33, row_length_34, row_length_35, row_length_36, row_length_37, row_length_38, row_length_39, row_length_40, row_length_41, row_length_42, row_length_43, row_length_44, row_length_45, row_length_46, row_length_47, row_length_48, row_length_49, row_length_50, row_length_51, row_length_52, row_length_53, row_length_54, row_length_55, row_length_56, row_length_57, row_length_58, row_length_59, row_length_60, row_length_61, row_length_62, row_length_63, row_length_64, row_length_65, row_length_66, row_length_67, row_length_68, row_length_69, row_length_70, row_length_71, row_length_72, row_length_73, row_length_74, row_length_75, row_length_76, row_length_77, row_length_78, row_length_79, row_length_80, row_length_81, row_length_82, row_length_83, row_length_84, row_length_85, row_length_86, row_length_87, row_length_88, row_length_89, row_length_90, row_length_91, row_length_92, row_length_93, row_length_94, row_length_95, row_length_96, row_length_97, row_length_98, row_length_99, row_length_100, row_length_101, row_length_102, row_length_103, row_length_104, row_length_105, row_length_106, row_length_107, row_length_108, row_length_109, row_length_110, row_length_111, row_length_112, row_length_113, row_length_114, row_length_115, row_length_116, row_length_117, row_length_118, row_length_119, row_length_120, row_length_121, row_length_122]
  rfl

theorem row_length_bound : ∀ r ∈ allRowBuckets, r.length ≤ 128 := by
  intro r hr
  have h := List.mem_map_of_mem (f := List.length) hr
  rw [row_lengths] at h
  have : r.length = 128 := (List.mem_replicate.mp h).2
  omega

theorem row_normalizations : residualRows.map (normalize matLe) =
    allRowBuckets.map (fun r => normalize matLe r.flatten) := by
  simp only [residualRows, allRowBuckets, List.map_cons, List.map_nil, row_partition_0, row_partition_1, row_partition_2, row_partition_3, row_partition_4, row_partition_5, row_partition_6, row_partition_7, row_partition_8, row_partition_9, row_partition_10, row_partition_11, row_partition_12, row_partition_13, row_partition_14, row_partition_15, row_partition_16, row_partition_17, row_partition_18, row_partition_19, row_partition_20, row_partition_21, row_partition_22, row_partition_23, row_partition_24, row_partition_25, row_partition_26, row_partition_27, row_partition_28, row_partition_29, row_partition_30, row_partition_31, row_partition_32, row_partition_33, row_partition_34, row_partition_35, row_partition_36, row_partition_37, row_partition_38, row_partition_39, row_partition_40, row_partition_41, row_partition_42, row_partition_43, row_partition_44, row_partition_45, row_partition_46, row_partition_47, row_partition_48, row_partition_49, row_partition_50, row_partition_51, row_partition_52, row_partition_53, row_partition_54, row_partition_55, row_partition_56, row_partition_57, row_partition_58, row_partition_59, row_partition_60, row_partition_61, row_partition_62, row_partition_63, row_partition_64, row_partition_65, row_partition_66, row_partition_67, row_partition_68, row_partition_69, row_partition_70, row_partition_71, row_partition_72, row_partition_73, row_partition_74, row_partition_75, row_partition_76, row_partition_77, row_partition_78, row_partition_79, row_partition_80, row_partition_81, row_partition_82, row_partition_83, row_partition_84, row_partition_85, row_partition_86, row_partition_87, row_partition_88, row_partition_89, row_partition_90, row_partition_91, row_partition_92, row_partition_93, row_partition_94, row_partition_95, row_partition_96, row_partition_97, row_partition_98, row_partition_99, row_partition_100, row_partition_101, row_partition_102, row_partition_103, row_partition_104, row_partition_105, row_partition_106, row_partition_107, row_partition_108, row_partition_109, row_partition_110, row_partition_111, row_partition_112, row_partition_113, row_partition_114, row_partition_115, row_partition_116, row_partition_117, row_partition_118, row_partition_119, row_partition_120, row_partition_121, row_partition_122]

theorem residual_eval (f : Mat3 → A) : eval f residual = eval f residualRows.flatten := by
  change eval f ((List.range 128).flatMap residualBucket) = _
  unfold residualBucket
  rw [eval_buckets 128 allRowBuckets row_length_bound]
  have he := congrArg (fun ps : List (Poly Mat3) => (ps.map (eval f)).sum) row_normalizations
  simp only [List.map_map, Function.comp_def, eval_normalize] at he
  simpa only [eval_flatMap, eval_flatten] using he.symm

theorem residual_l1 : intL1 residual = 29562852800 := by
  simp only [residual, intL1_flatten, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bucket_l1_0, bucket_l1_1, bucket_l1_2, bucket_l1_3, bucket_l1_4, bucket_l1_5, bucket_l1_6, bucket_l1_7, bucket_l1_8, bucket_l1_9, bucket_l1_10, bucket_l1_11, bucket_l1_12, bucket_l1_13, bucket_l1_14, bucket_l1_15, bucket_l1_16, bucket_l1_17, bucket_l1_18, bucket_l1_19, bucket_l1_20, bucket_l1_21, bucket_l1_22, bucket_l1_23, bucket_l1_24, bucket_l1_25, bucket_l1_26, bucket_l1_27, bucket_l1_28, bucket_l1_29, bucket_l1_30, bucket_l1_31, bucket_l1_32, bucket_l1_33, bucket_l1_34, bucket_l1_35, bucket_l1_36, bucket_l1_37, bucket_l1_38, bucket_l1_39, bucket_l1_40, bucket_l1_41, bucket_l1_42, bucket_l1_43, bucket_l1_44, bucket_l1_45, bucket_l1_46, bucket_l1_47, bucket_l1_48, bucket_l1_49, bucket_l1_50, bucket_l1_51, bucket_l1_52, bucket_l1_53, bucket_l1_54, bucket_l1_55, bucket_l1_56, bucket_l1_57, bucket_l1_58, bucket_l1_59, bucket_l1_60, bucket_l1_61, bucket_l1_62, bucket_l1_63, bucket_l1_64, bucket_l1_65, bucket_l1_66, bucket_l1_67, bucket_l1_68, bucket_l1_69, bucket_l1_70, bucket_l1_71, bucket_l1_72, bucket_l1_73, bucket_l1_74, bucket_l1_75, bucket_l1_76, bucket_l1_77, bucket_l1_78, bucket_l1_79, bucket_l1_80, bucket_l1_81, bucket_l1_82, bucket_l1_83, bucket_l1_84, bucket_l1_85, bucket_l1_86, bucket_l1_87, bucket_l1_88, bucket_l1_89, bucket_l1_90, bucket_l1_91, bucket_l1_92, bucket_l1_93, bucket_l1_94, bucket_l1_95, bucket_l1_96, bucket_l1_97, bucket_l1_98, bucket_l1_99, bucket_l1_100, bucket_l1_101, bucket_l1_102, bucket_l1_103, bucket_l1_104, bucket_l1_105, bucket_l1_106, bucket_l1_107, bucket_l1_108, bucket_l1_109, bucket_l1_110, bucket_l1_111, bucket_l1_112, bucket_l1_113, bucket_l1_114, bucket_l1_115, bucket_l1_116, bucket_l1_117, bucket_l1_118, bucket_l1_119, bucket_l1_120, bucket_l1_121, bucket_l1_122, bucket_l1_123, bucket_l1_124, bucket_l1_125, bucket_l1_126, bucket_l1_127]
  norm_num

theorem residual_augmentation : augmentation residual = 0 := by
  simp only [residual, augmentation_flatten, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  dsimp only [augmentation]
  rw [bucket_aug_0, bucket_aug_1, bucket_aug_2, bucket_aug_3, bucket_aug_4, bucket_aug_5, bucket_aug_6, bucket_aug_7, bucket_aug_8, bucket_aug_9, bucket_aug_10, bucket_aug_11, bucket_aug_12, bucket_aug_13, bucket_aug_14, bucket_aug_15, bucket_aug_16, bucket_aug_17, bucket_aug_18, bucket_aug_19, bucket_aug_20, bucket_aug_21, bucket_aug_22, bucket_aug_23, bucket_aug_24, bucket_aug_25, bucket_aug_26, bucket_aug_27, bucket_aug_28, bucket_aug_29, bucket_aug_30, bucket_aug_31, bucket_aug_32, bucket_aug_33, bucket_aug_34, bucket_aug_35, bucket_aug_36, bucket_aug_37, bucket_aug_38, bucket_aug_39, bucket_aug_40, bucket_aug_41, bucket_aug_42, bucket_aug_43, bucket_aug_44, bucket_aug_45, bucket_aug_46, bucket_aug_47, bucket_aug_48, bucket_aug_49, bucket_aug_50, bucket_aug_51, bucket_aug_52, bucket_aug_53, bucket_aug_54, bucket_aug_55, bucket_aug_56, bucket_aug_57, bucket_aug_58, bucket_aug_59, bucket_aug_60, bucket_aug_61, bucket_aug_62, bucket_aug_63, bucket_aug_64, bucket_aug_65, bucket_aug_66, bucket_aug_67, bucket_aug_68, bucket_aug_69, bucket_aug_70, bucket_aug_71, bucket_aug_72, bucket_aug_73, bucket_aug_74, bucket_aug_75, bucket_aug_76, bucket_aug_77, bucket_aug_78, bucket_aug_79, bucket_aug_80, bucket_aug_81, bucket_aug_82, bucket_aug_83, bucket_aug_84, bucket_aug_85, bucket_aug_86, bucket_aug_87, bucket_aug_88, bucket_aug_89, bucket_aug_90, bucket_aug_91, bucket_aug_92, bucket_aug_93, bucket_aug_94, bucket_aug_95, bucket_aug_96, bucket_aug_97, bucket_aug_98, bucket_aug_99, bucket_aug_100, bucket_aug_101, bucket_aug_102, bucket_aug_103, bucket_aug_104, bucket_aug_105, bucket_aug_106, bucket_aug_107, bucket_aug_108, bucket_aug_109, bucket_aug_110, bucket_aug_111, bucket_aug_112, bucket_aug_113, bucket_aug_114, bucket_aug_115, bucket_aug_116, bucket_aug_117, bucket_aug_118, bucket_aug_119, bucket_aug_120, bucket_aug_121, bucket_aug_122, bucket_aug_123, bucket_aug_124, bucket_aug_125, bucket_aug_126, bucket_aug_127]
  norm_num
end NuclearUltrapower.SOS
end

end OAI
