import OAI.Analysis.Laughlin.ThreeBody.PhysicalTrace

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

 theorem realOuter_add_left {I : Type*} (u v w : I → ℝ) :
    realOuter (u+v) w = realOuter u w + realOuter v w := by ext i j; simp [realOuter,add_mul]
 theorem realOuter_add_right {I : Type*} (u v w : I → ℝ) :
    realOuter u (v+w) = realOuter u v + realOuter u w := by ext i j; simp [realOuter,mul_add]
 theorem realOuter_smul_left {I : Type*} (c : ℝ) (u v : I → ℝ) :
    realOuter (c • u) v = c • realOuter u v := by ext i j; simp [realOuter,mul_assoc]
 theorem realOuter_smul_right {I : Type*} (c : ℝ) (u v : I → ℝ) :
    realOuter u (c • v) = c • realOuter u v := by ext i j; simp [realOuter]; ring
 theorem realOuter_list_sum_left {I : Type*} (l : List (I → ℝ)) (v : I → ℝ) :
    realOuter l.sum v = (l.map (fun u => realOuter u v)).sum := by
  induction l with
  | nil => ext i j; simp [realOuter]
  | cons a l ih => simp only [List.sum_cons,List.map_cons,realOuter_add_left,ih]
 theorem realOuter_list_sum_right {I : Type*} (l : List (I → ℝ)) (u : I → ℝ) :
    realOuter u l.sum = (l.map (realOuter u)).sum := by
  induction l with
  | nil => ext i j; simp [realOuter]
  | cons a l ih => simp only [List.sum_cons,List.map_cons,realOuter_add_right,ih]

 theorem source_threeBody_normal3_delta (t p j q l : ℕ) (he : t ≤ p+j) (hf : t ≤ q+l) :
    p+j-t=q+l-t ↔ p+j=q+l := by omega

 theorem source_threeBody_rows_support : ∀ row ∈ Certificate.rows,
    row.1 ≤ 7 ∧ ∀ e ∈ row.2.2, row.1 ≤ e.1+e.2.1 ∧ e.1+e.2.1 ≤ 15 ∧ e.1+e.2.1-row.1 ≤ 8 := by decide

 theorem list_map_ite_sum {I A : Type*} [AddMonoid A] (l : List I) (p : I → Prop)
    [DecidablePred p] (f : I → A) :
    (l.map (fun i => if p i then f i else 0)).sum = ((l.filter p).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h,ih]

 theorem threeBodyLevelVector_filtered (Q t T : ℕ) (entries : List (ℕ × ℕ × ℤ)) :
    threeBodyLevelVector Q t T entries =
      ((entries.filter (fun e => e.1+e.2.1=T)).map
        (fun e => sourceAlpha t e • pairOrbitalUnit Q e.1 e.2.1)).sum := by
  exact list_map_ite_sum _ _ _

theorem source_threeBody_normal3_level_expansion (Q t T : ℕ) (ell : ℤ)
    (entries : List (ℕ × ℕ × ℤ)) :
    threeBodyLevelMatrix Q t T ell entries =
      ((ell : ℝ)/10^7) •
        ((((entries.filter (fun e => e.1+e.2.1=T)).map (fun e =>
          sourceAlpha t e • realOuter (pairOrbitalUnit Q t (T-t)) (pairOrbitalUnit Q e.1 e.2.1))).sum) +
         (((entries.filter (fun e => e.1+e.2.1=T)).map (fun e =>
          sourceAlpha t e • realOuter (pairOrbitalUnit Q e.1 e.2.1) (pairOrbitalUnit Q t (T-t)))).sum)) +
      (((entries.filter (fun e => e.1+e.2.1=T)).map (fun e =>
        (((entries.filter (fun f => f.1+f.2.1=T)).map (fun f =>
          (sourceAlpha t e * sourceAlpha t f) •
            realOuter (pairOrbitalUnit Q e.1 e.2.1) (pairOrbitalUnit Q f.1 f.2.1))).sum))).sum) := by
  unfold threeBodyLevelMatrix
  rw [threeBodyLevelVector_filtered]
  simp_rw [realOuter_list_sum_left,realOuter_list_sum_right,List.map_map,Function.comp_def,
    realOuter_smul_left,realOuter_smul_right,smul_smul]

end Laughlin.Spin

end OAI
