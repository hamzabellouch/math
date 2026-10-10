import OAI.Analysis.Pureness.Quasitrace.PositiveQuasitrace
import OAI.Analysis.Pureness.Quasitrace.QuasitracePullback
import OAI.Analysis.Pureness.Cuntz.MatrixSimplicity
import OAI.Analysis.Pureness.Stabilization.MatrixEntries

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma PositiveQuasitrace.sum_commute {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (T : PositiveQuasitrace D) {κ : Type*} (s : Finset κ) (a : κ → Positive D)
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (a i).1 (a j).1) :
    T ⟨∑ i ∈ s, (a i).1, Finset.sum_nonneg fun i _ => (a i).2⟩ = ∑ i ∈ s, T (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact T.map_zero
  | @insert i s hi ih =>
    have he : (⟨∑ j ∈ insert i s, (a j).1, Finset.sum_nonneg fun j _ => (a j).2⟩ : Positive D) =
        Positive.add (a i) ⟨∑ j ∈ s, (a j).1, Finset.sum_nonneg fun j _ => (a j).2⟩ :=
      Subtype.ext (Finset.sum_insert hi)
    rw [he,T.map_add_commute,ih,Finset.sum_insert hi]
    · exact fun j hj k hk => hc j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    · exact Commute.sum_right s (fun j => (a j).1) (a i).1
        (fun j hj => hc i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj))

lemma positiveQuasitrace_matrixCorner_eq (T : PositiveQuasitrace (CStarMatrix ι ι A))
    (i j : ι) (a : Positive A) :
    T (Positive.map (matrixCorner i) a) = T (Positive.map (matrixCorner j) a) := by
  let w := singleMatrix i j (CFC.sqrt a.1)
  have hs : star w = singleMatrix j i (CFC.sqrt a.1) := by
    change CStarMatrix.ofMatrix (Matrix.single i j (CFC.sqrt a.1)).conjTranspose = _
    rw [Matrix.conjTranspose_single,(CFC.sqrt_nonneg a.1).star_eq]
    rfl
  have hl : Positive.starMul w = Positive.map (matrixCorner j) a := by
    apply Subtype.ext
    change star w*w = singleMatrix j j a.1
    rw [hs,singleMatrix_mul_same,CFC.sqrt_mul_sqrt_self a.1 a.2]
  have hr : Positive.mulStar w = Positive.map (matrixCorner i) a := by
    apply Subtype.ext
    change w*star w = singleMatrix i i a.1
    rw [hs,singleMatrix_mul_same,CFC.sqrt_mul_sqrt_self a.1 a.2]
  exact ((congrArg T.toFun hl).symm.trans ((T.polar w).trans (congrArg T.toFun hr))).symm

lemma positiveQuasitrace_scalarMatrix (T : PositiveQuasitrace (CStarMatrix ι ι A))
    (i : ι) (a : Positive A) :
    T (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) =
      (Fintype.card ι : ℝ)*T (Positive.map (matrixCorner i) a) := by
  let p (j : ι) : Positive (CStarMatrix ι ι A) := Positive.map (matrixCorner j) a
  have he : Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a =
      (⟨∑ j, (p j).1, Finset.sum_nonneg fun j _ => (p j).2⟩ : Positive (CStarMatrix ι ι A)) :=
    Subtype.ext (scalarMatrix_eq_sum_single a.1)
  rw [he,T.sum_commute]
  · simp only [p,positiveQuasitrace_matrixCorner_eq T _ i a,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul]
  · intro j _ k _
    by_cases hjk : j=k
    · subst k; exact Commute.refl _
    · change singleMatrix j j a.1 * singleMatrix k k a.1 = singleMatrix k k a.1 * singleMatrix j j a.1
      rw [singleMatrix_mul_ne _ _ _ _ hjk,singleMatrix_mul_ne _ _ _ _ (Ne.symm hjk)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrixInclusion_scalar_one (n : ℕ) (x : A) :
    matrixInclusion (show 1 ≤ n+1 from by omega) (scalarMatrixHom (ι := Fin 1) x) =
      matrixCorner (0 : Fin (n+1)) x := by
  apply CStarMatrix.ext
  intro i j
  by_cases hi : i=0 <;> by_cases hj : j=0
  · subst i; subst j
    exact matrixInclusion_entry_inside (show 1 ≤ n+1 from by omega)
      (scalarMatrixHom (ι := Fin 1) x) (0 : Fin 1) (0 : Fin 1)
  · subst i
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    rw [matrixInclusion_entry_outside (show 1 ≤ n+1 from by omega)
      (scalarMatrixHom (ι := Fin 1) x) 0 j (Or.inr (by omega))]
    simp [matrixCorner,Matrix.single,Ne.symm hj]
  · subst j
    have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [matrixInclusion_entry_outside (show 1 ≤ n+1 from by omega)
      (scalarMatrixHom (ι := Fin 1) x) i 0 (Or.inl (by omega))]
    simp [matrixCorner,Matrix.single,Ne.symm hi]
  · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
    rw [matrixInclusion_entry_outside (show 1 ≤ n+1 from by omega)
      (scalarMatrixHom (ι := Fin 1) x) i j (Or.inl (by omega))]
    simp [matrixCorner,Matrix.single,Ne.symm hi,Ne.symm hj]

variable (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
variable (hlsc : ∀ n, LowerSemicontinuous (fun a : Positive (FinMatrix A n) => d (finitePositiveClass n a)))
variable (hfinite : ∀ x, d x ≠ ⊤)

lemma finiteSpectralPositiveQuasitrace_scalarMatrix (n : ℕ) (a : Positive A) :
    finiteSpectralPositiveQuasitrace d hd hlsc hfinite (n+1)
      (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) =
        (n+1 : ℝ)*finiteSpectralPositiveQuasitrace d hd hlsc hfinite 1
          (Positive.map scalarMatrixHom.toNonUnitalStarAlgHom a) := by
  rw [positiveQuasitrace_scalarMatrix _ (0 : Fin (n+1)) a]
  have he : Positive.map (matrixCorner (0 : Fin (n+1))) a =
      Positive.map (matrixInclusion (show 1 ≤ n+1 from by omega))
        (Positive.map (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom a) :=
    Subtype.ext (matrixInclusion_scalar_one n a.1).symm
  rw [he,finiteSpectralPositiveQuasitrace_inclusion]
  simp
end CuntzPureness

end

end OAI
