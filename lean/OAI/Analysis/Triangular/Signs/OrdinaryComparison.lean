import OAI.Analysis.Triangular.Signs.Signs00
import OAI.Analysis.Triangular.Signs.Signs01
import OAI.Analysis.Triangular.Signs.Signs02
import OAI.Analysis.Triangular.Signs.Signs03
import OAI.Analysis.Triangular.Signs.Signs04
import OAI.Analysis.Triangular.Signs.Signs05
import OAI.Analysis.Triangular.Signs.Signs06
import OAI.Analysis.Triangular.Signs.Signs10
import OAI.Analysis.Triangular.Signs.Signs11
import OAI.Analysis.Triangular.Signs.Signs12
import OAI.Analysis.Triangular.Signs.Signs13
import OAI.Analysis.Triangular.Signs.Signs14
import OAI.Analysis.Triangular.Signs.Signs15
import OAI.Analysis.Triangular.Signs.Signs16
import OAI.Analysis.Triangular.Signs.DeletedAccuracy
import OAI.Analysis.Triangular.Signs.GaussianDeleted

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma near_positive_polynomial (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    nearError n y < finiteTaylor 1 (nearNode n) (nearDisplacement n y) e τ := by
  fin_cases n <;> fin_cases y
  · have hh := ordinary_sign_1_0_0 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_0_1 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_1_0 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_1_1 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_2_0 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_2_1 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_3_0 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_3_1 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_4_0 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_4_1 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_5_0 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_5_1 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_6_0 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_1_6_1 e he hτ
    change _ < finiteTaylor 1 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
lemma near_negative_polynomial (e : Fin 8 → ℝ) (he : ParameterPolytope e)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    nearError n y < (∑ r : Fin 8,ordinaryOffset n r*e r)-
      finiteTaylor 0 (nearNode n) (nearDisplacement n y) e τ := by
  fin_cases n <;> fin_cases y
  · have hh := ordinary_sign_0_0_0 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 0 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · exact False.elim (hne ⟨rfl,rfl⟩)
  · have hh := ordinary_sign_0_1_0 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 1 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_1_1 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 1 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_2_0 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 2 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_2_1 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 2 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_3_0 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 3 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_3_1 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 3 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_4_0 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 4 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_4_1 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 4 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_5_0 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 5 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_5_1 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 5 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_6_0 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 6 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
  · have hh := ordinary_sign_0_6_1 e he hτ
    change _ < (∑ r : Fin 8,ordinaryOffset 6 r*e r)-finiteTaylor 0 _ _ e τ at hh
    exact lt_trans (by norm_num [nearError]) hh
lemma ordinaryOffset_actual (n : Fin 7) (z : ℝ) :
    (∑ r : Fin 8,ordinaryOffset n r*actualParameter z r)=
      if n.val=0 then Q 1/(2*Z) else if n.val=1 then (4/5)*Q 1*Real.exp (-2/z) else 0 := by
  fin_cases n <;> norm_num [ordinaryOffset,actualParameter,Fin.sum_univ_succ]
lemma gaussian_ordinary_lower {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    (∑ r : Fin 8,ordinaryOffset n r*actualParameter z r) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  rw [ordinaryOffset_actual]
  by_cases hn0 : n=0
  · subst n
    have hy : y=0 := by fin_cases y <;> simp_all
    subst y
    norm_num [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum]
    have hh := gaussian_deleted_left (m:=1) hz (neg_nonpos.mpr hτ.1)
    norm_num at hh
    have hd := div_le_div_of_nonneg_left Q_one_pos.le (show 0<2*z by positivity) (show 2*z ≤ 2*Z by linarith)
    exact hd.trans hh
  · have hnval : n.val≠0 := by exact fun hh => hn0 (Fin.ext hh)
    simp only [hnval,ite_false]
    by_cases hn1 : n=1
    · subst n
      simp only [Fin.val_one,ite_true]
      have hv : nearDisplacement 1 y*τ ≤ 1/2 := by
        fin_cases y <;> norm_num[nearDisplacement,nearDisplacementNum] <;> nlinarith [hτ.1,hτ.2]
      have hh := gaussian_deleted_three hz hzB hv
      convert hh using 1
      norm_num [nearNode,finiteNode,residue]
    · have hnval1 : n.val≠1 := by exact fun hh => hn1 (Fin.ext hh)
      simp only [hnval1,ite_false]
      exact gaussian_deleted_nonneg hz _ _
lemma near_positive_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    0 ≤ deletedSecond (actualJ 1 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  have hh := near_positive_polynomial (actualParameter z) (actualParameter_mem hz hzB) n y hτ
  have he := (abs_lt.mp (deleted_accuracy 1 hz hzB n y hτ)).1
  linarith
lemma near_ordinary_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  have hh := near_negative_polynomial (actualParameter z) (actualParameter_mem hz hzB) n y hne hτ
  have he := (abs_lt.mp (deleted_accuracy 0 hz hzB n y hτ)).2
  have hg := gaussian_ordinary_lower hz hzB n y hne hτ
  linarith
end AtomicTriangular.Construction
end

end OAI
