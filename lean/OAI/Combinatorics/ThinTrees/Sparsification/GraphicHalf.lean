import Mathlib
import OAI.Combinatorics.ThinTrees.Sparsification.GraphicNormalization

namespace OAI

/-! Graphic half. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {n d m : ℕ}

def fullColumns (G : MultiGraph n m) (B : Finset (Fin m)) : Fin m → Fin n → ℚ :=
  fun e => if e ∈ B then qdiff (G.left e) (G.right e) else 0

lemma fullColumns_cast (G : MultiGraph n m) (B : Finset (Fin m)) (e : Fin m) :
    realVec (fullColumns G B) e=if e ∈ B then G.incidence e else 0 := by
  ext i
  by_cases he : e ∈ B
  · simp only [realVec,fullColumns,ite_eq_left he,cast_qinc]
  · simp only [fullColumns,he,ite_false,realVec,Pi.zero_apply,Rat.cast_zero]

lemma fullColumns_gram (G : MultiGraph n m) (B A : Finset (Fin m)) :
    StackedSigning.gram (realVec (fullColumns G B)) A=G.laplacian (A∩B) := by
  simp only [StackedSigning.gram,fullColumns_cast]
  rw [laplacian]
  rw [show A∩B=A.filter (fun e => e ∈ B) by ext; simp]
  rw [sum_filter]
  apply sum_congr rfl
  intro e he
  split_ifs <;> simp only [zero_vecMulVec]

def positiveForm (X : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  X+Matrix.of (fun _ _ => (n:ℚ)⁻¹)

lemma positiveForm_cast (X : Matrix (Fin n) (Fin n) ℚ) :
    (positiveForm X).map (fun q : ℚ => (q:ℝ))=regularize (X.map (fun q : ℚ => (q:ℝ))) := by
  ext i j
  simp only [positiveForm,map_apply,Matrix.add_apply,Rat.cast_add,Matrix.of_apply,Rat.cast_inv,
    Rat.cast_natCast,regularize,constantProjection,Matrix.smul_apply,smul_eq_mul,vecMulVec,ones,mul_one]

def scaledColumns (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :
    Fin m → Fin d → ℚ := fun e => s e • graphColumns G B e

def scaledForm (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :=
  covariance (graphColumns G B) (weights s)

lemma scaledColumns_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (s : Fin m → ℚ) (e : Fin m) :
    realVec (scaledColumns G B s) e=(s e:ℝ) • realColumns (graphColumns G B) e := by
  ext i
  simp only [realVec,scaledColumns,Pi.smul_apply,smul_eq_mul,Rat.cast_mul,realColumns]

lemma scaledForm_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :
    (scaledForm G B s).map (fun q : ℚ => (q:ℝ))=
      covariance (realColumns (graphColumns G B)) (realWeights s) := by
  ext i j
  simp only [scaledForm,covariance,map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    vecMulVec,weights,realColumns,realWeights,Rat.cast_sum,Rat.cast_mul,Rat.cast_pow,Matrix.of_apply]

lemma scaledColumns_gram (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :
    StackedSigning.gram (realVec (scaledColumns G B s)) univ=
      (scaledForm G B s).map (fun q : ℚ => (q:ℝ)) := by
  rw [scaledForm_cast]
  ext i j
  simp only [StackedSigning.gram,scaledColumns_cast,covariance,realWeights,
    Matrix.sum_apply,vecMulVec,Pi.smul_apply,smul_eq_mul,Matrix.smul_apply,Matrix.of_apply]
  apply sum_congr rfl
  intro e _
  ring

lemma scaledColumns_zero (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ)
    (e : Fin m) (he : e ∉ B) : realVec (scaledColumns G B s) e=0 := by
  rw [scaledColumns_cast,graphColumns_cast,ite_eq_right he,smul_zero]

lemma scaledColumns_leverage (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (s : Fin m → ℚ) (e : Fin m) :
    realVec (scaledColumns G B s) e ⬝ᵥ
      (((scaledForm G B s).map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec (scaledColumns G B s) e)=
      leverage (realColumns (graphColumns G B)) (realWeights s) e := by
  rw [scaledColumns_cast,scaledForm_cast]
  simp only [leverage,realWeights,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

def halfEdges (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (X : Matrix (Fin (d+1)) (Fin (d+1)) ℚ) (s : Fin m → ℚ) : Finset (Fin m) :=
  FormSigning.selected (positiveForm X) (scaledForm G B s)
    (fullColumns G B) (scaledColumns G B s) ∩ B

lemma laplacian_mono (G : MultiGraph n m) {A B : Finset (Fin m)} (h : A ⊆ B) :
    G.laplacian A ≤ G.laplacian B := by
  apply sum_le_sum_of_subset_of_nonneg h
  intro e _ _
  exact Matrix.nonneg_iff_posSemidef.mpr (ShortcutDual.outer_posSemidef _)

lemma fullColumns_covariance (G : MultiGraph n m) (B : Finset (Fin m))
    (X : Matrix (Fin n) (Fin n) ℚ) (hX : X.map (fun q : ℚ => (q:ℝ)) ∈ metricDomain G) :
    StackedSigning.gram (realVec (fullColumns G B)) univ ≤
      (positiveForm X).map (fun q : ℚ => (q:ℝ)) := by
  rw [fullColumns_gram,univ_inter,positiveForm_cast]
  apply ((laplacian_mono G (subset_univ B)).trans hX.2.2.1).trans
  exact le_add_of_nonneg_right (Matrix.nonneg_iff_posSemidef.mpr constantProjection_psd)

theorem half_bounds (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (X : Matrix (Fin (d+1)) (Fin (d+1)) ℚ) (s : Fin m → ℚ)
    (hconn : G.Connected univ) (hX : X.map (fun q : ℚ => (q:ℝ)) ∈ metricDomain G)
    (hQ : ((scaledForm G B s).map (fun q : ℚ => (q:ℝ))).PosDef)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnorm : ∀e, realVec (fullColumns G B) e ⬝ᵥ
        (((positiveForm X).map (fun q : ℚ => (q:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e)+
      leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ δ) :
    let A := halfEdges G B X s
    let ε := 20*Real.sqrt (2*δ)
    G.laplacian A ≤ (1/2:ℝ) • G.laplacian B+ε • regularize (X.map (fun q : ℚ => (q:ℝ))) ∧
    (1/2-ε) • (scaledForm G B s).map (fun q : ℚ => (q:ℝ)) ≤
      StackedSigning.gram (realVec (scaledColumns G B s)) A := by
  have hP : ((positiveForm X).map (fun q : ℚ => (q:ℝ))).PosDef := by
    rw [positiveForm_cast]
    exact regularize_pd (by omega) (domain_positive G (by omega) hconn hX)
  obtain ⟨hu,hv⟩ := FormSigning.simultaneous (positiveForm X) (scaledForm G B s) hP hQ
    (fullColumns G B) (scaledColumns G B s) hδ (fullColumns_covariance G B X hX)
    (scaledColumns_gram G B s).le (by simpa only [scaledColumns_leverage] using hnorm)
  simp only [fullColumns_gram,univ_inter,positiveForm_cast] at hu
  rw [scaledColumns_gram] at hv
  dsimp only
  constructor
  · exact (sub_le_iff_le_add.mp hu.2).trans_eq (add_comm _ _)
  · rw [halfEdges,FormSigning.gram_restrict _ B _ (scaledColumns_zero G B s)]
    rw [sub_smul]
    have hh := (le_sub_iff_add_le.mp hv.1)
    simpa only [add_comm,sub_eq_add_neg] using hh

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
