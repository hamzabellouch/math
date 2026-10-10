import Mathlib
import OAI.Probability.SKGap.Terminal.TerminalDeterministic
import OAI.Probability.SKGap.Matrix.GOEGlobalEvents

namespace OAI

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

lemma nat_pow_exp_neg_tendsto {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^k*exp (-a*(n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ=>a*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).div_const (a^k)
  simp only [zero_div] at h
  convert h using 1
  ext n
  simp only [Function.comp_apply,mul_pow,neg_mul]
  field_simp

lemma nat_pow_exp_sqrt_tendsto {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^k*exp (-a*sqrt (n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ=>a*sqrt (n:ℝ)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero (2*k)).comp ht).div_const (a^(2*k))
  simp only [zero_div] at h
  convert h using 1
  ext n
  simp only [Function.comp_apply,mul_pow,neg_mul,pow_mul,sq_sqrt (Nat.cast_nonneg n)]
  field_simp

def terminalEntryScale (n : ℕ) : ℝ := 1/sqrt (sqrt (n:ℝ))

lemma terminalEntryScale_nonneg (n : ℕ) : 0 ≤ terminalEntryScale n := by unfold terminalEntryScale;positivity

lemma terminalEntryScale_tendsto : Tendsto terminalEntryScale atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ=>1/sqrt (sqrt (n:ℝ))) atTop (𝓝 0)
  simpa only [one_div,Function.comp_def] using
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp (tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))

lemma terminalEntryScale_sq (n : ℕ) : terminalEntryScale n^2=1/sqrt (n:ℝ) := by
  unfold terminalEntryScale
  rw [div_pow,one_pow,sq_sqrt (sqrt_nonneg _)]

lemma terminalEntryScale_rate {n : ℕ} (hn : 0 < n) : (n:ℝ)*terminalEntryScale n^2=sqrt (n:ℝ) := by
  rw [terminalEntryScale_sq,mul_one_div]
  apply (div_eq_iff (sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne').mpr
  nlinarith only [sq_sqrt (Nat.cast_nonneg n)]
end SKGap

end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set Filter
open scoped BigOperators Topology

variable (j α ε : ℝ) (n : ℕ)
def terminalRowBound : ℝ := 4*j*(log 2+1)

def terminalRawGood (g : MatrixCoordinates (Fin n)→ℝ) : Prop :=
  ‖matrixOperator (goeMatrix (j/(n:ℝ)) g)‖ ≤ 2*sqrt j+1 ∧
  (∀ i,|goeMatrix (j/(n:ℝ)) g i i| ≤ terminalEntryScale n) ∧
  (∀ i k,|coupling (goeDisorder (j/(n:ℝ)) g) i k| ≤ terminalEntryScale n) ∧
  (∀ i,∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2 ≤ terminalRowBound j) ∧
  (∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
    principalOperatorNorm (goeMatrix (j/(n:ℝ)) g) S ≤ ε/3) ∧
  (∀ (i : Fin n) (S : Finset (Fin n)),(S.card:ℝ) ≤ α*(n:ℝ) →
    ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2 ≤ ε)

variable (l : ℝ)
def terminalRawTail : ℝ :=
  2*exp (-(n:ℝ)/(π^2*j))+
  2*(n:ℝ)*exp (-sqrt (n:ℝ)/(8*j))+
  2*(n:ℝ)^2*exp (-sqrt (n:ℝ)/(4*j))+
  (n:ℝ)*exp (-(n:ℝ))+
  2*exp (-(n:ℝ)*(ε^2/(36*π^2*j)-(l*α+log (1+exp (-l)))))+
  (n:ℝ)*exp (-(n:ℝ)*(ε/(4*j)-(l*α+log (1+exp (-l))+α*log 2)))

variable {j α ε n l}
lemma terminalRaw_bad_bound [NeZero n] (hj : 0 < j) (hα : 0 ≤ α) (hε : 0 < ε)
    (hl : 0 ≤ l) (hedge : 2*sqrt (j*α) ≤ ε/6) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real {g | ¬terminalRawGood j α ε n g} ≤
      terminalRawTail j α ε n l := by
  have hn : (0:ℝ) < n := by exact_mod_cast NeZero.pos n
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let E₁ := {g : MatrixCoordinates (Fin n)→ℝ | 2*sqrt j+1 < ‖matrixOperator (goeMatrix (j/(n:ℝ)) g)‖}
  let E₂ := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,terminalEntryScale n < |goeMatrix (j/(n:ℝ)) g i i|}
  let E₃ := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i k,terminalEntryScale n < |coupling (goeDisorder (j/(n:ℝ)) g) i k|}
  let E₄ := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,terminalRowBound j < ∑ k,coupling (goeDisorder (j/(n:ℝ)) g) i k^2}
  let E₅ := {g : MatrixCoordinates (Fin n)→ℝ | ∃ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) ∧ ε/3 < principalOperatorNorm (goeMatrix (j/(n:ℝ)) g) S}
  let E₆ := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,∃ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) ∧ ε < ∑ k∈S,coupling (goeDisorder (j/(n:ℝ)) g) i k^2}
  have he : {g | ¬terminalRawGood j α ε n g}=((((E₁ ∪ E₂) ∪ E₃) ∪ E₄) ∪ E₅) ∪ E₆ := by
    ext g
    simp only [terminalRawGood,E₁,E₂,E₃,E₄,E₅,E₆,Set.mem_union,Set.mem_ofPred_eq,not_and_or,not_forall,not_le,exists_prop,or_assoc]
  have h₁ : μ.real E₁ ≤ 2*exp (-(n:ℝ)/(π^2*j)) := by
    convert goe_norm_tail (ι:=Fin n) hj (by norm_num : (0:ℝ) ≤ 1) using 1 <;> simp [μ,E₁]
  have h₂ : μ.real E₂ ≤ 2*(n:ℝ)*exp (-sqrt (n:ℝ)/(8*j)) := by
    apply (goe_diagonal_tail (ι:=Fin n) (div_pos hj hn) (terminalEntryScale_nonneg n)).trans_eq
    simp only [Fintype.card_fin]
    congr 2
    have hr := terminalEntryScale_rate (NeZero.pos n)
    field_simp
    nlinarith only [hr]
  have h₃ : μ.real E₃ ≤ 2*(n:ℝ)^2*exp (-sqrt (n:ℝ)/(4*j)) := by
    apply (coupling_goe_max_entry_tail hj (terminalEntryScale_nonneg n)).trans_eq
    congr 2
    rw [neg_mul,terminalEntryScale_rate (NeZero.pos n)]
  have h₄ : μ.real E₄ ≤ (n:ℝ)*exp (-(n:ℝ)) := by
    apply (coupling_goe_all_rows_tail (t:=terminalRowBound j) hj).trans_eq
    have heq : terminalRowBound j/(4*j)-log 2=1 := by unfold terminalRowBound;field_simp;ring
    rw [heq,mul_one]
  have h₅ : μ.real E₅ ≤ 2*exp (-(n:ℝ)*(ε^2/(36*π^2*j)-(l*α+log (1+exp (-l))))) := by
    have hd : 2*sqrt (j*α) ≤ (ε/3)/2 := by linarith only [hedge]
    convert goe_sparse_union_tail (ι:=Fin n) hj hα (by positivity : 0 < ε/3) hl hd using 1
    · simp only [Fintype.card_fin]
      rfl
    · simp only [Fintype.card_fin]
      congr 2
      ring
  have h₆ : μ.real E₆ ≤ (n:ℝ)*exp (-(n:ℝ)*(ε/(4*j)-(l*α+log (1+exp (-l))+α*log 2))) :=
    coupling_goe_sparse_rows_tail hj hα hl
  rw [he]
  have hu : μ.real (((((E₁ ∪ E₂) ∪ E₃) ∪ E₄) ∪ E₅) ∪ E₆) ≤
      ((((μ.real E₁+μ.real E₂)+μ.real E₃)+μ.real E₄)+μ.real E₅)+μ.real E₆ := by
    calc
      _ ≤ μ.real ((((E₁ ∪ E₂) ∪ E₃) ∪ E₄) ∪ E₅)+μ.real E₆ := measureReal_union_le _ _
      _ ≤ (μ.real (((E₁ ∪ E₂) ∪ E₃) ∪ E₄)+μ.real E₅)+μ.real E₆ := by gcongr;exact measureReal_union_le _ _
      _ ≤ ((μ.real ((E₁ ∪ E₂) ∪ E₃)+μ.real E₄)+μ.real E₅)+μ.real E₆ := by gcongr;exact measureReal_union_le _ _
      _ ≤ (((μ.real (E₁ ∪ E₂)+μ.real E₃)+μ.real E₄)+μ.real E₅)+μ.real E₆ := by gcongr;exact measureReal_union_le _ _
      _ ≤ _ := by gcongr;exact measureReal_union_le _ _
  exact hu.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅) h₆)
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

def terminalMatrixBound (j : ℝ) : ℝ := 2*sqrt j+2+terminalRowBound j

def terminalMatrixData (M α ε : ℝ) (g : Disorder n) : Prop :=
  (∀ i k,|coupling g i k| ≤ terminalEntryScale n) ∧
  ‖Matrix.of (coupling g)‖ ≤ M ∧ ‖terminalU g‖ ≤ M ∧ ‖terminalQ g‖ ≤ M ∧
  (∀ i,∑ k,tanh (coupling g i k)^4 ≤ M*terminalEntryScale n^2) ∧
  (∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
    principalOperatorNorm (terminalU g) S ≤ ε ∧ principalOperatorNorm (terminalQ g) S ≤ ε)

lemma terminalMatrixData_of_raw {j α ε : ℝ} (hj : 0 < j) (hε : 0 ≤ ε)
    (hn1 : terminalEntryScale n ≤ 1)
    (hns : terminalEntryScale n*(1+terminalRowBound j/3) ≤ 2*ε/3)
    (g : MatrixCoordinates (Fin n)→ℝ) (hg : terminalRawGood j α ε n g) :
    terminalMatrixData (terminalMatrixBound j) α ε (goeDisorder (j/(n:ℝ)) g) := by
  let J := goeDisorder (j/(n:ℝ)) g
  have hR : 0 ≤ terminalRowBound j := by
    unfold terminalRowBound
    have hh : (0:ℝ) ≤ log 2 := log_nonneg (by norm_num)
    positivity
  have hd := terminalEntryScale_nonneg n
  obtain ⟨hG,hdiag,hma,hrow,hsp,hrowS⟩ := hg
  have hJ := coupling_norm_from_goe (j/(n:ℝ)) (terminalEntryScale n) (2*sqrt j+1) g hd hG hdiag
  have hJM : ‖Matrix.of (coupling J)‖ ≤ terminalMatrixBound j := by
    unfold terminalMatrixBound
    change ‖Matrix.of (coupling J)‖ ≤ _ at hJ
    linarith only [hJ,hn1,hR]
  refine ⟨hma,hJM,?_,?_,?_,?_⟩
  · have hrem := tanh_matrix_remainder_norm (Matrix.of (coupling J)) (coupling_symmetric J)
      hR hd hma hrow
    have he : terminalU J=Matrix.of (coupling J)+(terminalU J-Matrix.of (coupling J)) := by abel
    rw [he]
    apply (norm_add_le _ _).trans
    have hm := mul_le_mul_of_nonneg_right hn1 hR
    change ‖terminalU J-Matrix.of (coupling J)‖ ≤ _ at hrem
    change ‖Matrix.of (coupling J)‖ ≤ _ at hJ
    unfold terminalMatrixBound
    nlinarith only [hJ,hrem,hn1,hR,hm]
  · apply (tanh_matrix_Q_norm (Matrix.of (coupling J)) (coupling_symmetric J) hR hrow).trans
    unfold terminalMatrixBound
    have hsq := sqrt_nonneg j
    linarith only [hsq]
  · intro i
    apply (tanh_matrix_fourth_row (Matrix.of (coupling J)) hma hrow i).trans
    have hb : terminalRowBound j ≤ terminalMatrixBound j := by
      unfold terminalMatrixBound
      have hsq := sqrt_nonneg j
      linarith only [hsq]
    calc
      _ ≤ terminalEntryScale n^2*terminalMatrixBound j := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = _ := mul_comm _ _
  · intro S hS
    have hJs := coupling_principal_norm_from_goe (j/(n:ℝ)) (terminalEntryScale n) (ε/3) g S hd (hsp S hS) hdiag
    have hUs := tanh_principal_norm J S hd hR hma hrow hJs
    have hQs := tanh_square_principal_norm J S hε (fun i=>hrowS i S hS)
    constructor
    · change ‖matrixOperator ((terminalU J).submatrix (fun i : S=>i.1) (fun i : S=>i.1))‖ ≤ ε
      rw [matrixOperator_eq_toEuclideanCLM,Matrix.l2_opNorm_toEuclideanCLM]
      change ‖Matrix.of (fun i k : S=>tanh (coupling J i.1 k.1))‖ ≤ ε
      nlinarith only [hUs,hns]
    · change ‖matrixOperator ((terminalQ J).submatrix (fun i : S=>i.1) (fun i : S=>i.1))‖ ≤ ε
      rw [matrixOperator_eq_toEuclideanCLM,Matrix.l2_opNorm_toEuclideanCLM]
      exact hQs

lemma terminalMatrixData_forms {M α ε : ℝ} (g : Disorder n) (hg : terminalMatrixData M α ε g) :
    ∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
      ∀ w : EuclideanSpace ℝ (Fin n),(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalU g) w⟫| ≤ ε*‖w‖^2 ∧
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalQ g) w⟫| ≤ ε*‖w‖^2 := by
  intro S hS w hw
  exact ⟨supported_quad_le_principal _ _ (hg.2.2.2.2.2 S hS).1 w hw,
    supported_quad_le_principal _ _ (hg.2.2.2.2.2 S hS).2 w hw⟩
end SKGap

end
end

end OAI
