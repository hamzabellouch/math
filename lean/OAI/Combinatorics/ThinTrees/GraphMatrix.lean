import OAI.Combinatorics.ThinTrees.Matrix

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
def qform (X : Matrix V V ℝ) (v : V → ℝ) : ℝ := v ⬝ᵥ (X *ᵥ v)
omit [DecidableEq V] in
lemma qform_add (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X+Y) v=qform X v+qform Y v := by
  simp [qform,add_mulVec,dotProduct_add]
omit [DecidableEq V] in
lemma qform_sub (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X-Y) v=qform X v-qform Y v := by
  simp [qform,sub_mulVec,dotProduct_sub]
omit [DecidableEq V] in
lemma qform_smul (a : ℝ) (X : Matrix V V ℝ) (v : V → ℝ) : qform (a • X) v=a*qform X v := by
  simp [qform,smul_mulVec,dotProduct_smul]
omit [DecidableEq V] in
lemma qform_nonneg {X : Matrix V V ℝ} (hX : X.PosSemidef) (v : V → ℝ) : 0 ≤ qform X v := by
  simpa only [qform,star_trivial] using hX.dotProduct_mulVec_nonneg v
omit [DecidableEq V] in
lemma qform_mono {X Y : Matrix V V ℝ} (h : X ≤ Y) (v : V → ℝ) : qform X v ≤ qform Y v := by
  have hh := qform_nonneg (Matrix.le_iff.mp h) v
  rw [qform_sub] at hh
  linarith
omit [DecidableEq V] in
lemma qform_continuous (v : V → ℝ) : Continuous (fun X : Matrix V V ℝ => qform X v) := by
  unfold qform mulVec dotProduct
  fun_prop
lemma qform_single (X : Matrix V V ℝ) (i : V) : qform X (Pi.single i 1)=X i i := by
  simp [qform]
omit [Fintype V] [DecidableEq V] in
lemma posDef_of_le {X Y : Matrix V V ℝ} (hX : X.PosDef) (hXY : X ≤ Y) : Y.PosDef := by
  convert hX.add_posSemidef (Matrix.le_iff.mp hXY) using 1; abel

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
def laplacian (F : Finset (Fin m)) : Matrix (Fin n) (Fin n) ℝ := ∑e ∈ F, vecMulVec (G.incidence e) (G.incidence e)
def resistance (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ := qform X⁻¹ (G.incidence e)
lemma laplacian_psd (F : Finset (Fin m)) : (G.laplacian F).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (G.incidence e)
lemma laplacian_qform (F : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian F) v=∑e ∈ F, (v (G.left e)-v (G.right e))^2 := by
  simp only [laplacian,qform,sum_mulVec,dotProduct_sum,rankOne_quadratic]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm]
  congr 1
  exact G.eval_incidence v e
lemma laplacian_cut (F : Finset (Fin m)) (S : Finset (Fin n)) :
    qform (G.laplacian F) (cutIndicator S)=(G.cut F S).card := by
  rw [G.laplacian_qform]
  simp only [cut,card_eq_sum_ones,Nat.cast_sum,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> simp [cutIndicator,hl,hr]
lemma indicator_norm (S : Finset (Fin n)) : qform (1 : Matrix (Fin n) (Fin n) ℝ) (cutIndicator S)=S.card := by
  simp only [qform,one_mulVec,dotProduct,cutIndicator]
  simp

def baseMatrix : Matrix (Fin n) (Fin n) ℝ := G.laplacian univ+(n:ℝ)⁻¹ • 1
lemma baseMatrix_pd (hn : 0 < n) : G.baseMatrix.PosDef := by
  exact Matrix.PosDef.posSemidef_add (G.laplacian_psd univ) (Matrix.PosDef.one.smul (inv_pos.mpr (Nat.cast_pos.mpr hn)))
lemma baseMatrix_cut (S : Finset (Fin n)) :
    qform G.baseMatrix (cutIndicator S)=(G.cut univ S).card+S.card/(n:ℝ) := by
  rw [baseMatrix,qform_add,qform_smul,G.laplacian_cut,indicator_norm,mul_comm,←div_eq_mul_inv]
lemma resistance_nonneg {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) (e : Fin m) : 0 ≤ G.resistance X e :=
  qform_nonneg hX.inv.posSemidef _
lemma resistance_antitone {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) (hY : Y.PosDef)
    (h : Y ≤ X) (e : Fin m) : G.resistance X e ≤ G.resistance Y e :=
  StrongThinTree.resistance_antitone hX hY (Matrix.le_iff.mp h) _

end MultiGraph
end StrongThinTree

end
end

end OAI
