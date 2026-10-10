import OAI.InformationTheory.Entanglement.ReferenceFilter
import OAI.InformationTheory.Entanglement.ChoiTransfer

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {Ω : Type*} [MeasurableSpace Ω]
variable {n r q : Type} [Fintype n] [Fintype r] [Fintype q]
  [DecidableEq n] [DecidableEq r] [DecidableEq q]

structure CPOutcomeLaw (Ω : Type*) [MeasurableSpace Ω] (n : Type) [Fintype n] where
  law : Mat n →ₗ[ℂ] ComplexMeasure Ω
  cp : ∀ s, MeasurableSet s → CP
    ({ toFun := fun A => fun _ _ : Unit => law A s
       map_add' := by intro A B; ext i j; simp only [map_add]; rfl
       map_smul' := by intro c A; ext i j; simp only [map_smul]; rfl } : Map n Unit)
namespace CPOutcomeLaw
variable (L : CPOutcomeLaw Ω n)
def event (s : Set Ω) : Map n Unit where
  toFun A := fun _ _ => L.law A s
  map_add' A B := by ext i j; simp only [map_add]; rfl
  map_smul' c A := by ext i j; simp only [map_smul]; rfl
lemma law_expand (s : Set Ω) (A : Mat n) :
    L.law A s=∑ i, ∑ j, A i j*L.law (Matrix.single i j 1) s := by
  have hm : L.law A=∑ i, ∑ j, A i j • L.law (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum,← map_smul]
    simp
  have he := congrArg (fun c : ComplexMeasure Ω => c s) hm
  simpa only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul] using he
omit [DecidableEq n] in
lemma event_cp {s : Set Ω} (hs : MeasurableSet s) : CP (L.event s) := L.cp s hs

def probe : PositiveMatrixMeasure Ω n where
  entry i j := L.law (Matrix.single i j 1)
  positive s hs := by
    have h := cp_choi (L.event_cp hs)
    apply h.submatrix (fun i : n => (i,()))
lemma probe_value (s : Set Ω) (i j : n) :
    L.probe.value s i j=L.law (Matrix.single i j 1) s := rfl

def reference (R : Mat (n×r)) (hR : R.PosSemidef) : PositiveMatrixMeasure Ω r where
  entry a b := ∑ i, ∑ j, R (i,a) (j,b) • L.law (Matrix.single i j 1)
  positive s hs := by
    have h := L.event_cp hs r (R.submatrix Prod.swap Prod.swap) (hR.submatrix Prod.swap)
    have h' := h.submatrix (fun a : r => (a,()))
    have he : (fun a b => (∑ i, ∑ j, R (i,a) (j,b) • L.law (Matrix.single i j 1)) s)=
        (amplify (L.event s) (R.submatrix Prod.swap Prod.swap)).submatrix
          (fun a : r => (a,())) (fun a : r => (a,())) := by
      ext a b
      simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
      change (∑ i, ∑ j, R (i,a) (j,b)*L.law (Matrix.single i j 1) s)=
        L.law (Matrix.of fun i j => R (i,a) (j,b)) s
      simpa only [Matrix.of_apply] using
        (L.law_expand s (Matrix.of fun i j => R (i,a) (j,b))).symm
    rw [he]
    exact h' 
omit [DecidableEq r] in
lemma reference_value (R : Mat (n×r)) (hR : R.PosSemidef) (s : Set Ω) (a b : r) :
    (L.reference R hR).value s a b=∑ i, ∑ j, R (i,a) (j,b)*L.probe.value s i j := by
  simp only [reference,probe,PositiveMatrixMeasure.value,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]

omit [DecidableEq r] [DecidableEq q] in
lemma reference_filter_value (R : Mat (n×r)) (hR : R.PosSemidef)
    (K : Matrix q r ℂ) (s : Set Ω) (a b : q) :
    ((L.reference R hR).filter K).value s a b=
      ∑ i, ∑ j, (∑ c, ∑ d, K a c*R (i,c) (j,d)*star (K b d))*L.probe.value s i j := by
  rw [PositiveMatrixMeasure.filter_value]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,reference_value,
    Finset.sum_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext c; rw [Finset.sum_comm]; arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  ring
end CPOutcomeLaw
end SecretKey

end

end OAI
