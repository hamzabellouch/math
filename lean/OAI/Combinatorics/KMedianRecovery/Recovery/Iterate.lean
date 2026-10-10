import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CommonDen
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthPolynomial

namespace OAI

namespace MetricKMedianRecovery.BirdRationalIteration
open Matrix RationalHeight
open scoped BigOperators

def iterate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (t : ℕ) :=
  (BirdDet.Spec.stepEntry A)^[t] A
lemma iterate_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : iterate A 0=A := rfl
lemma iterate_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (t : ℕ) :
    iterate A (t+1)=BirdDet.Spec.stepEntry A (iterate A t) := by
  exact Function.iterate_succ_apply' ..
lemma step_smul {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℚ) (c d : ℚ) :
    BirdDet.Spec.stepEntry (c • A) (d • F)=(c*d) • BirdDet.Spec.stepEntry A F := by
  ext i j
  have hs : (∑ k∈Finset.Ioi i,(d*F i k)*(c*A k j))=
      (c*d)*∑ k∈Finset.Ioi i,F i k*A k j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [BirdDet.Spec.stepEntry_eq,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
    ←Finset.mul_sum,hs]
  ring
lemma iterate_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (t : ℕ) :
    iterate (c • A) t=c^(t+1) • iterate A t := by
  induction t with
  | zero => simp only [iterate_zero,Nat.zero_add,pow_one]
  | succ t ih =>
    rw [iterate_succ,ih,step_smul,iterate_succ]
    congr 1
    simp only [pow_succ]
    ring
lemma step_cast {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) :
    (BirdDet.Spec.stepEntry A F).map (Int.cast : ℤ→ℚ)=
      BirdDet.Spec.stepEntry (A.map (Int.cast : ℤ→ℚ)) (F.map (Int.cast : ℤ→ℚ)) := by
  ext i j
  simp only [Matrix.map_apply,BirdDet.Spec.stepEntry_eq,Matrix.of_apply,Int.cast_add,
    Int.cast_mul,Int.cast_neg,Int.cast_sum]
lemma iterate_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) :
    (BirdInteger.iterate A t).map (Int.cast : ℤ→ℚ)=iterate (A.map (Int.cast : ℤ→ℚ)) t := by
  induction t with
  | zero => simp only [BirdInteger.iterate,BirdInteger.freeze_eq,iterate_zero]
  | succ t ih =>
    simp only [BirdInteger.iterate,BirdInteger.freeze_eq,step_cast,ih,iterate_succ]

def flat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Fin n×Fin n → ℚ := fun p=>A p.1 p.2
def integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j=>BirdRational.scaled (flat A) (i,j)
lemma integral_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (integral A).map (Int.cast : ℤ→ℚ)=(BirdRational.commonDen (flat A):ℚ) • A := by
  ext i j
  exact BirdRational.scaled_cast (flat A) (i,j)
lemma commonDen_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j,Height (A i j) a) :
    (BirdRational.commonDen (flat A)).natAbs≤2^((n*n)*a) := by
  unfold BirdRational.commonDen
  rw [show (∏ i,((flat A i).den:ℤ)).natAbs=∏ i,((flat A i).den:ℤ).natAbs from map_prod Int.natAbsHom _ _]
  calc
    _ ≤ ∏ _p : Fin n×Fin n,2^a := Finset.prod_le_prod (fun p _=>by
      simpa only [Int.natAbs_natCast,flat] using (hA p.1 p.2).2)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,←pow_mul]; congr 1; ring

lemma iterate_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j,Height (A i j) a) (t : ℕ) (i j : Fin n) :
    Height (iterate A t i j) ((t+1)*((2*n*n+1)*a)+t*(n+1)) := by
  let Z := integral A
  let D := BirdRational.commonDen (flat A)
  have hD : (D:ℚ)≠0 := by exact_mod_cast (BirdRational.commonDen_pos (flat A)).ne'
  have hZ : ∀ i j,(Z i j).natAbs≤2^((n*n+1)*a) := by
    intro i j
    simpa only [Fintype.card_prod,Fintype.card_fin,Z,integral] using
      BirdRational.scaled_height (flat A) a (fun p=>hA p.1 p.2) (i,j)
  have hi := BirdInteger.iterate_height Z hZ t i j
  have he : ((BirdInteger.iterate Z t i j:ℤ):ℚ)=(D:ℚ)^(t+1)*iterate A t i j := by
    have hh := congrFun (congrFun (iterate_cast Z t) i) j
    rw [show Z.map (Int.cast : ℤ→ℚ)=(D:ℚ) • A from integral_cast A,iterate_smul] at hh
    exact hh
  have hf : iterate A t i j=((BirdInteger.iterate Z t i j:ℤ):ℚ)/(D:ℚ)^(t+1) := by
    rw [he,mul_div_cancel_left₀ _ (pow_ne_zero _ hD)]
  rw [hf]
  have hnum := BirdRational.intCast_height (BirdInteger.iterate Z t i j) _ hi
  have hden := (BirdRational.intCast_height D _ (commonDen_height A hA)).pow (t+1)
  convert hnum.div hden using 1; ring
def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 1
  | n+1, A => (-1)^n * iterate A n 0 0
lemma determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : determinant A=A.det := by
  rw [←BirdInteger.spec_eq_det]
  cases n with
  | zero => rfl
  | succ k => simp only [determinant,BirdDet.Spec.birdDetSpec_succ,iterate]
end MetricKMedianRecovery.BirdRationalIteration
namespace MetricKMedianRecovery.RationalHeight
lemma list_sum (xs : List ℚ) (b : ℕ) (hx : ∀ q∈xs,Height q b) :
    Height xs.sum (xs.length*(b+1)) := by
  induction xs with
  | nil => simpa using zero 0
  | cons x xs ih =>
    simp only [List.sum_cons,List.length_cons]
    have hh := (hx x (by simp)).add (ih (fun q hq=>hx q (by simp [hq])))
    convert hh using 1; ring
end MetricKMedianRecovery.RationalHeight

end OAI
