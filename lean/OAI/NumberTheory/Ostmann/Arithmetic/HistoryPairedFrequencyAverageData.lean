import OAI.NumberTheory.Ostmann.Arithmetic.PairedFrequencyTreeSumData

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairedFrequencyAverage
open Characters FrequencyTreeSum FrequencyExposure

def LabelsDivide (S : List Bool → Finset (ℤ × ℤ)) (Q : ℕ) :
    {l : ℕ} → {p : List Bool} → Assignment S l p → Prop
  | 0,_,x => x.val.1.natAbs ∣ Q ∧ x.val.2.natAbs ∣ Q
  | _+1,_,x => x.1.val.1.natAbs ∣ Q ∧ x.1.val.2.natAbs ∣ Q ∧
      LabelsDivide S Q x.2.1 ∧ LabelsDivide S Q x.2.2

theorem labelsDivide_mono (S : List Bool → Finset (ℤ × ℤ)) {Q Q' : ℕ}
    (hQ : Q∣Q') {l : ℕ} {p : List Bool} (x : Assignment S l p)
    (hx : LabelsDivide S Q x) : LabelsDivide S Q' x := by
  induction l generalizing p with
  | zero => exact ⟨hx.1.trans hQ,hx.2.trans hQ⟩
  | succ l ih => exact ⟨hx.1.trans hQ,hx.2.1.trans hQ,ih x.2.1 hx.2.2.1,ih x.2.2 hx.2.2.2⟩

def assignmentModulus (S : List Bool → Finset (ℤ × ℤ)) :
    {l : ℕ} → {p : List Bool} → Assignment S l p → ℕ
  | 0,_,x => x.val.1.natAbs*x.val.2.natAbs
  | _+1,_,x => (x.1.val.1.natAbs*x.1.val.2.natAbs)*
      (assignmentModulus S x.2.1*assignmentModulus S x.2.2)

theorem labelsDivide_assignmentModulus (S : List Bool → Finset (ℤ × ℤ))
    {l : ℕ} {p : List Bool} (x : Assignment S l p) :
    LabelsDivide S (assignmentModulus S x) x := by
  induction l generalizing p with
  | zero => exact ⟨dvd_mul_right _ _,dvd_mul_left _ _⟩
  | succ l ih =>
    refine ⟨dvd_mul_of_dvd_left (dvd_mul_right _ _) _,
      dvd_mul_of_dvd_left (dvd_mul_left _ _) _,?_,?_⟩
    · exact labelsDivide_mono S
        ((dvd_mul_right _ _).trans (dvd_mul_left _ _)) x.2.1 (ih x.2.1)
    · exact labelsDivide_mono S
        ((dvd_mul_left _ _).trans (dvd_mul_left _ _)) x.2.2 (ih x.2.2)

theorem assignmentModulus_ne_zero (S : List Bool → Finset (ℤ × ℤ))
    (hS : ∀p s,s∈S p→s.1≠0 ∧ s.2≠0) {l : ℕ} {p : List Bool}
    (x : Assignment S l p) : assignmentModulus S x≠0 := by
  induction l generalizing p with
  | zero =>
    exact mul_ne_zero (Int.natAbs_ne_zero.mpr (hS _ _ x.property).1)
      (Int.natAbs_ne_zero.mpr (hS _ _ x.property).2)
  | succ l ih =>
    exact mul_ne_zero
      (mul_ne_zero (Int.natAbs_ne_zero.mpr (hS _ _ x.1.property).1)
        (Int.natAbs_ne_zero.mpr (hS _ _ x.1.property).2))
      (mul_ne_zero (ih x.2.1) (ih x.2.2))

def localDataForward (S : List Bool → Finset (ℤ × ℤ)) (Q : ℕ) :
    {l : ℕ} → {p : List Bool} → (x : Assignment S l p) →
      LabelsDivide S Q x → List Bool → Data Q
  | 0,_,_,_,_ => PairedFrequencyTreeSum.defaultData Q
  | _+1,_,x,hx,[] => ⟨x.1.val.1,x.1.val.2,(root S x.2.1).1,(root S x.2.2).1,
      (root S x.2.1).2,(root S x.2.2).2,hx.1,hx.2.1⟩
  | _+1,_,x,hx,false::q => localDataForward S Q x.2.1 hx.2.2.1 q
  | _+1,_,x,hx,true::q => localDataForward S Q x.2.2 hx.2.2.2 q

def localData (S : List Bool → Finset (ℤ × ℤ)) (Q : ℕ)
    {l : ℕ} {p : List Bool} (x : Assignment S l p) (hx : LabelsDivide S Q x)
    (q : List Bool) : Data Q := localDataForward S Q x hx q.reverse

theorem localData_left (S : List Bool → Finset (ℤ × ℤ)) (Q : ℕ)
    {l : ℕ} {p : List Bool} (x : Assignment S (l+1) p) (hx : LabelsDivide S Q x)
    (q : List Bool) : localData S Q x hx (q++[false]) =
      localData S Q x.2.1 hx.2.2.1 q := by
  simp [localData,List.reverse_append,localDataForward]

theorem localData_right (S : List Bool → Finset (ℤ × ℤ)) (Q : ℕ)
    {l : ℕ} {p : List Bool} (x : Assignment S (l+1) p) (hx : LabelsDivide S Q x)
    (q : List Bool) : localData S Q x hx (q++[true]) =
      localData S Q x.2.2 hx.2.2.2 q := by
  simp [localData,List.reverse_append,localDataForward]

theorem localData_budget_eq_weight_shift (S : List Bool → Finset (ℤ × ℤ)) (Q : ℕ)
    (C : NNReal) (ε : ℝ) {l : ℕ} {p : List Bool} (x : Assignment S l p)
    (hx : LabelsDivide S Q x) (d : List Bool → Data Q) (r : List Bool)
    (hd : ∀ q, d (q++r)=localData S Q x hx q) :
    ((FrequencyExposure.budget C ε d l r).value:ℝ)=
      weight S (PairedFrequencyTreeSum.factor (C:ℝ) ε) x := by
  induction l generalizing p r with
  | zero => rfl
  | succ l ih =>
    have hleft : ∀ q, d (q++false::r)=localData S Q x.2.1 hx.2.2.1 q := by
      intro q
      calc
        _ = d ((q++[false])++r) := by simp only [List.append_assoc,List.cons_append,List.nil_append]
        _ = localData S Q x hx (q++[false]) := hd _
        _ = _ := localData_left S Q x hx q
    have hright : ∀ q, d (q++true::r)=localData S Q x.2.2 hx.2.2.2 q := by
      intro q
      calc
        _ = d ((q++[true])++r) := by simp only [List.append_assoc,List.cons_append,List.nil_append]
        _ = localData S Q x hx (q++[true]) := hd _
        _ = _ := localData_right S Q x hx q
    have hroot : d r=localData S Q x hx [] := by simpa using hd []
    change ((C:ℝ)*(reducedPair (d r):ℝ)^(ε-1))*
      ((FrequencyExposure.budget C ε d l (false::r)).value:ℝ)*
      ((FrequencyExposure.budget C ε d l (true::r)).value:ℝ)=_
    rw [ih x.2.1 hx.2.2.1 (false::r) hleft,ih x.2.2 hx.2.2.2 (true::r) hright,hroot]
    rfl

theorem localData_budget_eq_weight (S : List Bool → Finset (ℤ × ℤ)) (Q : ℕ)
    (C : NNReal) (ε : ℝ) {l : ℕ} {p : List Bool} (x : Assignment S l p)
    (hx : LabelsDivide S Q x) :
    ((FrequencyExposure.budget C ε (localData S Q x hx) l []).value:ℝ)=
      weight S (PairedFrequencyTreeSum.factor (C:ℝ) ε) x :=
  localData_budget_eq_weight_shift S Q C ε x hx _ [] (fun q=>by rw [List.append_nil])

end Ostmann.Arithmetic.HistoryPairedFrequencyAverage

end

end OAI
