import OAI.Combinatorics.ContingencyTables.Transport.IntegerPropagation
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts

namespace OAI

/-! # Binary integer matrix propagation for exact law tabulation -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

/-- Missing coordinates are zero. The loop runs over the vector's length. -/
def dot (z : List ℕ×List ℕ) : ℕ :=
  ((List.range z.1.length).map (fun i => z.1.getD i 0*z.2.getD i 0)).sum

def entryRealizer : Realizer
    (fun z : (List ℕ×List ℕ)×ℕ => z.1.1.getD z.2 0*z.1.2.getD z.2 0) :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) multiply

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_multiply

def dotRealizer : Realizer dot :=
  composition (f := fun z : List ℕ×List ℕ => (z,List.range z.1.length))
    (g := fun z : (List ℕ×List ℕ)×List ℕ =>
      (z.2.map (fun i => z.1.1.getD i 0*z.1.2.getD i 0)).sum)
    (pair identity (composition (composition first listLength) range))
    (composition (mapWith entryRealizer) listSum)

lemma polynomial_dot : PolynomialTime dotRealizer := by
  unfold dotRealizer
  apply polynomial_composition
  · apply polynomial_pair polynomial_identity
    exact polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength)
      Polynomial.X (fun z => by
        simpa using (list_length_le_weight z.1).trans (weight_fst z))
  · exact polynomial_composition (polynomial_mapWith polynomial_entry) polynomial_listSum

/-- A matrix is stored by columns, so each new coordinate is one dot product. -/
def propagate (z : List (List ℕ)×List ℕ) : List ℕ :=
  z.1.map (fun column => dot (z.2,column))

def propagateRealizer : Realizer propagate :=
  composition (pair second first) (mapWith dotRealizer)

lemma polynomial_propagate : PolynomialTime propagateRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_dot)

private lemma range_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum=∑ i : Fin n,f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.sum_range_succ,Fin.sum_univ_castSucc,ih]
    rfl

lemma dot_ofFn {n : ℕ} (v b : Fin n → ℕ) :
    dot (List.ofFn v,List.ofFn b)=∑ i,v i*b i := by
  unfold dot
  rw [List.length_ofFn,range_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [List.getD_eq_getElem?_getD,i.isLt]

lemma propagate_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (v : Fin n → ℕ) :
    propagate (List.ofFn (fun y => List.ofFn (fun x => B x y)),List.ofFn v)=
      List.ofFn (fun y => ∑ x,v x*B x y) := by
  simp only [propagate,List.map_ofFn,Function.comp_def,dot_ofFn]

/-- One iteration retains the transition table unchanged. -/
def step (z : ℕ×(List (List ℕ)×List ℕ)) : List (List ℕ)×List ℕ :=
  (z.2.1,propagate z.2)

def stepRealizer : Realizer step :=
  pair (composition second first) (composition second propagateRealizer)

lemma polynomial_step : PolynomialTime stepRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_propagate)

def iterate (z : ℕ×(List (List ℕ)×List ℕ)) : List ℕ :=
  (countDown step z.1 z.2).2

def iterateRealizer : Realizer iterate :=
  composition (composition identity (iterateDown stepRealizer)) second

private lemma countDown_table (N : ℕ) (B : List (List ℕ)) (v : List ℕ) :
    (countDown step N (B,v)).1=B := by
  induction N generalizing v with
  | zero => rfl
  | succ N ih => exact ih _

lemma iterate_succ (N : ℕ) (B : List (List ℕ)) (v : List ℕ) :
    iterate (N+1,(B,v))=iterate (N,(B,propagate (B,v))) := rfl

lemma iterate_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (start : Fin n) (N : ℕ) :
    iterate (N,(List.ofFn (fun y => List.ofFn (fun x => B x y)),
      List.ofFn (fun x => if x=start then 1 else 0)))=
      List.ofFn (IntegerPropagation.numerators B start N) := by
  have hi (N : ℕ) (v : Fin n → ℕ) :
      countDown step N (List.ofFn (fun y => List.ofFn (fun x => B x y)),List.ofFn v)=
      (List.ofFn (fun y => List.ofFn (fun x => B x y)),
        List.ofFn ((fun v y => ∑ x,v x*B x y)^[N] v)) := by
    induction N generalizing v with
    | zero => rfl
    | succ N ih =>
      rw [countDown]
      change countDown step N (_,propagate (_,List.ofFn v))=_
      rw [propagate_ofFn,ih,Function.iterate_succ_apply]
  have hn (N : ℕ) : ((fun v y => ∑ x,v x*B x y)^[N]
      (fun x => if x=start then 1 else 0))=IntegerPropagation.numerators B start N := by
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [Function.iterate_succ_apply',ih]
      rfl
  unfold iterate
  rw [hi,hn]

lemma dot_nil (b : List ℕ) : dot ([],b)=0 := by simp [dot]

lemma dot_cons (a : ℕ) (v b : List ℕ) :
    dot (a::v,b)=a*b.headD 0+dot (v,b.tail) := by
  have hzero : b.getD 0 0=b.headD 0 := by cases b <;> rfl
  simp only [dot,List.length_cons,List.sum_range_succ',List.getD_cons_zero]
  rw [hzero]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i _
  cases b <;> simp

lemma dot_le (v b : List ℕ) : dot (v,b) ≤ v.sum*b.sum := by
  induction v generalizing b with
  | nil => simp [dot_nil]
  | cons a v ih =>
    rw [dot_cons]
    cases b with
    | nil => simpa using ih []
    | cons b bs =>
      have hb:=ih bs
      simp only [List.headD_cons,List.tail_cons,List.sum_cons]
      nlinarith [Nat.zero_le (a*bs.sum),Nat.zero_le (v.sum*b)]

def matrixTotal (B : List (List ℕ)) : ℕ := (B.map List.sum).sum

lemma propagate_sum_le (B : List (List ℕ)) (v : List ℕ) :
    (propagate (B,v)).sum ≤ v.sum*matrixTotal B := by
  induction B with
  | nil => simp [propagate,matrixTotal]
  | cons b B ih =>
    have hb:=dot_le v b
    simp only [propagate,List.map_cons,List.sum_cons,matrixTotal] at *
    nlinarith

lemma sum_size_le_weight (v : List ℕ) : v.sum.size ≤ weight v := by
  induction v with
  | nil => simp
  | cons a v ih =>
    have ha:=size_le_weight a
    have hs:=nat_size_add a v.sum
    rw [List.sum_cons,weight_cons]
    have hm : max a.size v.sum.size ≤ weight a+weight v := max_le (by omega) (by omega)
    omega

lemma matrixTotal_size_le_weight (B : List (List ℕ)) : (matrixTotal B).size ≤ weight B := by
  induction B with
  | nil => simp [matrixTotal]
  | cons b B ih =>
    have hb:=sum_size_le_weight b
    have hs:=nat_size_add b.sum (matrixTotal B)
    change (b.sum+matrixTotal B).size ≤ weight (b::B)
    rw [weight_cons]
    have hm : max b.sum.size (matrixTotal B).size ≤ weight b+weight B :=
      max_le (by omega) (by omega)
    omega

lemma pow_size_le (a N : ℕ) : (a^N).size ≤ 1+N*a.size := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs:=nat_size_mul (a^N) a
    rw [pow_succ]
    nlinarith

lemma weight_of_entry_bound (v : List ℕ) (M : ℕ) (h : ∀ a∈v,a.size ≤ M) :
    weight v ≤ v.length*(4*M+2)+1 := by
  have hw:=weight_map_bound (as := v) (f := id) (N := 4*M+1) (by
    intro a ha
    have hs:=h a ha
    have hw:=weight_nat_le a
    simpa using (show weight a ≤ 4*M+1 by omega))
  simpa using hw

/-- The iteration bound uses the number of steps and the binary input size.
The numerical values of the matrix entries never control a loop. -/
theorem work_iterate : WorkBound iterateRealizer
    (fun z => z.1+weight z.2) := by
  unfold iterateRealizer
  apply work_then_polynomial _ polynomial_second
  apply work_boundedRepeat
    (work_of_polynomial polynomial_identity (5*Polynomial.X+3) (by
      intro z
      have hn:=weight_nat_numeric z.1
      rw [←Prod.eta z,weight_prod]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X]
      omega)) polynomial_step Polynomial.X
    (2+Polynomial.X+Polynomial.X*(4*(Polynomial.X+1+Polynomial.X*(Polynomial.X+2))+2))
    (fun z k state => state.1=z.2.1 ∧ state.2.length ≤ z.1+weight z.2 ∧
      state.2.sum ≤ z.2.2.sum*(matrixTotal z.2.1+1)^(z.1-k))
  · intro z
    simp
  · intro z
    refine ⟨rfl,?_,?_⟩
    · have hv:=weight_snd z.2
      exact (list_length_le_weight z.2.2).trans (by omega)
    · simp
  · intro z k hk state hs
    change k<z.1 at hk
    rcases hs with ⟨hB,hlen,hsum⟩
    change state.1=z.2.1 ∧ (propagate state).length ≤ _ ∧ _
    refine ⟨hB,?_,?_⟩
    · simp only [propagate,List.length_map,hB]
      have hB:=weight_fst z.2
      exact (list_length_le_weight z.2.1).trans (by omega)
    · have hp:=propagate_sum_le state.1 state.2
      have hm : matrixTotal state.1  ≤  matrixTotal z.2.1+1 := by rw [hB]; omega
      have hb:=Nat.mul_le_mul hsum hm
      have he : z.1-k=(z.1-(k+1))+1 := by omega
      calc
        (propagate state).sum ≤ state.2.sum*matrixTotal state.1 := hp
        _ ≤ (z.2.2.sum*(matrixTotal z.2.1+1)^(z.1-(k+1)))*(matrixTotal z.2.1+1) := hb
        _=z.2.2.sum*(matrixTotal z.2.1+1)^(z.1-k) := by rw [he,pow_succ]; ac_rfl
  · intro z k state hs
    rcases hs with ⟨hB,hlen,hsum⟩
    let S:=z.1+weight z.2
    change state.2.length ≤ S at hlen
    have hN : z.1-k ≤ S := by dsimp [S]; omega
    have hBweight : weight z.2.1 ≤ S := (weight_fst z.2).trans (by dsimp [S]; omega)
    have hvweight : weight z.2.2 ≤ S := (weight_snd z.2).trans (by dsimp [S]; omega)
    have hQ : (matrixTotal z.2.1+1).size ≤ S+2 := by
      have hm:=matrixTotal_size_le_weight z.2.1
      have ha:=nat_size_add (matrixTotal z.2.1) 1
      norm_num at ha
      have hh : max (matrixTotal z.2.1).size 1 ≤ S+1 := max_le (by omega) (by omega)
      omega
    have hv : z.2.2.sum.size ≤ S := (sum_size_le_weight z.2.2).trans hvweight
    have hsbit : state.2.sum.size ≤ S+1+S*(S+2) := by
      have hm:=Nat.size_le_size hsum
      have hm':=nat_size_mul z.2.2.sum ((matrixTotal z.2.1+1)^(z.1-k))
      have hp:=pow_size_le (matrixTotal z.2.1+1) (z.1-k)
      have hn:=Nat.mul_le_mul hN hQ
      omega
    have ha : ∀ a∈state.2,a.size ≤ S+1+S*(S+2) := by
      intro a ha
      exact (Nat.size_le_size (List.single_le_sum (fun _ _ => Nat.zero_le _) _ ha)).trans hsbit
    have hw:=weight_of_entry_bound state.2 (S+1+S*(S+2)) ha
    have hm:=Nat.mul_le_mul_right (4*(S+1+S*(S+2))+2) hlen
    change weight state ≤ _
    rw [←Prod.eta state,weight_prod,hB]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    change 1+weight z.2.1+weight state.2 ≤ 2+S+S*(4*(S+1+S*(S+2))+2)
    omega

end ContingencyTables.IntegerMatrixPrograms

end OAI
