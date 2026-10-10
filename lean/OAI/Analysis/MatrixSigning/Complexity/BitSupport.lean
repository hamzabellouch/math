import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ArithmeticBounds
import OAI.Analysis.MatrixSigning.Optimization.Coordinates

namespace OAI

namespace CurrentKS.RationalBits

def Parts (b : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ 2^b ∧ q.den ≤ 2^b

lemma Parts.mono {b c:ℕ} {q:ℚ} (hq:Parts b q) (hbc:b≤c) : Parts c q :=
  ⟨hq.1.trans (Nat.pow_le_pow_right (by decide) hbc),
    hq.2.trans (Nat.pow_le_pow_right (by decide) hbc)⟩
lemma Parts.mul {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c) (q*r) :=
  KS.W30.mul_parts_le_two_pow q r b c hq.1 hq.2 hr.1 hr.2
lemma Parts.add {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c+1) (q+r) := by
  have h := KS.W30.add_parts_le_two_pow q r b c hq.1 hq.2 hr.1 hr.2
  exact ⟨h.1,h.2.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))⟩
lemma Parts.inv {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b q⁻¹ :=
  KS.W30.inv_parts_le_two_pow q b hq.1 hq.2
lemma Parts.div {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c) (q/r) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv
lemma Parts.neg {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b (-q) := by
  simpa only [Parts,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hq
lemma Parts.abs {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b |q| := by
  rcases le_total 0 q with h|h
  · rwa [abs_of_nonneg h]
  · rw [abs_of_nonpos h]; exact hq.neg
lemma parts_size (q:ℚ) : Parts (q.num.natAbs.size+q.den.size) q := by
  constructor
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (by omega))

variable {ι : Type*}

def LinearBits (f : (ι → ℚ) → ℚ) : Prop :=
  ∃ C:ℕ, 0<C ∧ ∀ b x, (∀i,Parts b (x i)) → Parts (C*(b+1)) (f x)

lemma LinearBits.coordinate (i:ι) : LinearBits (fun x : ι→ℚ => x i) := by
  refine ⟨1,by decide,?_⟩
  intro b x hx
  exact (hx i).mono (by omega)
lemma LinearBits.constant (q:ℚ) : LinearBits (fun _ : ι→ℚ => q) := by
  refine ⟨q.num.natAbs.size+q.den.size+1,by omega,?_⟩
  intro b x hx
  exact (parts_size q).mono (by nlinarith)
lemma LinearBits.add {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => f x+g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D+1,by omega,?_⟩
  intro b x hx
  exact ((hf b x hx).add (hg b x hx)).mono (by nlinarith)
lemma LinearBits.mul {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => f x*g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,by omega,?_⟩
  intro b x hx
  exact ((hf b x hx).mul (hg b x hx)).mono (by nlinarith)
lemma LinearBits.inv {f:(ι→ℚ)→ℚ} (hf:LinearBits f) : LinearBits (fun x => (f x)⁻¹) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C,hC,fun b x hx => (hf b x hx).inv⟩
lemma LinearBits.div {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => f x/g x) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv
lemma LinearBits.abs {f:(ι→ℚ)→ℚ} (hf:LinearBits f) : LinearBits (fun x => |f x|) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C,hC,fun b x hx => (hf b x hx).abs⟩
lemma LinearBits.pow {f:(ι→ℚ)→ℚ} (hf:LinearBits f) (k:ℕ) :
    LinearBits (fun x => (f x)^k) := by
  induction k with
  | zero => simpa only [pow_zero] using LinearBits.constant (ι:=ι) 1
  | succ k ih => simpa only [pow_succ] using ih.mul hf
lemma LinearBits.choose {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g)
    (p:(ι→ℚ)→Prop) [DecidablePred p] : LinearBits (fun x => if p x then f x else g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,by omega,?_⟩
  intro b x hx
  dsimp only
  split_ifs
  · exact (hf b x hx).mono (by nlinarith)
  · exact (hg b x hx).mono (by nlinarith)
lemma LinearBits.min {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => min (f x) (g x)) := by
  simpa only [min_def] using hf.choose hg (fun x => f x≤g x)
lemma LinearBits.max {f g:(ι→ℚ)→ℚ} (hf:LinearBits f) (hg:LinearBits g) :
    LinearBits (fun x => max (f x) (g x)) := by
  simpa only [max_def] using hg.choose hf (fun x => f x≤g x)

end CurrentKS.RationalBits

namespace CurrentKS
open scoped BigOperators
open CurrentKS.RationalBits

lemma frame_length (l : List Bool) : (frame l).length=2*l.length+1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [frame,ih]; omega

lemma payload_length (n : ℕ) : (Computability.encodeNat n).length=n.size := by
  have hp (p : PosNum) : (Computability.encodePosNum p).length=p.natSize := by
    induction p <;> simp_all [Computability.encodePosNum,PosNum.natSize]
  have hn (p : Num) : (Computability.encodeNum p).length=p.natSize := by
    cases p with
    | zero => rfl
    | pos p => exact hp p
  unfold Computability.encodeNat
  rw [hn,Num.natSize_to_nat,Num.to_of_nat]

lemma encodeNat_length (n : ℕ) : (encodeNat n).length=2*n.size+1 := by
  simp [encodeNat,frame_length,payload_length]

lemma int_parts_length (n : ℤ) : Parts (encodeInt n).length (n:ℚ) := by
  have hs : n.natAbs.size ≤ (encodeInt n).length := by
    cases n with
    | ofNat n => simp [encodeInt,encodeNat_length];omega
    | negSucc n =>
      have hlt := Nat.lt_size_self n
      have hpos : 0<2^n.size := pow_pos (by decide) _
      have hn1 : (n+1).size ≤ n.size+1 := by
        apply Nat.size_le.mpr
        rw [pow_succ]
        omega
      simp only [Int.natAbs_negSucc,encodeInt,List.length_cons,encodeNat_length,Nat.succ_eq_add_one]
      omega
  constructor
  · simpa using (Nat.lt_size_self n.natAbs).le.trans
      (Nat.pow_le_pow_right (by decide) hs)
  · simp [Nat.one_le_two_pow]

lemma nat_parts_length (n : ℕ) : Parts (encodeNat n).length (n:ℚ) := by
  have hs : n.size ≤ (encodeNat n).length := by rw [encodeNat_length];omega
  constructor
  · simpa using (Nat.lt_size_self n).le.trans
      (Nat.pow_le_pow_right (by decide) hs)
  · simp [Nat.one_le_two_pow]

lemma RationalEntry.parts_length (a : RationalEntry) : Parts a.encode.length a.value := by
  simpa only [RationalEntry.encode,List.length_append,RationalEntry.value] using
    (int_parts_length a.numerator).div (nat_parts_length a.denominator)

lemma Input.matrix_length (x : Input) (i : Fin x.N) :
    (x.encodeMatrix i).length=1+∑ j,∑ k,(encodeComplex (x.entries i j k)).length := by
  simp [Input.encodeMatrix,List.length_flatten,List.length_flatMap,List.map_ofFn,
    List.sum_ofFn,Function.comp_def,Nat.add_comm]

lemma Input.length_eq (x : Input) :
    x.length=(encodeNat x.d).length+(encodeNat x.N).length+
      ∑ i,(x.encodeMatrix i).length := by
  simp [Input.length,Input.encode,List.length_flatten,List.map_ofFn,List.sum_ofFn,
    Function.comp_def,Nat.add_assoc]

lemma Input.count_le_length (x : Input) : x.N ≤ x.length := by
  have hm : ∀ i,1 ≤ (x.encodeMatrix i).length := by
    intro i;rw [Input.matrix_length];omega
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hm i)
  simp only [Finset.sum_const,Finset.card_fin,smul_eq_mul,mul_one] at hh
  rw [Input.length_eq]
  omega

lemma Input.each_matrix_le_length (x : Input) (i : Fin x.N) :
    (x.encodeMatrix i).length ≤ x.length := by
  have hh := Finset.single_le_sum (f:=fun i => (x.encodeMatrix i).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [Input.length_eq]
  omega

lemma Input.each_complex_le_length (x : Input) (i : Fin x.N) (j k : Fin x.d) :
    (encodeComplex (x.entries i j k)).length ≤ x.length := by
  have h1 := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun k => (encodeComplex (x.entries i j k)).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h2 := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j => ∑ k,(encodeComplex (x.entries i j k)).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hm := x.each_matrix_le_length i
  rw [Input.matrix_length] at hm
  omega

lemma complex_encode_pos (z : RationalComplex) : 1 ≤ (encodeComplex z).length := by
  rcases z with ⟨a,b⟩
  simp only [encodeComplex,RationalEntry.encode,List.length_append]
  have ha : 1 ≤ (encodeNat a.denominator).length := by rw [encodeNat_length];omega
  omega

lemma Input.dimension_le_length (x : Input) (hN : x.N ≠ 0) : x.d ≤ x.length := by
  by_cases hd : x.d=0
  · omega
  let i : Fin x.N := ⟨0,Nat.pos_of_ne_zero hN⟩
  have hrow (j : Fin x.d) : x.d ≤ ∑ k,(encodeComplex (x.entries i j k)).length := by
    simpa using Finset.sum_le_sum (s:=Finset.univ)
      (fun k _ => complex_encode_pos (x.entries i j k))
  let j : Fin x.d := ⟨0,Nat.pos_of_ne_zero hd⟩
  have hj := hrow j
  have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j => ∑ k,(encodeComplex (x.entries i j k)).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hm := x.each_matrix_le_length i
  rw [Input.matrix_length] at hm
  omega

lemma Input.real_parts (x : Input) (i : Fin x.N) (j k : Fin x.d) :
    Parts x.length (x.entries i j k).1.value := by
  apply ((x.entries i j k).1.parts_length).mono
  have hh := x.each_complex_le_length i j k
  simp only [encodeComplex,List.length_append] at hh
  omega

lemma Input.imag_parts (x : Input) (i : Fin x.N) (j k : Fin x.d) :
    Parts x.length (x.entries i j k).2.value := by
  apply ((x.entries i j k).2.parts_length).mono
  have hh := x.each_complex_le_length i j k
  simp only [encodeComplex,List.length_append] at hh
  omega

end CurrentKS

namespace CurrentKS.RationalBits
open scoped BigOperators

lemma parts_zero : Parts 0 (0:ℚ) := by norm_num [Parts]
lemma parts_one : Parts 0 (1:ℚ) := by norm_num [Parts]

lemma sum_parts (n b : ℕ) (f : Fin n → ℚ) (hf : ∀i,Parts b (f i)) :
    Parts (n*(b+1)) (∑ i,f i) := by
  induction n with
  | zero => simpa using parts_zero
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have hh := (hf 0).add (ih (fun i => f i.succ) (fun i => hf i.succ))
    convert hh using 1
    ring

lemma Parts.binary_size {b : ℕ} {q : ℚ} (hq : Parts b q) :
    q.num.natAbs.size+q.den.size ≤ 2*(b+1) := by
  have hb : 2^b<2^(b+1) := by
    rw [pow_succ]
    have hh : 0<2^b := pow_pos (by decide) _
    omega
  have hn := Nat.size_le.mpr (hq.1.trans_lt hb)
  have hd := Nat.size_le.mpr (hq.2.trans_lt hb)
  omega
end CurrentKS.RationalBits

namespace CurrentKS.RationalInput
open CurrentKS.RationalBits
open scoped BigOperators

lemma coordinates_parts (x : Input) (i : Fin x.N) (p : Fin x.d×Fin x.d) :
    Parts x.length (coordinates x i p) := by
  unfold coordinates
  split_ifs
  · exact x.real_parts i _ _
  · exact x.imag_parts i _ _

lemma trace_parts (x : Input) (i : Fin x.N) :
    Parts (x.d*(x.length+1)) (trace x i) := by
  exact sum_parts x.d x.length _ (fun j => x.real_parts i j j)

lemma scale_parts (x : Input) :
    Parts (x.N*(x.d*(x.length+1)+1)) (scale x) := by
  exact sum_parts x.N (x.d*(x.length+1)) _ (fun i => (trace_parts x i).abs)

lemma orientation_parts (x : Input) (i : Fin x.N) : Parts 0 (orientation x i) := by
  unfold orientation
  split_ifs
  · exact parts_one
  · exact parts_one.neg

theorem normalized_parts_input_length (x : Input) (j : Fin (indices x).length)
    (p : Fin x.d×Fin x.d) :
    Parts (x.length*(x.length*(x.length+1)+1)+x.length) (normalizedCoordinates x j p) := by
  have hh := (scale_parts x).inv.mul
    ((orientation_parts x (index x j)).mul (coordinates_parts x (index x j) p))
  change Parts (x.N*(x.d*(x.length+1)+1)+(0+x.length))
    (normalizedCoordinates x j p) at hh
  apply hh.mono
  have hN := x.count_le_length
  have hd := x.dimension_le_length (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) (index x j).isLt))
  simp only [zero_add]
  gcongr

theorem normalized_binary_size (x : Input) (j : Fin (indices x).length)
    (p : Fin x.d×Fin x.d) :
    (normalizedCoordinates x j p).num.natAbs.size+(normalizedCoordinates x j p).den.size ≤
      2*(x.length*(x.length*(x.length+1)+1)+x.length+1) :=
  (normalized_parts_input_length x j p).binary_size
end CurrentKS.RationalInput

end OAI
