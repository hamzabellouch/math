import Mathlib
import OAI.Combinatorics.KMedian.Compression.CompressionListStep
import OAI.Combinatorics.KMedian.Binary.BinaryIntegerHeight

namespace OAI


                                              
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Finset Polynomial

def lawStep {n d : ℕ} (v : Fin n → Fin d → ℤ) (μ : IntegerLaw (Fin n)) : IntegerLaw (Fin n) :=
  if h : d+1 < μ.support.card then compressionStepAuto μ v h else μ

theorem input_iterate (I : Input) (t : ℕ) :
    Input.step^[t] I=⟨I.n,I.d,(lawStep I.v)^[t] I.μ,I.v⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
      rfl

theorem lawStep_denominator {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j|≤(2:ℤ)^L) :
    (lawStep v μ).denominator ≤ μ.denominator*(2:ℤ)^((2*(d+1)*(d+1+L))*(n+1)) := by
  unfold lawStep
  split_ifs with h
  · rw [compressionStepAuto_eq μ v L hv h]
    exact (compressionStep_spec μ v L hv h).1
  · exact le_mul_of_one_le_right μ.denominator_pos.le (one_le_pow₀ (by norm_num))

theorem iterate_denominator {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j|≤(2:ℤ)^L) (hμ : μ.denominator≤(2:ℤ)^L) (t : ℕ) :
    ((lawStep v)^[t] μ).denominator ≤ (2:ℤ)^(L+((2*(d+1)*(d+1+L))*(n+1))*t) := by
  induction t with
  | zero => simpa using hμ
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      apply (lawStep_denominator _ v L hv).trans
      apply (mul_le_mul_of_nonneg_right ih (by positivity)).trans
      rw [← pow_add]
      have he : L+((2*(d+1)*(d+1+L))*(n+1))*t+((2*(d+1)*(d+1+L))*(n+1))=
          L+((2*(d+1)*(d+1+L))*(n+1))*(t+1) := by ring
      rw [he]

theorem input_bounds (I : Input) :
    I.n≤I.encode.length ∧ I.d≤I.encode.length ∧
    I.μ.denominator≤(2:ℤ)^I.encode.length ∧ ∀ i j, |I.v i j|≤(2:ℤ)^I.encode.length := by
  let L := I.encode.length
  have hl : L=2*I.d+1+2*(ListPivot.el I.lawData).length+1+(em I.features).length := by
    simp only [L,Input.raw,encodePair_length,Gaussian.ListOperation.slots_size]
    omega
  have hn := EncodedList.length_le Signed.encode (List.ofFn I.μ.numerator)
  simp only [List.length_ofFn] at hn
  have hlaw : (ListPivot.el I.lawData).length=2*(Signed.encode I.μ.denominator).length+1+(er (List.ofFn I.μ.numerator)).length := by
    simp only [Input.lawData,ListPivot.el,encodePair_length]
  refine ⟨by change I.n≤L; change I.n≤(er (List.ofFn I.μ.numerator)).length at hn; omega,by change I.d≤L; omega,?_,?_⟩
  · have hlen : (Signed.encode I.μ.denominator).length≤L := by omega
    exact (le_abs_self _).trans ((Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) hlen))
  · intro i j
    have hrow : List.ofFn (I.v i)∈I.features := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hcol : I.v i j∈List.ofFn (I.v i) := List.mem_ofFn.mpr ⟨j,rfl⟩
    have h1 := EncodedList.member_length Signed.encode (List.ofFn (I.v i)) _ hcol
    have h2 := EncodedList.member_length er I.features _ hrow
    change (Signed.encode (I.v i j)).length≤(er (List.ofFn (I.v i))).length at h1
    change (er (List.ofFn (I.v i))).length≤(em I.features).length at h2
    exact (Signed.height_length _).trans (pow_le_pow_right₀ (by norm_num) (by omega))

def height (L : ℕ) := L+(2*(L+1)*(L+1+L)*(L+1))*L
noncomputable def heightPolynomial : Polynomial ℕ := X+(2*(X+1)*(X+1+X)*(X+1))*X
noncomputable def statePolynomial : Polynomial ℕ := 3*X+2+2*(X+1)*(2*heightPolynomial+9)

theorem heightPolynomial_eval (L : ℕ) : heightPolynomial.eval L=height L := by
  simp only [heightPolynomial,height,eval_add,eval_mul,eval_X,eval_ofNat,eval_one]

theorem statePolynomial_eval (L : ℕ) :
    statePolynomial.eval L=3*L+2+2*(L+1)*(2*height L+9) := by
  simp only [statePolynomial,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,heightPolynomial_eval]

theorem Input.encode_length (I : Input) : I.encode.length =
    2*I.d+1+(2*(2*(Signed.encode I.μ.denominator).length+1+
      (er (List.ofFn I.μ.numerator)).length)+1+(em I.features).length) := by
  simp only [Input.encode,Input.raw,Input.lawData,ed,el,ListPivot.el,encodePair_length,
    Gaussian.ListOperation.slots_size]

theorem size_arithmetic (L d den num feat H : ℕ) (hd : d≤L) (hden : den≤H+4)
    (hnum : num≤L*(2*(H+4)+1)) (hfeat : feat≤L) :
    2*d+1+(2*(2*den+1+num)+1+feat)≤3*L+2+2*(L+1)*(2*H+9) := by
  nlinarith

theorem state_size (I : Input) (t : ℕ) (ht : t≤I.n) :
    (Input.encode (Input.step^[t] I)).length≤ statePolynomial.eval I.encode.length := by
  let L := I.encode.length
  let ν := (lawStep I.v)^[t] I.μ
  obtain ⟨hn,hd,hμ,hv⟩ := input_bounds I
  have hν : ν.denominator≤(2:ℤ)^(height L) := by
    apply (iterate_denominator I.μ I.v L hv hμ t).trans
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [height]
    gcongr
    exact ht.trans hn
  have hden : (Signed.encode ν.denominator).length≤height L+4 :=
    Signed.length_height (by rwa [abs_of_pos ν.denominator_pos])
  have hnum : (er (List.ofFn ν.numerator)).length ≤ L*(2*(height L+4)+1) := by
    apply (EncodedList.length_bound Signed.encode (List.ofFn ν.numerator) (height L+4) ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*(height L+4)+1) hn
    · intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      apply Signed.length_height
      rw [abs_of_nonneg (ν.numerator_nonneg i)]
      exact (ν.numerator_le i).trans hν
  have hfeat : (em I.features).length≤L := by
    simp only [L,Input.raw,encodePair_length]
    omega
  rw [input_iterate,Input.encode_length,statePolynomial_eval]
  exact size_arithmetic L I.d (Signed.encode ν.denominator).length
    (er (List.ofFn ν.numerator)).length (em I.features).length (height L) hd hden hnum hfeat

theorem compressSteps_eq_iterate {n d : ℕ} (v : Fin n → Fin d → ℤ) (t : ℕ) (μ : IntegerLaw (Fin n)) :
    compressStepsAuto v t μ=(lawStep v)^[t] μ := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
      rw [compressStepsAuto,Function.iterate_succ_apply]
      split_ifs with h
      · rw [show lawStep v μ=compressionStepAuto μ v h from dite_eq_left h,ih]
      · have he : lawStep v μ=μ := dite_eq_right h
        rw [he,Function.iterate_fixed he]

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
