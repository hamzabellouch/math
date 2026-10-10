import Mathlib
import OAI.Probability.ParisiFinite.SecondCoefficient

namespace OAI

/-! Reverse Word. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open Filter
namespace TensorWordGram
open QuantumCLT CoherentFock

variable {κ : Type*}
def reverseWord (neg : κ → κ) (w : List κ) : List κ := w.reverse.map neg

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [StarRing A] [ContinuousStar A] [StarModule ℂ A]

omit [StarRing A] [ContinuousStar A] [StarModule ℂ A] in
theorem generators_append (X : κ → A) (u w : List κ) (r : ℝ) :
    generators ((u++w).map X) r=generators (u.map X) r*generators (w.map X) r := by
  simp [generators]

 
theorem generators_star (neg : κ → κ) (X : κ → A)
    (hn : ∀i,X (neg i)= -X i) (hs : ∀i,star (X i)= -X i) (w : List κ) (r : ℝ) :
    star (generators (w.map X) r)=generators ((reverseWord neg w).map X) r := by
  induction w with
  | nil => simp [generators,reverseWord]
  | cons i w ih =>
    simp only [generators,List.map_cons,List.prod_cons,star_mul,NormedSpace.star_exp,
      star_smul,Complex.star_def,Complex.conj_ofReal,hs]
    change star (generators (w.map X) r)*NormedSpace.exp ((r:ℂ) • (-X i))=_
    rw [ih]
    simp only [reverseWord,List.reverse_cons,List.map_append,List.map_singleton,
      generators,List.prod_append,List.prod_cons,List.prod_nil,mul_one,hn]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem weylProduct_append (d : κ → E) (u w : List κ) (x : Space E) :
    weylProduct ((u++w).map d) x=weylProduct (u.map d) (weylProduct (w.map d) x) := by
  induction u with
  | nil => rfl
  | cons i u ih => simpa only [List.cons_append,List.map_cons,weylProduct,
      ContinuousLinearMap.comp_apply] using congrArg (W (d i)) ih

 
theorem weylProduct_inner (neg : κ → κ) (d : κ → E)
    (hn : ∀i,d (neg i)= -d i) (w : List κ) (x y : Space E) :
    ⟪weylProduct (w.map d) x,y⟫_ℂ=
      ⟪x,weylProduct ((reverseWord neg w).map d) y⟫_ℂ := by
  induction w generalizing x y with
  | nil => rfl
  | cons i w ih =>
    change ⟪W (d i) (weylProduct (w.map d) x),y⟫_ℂ=_
    have hi : ⟪W (d i) (weylProduct (w.map d) x),y⟫_ℂ=
        ⟪weylProduct (w.map d) x,W (-d i) y⟫_ℂ := by
      exact (weyl (d i)).inner_map_eq_flip _ _
    rw [hi,ih]
    rw [show reverseWord neg (i::w)=reverseWord neg w++[neg i] by simp [reverseWord],
      weylProduct_append]
    simp only [List.map_singleton,weylProduct,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply,hn]

 

theorem tensor_word_gram_limit
    (ι : ℕ → Type*) [∀n,Fintype (ι n)] [∀n,DecidableEq (ι n)] [∀n,Nonempty (ι n)]
    (Ω : ∀n,EuclideanSpace ℂ (ι n))
    (X : ∀n,κ → EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (neg : κ → κ) (d : κ → E) (L : ℝ) (hL : 0≤L)
    (hΩ : ∀n,‖Ω n‖=1) (hX : ∀n i,‖X n i‖≤L)
    (hneg : ∀n i,X n (neg i)= -X n i) (hstar : ∀n i,star (X n i)= -X n i)
    (hdneg : ∀i,d (neg i)= -d i)
    (hc : ∀n i,⟪Ω n,X n i (Ω n)⟫_ℂ=0)
    (hq : ∀i j,Tendsto (fun n => ⟪Ω n,X n i (X n j (Ω n))⟫_ℂ)
      atTop (𝓝 (-⟪d i,d j⟫_ℂ))) (u w : List κ) :
    Tendsto (fun n => ⟪FiniteTensor.power n ((generators (u.map (X n)) (Real.sqrt (n:ℝ))⁻¹) (Ω n)),
      FiniteTensor.power n ((generators (w.map (X n)) (Real.sqrt (n:ℝ))⁻¹) (Ω n))⟫_ℂ)
      atTop (𝓝 ⟪weylProduct (u.map d) (coherent 0),weylProduct (w.map d) (coherent 0)⟫_ℂ) := by
  let l := reverseWord neg u++w
  have hφ (n : ℕ) : ‖vacuumFunctional (Ω n)‖≤1 := by
    simpa only [hΩ n,one_pow] using vacuumFunctional_norm (Ω n)
  have h1 (n : ℕ) : vacuumFunctional (Ω n) 1=1 := by
    simp only [vacuumFunctional_apply,one_apply_eq_self,inner_self_eq_norm_sq_to_K,hΩ n]
    norm_num
  have hz (n : ℕ) : vacuumFunctional (Ω n) (l.map (X n)).sum=0 := by
    unfold vacuumFunctional
    change ⟪Ω n,((l.map (X n)).sum) (Ω n)⟫_ℂ=0
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons,List.sum_cons,add_apply,inner_add_right,hc]
      simpa only [zero_add] using ih
  have hh := moving_generators_weyl_limit
    (fun n => EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    l X (fun n => vacuumFunctional (Ω n)) d L 1 hL (by norm_num)
    (fun n i _ => hX n i) hφ h1 hz (fun i _ j _ => by
      simpa only [vacuumFunctional_apply,mul_apply_eq_comp] using hq i j)
  have he (n : ℕ) :
      ⟪FiniteTensor.power n ((generators (u.map (X n)) (Real.sqrt (n:ℝ))⁻¹) (Ω n)),
        FiniteTensor.power n ((generators (w.map (X n)) (Real.sqrt (n:ℝ))⁻¹) (Ω n))⟫_ℂ =
      (vacuumFunctional (Ω n) (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹))^n := by
    rw [FiniteTensor.inner_power]
    congr 1
    rw [vacuumFunctional_apply,generators_append]
    rw [←generators_star neg (X n) (hneg n) (hstar n)]
    exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  simp_rw [he]
  have href : ⟪weylProduct (u.map d) (coherent 0),weylProduct (w.map d) (coherent 0)⟫_ℂ=
      ⟪coherent 0,weylProduct (l.map d) (coherent 0)⟫_ℂ := by
    rw [weylProduct_inner neg d hdneg]
    rw [weylProduct_append]
  rw [href]
  exact hh

end TensorWordGram

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace TensorPackets
open QuantumCLT CoherentFock SpinOperators

structure Term (κ : Type*) where
  spin : Fin 2
  coeff : ℂ
  history : List κ

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def term (s : List κ → H) (t : Term κ) : Double H :=
  t.coeff • PiLp.single 2 t.spin (s t.history)

def packet (s : List κ → H) (ts : List (Term κ)) : Double H :=
  (ts.map (term s)).sum

@[simp] theorem term_apply (s : List κ → H) (t : Term κ) (i : Fin 2) :
    term s t i = if i=t.spin then t.coeff • s t.history else 0 := by
  classical
  simp only [term,PiLp.smul_apply,PiLp.single_apply]
  split_ifs <;> simp_all

theorem inner_term (s : List κ → H) (t u : Term κ) :
    ⟪term s t,term s u⟫_ℂ =
      if t.spin=u.spin then star t.coeff*u.coeff*⟪s t.history,s u.history⟫_ℂ else 0 := by
  classical
  simp only [PiLp.inner_apply,term_apply]
  obtain ⟨j,c,w⟩ := t
  obtain ⟨k,b,v⟩ := u
  fin_cases j <;> fin_cases k <;> simp [inner_smul_left,inner_smul_right,mul_assoc,mul_left_comm]

@[simp] theorem packet_nil (s : List κ → H) : packet s []=0 := rfl
@[simp] theorem packet_cons (s : List κ → H) (t : Term κ) (ts : List (Term κ)) :
    packet s (t::ts)=term s t+packet s ts := rfl

theorem Gram_limit
    (Hn : ℕ → Type*) [∀n,NormedAddCommGroup (Hn n)] [∀n,InnerProductSpace ℂ (Hn n)]
    (sn : ∀n,List κ → Hn n) (s : List κ → H)
    (hg : ∀u w,Tendsto (fun n => ⟪sn n u,sn n w⟫_ℂ) atTop (𝓝 ⟪s u,s w⟫_ℂ))
    (ts us : List (Term κ)) :
    Tendsto (fun n => ⟪packet (sn n) ts,packet (sn n) us⟫_ℂ)
      atTop (𝓝 ⟪packet s ts,packet s us⟫_ℂ) := by
  have ht (t u : Term κ) : Tendsto (fun n => ⟪term (sn n) t,term (sn n) u⟫_ℂ)
      atTop (𝓝 ⟪term s t,term s u⟫_ℂ) := by
    simp_rw [inner_term]
    split_ifs
    · exact tendsto_const_nhds.mul (hg _ _)
    · exact tendsto_const_nhds
  have hp (t : Term κ) (us : List (Term κ)) :
      Tendsto (fun n => ⟪term (sn n) t,packet (sn n) us⟫_ℂ)
        atTop (𝓝 ⟪term s t,packet s us⟫_ℂ) := by
    induction us with
    | nil => simp only [packet_nil,inner_zero_right]; exact tendsto_const_nhds
    | cons u us ih => simp only [packet_cons,inner_add_right]; exact (ht t u).add ih
  induction ts with
  | nil => simp only [packet_nil,inner_zero_left]; exact tendsto_const_nhds
  | cons t ts ih => simp only [packet_cons,inner_add_left]; exact (hp t us).add ih

 
def mixTerm (A : Matrix (Fin 2) (Fin 2) ℂ) (t : Term κ) : List (Term κ) :=
  [⟨0,A 0 t.spin*t.coeff,t.history⟩,⟨1,A 1 t.spin*t.coeff,t.history⟩]

def mixPacket (A : Matrix (Fin 2) (Fin 2) ℂ) (ts : List (Term κ)) : List (Term κ) :=
  ts.flatMap (mixTerm A)

theorem act_term (s : List κ → H) (A : Matrix (Fin 2) (Fin 2) ℂ) (t : Term κ) :
    act A (term s t)=packet s (mixTerm A t) := by
  classical
  ext i
  simp only [act_apply,term_apply]
  simp only [mixTerm,packet_cons,packet_nil,PiLp.add_apply,term_apply,
    Fin.sum_univ_two,add_zero]
  obtain ⟨j,c,w⟩ := t
  fin_cases i <;> fin_cases j <;> simp [smul_smul]

theorem act_packet (s : List κ → H) (A : Matrix (Fin 2) (Fin 2) ℂ) (ts : List (Term κ)) :
    act A (packet s ts)=packet s (mixPacket A ts) := by
  induction ts with
  | nil => simp [mixPacket]
  | cons t ts ih =>
    rw [packet_cons,map_add,act_term,ih]
    simp only [mixPacket,List.flatMap_cons,packet,List.map_append,List.sum_append]

 
def prefixTerm (a : Fin 2 → κ) (t : Term κ) : Term κ :=
  ⟨t.spin,t.coeff,a t.spin::t.history⟩
def prefixPacket (a : Fin 2 → κ) (ts : List (Term κ)) : List (Term κ) :=
  ts.map (prefixTerm a)

 
def diagonal (K : Fin 2 → H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (K i).comp (PiLp.proj 2 (fun _ : Fin 2 => H) i)))
@[simp] theorem diagonal_apply (K : Fin 2 → H →L[ℂ] H) (x : Double H) (i : Fin 2) :
    diagonal K x i=K i (x i) := by simp [diagonal,PiLp.proj_apply]

theorem diagonal_term (s : List κ → H) (K : Fin 2 → H →L[ℂ] H) (a : Fin 2 → κ)
    (ha : ∀i w,K i (s w)=s (a i::w)) (t : Term κ) :
    diagonal K (term s t)=term s (prefixTerm a t) := by
  classical
  ext i
  simp only [diagonal_apply,term_apply,prefixTerm]
  split_ifs with h
  · rw [h,map_smul,ha]
  · exact map_zero _

theorem diagonal_packet (s : List κ → H) (K : Fin 2 → H →L[ℂ] H) (a : Fin 2 → κ)
    (ha : ∀i w,K i (s w)=s (a i::w)) (ts : List (Term κ)) :
    diagonal K (packet s ts)=packet s (prefixPacket a ts) := by
  induction ts with
  | nil => simp [prefixPacket]
  | cons t ts ih => simp only [packet_cons,map_add,diagonal_term s K a ha,ih,
      prefixPacket,List.map_cons]

end TensorPackets

 

open scoped InnerProductSpace Topology BigOperators
open Filter
namespace RootTensorCLT
open QuantumCLT CoherentFock SpinOperators TensorPackets

inductive Pulse (κ : Type*)
  | root (A : Matrix (Fin 2) (Fin 2) ℂ)
  | control (a : Fin 2 → κ)

variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def applyPulse (K : κ → H →L[ℂ] H) : Pulse κ → Double H →L[ℂ] Double H
  | .root A => act A
  | .control a => diagonal (K ∘ a)

def run (K : κ → H →L[ℂ] H) : List (Pulse κ) → Double H →L[ℂ] Double H
  | [] => ContinuousLinearMap.id ℂ _
  | p::w => (applyPulse K p).comp (run K w)

def compilePulse : Pulse κ → List (Term κ) → List (Term κ)
  | .root A => mixPacket A
  | .control a => prefixPacket a

def compile : List (Pulse κ) → List (Term κ) → List (Term κ)
  | [] => id
  | p::w => compilePulse p ∘ compile w

theorem applyPulse_packet (s : List κ → H) (K : κ → H →L[ℂ] H)
    (hs : ∀i w,K i (s w)=s (i::w)) (p : Pulse κ) (ts : List (Term κ)) :
    applyPulse K p (packet s ts)=packet s (compilePulse p ts) := by
  cases p with
  | root A => exact act_packet s A ts
  | control a => exact diagonal_packet s (K ∘ a) a (fun i w => hs (a i) w) ts

theorem run_packet (s : List κ → H) (K : κ → H →L[ℂ] H)
    (hs : ∀i w,K i (s w)=s (i::w)) (w : List (Pulse κ)) (ts : List (Term κ)) :
    run K w (packet s ts)=packet s (compile w ts) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change applyPulse K p (run K w (packet s ts))=_
    rw [ih,applyPulse_packet s K hs]
    rfl

def start : List (Term κ) :=
  [⟨0,(((Real.sqrt 2)⁻¹:ℝ):ℂ),[]⟩,⟨1,(((Real.sqrt 2)⁻¹:ℝ):ℂ),[]⟩]

theorem start_packet (s : List κ → H) : packet s start=PointedTree.plusEmbedding (s []) := by
  ext i
  fin_cases i <;> simp [start,packet_cons,term_apply,PointedTree.plusEmbedding_apply]

 

def tensorState {ι : Type*} [Fintype ι]
    (D : ℕ) (Ω : EuclideanSpace ℂ ι)
    (X : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (w : List κ) :
    EuclideanSpace ℂ (Fin D → ι) :=
  FiniteTensor.power D ((generators (w.map X) (Real.sqrt (D:ℝ))⁻¹) Ω)

def tensorPulse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) (X : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (i : κ) :
    EuclideanSpace ℂ (Fin D → ι) →L[ℂ] EuclideanSpace ℂ (Fin D → ι) :=
  FiniteTensor.operatorPower D (NormedSpace.exp (((Real.sqrt (D:ℝ))⁻¹:ℂ) • X i))

theorem tensor_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) (Ω : EuclideanSpace ℂ ι)
    (X : κ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (i : κ) (w : List κ) :
    tensorPulse D X i (tensorState D Ω X w)=tensorState D Ω X (i::w) := by
  rw [tensorPulse,tensorState,FiniteTensor.operatorPower_apply]
  simp only [tensorState,generators,List.map_cons,List.prod_cons,mul_apply_eq_comp,Complex.ofReal_inv]

def fockState {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (d : κ → E) (w : List κ) : Space E := weylProduct (w.map d) (coherent 0)

theorem fock_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (d : κ → E) (i : κ) (w : List κ) : W (d i) (fockState d w)=fockState d (i::w) := rfl

 

theorem root_circuit_Gram_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ι : ℕ → Type*) [∀n,Fintype (ι n)] [∀n,DecidableEq (ι n)] [∀n,Nonempty (ι n)]
    (Ω : ∀n,EuclideanSpace ℂ (ι n))
    (X : ∀n,κ → EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (neg : κ → κ) (d : κ → E) (L : ℝ) (hL : 0≤L)
    (hΩ : ∀n,‖Ω n‖=1) (hX : ∀n i,‖X n i‖≤L)
    (hneg : ∀n i,X n (neg i)= -X n i) (hstar : ∀n i,star (X n i)= -X n i)
    (hdneg : ∀i,d (neg i)= -d i)
    (hc : ∀n i,⟪Ω n,X n i (Ω n)⟫_ℂ=0)
    (hq : ∀i j,Tendsto (fun n => ⟪Ω n,X n i (X n j (Ω n))⟫_ℂ)
      atTop (𝓝 (-⟪d i,d j⟫_ℂ))) (u w : List (Pulse κ)) :
    Tendsto (fun n =>
      ⟪run (tensorPulse n (X n)) u (PointedTree.plusEmbedding (FiniteTensor.power n (Ω n))),
        run (tensorPulse n (X n)) w (PointedTree.plusEmbedding (FiniteTensor.power n (Ω n)))⟫_ℂ)
      atTop (𝓝 ⟪run (W ∘ d) u (PointedTree.vacuum E),run (W ∘ d) w (PointedTree.vacuum E)⟫_ℂ) := by
  have hg := TensorWordGram.tensor_word_gram_limit ι Ω X neg d L hL hΩ hX hneg hstar hdneg hc hq
  have hall := TensorPackets.Gram_limit
    (fun n => EuclideanSpace ℂ (Fin n → ι n)) (fun n => tensorState n (Ω n) (X n))
    (fockState d) hg (compile u start) (compile w start)
  have hn (n : ℕ) (v : List (Pulse κ)) :
      run (tensorPulse n (X n)) v (PointedTree.plusEmbedding (FiniteTensor.power n (Ω n)))=
        packet (tensorState n (Ω n) (X n)) (compile v start) := by
    have he : tensorState n (Ω n) (X n) []=FiniteTensor.power n (Ω n) := by
      simp [tensorState,generators]
    rw [←he,←start_packet,run_packet _ _ (tensor_step n (Ω n) (X n))]
  have hf (v : List (Pulse κ)) :
      run (W ∘ d) v (PointedTree.vacuum E)=packet (fockState d) (compile v start) := by
    change run (W ∘ d) v (PointedTree.plusEmbedding (fockState d []))=_
    rw [←start_packet]
    exact run_packet (fockState d) (W ∘ d) (fock_step d) v start
  simpa only [hn,hf] using hall

end RootTensorCLT

 

open scoped InnerProductSpace BigOperators
namespace FiniteTensor
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem matrixPower_one (D : ℕ) : matrixPower D (1 : Matrix ι ι ℂ)=1 := by
  classical
  ext σ τ
  simp only [matrixPower,Matrix.one_apply]
  by_cases h : σ=τ
  · subst τ; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

omit [DecidableEq ι] in
theorem matrixPower_mul (D : ℕ) (A B : Matrix ι ι ℂ) :
    matrixPower D (A*B)=matrixPower D A*matrixPower D B := by
  ext σ τ
  simp only [matrixPower,Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact Finset.prod_mul_distrib

omit [Fintype ι] [DecidableEq ι] in
theorem matrixPower_star (D : ℕ) (A : Matrix ι ι ℂ) :
    matrixPower D (star A)=star (matrixPower D A) := by
  ext σ τ
  simp only [matrixPower,Matrix.star_apply,star_prod]

theorem operatorPower_one (D : ℕ) :
    operatorPower D (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)=1 := by
  simp [operatorPower,matrixPower_one]

theorem operatorPower_mul (D : ℕ) (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    operatorPower D (A*B)=operatorPower D A*operatorPower D B := by
  simp [operatorPower,matrixPower_mul]

theorem operatorPower_star (D : ℕ) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    operatorPower D (star A)=star (operatorPower D A) := by
  unfold operatorPower
  have hs : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm (star A)=
      star ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm A) :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm.map_star' A
  rw [hs,matrixPower_star]
  exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin D → ι)).map_star' _

 

theorem operatorPower_unitary (D : ℕ) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (hA : A ∈ unitary _) : operatorPower D A ∈ unitary _ := by
  rw [Unitary.mem_iff] at hA ⊢
  constructor
  · rw [←operatorPower_star,←operatorPower_mul,hA.1,operatorPower_one]
  · rw [←operatorPower_star,←operatorPower_mul,hA.2,operatorPower_one]

end FiniteTensor

namespace TensorPackets
open SpinOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem diagonal_mul (K L : Fin 2 → H →L[ℂ] H) :
    diagonal (fun i => K i*L i)=diagonal K*diagonal L := by
  ext x i
  simp only [diagonal_apply,mul_apply_eq_comp]

omit [CompleteSpace H] in
theorem diagonal_one : diagonal (fun _ : Fin 2 => (1 : H →L[ℂ] H))=1 := by
  ext x i
  simp

theorem diagonal_star (K : Fin 2 → H →L[ℂ] H) :
    diagonal (fun i => star (K i))=star (diagonal K) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change ⟪diagonal (fun i => star (K i)) x,y⟫_ℂ=
    ⟪ContinuousLinearMap.adjoint (diagonal K) x,y⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply,diagonal_apply,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem diagonal_unitary (K : Fin 2 → H →L[ℂ] H) (hK : ∀i,K i ∈ unitary _) :
    diagonal K ∈ unitary _ := by
  rw [Unitary.mem_iff]
  have hl (i : Fin 2) : star (K i)*K i=1 := (Unitary.mem_iff.mp (hK i)).1
  have hr (i : Fin 2) : K i*star (K i)=1 := (Unitary.mem_iff.mp (hK i)).2
  constructor
  · rw [←diagonal_star,←diagonal_mul]; simp_rw [hl]; exact diagonal_one
  · rw [←diagonal_star,←diagonal_mul]; simp_rw [hr]; exact diagonal_one

end TensorPackets

 

open scoped InnerProductSpace BigOperators
namespace FiniteTree
open SpinOperators PointedTree

 

@[reducible] def Index (D : ℕ) : ℕ → Type
  | 0 => Fin 2
  | h+1 => Σ _ : Fin 2, Fin D → Index D h

@[reducible] instance indexFintype (D : ℕ) : (h : ℕ) → Fintype (Index D h)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | h+1 => by
      have := indexFintype D h
      exact inferInstanceAs (Fintype (Σ _ : Fin 2, Fin D → Index D h))
@[reducible] instance indexDecidableEq (D : ℕ) : (h : ℕ) → DecidableEq (Index D h)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | h+1 => by
      have := indexDecidableEq D h
      exact inferInstanceAs (DecidableEq (Σ _ : Fin 2, Fin D → Index D h))
instance indexNonempty (D : ℕ) : (h : ℕ) → Nonempty (Index D h)
  | 0 => inferInstanceAs (Nonempty (Fin 2))
  | h+1 => by
      exact ⟨⟨0, fun _ => Classical.choice (indexNonempty D h)⟩⟩

abbrev Space (D h : ℕ) := EuclideanSpace ℂ (Index D h)

@[reducible] def Tail (D : ℕ) : ℕ → Type
  | 0 => ℂ
  | h+1 => EuclideanSpace ℂ (Fin D → Index D h)
@[reducible] instance tailNormed (D : ℕ) : (h : ℕ) → NormedAddCommGroup (Tail D h)
  | 0 => inferInstanceAs (NormedAddCommGroup ℂ)
  | h+1 => inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin D → Index D h)))
@[reducible] instance tailInner (D : ℕ) : (h : ℕ) → InnerProductSpace ℂ (Tail D h)
  | 0 => inferInstanceAs (InnerProductSpace ℂ ℂ)
  | h+1 => inferInstanceAs (InnerProductSpace ℂ (EuclideanSpace ℂ (Fin D → Index D h)))
instance tailComplete (D : ℕ) : (h : ℕ) → CompleteSpace (Tail D h)
  | 0 => inferInstanceAs (CompleteSpace ℂ)
  | h+1 => inferInstanceAs (CompleteSpace (EuclideanSpace ℂ (Fin D → Index D h)))

 
def split (D : ℕ) : (h : ℕ) → Space D h ≃ₗᵢ[ℂ] Double (Tail D h)
  | 0 => LinearIsometryEquiv.refl ℂ _
  | h+1 => LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Fin 2) (_ : Fin D → Index D h) => ℂ)

 
def root (D h : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Space D h →L[ℂ] Space D h :=
  (split D h).symm.conjStarAlgEquiv (act A)

@[simp] theorem split_root (D h : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Space D h) :
    split D h (root D h A x)=act A (split D h x) := by simp [root]

theorem root_one (D h : ℕ) : root D h 1=1 := by
  unfold root
  rw [act_one]
  exact map_one _
theorem root_mul (D h : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    root D h (A*B)=root D h A*root D h B := by
  change (split D h).symm.conjStarAlgEquiv (act (A*B))=_
  rw [act_mul]
  exact map_mul _ _ _
theorem root_star (D h : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    root D h (star A)=star (root D h A) := by
  unfold root
  rw [show act (star A)=(star (act A : Double (Tail D h) →L[ℂ] Double (Tail D h)))
    from (starRep (H := Tail D h)).map_star' A]
  exact (split D h).symm.conjStarAlgEquiv.map_star' _

theorem root_unitary (D h : ℕ) {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ unitary _) :
    root D h A ∈ unitary _ :=
  by
    rw [Unitary.mem_iff] at hA ⊢
    constructor
    · rw [←root_star,←root_mul,hA.1,root_one]
    · rw [←root_star,←root_mul,hA.2,root_one]

 
def vac (D : ℕ) : (h : ℕ) → Space D h
  | 0 => PointedTree.plus
  | h+1 => (split D (h+1)).symm (plusEmbedding (FiniteTensor.power D (vac D h)))

theorem norm_power_of_norm_one {ι : Type*} [Fintype ι]
    (D : ℕ) (v : EuclideanSpace ℂ ι) (hv : ‖v‖=1) : ‖FiniteTensor.power D v‖=1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),FiniteTensor.inner_power,
    inner_self_eq_norm_sq_to_K,hv]
  norm_num

@[simp] theorem norm_vac (D h : ℕ) : ‖vac D h‖=1 := by
  induction h with
  | zero => exact PointedTree.norm_plus
  | succ h ih =>
      rw [vac,LinearIsometryEquiv.norm_map]
      exact (plusEmbedding.norm_map _).trans (norm_power_of_norm_one D (vac D h) ih)

 

def control (D h : ℕ) (K : Fin 2 → Space D h →L[ℂ] Space D h) :
    Space D (h+1) →L[ℂ] Space D (h+1) :=
  (split D (h+1)).symm.conjStarAlgEquiv (TensorPackets.diagonal (fun i => FiniteTensor.operatorPower D (K i)))

@[simp] theorem split_control (D h : ℕ) (K : Fin 2 → Space D h →L[ℂ] Space D h)
    (x : Space D (h+1)) :
    split D (h+1) (control D h K x)=
      TensorPackets.diagonal (fun i => FiniteTensor.operatorPower D (K i)) (split D (h+1) x) := by
  simp only [control, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]

theorem isometry_conj_unitary {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (hA : A ∈ unitary _) :
    e.conjStarAlgEquiv A ∈ unitary _ := by
  let f := e.conjStarAlgEquiv
  have hs : star (f A)=f (star A) := (f.map_star' A).symm
  have hm (B C : H →L[ℂ] H) : f (B*C)=f B*f C := f.map_mul' B C
  have ho : f 1=1 := map_one f
  change f A ∈ unitary _
  rw [Unitary.mem_iff] at hA ⊢
  constructor
  · rw [hs,←hm,hA.1,ho]
  · rw [hs,←hm,hA.2,ho]

theorem control_unitary (D h : ℕ) (K : Fin 2 → Space D h →L[ℂ] Space D h)
    (hK : ∀i,K i ∈ unitary _) : control D h K ∈ unitary _ :=
  isometry_conj_unitary (split D (h+1)).symm _
    (TensorPackets.diagonal_unitary _ (fun i => FiniteTensor.operatorPower_unitary D (K i) (hK i)))

end FiniteTree

 

open scoped InnerProductSpace BigOperators
namespace FiniteTree
open SpinOperators TensorPackets RootSpin

 
def spinFlip {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  act X*TensorPackets.diagonal (fun _ => T)

@[simp] theorem spinFlip_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (x : Double H) (i : Fin 2) :
    spinFlip T x i=T (x (1-i)) := by
  fin_cases i <;> simp [spinFlip,mul_apply_eq_comp,act_apply,X,Fin.sum_univ_two]

theorem spinFlip_square {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (hT : T*T=1) : spinFlip T*spinFlip T=1 := by
  ext x i
  have ht (y : H) : T (T y)=y := by
    simpa only [mul_apply_eq_comp,one_apply_eq_self] using congrArg (fun A : H →L[ℂ] H => A y) hT
  fin_cases i <;> simp [mul_apply_eq_comp,spinFlip_apply,ht]

theorem spinFlip_unitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) (hT : T ∈ unitary _) : spinFlip T ∈ unitary _ := by
  exact (unitary _).mul_mem (act_mem_unitary X_unitary) (diagonal_unitary _ (fun _ => hT))

theorem spinFlip_Z {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (x : Double H) :
    spinFlip T (act Z x)= -act Z (spinFlip T x) := by
  ext i
  fin_cases i <;> simp [spinFlip_apply,act_apply,Z,Fin.sum_univ_two]

theorem spinFlip_R {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (t : ℝ) (x : Double H) :
    spinFlip T (act (R t) x)=act (R t) (spinFlip T x) := by
  ext i
  fin_cases i <;> simp [spinFlip_apply,act_apply,R,X,Fin.sum_univ_two,map_add,map_smul,add_comm]

 
def flip (D : ℕ) : (h : ℕ) → Space D h →L[ℂ] Space D h
  | 0 => root D 0 X
  | h+1 => (split D (h+1)).symm.conjStarAlgEquiv
      (spinFlip (FiniteTensor.operatorPower D (flip D h)))

theorem flip_square (D h : ℕ) : flip D h*flip D h=1 := by
  induction h with
  | zero => rw [flip,←root_mul,X_sq,root_one]
  | succ h ih =>
    change (split D (h+1)).symm.conjStarAlgEquiv _*(split D (h+1)).symm.conjStarAlgEquiv _=_
    rw [←map_mul,spinFlip_square _ (by rw [←FiniteTensor.operatorPower_mul,ih,FiniteTensor.operatorPower_one]),map_one]

theorem flip_unitary (D h : ℕ) : flip D h ∈ unitary _ := by
  induction h with
  | zero => exact root_unitary D 0 X_unitary
  | succ h ih =>
    exact isometry_conj_unitary (split D (h+1)).symm _
      (spinFlip_unitary _ (FiniteTensor.operatorPower_unitary D _ ih))

@[simp] theorem split_flip (D h : ℕ) (x : Space D (h+1)) :
    split D (h+1) (flip D (h+1) x)=
      spinFlip (FiniteTensor.operatorPower D (flip D h)) (split D (h+1) x) := by
  simp [flip]

theorem flip_vac (D h : ℕ) : flip D h (vac D h)=vac D h := by
  induction h with
  | zero =>
    change act X PointedTree.plus=PointedTree.plus
    ext i
    fin_cases i <;> simp [act_apply,X,Fin.sum_univ_two,PointedTree.plus]
  | succ h ih =>
    apply (split D (h+1)).injective
    rw [split_flip]
    simp only [vac,LinearIsometryEquiv.apply_symm_apply]
    ext i
    simp only [spinFlip_apply,PointedTree.plusEmbedding_apply,map_smul,
      FiniteTensor.operatorPower_apply,ih]

theorem flip_rootZ (D h : ℕ) (x : Space D h) :
    flip D h (root D h Z x)= -root D h Z (flip D h x) := by
  cases h with
  | zero =>
    change act X (act Z x)= -act Z (act X x)
    ext i
    fin_cases i <;> simp [act_apply,X,Z,Fin.sum_univ_two]
  | succ h =>
    apply (split D (h+1)).injective
    rw [split_flip,split_root,map_neg,split_root,split_flip]
    exact spinFlip_Z _ _

theorem flip_rootR (D h : ℕ) (t : ℝ) (x : Space D h) :
    flip D h (root D h (R t) x)=root D h (R t) (flip D h x) := by
  cases h with
  | zero =>
    change act X (act (R t) x)=act (R t) (act X x)
    ext i
    fin_cases i <;> simp [act_apply,X,R,Fin.sum_univ_two,add_comm]
  | succ h =>
    apply (split D (h+1)).injective
    rw [split_flip,split_root,split_root,split_flip]
    exact spinFlip_R _ _ _

end FiniteTree

end

end OAI
