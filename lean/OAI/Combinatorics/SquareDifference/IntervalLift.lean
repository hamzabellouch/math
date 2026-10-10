import OAI.Combinatorics.SquareDifference.UniformTransfer

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

noncomputable def intervalInput (a L : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n∈Ico a (a+L) then f n else 0

lemma intervalInput_bound (a L : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0≤M)
    (hf : ∀n,|f n|≤M) (n : ℕ) : |intervalInput a L f n|≤M := by
  unfold intervalInput
  split_ifs
  · exact hf n
  · simpa only [abs_zero] using hM

lemma interval_sum_mask {E : Type*} [AddCommMonoid E] (N a L : ℕ) (f : ℕ → E)
    (hf : ∀n,N≤n → f n=0) :
    (∑n∈range N,if n∈Ico a (a+L) then f n else 0)=∑t∈range L,f (a+t) := by
  rw [←sum_filter,filter_mem_eq_inter,inter_comm]
  have h := sum_subset (inter_subset_left (s₁:=Ico a (a+L)) (s₂:=range N))
    (f:=f) (fun n hn hni => hf n (by simpa only [mem_inter,hn,true_and,mem_range,not_lt] using hni))
  rw [h,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]

section Interval

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

noncomputable def intervalPiece (a L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) : ℝ :=
  (L:ℝ)⁻¹*∑t∈range L,f (a+t)*exactGate p U (x-fun j => ((a+t:ℕ):ZMod (p j)))

noncomputable def intervalLift (a L Q : ℕ) (f : ℕ → ℝ) (x : ResidueSpace p) : ℝ :=
  ∑U∈liftSupportFamily p Q,intervalPiece p a L f U x

lemma intervalPiece_shift {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (a L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) :
    intervalPiece p a L f U x=actualLiftPiece p L (fun n => f (a+n)) U
      (x-fun j => (a:ZMod (p j))) := by
  unfold intervalPiece actualLiftPiece LiftAnalysis.SquareDifference.liftPiece
  congr 1
  apply sum_congr rfl
  intro n _
  congr 2
  funext j
  simp only [Pi.sub_apply,Nat.cast_add]
  ring

lemma intervalLift_shift (a L Q : ℕ) (f : ℕ → ℝ) (x : ResidueSpace p) :
    intervalLift p a L Q f x=actualTruncatedLift p L Q (fun n => f (a+n))
      (x-fun j => (a:ZMod (p j))) := by
  simp only [intervalLift,intervalPiece_shift,actualTruncatedLift,LiftAnalysis.SquareDifference.truncatedLift]

lemma intervalPiece_exactSupport {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (a L : ℕ) (f : ℕ → ℝ) (U : Finset J) :
    ExactSupport U (intervalPiece p a L f U) := by
  constructor
  · intro j hj x
    simp only [intervalPiece,←mul_expect,expect_sum_comm,exactGate_update_mean p U j hj,
      mul_zero,sum_const_zero]
  · intro j hj x t
    simp only [intervalPiece,exactGate_update_outside p U j hj]

lemma intervalPiece_global {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (N a L : ℕ) (hN : 0<N) (f : ℕ → ℝ)
    (hf : ∀n,N≤n → f n=0) (U : Finset J) (x : ResidueSpace p) :
    intervalPiece p a L f U x=(N:ℝ)/L*actualLiftPiece p N (intervalInput a L f) U x := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold intervalPiece actualLiftPiece LiftAnalysis.SquareDifference.liftPiece intervalInput
  simp only [ite_mul,zero_mul]
  change (L:ℝ)⁻¹*(∑t∈range L,f (a+t)*exactGate p U (x-fun j => ((a+t:ℕ):ZMod (p j)))) =
    (N:ℝ)/L*((N:ℝ)⁻¹*∑n∈range N,if n∈Ico a (a+L) then f n*exactGate p U (x-fun j => (n:ZMod (p j))) else 0)
  rw [interval_sum_mask N a L (fun n => f n*exactGate p U (x-fun j =>(n:ZMod (p j))))
    (fun n hn => by rw [hf n hn,zero_mul])]
  field_simp

lemma intervalLift_global (N a L Q : ℕ) (hN : 0<N) (f : ℕ → ℝ)
    (hf : ∀n,N≤n → f n=0) (x : ResidueSpace p) :
    intervalLift p a L Q f x=(N:ℝ)/L*actualTruncatedLift p N Q (intervalInput a L f) x := by
  simp only [intervalLift,intervalPiece_global p N a L hN f hf,actualTruncatedLift,LiftAnalysis.SquareDifference.truncatedLift,mul_sum]

lemma intervalPiece_moment (a L : ℕ) (f : ℕ → ℝ) (s : Finset (Finset J)) (r : ℕ) :
    (𝔼 x,(∑U∈s,intervalPiece p a L f U x)^r)=
      𝔼 x,(∑U∈s,actualLiftPiece p L (fun n => f (a+n)) U x)^r := by
  simp only [intervalPiece_shift]
  exact Fintype.expect_equiv (Equiv.subRight (fun j => (a:ZMod (p j)))) _ _ (fun _ => rfl)

lemma blockPiece_decomposition {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (N K L : ℕ) (hN : 0<N) (hL : 0<L) (hcover : N≤K*L)
    (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0) (U : Finset J) (x : ResidueSpace p) :
    actualLiftPiece p N f U x=(L:ℝ)/N*∑i∈range K,intervalPiece p (L*i) L f U x := by
  have hs := sum_subset (range_mono hcover) (f:=fun n => f n*exactGate p U (x-fun j =>(n:ZMod (p j))))
    (fun n hn hni => by rw [hf n (by simpa only [mem_range,not_lt] using hni),zero_mul])
  rw [mul_comm K L,LiftAnalysis.SquareDifference.sum_range_blocks _ L K hL,sum_comm] at hs
  unfold actualLiftPiece LiftAnalysis.SquareDifference.liftPiece intervalPiece
  change (N:ℝ)⁻¹*(∑n∈range N,f n*exactGate p U (x-fun j => (n:ZMod (p j)))) = _
  rw [hs]
  rw [←mul_sum]
  have hl : (L:ℝ)≠0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro t _
  rw [Nat.add_comm t (L*i)]

lemma blockLift_decomposition (N K L Q : ℕ) (hN : 0<N) (hL : 0<L) (hcover : N≤K*L)
    (f : ℕ → ℝ) (hf : ∀n,N≤n → f n=0) (x : ResidueSpace p) :
    actualTruncatedLift p N Q f x=(L:ℝ)/N*∑i∈range K,intervalLift p (L*i) L Q f x := by
  change (∑U∈liftSupportFamily p Q,actualLiftPiece p N f U x)=_
  unfold intervalLift
  simp_rw [blockPiece_decomposition p N K L hN hL hcover f hf]
  rw [←mul_sum,sum_comm]

end Interval

lemma uniform_interval_moments (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ)
      [∀j,Fact (p j).Prime],Function.Injective p →
      ∀(a L Q N : ℕ),LiftSizeConditions L Q → Q≤N →
      ∀(f : ℕ → ℝ) (M : ℝ),0≤M → (∀n,|f n|≤M) →
      ∀s,s⊆liftSupportFamily p Q → ∀r,r=1 ∨ r+1=Fintype.card TupleVertex →
      (𝔼 x,(∑U∈s,intervalPiece p a L f U x)^(2*r))≤(C*M*(N:ℝ)^ε)^(2*r) := by
  obtain ⟨C,hC,hb⟩ := uniform_partial_lift_moments ε hε
  refine ⟨C,hC,?_⟩
  intro J _ _ p _ hinj a L Q N hs hQN f M hM hf s hsub r hr
  rw [intervalPiece_moment]
  exact hb p hinj L Q N hs hQN _ M hM (fun _ _ => hf _) s hsub r hr

end SquareDifference

end

end OAI
