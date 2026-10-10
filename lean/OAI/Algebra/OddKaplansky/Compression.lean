import OAI.Algebra.OddKaplansky.OrderedZero

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3 contextUniverse4 contextUniverse5 contextUniverse6

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9 portUniverse10 portUniverse11 portUniverse12

section
namespace OddKaplansky.Compression
noncomputable section
open scoped Classical BigOperators Matrix
variable {K : Type portUniverse1} {R : Type portUniverse2} {I : Type portUniverse3} {T : Type portUniverse4} {W : Type portUniverse5} {N : Type portUniverse6} [Field K] [Ring R] [Algebra K R]
variable [sectionInstance71 : Fintype I] [sectionInstance72 : Fintype T] [sectionInstance74 : Fintype W] [sectionInstance73 : Fintype N]
lemma nilpotent_lower {S : Type portUniverse7} [Ring S] {n : ℕ} (ix : I → Fin n)
    (A : Matrix I I S) (hA : ∀ i j, (ix i).val ≤ (ix j).val → A i j=0) : A^n=0 := by
  have hp (k : ℕ) : ∀ i j, (ix i).val < (ix j).val+k → (A^k) i j=0 := by
    induction k with
    | zero =>
      intro i j h
      have hij : i≠j := by intro he; subst j; omega
      simp [hij]
    | succ k ih =>
      intro i j h
      rw [pow_succ',Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : (ix a).val < (ix j).val+k
      · rw [ih a j ha,mul_zero]
      · rw [hA i a (by omega),zero_mul]
  funext i j
  exact hp n i j (by have := (ix i).isLt; omega)

def C₀ (P : I → R) (β : I → T → K) : Matrix T I R := fun t i => β i t • P i
def D₀ (P : I → R) (α : I → T → K) : Matrix I T R := fun i t => α i t • P i
lemma D₀C₀
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    [contextInstance4 : Field.{contextUniverse1} K]
    [contextInstance5 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance4))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance5)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T] (P : I → R) (α β : I → T → K) (i j : I) :
    (D₀ P α * C₀ P β) i j = (∑ t, α i t*β j t) • (P i*P j) := by
  simp only [Matrix.mul_apply,D₀,C₀,smul_mul_assoc,mul_smul_comm,smul_smul,Finset.sum_smul,mul_comm]
lemma diag_idempotent (P : I → R) (hP : ∀ i, P i*P i=P i) :
    Matrix.diagonal P * Matrix.diagonal P = Matrix.diagonal P := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact hP i
lemma C₀_diag
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    [contextInstance4 : Field.{contextUniverse1} K]
    [contextInstance5 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance4))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance5)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T] (P : I → R) (hP : ∀ i, P i*P i=P i) (β : I → T → K) :
    C₀ P β * Matrix.diagonal P = C₀ P β := by
  funext t i
  simp only [Matrix.mul_diagonal,C₀,smul_mul_assoc,hP]
lemma diag_D₀
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    [contextInstance4 : Field.{contextUniverse1} K]
    [contextInstance5 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance4))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance5)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T] (P : I → R) (hP : ∀ i, P i*P i=P i) (α : I → T → K) :
    Matrix.diagonal P * D₀ P α = D₀ P α := by
  funext i t
  simp only [Matrix.diagonal_mul,D₀,mul_smul_comm,hP]

def error (P : I → R) (α β : I → T → K) : Matrix I I R := D₀ P α * C₀ P β - Matrix.diagonal P
def correction (P : I → R) (α β : I → T → K) : Matrix I I R :=
  (∑ k ∈ Finset.range (Fintype.card I), (-error P α β)^k) * Matrix.diagonal P
def D₁ (P : I → R) (α β : I → T → K) : Matrix I T R := correction P α β * D₀ P α
lemma corrected (P : I → R) (hP : ∀ i, P i*P i=P i) (α β : I → T → K)
    (ix : I → Fin (Fintype.card I)) (hix : Function.Injective ix)
    (hdiag : ∀ i, ∑ t, α i t*β i t=1)
    (hupper : ∀ i j, (ix i).val < (ix j).val → (∑ t, α i t*β j t) • (P i*P j)=0) :
    D₁ P α β * C₀ P β = Matrix.diagonal P := by
  let E := error P α β
  let Q := Matrix.diagonal P
  have hQ : Q*Q=Q := diag_idempotent P hP
  have hEQ : E*Q=E := by
    dsimp [E,Q,error]
    rw [sub_mul,Matrix.mul_assoc,C₀_diag P hP,diag_idempotent P hP]
  have hQE : Q*E=E := by
    dsimp [E,Q,error]
    rw [mul_sub,← Matrix.mul_assoc,diag_D₀ P hP,diag_idempotent P hP]
  have hnil : E^(Fintype.card I)=0 := by
    apply nilpotent_lower ix E
    intro i j hij
    dsimp [E,error]
    rw [D₀C₀]
    by_cases he : i=j
    · subst j
      simp [hdiag,hP]
    · rw [Matrix.diagonal_apply_ne _ he,sub_zero]
      apply hupper i j
      have hne : (ix i).val ≠ (ix j).val := fun h => he (hix (Fin.ext h))
      omega
  have hgeom : (∑ k ∈ Finset.range (Fintype.card I), (-E)^k) * (1+E)=1 := by
    have hh := geom_sum_mul (-E) (Fintype.card I)
    have hn : (-E)^(Fintype.card I)=0 := by rw [neg_pow,hnil,mul_zero]
    rw [hn] at hh
    have hm : -(1+E)= -E-1 := by noncomm_ring
    rw [← hm,mul_neg] at hh
    have := congrArg Neg.neg hh
    simpa only [neg_neg,zero_sub,neg_neg] using this
  unfold D₁ correction
  change ((∑ k ∈ Finset.range (Fintype.card I), (-E)^k)*Q*D₀ P α)*C₀ P β=Q
  rw [Matrix.mul_assoc,show D₀ P α*C₀ P β=Q+E by dsimp [E,Q,error]; abel]
  have hh : Q*(Q+E)=(1+E)*Q := by rw [mul_add,hQ,hQE,add_mul,one_mul,hEQ]
  rw [mul_assoc,hh,← mul_assoc,hgeom,one_mul]

def rep {A : Type portUniverse8} {B : Type portUniverse9} (X : Matrix A B R) : Matrix (W×A) (W×B) R := fun a b => if a.1=b.1 then X a.2 b.2 else 0
lemma rep_mul {A : Type portUniverse10} {B : Type portUniverse11} {C : Type portUniverse12} [Fintype B] (X : Matrix A B R) (Y : Matrix B C R) :
    rep (W := W) (X*Y)=
      (rep X : Matrix (W×A) (W×B) R) * (rep Y : Matrix (W×B) (W×C) R) := by
  funext a c
  simp only [rep,Matrix.mul_apply,Fintype.sum_prod_type]
  by_cases he : a.1=c.1
  · simp [he]
  · simp [he]
def blockJ (J : I → Matrix W N R) : Matrix (W×I) (I×N) R := fun a b => if a.2=b.1 then J a.2 a.1 b.2 else 0
def blockY (Y : I → Matrix N W R) : Matrix (I×N) (W×I) R := fun a b => if a.1=b.2 then Y a.1 a.2 b.1 else 0
lemma blockYJ
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {W : Type contextUniverse3}
    {N : Type contextUniverse4}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} W]
    [Fintype.{contextUniverse4} N] (f : R) (J : I → Matrix W N R) (Y : I → Matrix N W R)
    (hYJ : ∀ i, Y i*J i=Matrix.diagonal (fun _ => f)) : blockY Y*blockJ J=Matrix.diagonal (fun _ => f) := by
  funext a b
  simp only [Matrix.mul_apply,blockY,blockJ,Fintype.sum_prod_type]
  by_cases he : a.1=b.1
  · simp only [← he,ite_mul,zero_mul,mul_ite,mul_zero,]
    have hh := congrFun (congrFun (hYJ a.1) a.2) b.2
    simpa [Matrix.mul_apply,Matrix.diagonal_apply,Prod.ext_iff,he] using hh
  · simp [he,Prod.ext_iff]
lemma blockJY
    {R : Type contextUniverse1}
    {I : Type contextUniverse2}
    {W : Type contextUniverse3}
    {N : Type contextUniverse4}
    [Ring.{contextUniverse1} R]
    [Fintype.{contextUniverse2} I]
    [Fintype.{contextUniverse3} W]
    [Fintype.{contextUniverse4} N] (P : I → R) (J : I → Matrix W N R) (Y : I → Matrix N W R)
    (hJY : ∀ i, J i*Y i=Matrix.diagonal (fun _ => P i)) : blockJ J*blockY Y=rep (Matrix.diagonal P) := by
  funext a b
  simp only [Matrix.mul_apply,blockY,blockJ,Fintype.sum_prod_type,rep]
  by_cases he : a.2=b.2
  · simp only [← he,ite_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_irrel,]
    have hh := congrFun (congrFun (hJY a.2) a.1) b.1
    simpa [Matrix.mul_apply,Matrix.diagonal_apply] using hh
  · simp [he]
def Csharp (P : I → R) (β : I → T → K) (J : I → Matrix W N R) : Matrix (W×T) (I×N) R :=
  (rep (C₀ P β) : Matrix (W×T) (W×I) R) * (blockJ J : Matrix (W×I) (I×N) R)
def Dsharp (P : I → R) (α β : I → T → K) (Y : I → Matrix N W R) : Matrix (I×N) (W×T) R :=
  (blockY Y : Matrix (I×N) (W×I) R) * (rep (D₁ P α β) : Matrix (W×I) (W×T) R)
lemma compressed (f : R) (hf : f*f=f)
    (P : I → R) (hP : ∀ i, P i*P i=P i) (α β : I → T → K)
    (ix : I → Fin (Fintype.card I)) (hix : Function.Injective ix)
    (hdiag : ∀ i, ∑ t, α i t*β i t=1)
    (hupper : ∀ i j, (ix i).val < (ix j).val → (∑ t, α i t*β j t) • (P i*P j)=0)
    (J : I → Matrix W N R) (Y : I → Matrix N W R)
    (hYJ : ∀ i, Y i*J i=Matrix.diagonal (fun _ => f))
    (hJY : ∀ i, J i*Y i=Matrix.diagonal (fun _ => P i)) :
    Dsharp P α β Y * Csharp P β J = Matrix.diagonal (fun _ => f) := by
  unfold Dsharp Csharp
  rw [Matrix.mul_assoc,← Matrix.mul_assoc (rep (D₁ P α β)),← rep_mul,corrected P hP α β ix hix hdiag hupper]
  rw [← blockJY P J Y hJY]
  calc
    blockY Y * ((blockJ J*blockY Y)*blockJ J) = (blockY Y*blockJ J)*(blockY Y*blockJ J) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [blockYJ f J Y hYJ,Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact hf

lemma Csharp_sector
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    {W : Type contextUniverse5}
    {N : Type contextUniverse6}
    [contextInstance6 : Field.{contextUniverse1} K]
    [contextInstance7 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance6))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance7)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T]
    [Fintype.{contextUniverse5} W]
    [Fintype.{contextUniverse6} N] (f : R) (P : I → R) (hP : ∀ i, f*P i=P i) (β : I → T → K) (J : I → Matrix W N R) :
    ∀ a b, f*Csharp P β J a b=Csharp P β J a b := by
  intro a b
  simp only [Csharp,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← mul_assoc]
  congr 1
  simp only [rep,C₀]
  split_ifs <;> simp [hP]
lemma Dsharp_sector
    {K : Type contextUniverse1}
    {R : Type contextUniverse2}
    {I : Type contextUniverse3}
    {T : Type contextUniverse4}
    {W : Type contextUniverse5}
    {N : Type contextUniverse6}
    [contextInstance6 : Field.{contextUniverse1} K]
    [contextInstance7 : Ring.{contextUniverse2} R]
    [@Algebra.{contextUniverse1, contextUniverse2} K R (@Semifield.toCommSemiring.{contextUniverse1} K (@Field.toSemifield.{contextUniverse1} K contextInstance6))
  (@Ring.toSemiring.{contextUniverse2} R contextInstance7)]
    [Fintype.{contextUniverse3} I]
    [Fintype.{contextUniverse4} T]
    [Fintype.{contextUniverse5} W]
    [Fintype.{contextUniverse6} N] (f : R) (P : I → R) (α β : I → T → K) (Y : I → Matrix N W R)
    (hY : ∀ i n w, f*Y i n w=Y i n w) : ∀ a b, f*Dsharp P α β Y a b=Dsharp P α β Y a b := by
  intro a b
  simp only [Dsharp,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← mul_assoc]
  congr 1
  simp only [blockY]
  split_ifs <;> simp [hY]
end
end OddKaplansky.Compression

end

end OAI
