import OAI.Analysis.InterpolatedFactors.Mixed

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
namespace FreeGroupFactorMain.RectangularAbsorption

section
variable {A : Type u_1} [Ring A]

def part (p q : A) (C : ℕ → A) (n : ℕ) : A := p*C n*q
def remainder (p q : A) (C : ℕ → A) (n : ℕ) : A := C n-part p q C n
def shifted (p q D : A) (C : ℕ → A) : ℕ → A
  | 0 => D+remainder p q C 0
  | n+1 => part p q C n+remainder p q C (n+1)

 theorem part_supported (p q : A) (hp : p*p=p) (hq : q*q=q) (C : ℕ → A) (n : ℕ) :
    p*part p q C n*q=part p q C n := by
  calc
    _ = (p*p)*C n*(q*q) := by dsimp [part];noncomm_ring
    _ = _ := by rw [hp,hq];rfl

 theorem remainder_compression (p q : A) (hp : p*p=p) (hq : q*q=q) (C : ℕ → A) (n : ℕ) :
    p*remainder p q C n*q=0 := by
  rw [remainder,mul_sub,sub_mul,part_supported p q hp hq]
  exact sub_self _

 theorem shifted_zero_compression (p q D : A) (hp : p*p=p) (hq : q*q=q)
    (hD : p*D*q=D) (C : ℕ → A) : p*shifted p q D C 0*q=D := by
  rw [shifted,mul_add,add_mul,hD,remainder_compression p q hp hq,add_zero]

 theorem shifted_succ_compression (p q D : A) (hp : p*p=p) (hq : q*q=q)
    (C : ℕ → A) (n : ℕ) : p*shifted p q D C (n+1)*q=part p q C n := by
  rw [shifted,mul_add,add_mul,part_supported p q hp hq,remainder_compression p q hp hq,add_zero]

 theorem recover (p q D : A) (hp : p*p=p) (hq : q*q=q) (hD : p*D*q=D)
    (C : ℕ → A) (n : ℕ) :
    C n=p*shifted p q D C (n+1)*q+shifted p q D C n-p*shifted p q D C n*q := by
  rw [shifted_succ_compression p q D hp hq]
  cases n with
  | zero => rw [shifted_zero_compression p q D hp hq hD,shifted,remainder];abel
  | succ n => rw [shifted_succ_compression p q D hp hq,shifted,remainder];abel

variable [StarRing A]
def paired (x y : A) : A := x+star y

 theorem paired_compression (p q x y : A) (hp : star p=p) (hq : star q=q) :
    paired (p*x*q) (q*y*p)=p*paired x y*q := by
  simp only [paired,star_mul,hp,hq,mul_add,add_mul,mul_assoc]

 theorem paired_shifted_zero (p q D E : A) (hp : star p=p) (hq : star q=q)
    (C F : ℕ → A) :
    paired (shifted p q D C 0) (shifted q p E F 0)=
      paired D E+paired (C 0) (F 0)-p*paired (C 0) (F 0)*q := by
  simp only [paired,shifted,remainder,part,star_add,star_sub,star_mul,hp,hq]
  noncomm_ring

 theorem paired_shifted_succ (p q D E : A) (hp : star p=p) (hq : star q=q)
    (C F : ℕ → A) (n : ℕ) :
    paired (shifted p q D C (n+1)) (shifted q p E F (n+1))=
      p*paired (C n) (F n)*q+paired (C (n+1)) (F (n+1))-
        p*paired (C (n+1)) (F (n+1))*q := by
  simp only [paired,shifted,remainder,part,star_add,star_sub,star_mul,hp,hq]
  noncomm_ring

 theorem recover_paired (p q D E : A) (hp : p*p=p) (hq : q*q=q)
    (hps : star p=p) (hqs : star q=q) (hD : p*D*q=D) (hE : q*E*p=E)
    (C F : ℕ → A) (n : ℕ) :
    paired (C n) (F n)=
      p*paired (shifted p q D C (n+1)) (shifted q p E F (n+1))*q+
      paired (shifted p q D C n) (shifted q p E F n)-
      p*paired (shifted p q D C n) (shifted q p E F n)*q := by
  have h := congrArg₂ paired (recover p q D hp hq hD C n) (recover q p E hq hp hE F n)
  rw [h]
  simp only [paired,star_sub,star_add,star_mul,hps,hqs]
  noncomm_ring

 theorem recover_supported_paired (p q D E : A) (hp : p*p=p) (hq : q*q=q)
    (hps : star p=p) (hqs : star q=q) (hD : p*D*q=D) (hE : q*E*p=E)
    (C F : ℕ → A) :
    paired D E=p*paired (shifted p q D C 0) (shifted q p E F 0)*q := by
  rw [← paired_compression p q _ _ hps hqs,
    shifted_zero_compression p q D hp hq hD,shifted_zero_compression q p E hq hp hE]

variable [Algebra ℂ A] [StarModule ℂ A]

 theorem generation_equivalence (p q D E : A) (hp : p*p=p) (hq : q*q=q)
    (hps : star p=p) (hqs : star q=q) (hD : p*D*q=D) (hE : q*E*p=E)
    (C F : ℕ → A) (M : StarSubalgebra ℂ A) (hMp : p∈M) (hMq : q∈M) :
    (paired D E∈M ∧ ∀ n,paired (C n) (F n)∈M) ↔
      ∀ n,paired (shifted p q D C n) (shifted q p E F n)∈M := by
  constructor
  · rintro ⟨hDE,hCF⟩ n
    cases n with
    | zero =>
      rw [paired_shifted_zero p q D E hps hqs]
      exact sub_mem (add_mem hDE (hCF 0)) (mul_mem (mul_mem hMp (hCF 0)) hMq)
    | succ n =>
      rw [paired_shifted_succ p q D E hps hqs]
      exact sub_mem (add_mem (mul_mem (mul_mem hMp (hCF n)) hMq) (hCF (n+1)))
        (mul_mem (mul_mem hMp (hCF (n+1))) hMq)
  · intro h
    constructor
    · rw [recover_supported_paired p q D E hp hq hps hqs hD hE C F]
      exact mul_mem (mul_mem hMp (h 0)) hMq
    · intro n
      rw [recover_paired p q D E hp hq hps hqs hD hE C F]
      exact sub_mem (add_mem (mul_mem (mul_mem hMp (h (n+1))) hMq) (h n))
        (mul_mem (mul_mem hMp (h n)) hMq)

end
section
variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

structure Data (B : StarSubalgebra ℂ A) where
  p : B
  q : B
  projection : IsStarProjection p
  projectionq : IsStarProjection q
  τ : B →ₗ[ℂ] ℂ
  tracial : ∀ a b,τ (a*b)=τ (b*a)
  C : ℕ → A
  D : A
  D_supported : (p:A)*D*(q:A)=D
  C_cov : ∀ (a : B) n m,star (C n)*(a:A)*C m=if n=m then τ a • (1:A) else 0
  D_cov : ∀ (a : B),star D*(a:A)*D=τ (a*p) • (q:A)
  C_D : ∀ (a : B) n,star (C n)*(a:A)*D=0
  D_C : ∀ (a : B) n,star D*(a:A)*C n=0

namespace Data
variable {B : StarSubalgebra ℂ A} (d : Data B)

 theorem p_square : (d.p:A)*(d.p:A)=(d.p:A) :=
  congrArg Subtype.val d.projection.isIdempotentElem.eq
 theorem p_star : star (d.p:A)=(d.p:A) :=
  congrArg Subtype.val d.projection.isSelfAdjoint.star_eq
 theorem q_square : (d.q:A)*(d.q:A)=(d.q:A) :=
  congrArg Subtype.val d.projectionq.isIdempotentElem.eq
 theorem q_star : star (d.q:A)=(d.q:A) :=
  congrArg Subtype.val d.projectionq.isSelfAdjoint.star_eq
 theorem trace_pa (a : B) : d.τ (d.p*a)=d.τ (a*d.p) := d.tracial _ _
 theorem trace_pap (a : B) : d.τ (d.p*a*d.p)=d.τ (a*d.p) := by
  rw [mul_assoc,d.tracial,mul_assoc,d.projection.isIdempotentElem.eq]

 theorem part_part (a : B) (n m : ℕ) :
    star (part (d.p:A) (d.q:A) d.C n)*(a:A)*part (d.p:A) (d.q:A) d.C m=
      if n=m then d.τ (a*d.p) • (d.q:A) else 0 := by
  calc
    _ = (d.q:A)*(star (d.C n)*((d.p*a*d.p:B):A)*d.C m)*(d.q:A) := by
      simp only [part,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul]
      noncomm_ring
    _ = _ := by
      rw [d.C_cov,d.trace_pap]
      split_ifs <;> simp only [mul_smul_comm,smul_mul_assoc,mul_one,d.q_square,mul_zero,zero_mul]

 theorem part_remainder (a : B) (n m : ℕ) :
    star (part (d.p:A) (d.q:A) d.C n)*(a:A)*remainder (d.p:A) (d.q:A) d.C m=0 := by
  calc
    _ = (d.q:A)*(star (d.C n)*((d.p*a:B):A)*d.C m)-
        (d.q:A)*(star (d.C n)*((d.p*a*d.p:B):A)*d.C m)*(d.q:A) := by
      simp only [part,remainder,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul]
      noncomm_ring
    _ = 0 := by
      rw [d.C_cov,d.C_cov,d.trace_pa,d.trace_pap]
      split_ifs <;>
        simp only [mul_smul_comm,smul_mul_assoc,mul_one,d.q_square,mul_zero,zero_mul,sub_self]

 theorem remainder_part (a : B) (n m : ℕ) :
    star (remainder (d.p:A) (d.q:A) d.C n)*(a:A)*part (d.p:A) (d.q:A) d.C m=0 := by
  have h := congrArg star (d.part_remainder (star a) m n)
  simpa only [star_mul,star_star,StarMemClass.coe_star,star_zero,mul_assoc] using h

 theorem remainder_remainder (a : B) (n m : ℕ) :
    star (remainder (d.p:A) (d.q:A) d.C n)*(a:A)*remainder (d.p:A) (d.q:A) d.C m=
      if n=m then d.τ a • (1:A)-d.τ (a*d.p) • (d.q:A) else 0 := by
  calc
    _ = star (d.C n)*(a:A)*d.C m-
        (star (d.C n)*((a*d.p:B):A)*d.C m)*(d.q:A)-
        (d.q:A)*(star (d.C n)*((d.p*a:B):A)*d.C m)+
        (d.q:A)*(star (d.C n)*((d.p*a*d.p:B):A)*d.C m)*(d.q:A) := by
      simp only [part,remainder,star_sub,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul]
      noncomm_ring
    _ = _ := by
      simp only [d.C_cov,d.trace_pa,d.trace_pap]
      split_ifs <;>
        simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,d.q_square,
          mul_zero,zero_mul,sub_zero,add_zero]
      all_goals abel

 theorem part_D (a : B) (n : ℕ) :
    star (part (d.p:A) (d.q:A) d.C n)*(a:A)*d.D=0 := by
  calc
    _ = (d.q:A)*(star (d.C n)*((d.p*a:B):A)*d.D) := by
      simp only [part,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [d.C_D,mul_zero]

 theorem D_part (a : B) (n : ℕ) :
    star d.D*(a:A)*part (d.p:A) (d.q:A) d.C n=0 := by
  calc
    _ = (star d.D*((a*d.p:B):A)*d.C n)*(d.q:A) := by
      simp only [part,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [d.D_C,zero_mul]

 theorem remainder_D (a : B) (n : ℕ) :
    star (remainder (d.p:A) (d.q:A) d.C n)*(a:A)*d.D=0 := by
  simp only [remainder,star_sub,sub_mul,d.C_D,d.part_D,sub_self]

 theorem D_remainder (a : B) (n : ℕ) :
    star d.D*(a:A)*remainder (d.p:A) (d.q:A) d.C n=0 := by
  simp only [remainder,mul_sub,d.D_C,d.D_part,sub_self]

 theorem shifted_covariance (a : B) (n m : ℕ) :
    star (shifted (d.p:A) (d.q:A) d.D d.C n)*(a:A)*shifted (d.p:A) (d.q:A) d.D d.C m=
      if n=m then d.τ a • (1:A) else 0 := by
  cases n with
  | zero =>
    cases m with
    | zero =>
      simp only [shifted,star_add,add_mul,mul_add,d.D_cov,d.D_remainder,d.remainder_D,
        d.remainder_remainder,ite_true,add_zero,zero_add]
      abel
    | succ m =>
      simp only [shifted,star_add,add_mul,mul_add,d.D_part,d.D_remainder,d.remainder_part,
        d.remainder_remainder,Nat.zero_ne_add_one,ite_false,add_zero]
  | succ n =>
    cases m with
    | zero =>
      simp only [shifted,star_add,add_mul,mul_add,d.part_D,d.part_remainder,d.remainder_D,
        d.remainder_remainder,Nat.add_one_ne_zero,ite_false,add_zero]
    | succ m =>
      simp only [shifted,star_add,add_mul,mul_add,d.part_part,d.part_remainder,d.remainder_part,
        d.remainder_remainder,Nat.add_right_cancel_iff,add_zero,zero_add]
      split_ifs <;> abel

end Data
end
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def Orthogonal (B : StarSubalgebra ℂ A) (x y : A) : Prop :=
  ∀ a : B,star x*(a:A)*y=0

namespace Orthogonal
variable {B : StarSubalgebra ℂ A} {x y z : A}
 theorem add_left (h : Orthogonal B x z) (k : Orthogonal B y z) : Orthogonal B (x+y) z := by
  intro a
  simp only [star_add,add_mul,h a,k a,add_zero]
 theorem sub_left (h : Orthogonal B x z) (k : Orthogonal B y z) : Orthogonal B (x-y) z := by
  intro a
  simp only [star_sub,sub_mul,h a,k a,sub_self]
 theorem add_right (h : Orthogonal B x y) (k : Orthogonal B x z) : Orthogonal B x (y+z) := by
  intro a
  simp only [mul_add,h a,k a,add_zero]
 theorem sub_right (h : Orthogonal B x y) (k : Orthogonal B x z) : Orthogonal B x (y-z) := by
  intro a
  simp only [mul_sub,h a,k a,sub_self]
 theorem symm (h : Orthogonal B x y) : Orthogonal B y x := by
  intro a
  have ht := congrArg star (h (star a))
  simpa only [star_mul,star_star,StarMemClass.coe_star,star_zero,mul_assoc] using ht
 theorem sandwich_left (h : Orthogonal B x y) (p q : B) :
    Orthogonal B ((p:A)*x*(q:A)) y := by
  intro a
  calc
    _ = star (q:A)*(star x*((star p*a:B):A)*y) := by
      simp only [star_mul,StarMemClass.coe_star,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [h (star p*a),mul_zero]
 theorem sandwich_right (h : Orthogonal B x y) (p q : B) :
    Orthogonal B x ((p:A)*y*(q:A)) := (h.symm.sandwich_left p q).symm

 theorem part_left {C : ℕ → A} (h : ∀ n,Orthogonal B (C n) y) (p q : B) (n : ℕ) :
    Orthogonal B (part (p:A) (q:A) C n) y := (h n).sandwich_left p q
 theorem part_right {C : ℕ → A} (h : ∀ n,Orthogonal B x (C n)) (p q : B) (n : ℕ) :
    Orthogonal B x (part (p:A) (q:A) C n) := (h n).sandwich_right p q
 theorem remainder_left {C : ℕ → A} (h : ∀ n,Orthogonal B (C n) y) (p q : B) (n : ℕ) :
    Orthogonal B (remainder (p:A) (q:A) C n) y := (h n).sub_left (part_left h p q n)
 theorem remainder_right {C : ℕ → A} (h : ∀ n,Orthogonal B x (C n)) (p q : B) (n : ℕ) :
    Orthogonal B x (remainder (p:A) (q:A) C n) := (h n).sub_right (part_right h p q n)

 theorem shifted_left {C : ℕ → A} {D : A} (hD : Orthogonal B D y)
    (hC : ∀ n,Orthogonal B (C n) y) (p q : B) (n : ℕ) :
    Orthogonal B (shifted (p:A) (q:A) D C n) y := by
  cases n with
  | zero => exact hD.add_left (remainder_left hC p q 0)
  | succ n => exact (part_left hC p q n).add_left (remainder_left hC p q (n+1))
 theorem shifted_right {C : ℕ → A} {D : A} (hD : Orthogonal B x D)
    (hC : ∀ n,Orthogonal B x (C n)) (p q : B) (n : ℕ) :
    Orthogonal B x (shifted (p:A) (q:A) D C n) :=
  (shifted_left hD.symm (fun n => (hC n).symm) p q n).symm

 theorem shifted {C F : ℕ → A} {D E : A} (hDE : Orthogonal B D E)
    (hDF : ∀ m,Orthogonal B D (F m)) (hCE : ∀ n,Orthogonal B (C n) E)
    (hCF : ∀ n m,Orthogonal B (C n) (F m)) (p q r s : B) (n m : ℕ) :
    Orthogonal B (RectangularAbsorption.shifted (p:A) (q:A) D C n)
      (RectangularAbsorption.shifted (r:A) (s:A) E F m) :=
  shifted_left (shifted_right hDE hDF r s m)
    (fun n => shifted_right (hCE n) (hCF n) r s m) p q n
end Orthogonal

structure Family (B : StarSubalgebra ℂ A) (I : Type u_4) where
  data : I → Data B
  CC : ∀ i j,i≠j → ∀ n m,Orthogonal B ((data i).C n) ((data j).C m)
  CD : ∀ i j,i≠j → ∀ n,Orthogonal B ((data i).C n) (data j).D
  DD : ∀ i j,i≠j → Orthogonal B (data i).D (data j).D

namespace Family
open scoped Classical
variable {B : StarSubalgebra ℂ A} {I : Type u_5} (d : Family B I)

def output (i : I) (n : ℕ) : A :=
  shifted ((d.data i).p:A) ((d.data i).q:A) (d.data i).D (d.data i).C n

 theorem output_cross {i j : I} (hij : i≠j) (n m : ℕ) :
    Orthogonal B (d.output i n) (d.output j m) :=
  Orthogonal.shifted (d.DD i j hij)
    (fun m => (d.CD j i hij.symm m).symm) (d.CD i j hij) (d.CC i j hij)
    (d.data i).p (d.data i).q (d.data j).p (d.data j).q n m

 theorem output_covariance (i j : I) (n m : ℕ) (a : B) :
    star (d.output i n)*(a:A)*d.output j m=
      if i=j ∧ n=m then (d.data i).τ a • (1:A) else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    simpa only [output,true_and] using (d.data i).shifted_covariance a n m
  · rw [ite_eq_right (fun h => hij h.1)]
    exact d.output_cross hij n m a

 theorem output_generation (σ : I → I)
    (hpq : ∀ i,(d.data (σ i)).p=(d.data i).q)
    (hqp : ∀ i,(d.data (σ i)).q=(d.data i).p)
    (M : StarSubalgebra ℂ A)
    (hpM : ∀ i,((d.data i).p:A)∈M) (hqM : ∀ i,((d.data i).q:A)∈M) :
    ((∀ i,paired (d.data i).D (d.data (σ i)).D∈M) ∧
      ∀ i n,paired ((d.data i).C n) ((d.data (σ i)).C n)∈M) ↔
        ∀ i n,paired (d.output i n) (d.output (σ i) n)∈M := by
  have he (i : I) :
      (paired (d.data i).D (d.data (σ i)).D∈M ∧
        ∀ n,paired ((d.data i).C n) ((d.data (σ i)).C n)∈M) ↔
          ∀ n,paired (d.output i n) (d.output (σ i) n)∈M := by
    have hE : ((d.data i).q:A)*(d.data (σ i)).D*((d.data i).p:A)=(d.data (σ i)).D := by
      simpa only [hpq,hqp] using (d.data (σ i)).D_supported
    simpa only [output,hpq,hqp] using
      generation_equivalence ((d.data i).p:A) ((d.data i).q:A) (d.data i).D (d.data (σ i)).D
        (d.data i).p_square (d.data i).q_square (d.data i).p_star (d.data i).q_star
        (d.data i).D_supported hE (d.data i).C (d.data (σ i)).C M (hpM i) (hqM i)
  constructor
  · rintro ⟨hD,hC⟩ i
    exact (he i).mp ⟨hD i,hC i⟩
  · intro h
    exact ⟨fun i => ((he i).mpr (h i)).1,fun i => ((he i).mpr (h i)).2⟩

end Family
end FreeGroupFactorMain.RectangularAbsorption

end

end OAI
