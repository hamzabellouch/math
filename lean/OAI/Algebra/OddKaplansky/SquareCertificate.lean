import OAI.Algebra.OddKaplansky.Compression

namespace OAI

universe contextUniverse1 contextUniverse2 contextUniverse3

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.SquareCertificate
noncomputable section
open scoped Classical BigOperators Matrix
variable {S : Type portUniverse1} {R : Type portUniverse2} {N : Type portUniverse3} [Ring S] [Fintype R] [sectionInstance75 : Fintype N]
def cutD (σ : R → N) (D : Matrix N R S) : Matrix R R S := fun i j => D (σ i) j
def cutC (σ : R → N) (C : Matrix R N S) : Matrix R R S := fun i j => C i (σ j)
def A (f : S) (σ : R → N) (D : Matrix N R S) : Matrix R R S := cutD σ D + Matrix.diagonal (fun _ => 1-f)
def B (f : S) (σ : R → N) (C : Matrix R N S) : Matrix R R S := cutC σ C + Matrix.diagonal (fun _ => 1-f)
lemma sector_right (f x : S) (hc : Commute f x) (hx : f*x=x) : x*f=x := hc.eq.symm.trans hx
lemma complement_left (f x : S) (hx : f*x=x) : (1-f)*x=0 := by rw [sub_mul,one_mul,hx,sub_self]
lemma complement_right (f x : S) (hx : x*f=x) : x*(1-f)=0 := by rw [mul_sub,mul_one,hx,sub_self]
lemma products
    {S : Type contextUniverse1}
    {R : Type contextUniverse2}
    {N : Type contextUniverse3}
    [Ring.{contextUniverse1} S]
    [Fintype.{contextUniverse2} R]
    [Fintype.{contextUniverse3} N] (f : S) (hf : f*f=f) (hc : ∀ x, Commute f x)
    (σ : R → N) (hσ : Function.Injective σ) (C : Matrix R N S) (D : Matrix N R S)
    (hC : ∀ i j, f*C i j=C i j) (hD : ∀ i j, f*D i j=D i j)
    (hDC : D*C=Matrix.diagonal (fun _ => f)) : A f σ D * B f σ C=1 := by
  have hDC' : cutD σ D*cutC σ C=Matrix.diagonal (fun _ => f) := by
    funext i j
    change (D*C) (σ i) (σ j)=_
    rw [hDC]
    simp [Matrix.diagonal_apply,hσ.eq_iff]
  have hleft : Matrix.diagonal (fun _ : R => 1-f)*cutC σ C=0 := by
    funext i j
    rw [Matrix.diagonal_mul]
    exact complement_left f _ (hC i (σ j))
  have hright : cutD σ D*Matrix.diagonal (fun _ : R => 1-f)=0 := by
    funext i j
    rw [Matrix.mul_diagonal]
    exact complement_right f _ (sector_right f _ (hc _) (hD (σ i) j))
  have hcomp : Matrix.diagonal (fun _ : R => 1-f)*Matrix.diagonal (fun _ : R => 1-f)=Matrix.diagonal (fun _ : R => 1-f) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    noncomm_ring [hf]
  rw [A,B,add_mul,mul_add,mul_add,hDC',hleft,hright,hcomp]
  funext i j
  by_cases he : i=j <;> simp [he,Matrix.one_apply]

def u (f : S) (a : N) : N → S := Pi.single a f
def v (f : S) (C : Matrix R N S) (a : N) : R → S := C *ᵥ u f a
lemma certificate (f : S) (hf : f*f=f) (hf0 : f ≠ 0) (_hc : ∀ x, Commute f x)
    (σ : R → N) (C : Matrix R N S) (D : Matrix N R S)
    (hC : ∀ i j, f*C i j=C i j)
    (hDC : D*C=Matrix.diagonal (fun _ => f)) (a : N) (ha : ∀ i, σ i ≠ a) :
    v f C a ≠ 0 ∧ D *ᵥ v f C a=u f a ∧ A f σ D *ᵥ v f C a=0 ∧ (B f σ C*A f σ D-1)*ᵥ v f C a = -v f C a := by
  have hDu : D *ᵥ v f C a=u f a := by
    rw [v,Matrix.mulVec_mulVec,hDC]
    funext i
    simp only [Matrix.mulVec_diagonal,u]
    by_cases hi : i=a
    · subst i; simp [hf]
    · simp [hi]
  have hu : u f a ≠ 0 := by
    intro he
    have hh := congrFun he a
    exact hf0 (by simpa [u] using hh)
  have hv : v f C a ≠ 0 := by
    intro he
    rw [he,Matrix.mulVec_zero] at hDu
    exact hu hDu.symm
  have hvs (i : R) : f*v f C a i=v f C a i := by
    simp only [v,Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc,hC]
  have hAv : A f σ D *ᵥ v f C a=0 := by
    rw [A,Matrix.add_mulVec]
    have hcut : cutD σ D *ᵥ v f C a=0 := by
      funext i
      change (D *ᵥ v f C a) (σ i)=0
      rw [hDu]
      simp [u,ha i]
    rw [hcut,zero_add]
    funext i
    rw [Matrix.mulVec_diagonal]
    exact complement_left f _ (hvs i)
  refine ⟨hv,hDu,hAv,?_⟩
  rw [Matrix.sub_mulVec,← Matrix.mulVec_mulVec,hAv,Matrix.mulVec_zero,Matrix.one_mulVec,zero_sub]
lemma reverse_ne (f : S) (hf : f*f=f) (hf0 : f ≠ 0) (hc : ∀ x, Commute f x)
    (σ : R → N) (C : Matrix R N S) (D : Matrix N R S)
    (hC : ∀ i j, f*C i j=C i j)
    (hDC : D*C=Matrix.diagonal (fun _ => f)) (a : N) (ha : ∀ i, σ i ≠ a) : B f σ C*A f σ D ≠ 1 := by
  obtain ⟨hv,_,hAv,_⟩ := certificate f hf hf0 hc σ C D hC hDC a ha
  intro he
  have hh := congrArg (fun E => E *ᵥ v f C a) he
  rw [← Matrix.mulVec_mulVec,hAv,Matrix.mulVec_zero,Matrix.one_mulVec] at hh
  exact hv hh.symm
end
end OddKaplansky.SquareCertificate

end

end OAI
