import Mathlib
import OAI.Probability.SKGap.Gaussian.PhiStein
import OAI.Probability.SKGap.Localization.PrimaryDifferentiation

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Primary
open Matrix SKGap.Stein
variable {n : ℕ}

def mag (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  (primaryState j J h k).1

def fld (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  (primaryState j J h k).2

def onsager (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : Spin n→ℝ :=
  siteMean (fun x i=>1-(mag j J h k x i)^2)

def residual (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  fun x i=>mag j J h k x i-mag j J h (k+1) x i

def previousResidual (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : VectorFields n :=
  fun x i=>mag j J h (k-1) x i-mag j J h k x i

lemma mag_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) : mag j J h 0=spin := rfl
lemma mag_succ (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) (i : Fin n) :
    mag j J h (k+1) x i=Real.tanh (fld j J h k x i) := rfl
lemma onsager_zero (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    onsager j J h 0 x=0 := by simp [onsager,siteMean,mag_zero,spin_sq]

lemma fld_eq (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) (i : Fin n) :
    fld j J h k x i=h i+∑a,J i a*mag j J h k x a-
      j*onsager j J h k x*mag j J h (k-1) x i := by
  cases k with
  | zero => simp [fld,primaryState,mag,onsager_zero]
  | succ k => rfl

lemma primary_residual_field (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) (i : Fin n) :
    let a:=j*(onsager j J h (k+1) x-onsager j J h k x)
    fld j J h k x i-fld j J h (k+1) x i-a*mag j J h (k+1) x i=
      (∑l,J i l*residual j J h k x l)+a*residual j J h k x i-
        j*onsager j J h k x*previousResidual j J h k x i := by
  dsimp only
  rw [fld_eq,fld_eq]
  simp only [Nat.add_sub_cancel,residual,previousResidual,mul_sub,Finset.sum_sub_distrib]
  ring

lemma residual_inner_product (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    (∑i,residual j J h k x i*mag j J h k x i)=
      (n:ℝ)*(onsager j J h (k+1) x-onsager j J h k x)-
      ∑i,residual j J h k x i*mag j J h (k+1) x i := by
  have hnR : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [onsager,siteMean,mul_sub,mul_div_cancel₀ _ hnR]
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [residual]
  ring

lemma mulVec_pair_symmetric (J : Interaction n) (hJ : J.IsSymm) (u v : Fin n→ℝ) :
    (∑i,(∑l,J i l*u l)*v i)=∑l,u l*(∑i,J l i*v i) := by
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro i _
  rw [hJ.apply i l]
  ring

def steinSource (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) : VectorFields n := fun x i=>
  phi (fld j J h k x i) (fld j J h (k+1) x i)
    (j*(onsager j J h (k+1) x-onsager j J h k x))*U x i

def steinPartial (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) : VectorFields n := fun x i=>
  phiZ (fld j J h k x i) (fld j J h (k+1) x i)
    (j*(onsager j J h (k+1) x-onsager j J h k x))*U x i

lemma stein_residual_pointwise (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) (x : Spin n) (i : Fin n) :
    residual j J h (k+1) x i*U x i=
      (fld j J h k x i-fld j J h (k+1) x i-
        j*(onsager j J h (k+1) x-onsager j J h k x)*mag j J h (k+1) x i)*
      steinSource j J h k U x i-
      j*(onsager j J h (k+1) x-onsager j J h k x)*steinPartial j J h k U x i := by
  dsimp only [steinSource,steinPartial,residual]
  simp only [mag_succ]
  rw [←phi_stein (fld j J h k x i) (fld j J h (k+1) x i)
    (j*(onsager j J h (k+1) x-onsager j J h k x))]
  ring

def nextField {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) (L : ι→ℕ) (α : ι→Spin n→ℝ)
    (W : κ→VectorFields n) (γ : κ→Spin n→ℝ) : VectorFields n := fun x i=>
  (∑l,J i l*steinSource j J h k U x l)-
  j*siteMean (steinPartial j J h k U) x*mag j J h k x i-
  j*(∑l,α l x*mag j J h (L l) x i)-j*∑b,γ b x*W b x i

theorem residual_induction_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hn : 0<n) (j : ℝ) (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ) (k : ℕ)
    (U : VectorFields n) (L : ι→ℕ) (α : ι→Spin n→ℝ)
    (W : κ→VectorFields n) (γ : κ→Spin n→ℝ) (x : Spin n) :
    (∑i,residual j J h (k+1) x i*U x i)=
      (∑i,residual j J h k x i*nextField j J h k U L α W γ x i)+
      j*(onsager j J h (k+1) x-onsager j J h k x)*
        (∑i,residual j J h k x i*steinSource j J h k U x i)-
      j*onsager j J h k x*(∑i,previousResidual j J h k x i*steinSource j J h k U x i)+
      j*(∑b,γ b x*∑i,residual j J h k x i*W b x i)+
      j*(∑l,α l x*∑i,residual j J h k x i*mag j J h (L l) x i)-
      j*siteMean (steinPartial j J h k U) x*
        (∑i,residual j J h k x i*mag j J h (k+1) x i) := by
  have hnR : (n:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hsum : (∑i,steinPartial j J h k U x i)=
      (n:ℝ)*siteMean (steinPartial j J h k U) x := by
    dsimp [siteMean]; field_simp
  have he:=residual_inner_product hn j J h k x
  have hs:=mulVec_pair_symmetric J hJ (residual j J h k x) (steinSource j J h k U x)
  have hon := primary_residual_field j J h k x
  have hfirst : (∑i,residual j J h (k+1) x i*U x i)=
      (∑i,(∑l,J i l*residual j J h k x l)*steinSource j J h k U x i)+
       j*(onsager j J h (k+1) x-onsager j J h k x)*
         (∑i,residual j J h k x i*steinSource j J h k U x i)-
       j*onsager j J h k x*(∑i,previousResidual j J h k x i*steinSource j J h k U x i)-
       j*(onsager j J h (k+1) x-onsager j J h k x)*
         (n:ℝ)*siteMean (steinPartial j J h k U) x := by
    simp_rw [stein_residual_pointwise j J h k U x,primary_residual_field]
    simp only [add_mul,sub_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ←Finset.mul_sum,mul_assoc]
    rw [hsum]
  rw [hs] at hfirst
  have hy : (∑i,residual j J h k x i*nextField j J h k U L α W γ x i)=
      (∑i,residual j J h k x i*(∑l,J i l*steinSource j J h k U x l))-
      j*siteMean (steinPartial j J h k U) x*(∑i,residual j J h k x i*mag j J h k x i)-
      j*(∑l,α l x*∑i,residual j J h k x i*mag j J h (L l) x i)-
      j*(∑b,γ b x*∑i,residual j J h k x i*W b x i) := by
    dsimp [nextField]
    simp only [mul_sub,Finset.sum_sub_distrib]
    congr 2
    · congr 1
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro i _; ring
    · simp only [Finset.mul_sum]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro i _; ring
  rw [hy,he,hfirst]
  ring

end SKGapCutoff.Primary

end
end

end OAI
