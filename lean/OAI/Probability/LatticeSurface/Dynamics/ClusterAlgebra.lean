import Mathlib

namespace OAI

noncomputable section

namespace ClusterDisplacement

open Set

variable {V I : Type*} [Fintype V] [Fintype I]

def energy (u : V → ℝ) : ℝ := ∑x,u x^2

lemma weighted_sq_le (w d : I → ℝ) (hw : ∀i,0≤w i) (hs : (∑i,w i)≤1) :
    (∑i,w i*d i)^2≤∑i,w i*d i^2 := by
  let m:=∑i,w i*d i
  have hn : 0≤(∑i,w i*(d i-m)^2)+(1-∑i,w i)*m^2 :=
    add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)) (mul_nonneg (by linarith) (sq_nonneg _))
  have hi : (∑i,w i*(d i-m)^2)+(1-∑i,w i)*m^2=(∑i,w i*d i^2)-m^2 := by
    have hs' : (∑i,w i*(d i-m)^2)=(∑i,w i*d i^2)-2*m*(∑i,w i*d i)+m^2*(∑i,w i) := by
      simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi;ring
    rw [hs']
    change (∑i,w i*d i^2)-2*m*m+m^2*(∑i,w i)+(1-∑i,w i)*m^2=(∑i,w i*d i^2)-m^2
    ring
  rw [hi] at hn
  linarith

structure Kernel (V : Type*) [Fintype V] where
  val : V → V → ℝ
  nonneg : ∀x y,0≤val x y
  row : ∀x,(∑y,val x y)≤1
  col : ∀y,(∑x,val x y)≤1

def Kernel.apply (K : Kernel V) (u : V → ℝ) (x : V) : ℝ := ∑y,K.val x y*u y

lemma Kernel.apply_nonneg (K : Kernel V) (u : V → ℝ) (hu : ∀x,0≤u x) (x : V) : 0≤K.apply u x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (K.nonneg x y) (hu y)

lemma Kernel.square_bound (K : Kernel V) (u : V → ℝ) (x : V) :
    (K.apply u x)^2≤∑y,K.val x y*u y^2 := weighted_sq_le _ _ (K.nonneg x) (K.row x)

lemma Kernel.energy_bound (K : Kernel V) (u : V → ℝ) : energy (K.apply u)≤energy u := by
  calc
    _ ≤ ∑x,∑y,K.val x y*u y^2 := Finset.sum_le_sum fun x _ => K.square_bound u x
    _ = ∑y,(∑x,K.val x y)*u y^2 := by rw [Finset.sum_comm];simp only [Finset.sum_mul]
    _ ≤ energy u := Finset.sum_le_sum fun y _ => by simpa using mul_le_mul_of_nonneg_right (K.col y) (sq_nonneg (u y))

def Kernel.identity : Kernel V := by
  classical
  exact {val := fun x y => if x=y then 1 else 0
         nonneg := fun x y => by split_ifs <;> norm_num
         row := fun x => by simp
         col := fun y => by simp}

lemma Kernel.identity_apply (u : V → ℝ) : Kernel.identity.apply u=u := by
  classical
  funext x
  simp [Kernel.apply,Kernel.identity]

def Kernel.comp (A B : Kernel V) : Kernel V where
  val x y := ∑z,A.val x z*B.val z y
  nonneg x y := Finset.sum_nonneg fun z _ => mul_nonneg (A.nonneg x z) (B.nonneg z y)
  row x := by
    calc
      _ = ∑z,A.val x z*(∑y,B.val z y) := by rw [Finset.sum_comm];simp only [Finset.mul_sum]
      _ ≤ ∑z,A.val x z := Finset.sum_le_sum fun z _ => by simpa using mul_le_mul_of_nonneg_left (B.row z) (A.nonneg x z)
      _ ≤ 1 := A.row x
  col y := by
    calc
      _ = ∑z,(∑x,A.val x z)*B.val z y := by rw [Finset.sum_comm];simp only [Finset.sum_mul]
      _ ≤ ∑z,B.val z y := Finset.sum_le_sum fun z _ => by simpa using mul_le_mul_of_nonneg_right (A.col z) (B.nonneg z y)
      _ ≤ 1 := B.col y

lemma Kernel.comp_apply (A B : Kernel V) (u : V → ℝ) : (A.comp B).apply u=A.apply (B.apply u) := by
  funext x
  simp only [Kernel.apply,Kernel.comp,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

lemma Kernel.row_deficit_nonneg (K : Kernel V) (u : V → ℝ) (x : V) :
    0≤(∑y,K.val x y*u y^2)-(K.apply u x)^2 := sub_nonneg.mpr (K.square_bound u x)

lemma Kernel.row_deficit_le (K : Kernel V) (u : V → ℝ) (x : V) :
    (∑y,K.val x y*u y^2)-(K.apply u x)^2≤energy u-energy (K.apply u) := by
  classical
  calc
    _ ≤ ∑z,((∑y,K.val z y*u y^2)-(K.apply u z)^2) := Finset.single_le_sum (fun z _ => K.row_deficit_nonneg u z) (Finset.mem_univ x)
    _ = (∑y,(∑z,K.val z y)*u y^2)-energy (K.apply u) := by rw [Finset.sum_sub_distrib,Finset.sum_comm];simp only [Finset.sum_mul,energy]
    _ ≤ _ := sub_le_sub_right (Finset.sum_le_sum fun y _ => by simpa using mul_le_mul_of_nonneg_right (K.col y) (sq_nonneg (u y))) _

lemma Kernel.near_initial_level (K : Kernel V) (u : V → ℝ) (x : V) (D : ℝ)
    (hD : energy u-energy (K.apply u)≤D) :
    ∃ y : V ⊕ Unit,|K.apply u x-(Sum.elim u (fun _ => 0)) y|≤Real.sqrt D := by
  classical
  let m:=K.apply u x
  let r:=Real.sqrt D
  have hD0 : 0≤D := le_trans (sub_nonneg.mpr (K.energy_bound u)) hD
  have hr : r^2=D := Real.sq_sqrt hD0
  have hr0 : 0≤r := Real.sqrt_nonneg D
  have hd := (K.row_deficit_le u x).trans hD
  have hv : (∑y,K.val x y*(m-u y)^2)+(1-∑y,K.val x y)*m^2=(∑y,K.val x y*u y^2)-m^2 := by
    have hi : (∑y,K.val x y*(m-u y)^2)=(∑y,K.val x y)*m^2-2*m*(∑y,K.val x y*u y)+(∑y,K.val x y*u y^2) := by
      simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y hy;ring
    rw [hi]
    change (∑y,K.val x y)*m^2-2*m*m+(∑y,K.val x y*u y^2)+(1-∑y,K.val x y)*m^2=(∑y,K.val x y*u y^2)-m^2
    ring
  by_contra hn
  push Not at hn
  have hdist (y : V ⊕ Unit) : D<(m-(Sum.elim u (fun _ => 0)) y)^2 := by
    have h:=hn y
    change r < |m-(Sum.elim u (fun _ => 0)) y| at h
    nlinarith [sq_abs (m-(Sum.elim u (fun _ => 0)) y)]
  have hw : 0≤1-∑y,K.val x y := sub_nonneg.mpr (K.row x)
  have hle (y : V) : K.val x y*D≤K.val x y*(m-u y)^2 := mul_le_mul_of_nonneg_left (hdist (.inl y)).le (K.nonneg x y)
  have hzero : D < m^2 := by simpa using hdist (.inr ())
  by_cases hwpos : 0<1-∑y,K.val x y
  · have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hle y)
    simp only [← Finset.sum_mul] at hsum
    have hs := mul_lt_mul_of_pos_left hzero hwpos
    nlinarith [hv]
  · have hweq : (∑y,K.val x y)=1 := by linarith
    obtain ⟨y,hy⟩ : ∃y,0<K.val x y := by
      by_contra h
      push Not at h
      have hz : (∑y,K.val x y)≤0 := Finset.sum_nonpos fun y _ => h y
      linarith
    have hstrict := Finset.sum_lt_sum (fun y _ => hle y) ⟨y,Finset.mem_univ y,mul_lt_mul_of_pos_left (hdist (.inl y)) hy⟩
    simp only [← Finset.sum_mul,hweq,one_mul] at hstrict
    rw [hweq] at hv
    nlinarith

end ClusterDisplacement

end

end OAI
