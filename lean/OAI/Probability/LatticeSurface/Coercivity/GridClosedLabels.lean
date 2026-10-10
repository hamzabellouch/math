import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridClosedLabels

def potential {A : Type*} [AddCommGroup A] (H V : ℕ → ℕ → A) (i j : ℕ) : A :=
  (∑ k ∈ Finset.range i, H k 0) + ∑ k ∈ Finset.range j, V i k

lemma potential_vertical {A : Type*} [AddCommGroup A] (H V : ℕ → ℕ → A) (i j : ℕ) :
    potential H V i (j+1)-potential H V i j = V i j := by
  simp only [potential,Finset.sum_range_succ]
  abel

lemma telescope_faces {A : Type*} [AddCommGroup A] (H V : ℕ → ℕ → A)
    {N i j : ℕ} (hi : i < N) (hj : j ≤ N)
    (hface : ∀ a < N, ∀ b < N, H a (b+1)-H a b = V (a+1) b-V a b) :
    H i j-H i 0 = (∑ k ∈ Finset.range j, V (i+1) k) - ∑ k ∈ Finset.range j, V i k := by
  rw [← Finset.sum_sub_distrib,← Finset.sum_range_sub (H i)]
  apply Finset.sum_congr rfl
  intro k hk
  exact hface i hi k ((Finset.mem_range.mp hk).trans_le hj)

lemma potential_horizontal {A : Type*} [AddCommGroup A] (H V : ℕ → ℕ → A)
    {N i j : ℕ} (hi : i < N) (hj : j ≤ N)
    (hface : ∀ a < N, ∀ b < N, H a (b+1)-H a b = V (a+1) b-V a b) :
    potential H V (i+1) j-potential H V i j = H i j := by
  have h := telescope_faces H V hi hj hface
  calc
    potential H V (i+1) j-potential H V i j =
        H i 0 + ((∑ k ∈ Finset.range j, V (i+1) k) - ∑ k ∈ Finset.range j, V i k) := by
      simp only [potential, Finset.sum_range_succ]
      abel
    _ = H i 0 + (H i j - H i 0) := by rw [← h]
    _ = H i j := by abel

theorem exact_of_closed {A : Type*} [AddCommGroup A] (N : ℕ) (H V : ℕ → ℕ → A)
    (hface : ∀ a < N, ∀ b < N, H a (b+1)-H a b = V (a+1) b-V a b) :
    ∃ f : ℕ → ℕ → A,
      (∀ i < N, ∀ j ≤ N, f (i+1) j-f i j=H i j) ∧
      (∀ i ≤ N, ∀ j < N, f i (j+1)-f i j=V i j) := by
  refine ⟨potential H V,?_,?_⟩
  · intro i hi j hj;exact potential_horizontal H V hi hj hface
  · intro i hi j hj;exact potential_vertical H V i j

end GridClosedLabels

namespace GridClosedLabels

def rayPotential {A : Type*} [AddCommGroup A] (H : ℤ → ℤ → A) (a x y : ℤ) : A :=
  ∑ k ∈ Finset.range (x-a).toNat, H (a+k) y

lemma ray_horizontal {A : Type*} [AddCommGroup A] (H : ℤ → ℤ → A) (a x y : ℤ)
    (hleft : ∀ x < a, ∀ y, H x y=0) :
    rayPotential H a (x+1) y-rayPotential H a x y=H x y := by
  by_cases hx : a ≤ x
  · have hn : (x+1-a).toNat=(x-a).toNat+1 := by omega
    have he : a+((x-a).toNat:ℤ)=x := by omega
    simp only [rayPotential,hn,Finset.sum_range_succ,he]
    abel
  · have hn : (x-a).toNat=0 := by omega
    have hn' : (x+1-a).toNat=0 := by omega
    simp [rayPotential,hn,hn',hleft x (by omega) y]

lemma ray_vertical {A : Type*} [AddCommGroup A] (H V : ℤ → ℤ → A) (a x y : ℤ)
    (hleft : ∀ x ≤ a, ∀ y, V x y=0)
    (hface : ∀ x y, H x (y+1)-H x y=V (x+1) y-V x y) :
    rayPotential H a x (y+1)-rayPotential H a x y=V x y := by
  by_cases hx : a ≤ x
  · have he : a+((x-a).toNat:ℤ)=x := by omega
    change (∑ k ∈ Finset.range (x-a).toNat, H (a+k) (y+1)) -
      (∑ k ∈ Finset.range (x-a).toNat, H (a+k) y) = V x y
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ k ∈ Finset.range (x-a).toNat,
          (V (a+((k+1:ℕ):ℤ)) y-V (a+k) y) := by
        apply Finset.sum_congr rfl
        intro k hk
        simpa [Nat.cast_add,Nat.cast_one,add_assoc] using hface (a+k) y
      _ = V (a+((x-a).toNat:ℤ)) y-V (a+0) y := by
        simpa only [Nat.cast_zero] using
          Finset.sum_range_sub (fun k : ℕ => V (a+(k:ℤ)) y) (x-a).toNat
      _ = V x y := by rw [he,add_zero,hleft a le_rfl y,sub_zero]
  · have hn : (x-a).toNat=0 := by omega
    simp [rayPotential,hn,hleft x (by omega) y]

lemma square_binary (b0 b1 b2 b3 : Bool) (s0 s1 s2 s3 : ZMod 2)
    (h0 : b0=true → s0=0) (h1 : b1=true → s1=0)
    (h2 : b2=true → s2=0) (h3 : b3=true → s3=0)
    (h01 : b0=false → b1=false → s0=s1)
    (h12 : b1=false → b2=false → s1=s2)
    (h23 : b2=false → b3=false → s2=s3)
    (h30 : b3=false → b0=false → s3=s0) :
    ((if b3 then s2 else 0)+(if b2 then s3 else 0)) -
      ((if b0 then s1 else 0)+(if b1 then s0 else 0)) =
    ((if b1 then s2 else 0)+(if b2 then s1 else 0)) -
      ((if b0 then s3 else 0)+(if b3 then s0 else 0)) := by
  have hneg : ∀ z : ZMod 2, -z=z := by decide
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> simp_all [sub_eq_add_neg]
  ring

end GridClosedLabels

end

end OAI
