import Mathlib

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A] [DecidableEq A]

def energy (S F : Finset A) (u : A → ℝ) : ℝ :=
  ∑ x∈F, ∑ s∈S, (u (x*s)-u x)^2

omit [DecidableEq A] in
lemma energy_nonneg (S F : Finset A) (u : A → ℝ) : 0≤energy S F u := by
  exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun s _ => sq_nonneg _))

omit [DecidableEq A] in
lemma energy_mono (S : Finset A) {F H : Finset A} (h : F⊆H) (u : A → ℝ) :
    energy S F u≤energy S H u := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro x _ _
  exact Finset.sum_nonneg (fun s _ => sq_nonneg _)

lemma shifted_gradient_le_energy (S : Finset A) (u : A → ℝ)
    (r n : ℕ) (a s : A) (ha : a∈S^n) (hs : s∈S) :
    (∑ x∈S^r, (u ((x*a)*s)-u (x*a))^2)≤energy S (S^(r+n)) u := by
  let F := (S^r).image (fun x => x*a)
  have hF : F⊆S^(r+n) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    rw [pow_add]
    exact Finset.mem_mul.mpr ⟨x,hx,a,ha,rfl⟩
  calc
    _ = ∑ y∈F, (u (y*s)-u y)^2 := by
      rw [Finset.sum_image]
      intro x _ y _ h
      exact mul_right_cancel h
    _ ≤ energy S F u := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.single_le_sum (f := fun b : A => (u (x*b)-u x)^2)
        (fun b _ => sq_nonneg _) hs
    _ ≤ energy S (S^(r+n)) u := energy_mono S hF u

lemma word_difference_energy (S : Finset A) (h1 : (1:A)∈S)
    (u : A → ℝ) (r n : ℕ) (a : A) (ha : a∈S^n) :
    (∑ x∈S^r, (u (x*a)-u x)^2)≤(n:ℝ)^2*energy S (S^(r+n)) u := by
  induction n generalizing a with
  | zero =>
    have he : a=1 := by simpa using ha
    simp [he]
  | succ n ih =>
    rw [pow_succ] at ha
    obtain ⟨b,hb,s,hs,rfl⟩ := Finset.mem_mul.mp ha
    let E := energy S (S^(r+(n+1))) u
    have hmono : energy S (S^(r+n)) u≤E :=
      energy_mono S (Finset.pow_subset_pow_right h1 (by omega)) u
    have hbnd : (∑ x∈S^r, (u (x*b)-u x)^2)≤(n:ℝ)^2*E :=
      (ih b hb).trans (mul_le_mul_of_nonneg_left hmono (sq_nonneg _))
    have hsnd : (∑ x∈S^r, (u ((x*b)*s)-u (x*b))^2)≤E :=
      (shifted_gradient_le_energy S u r n b s hb hs).trans hmono
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      have he : b=1 := by simpa using hb
      simpa [he,E] using hsnd
    · have hn' : (0:ℝ)<n := by exact_mod_cast hn
      have hpt (x : A) :
          (n:ℝ)*(u (x*(b*s))-u x)^2 ≤
          ((n:ℝ)+1)*(u (x*b)-u x)^2+
          (n:ℝ)*((n:ℝ)+1)*(u ((x*b)*s)-u (x*b))^2 := by
        have hsq := sq_nonneg ((u (x*b)-u x)-(n:ℝ)*(u ((x*b)*s)-u (x*b)))
        simp only [mul_assoc] at hsq ⊢
        nlinarith
      have hsum := Finset.sum_le_sum (fun x (_ : x∈S^r) => hpt x)
      simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
      have hp1 : 0≤(n:ℝ)+1 := by positivity
      have hstep := mul_le_mul_of_nonneg_left hbnd hp1
      have hstep' := mul_le_mul_of_nonneg_left hsnd (mul_nonneg hn'.le hp1)
      change _≤((n+1:ℕ):ℝ)^2*E
      push_cast
      nlinarith

omit [Group A] [DecidableEq A] in
lemma finite_variance_identity (F : Finset A) (u : A → ℝ) :
    (∑ x∈F, ∑ y∈F, (u x-u y)^2) =
      2*(F.card:ℝ)*(∑ x∈F, (u x)^2)-2*(∑ x∈F, u x)^2 := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_const,←Finset.sum_mul,←Finset.mul_sum,nsmul_eq_mul]
  ring

theorem word_ball_poincare (S : Finset A) (h1 : (1:A)∈S)
    (hinv : S⁻¹=S) (u : A → ℝ) (r : ℕ)
    (hu : (∑ x∈S^r, u x)=0) :
    (((S^r).card:ℝ)*(∑ x∈S^r, (u x)^2)) ≤
      2*(r:ℝ)^2*((S^(2*r)).card:ℝ)*energy S (S^(3*r)) u := by
  have hpair (x : A) (hx : x∈S^r) :
      (∑ y∈S^r, (u x-u y)^2) ≤
        ∑ a∈S^(2*r), (u (x*a)-u x)^2 := by
    let F := (S^r).image (fun y => x⁻¹*y)
    have hF : F⊆S^(2*r) := by
      intro a ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ha
      have hxi : x⁻¹∈S^r := by
        have hh : x⁻¹∈(S^r)⁻¹ := Finset.inv_mem_inv hx
        simpa [←inv_pow,hinv] using hh
      rw [show 2*r=r+r by omega,pow_add]
      exact Finset.mem_mul.mpr ⟨x⁻¹,hxi,y,hy,rfl⟩
    calc
      _ = ∑ a∈F, (u (x*a)-u x)^2 := by
        rw [Finset.sum_image]
        · apply Finset.sum_congr rfl
          intro y _
          simp only [mul_inv_cancel_left]
          ring
        · intro y _ z _ h
          exact mul_left_cancel h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hF (by intros; positivity)
  have hsum := Finset.sum_le_sum hpair
  rw [finite_variance_identity,hu,pow_two,zero_mul,mul_zero,sub_zero,Finset.sum_comm] at hsum
  have hw := Finset.sum_le_sum (fun a (ha : a∈S^(2*r)) =>
    word_difference_energy S h1 u r (2*r) a ha)
  simp only [Finset.sum_const,nsmul_eq_mul] at hw
  rw [show r+2*r=3*r by omega] at hw
  have he : 2*((S^r).card:ℝ)*(∑ x∈S^r, (u x)^2)≤
      ((S^(2*r)).card:ℝ)*(2*(r:ℝ))^2*energy S (S^(3*r)) u := by
    have hh := hsum.trans hw
    push_cast at hh
    nlinarith
  nlinarith

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
