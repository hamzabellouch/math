import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.LazyWalkHilbert

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma lazyWalk_coordinate (f : RegularHilbert A) (x : A) :
    W.lazyWalk f x = (1/2:ℝ)*(f x+
      (W.generators.card:ℝ)⁻¹*∑ s∈W.generators, f (s⁻¹*x)) := by
  simp only [W.lazyWalk_apply,W.walkAverage_apply,lp.coeFn_smul,lp.coeFn_add,
    lp.coeFn_sum,Pi.smul_apply,Pi.add_apply,Finset.sum_apply,regular_apply,smul_eq_mul]

lemma lazyWalk_nonnegative (f : RegularHilbert A) (hf : ∀ x, 0≤f x) :
    ∀ x, 0≤W.lazyWalk f x := by
  intro x
  rw [W.lazyWalk_coordinate]
  exact mul_nonneg (by norm_num) (add_nonneg (hf x)
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun s _ => hf _))))

lemma lazyWalk_mass (f : RegularHilbert A) (m : ℝ) (hf : HasSum (fun x => f x) m) :
    HasSum (fun x => W.lazyWalk f x) m := by
  have hs : HasSum (fun x => ∑ s∈W.generators, f (s⁻¹*x))
      ((W.generators.card:ℝ)*m) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,Function.comp_apply,Equiv.coe_mulLeft] using
      hasSum_sum (s := W.generators) (fun s _ =>
        (Equiv.mulLeft s⁻¹).hasSum_iff.mpr hf)
  have hc : (W.generators.card:ℝ)≠0 := by exact_mod_cast W.generators_card_pos.ne'
  have hh := HasSum.mul_left (1/2:ℝ) (hf.add (HasSum.mul_left (W.generators.card:ℝ)⁻¹ hs))
  have he : (1/2:ℝ)*(m+(W.generators.card:ℝ)⁻¹*((W.generators.card:ℝ)*m))=m := by
    field_simp; ring
  rw [he] at hh
  simpa only [W.lazyWalk_coordinate] using hh

def walkState (n : ℕ) : RegularHilbert A :=
  (W.lazyWalk^n) (lp.single 2 (1:A) (1:ℝ))

@[simp] lemma walkState_zero : W.walkState 0=lp.single 2 (1:A) (1:ℝ) := rfl

lemma walkState_succ (n : ℕ) : W.walkState (n+1)=W.lazyWalk (W.walkState n) := by
  simp only [walkState,pow_succ',Module.End.mul_apply]

lemma walkState_nonnegative (n : ℕ) : ∀ x, 0≤W.walkState n x := by
  induction n with
  | zero => intro x; simp only [walkState_zero,lp.single_apply,Pi.single_apply]; split <;> norm_num
  | succ n ih => rw [W.walkState_succ]; exact W.lazyWalk_nonnegative _ ih

lemma walkState_mass (n : ℕ) : HasSum (fun x => W.walkState n x) 1 := by
  induction n with
  | zero =>
    simpa only [walkState_zero,lp.single_apply,Pi.single_apply] using hasSum_ite_eq (1:A) (1:ℝ)
  | succ n ih => rw [W.walkState_succ]; exact W.lazyWalk_mass _ _ ih

lemma walkState_one_pos (n : ℕ) : 0<W.walkState n 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate]
    have hs : 0≤(W.generators.card:ℝ)⁻¹*∑ s∈W.generators, W.walkState n (s⁻¹*1) := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun s _ => W.walkState_nonnegative n _)
    positivity

lemma walkState_support (n : ℕ) {x : A} (hx : x∉W.ball n) : W.walkState n x=0 := by
  induction n generalizing x with
  | zero =>
    have hh : x≠1 := by simpa [ball] using hx
    simp [hh]
  | succ n ih =>
    rw [W.walkState_succ,W.lazyWalk_coordinate]
    have hxn : x∉W.ball n := fun h => hx (W.ball_mono (by omega) h)
    rw [ih hxn]
    have hs : (∑ s∈W.generators, W.walkState n (s⁻¹*x))=0 := by
      apply Finset.sum_eq_zero
      intro s hs
      apply ih
      intro h
      apply hx
      change x∈W.generators^(n+1)
      rw [pow_succ']
      exact Finset.mem_mul.mpr ⟨s,hs,s⁻¹*x,h,mul_inv_cancel_left s x⟩
    rw [hs]; ring

lemma walkPower_symmetric (n : ℕ) (f g : RegularHilbert A) :
    inner ℝ ((W.lazyWalk^n) f) g=inner ℝ f ((W.lazyWalk^n) g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    calc
      _ = inner ℝ ((W.lazyWalk^n) (W.lazyWalk f)) g := by
        rw [pow_succ,Module.End.mul_apply]
      _ = inner ℝ (W.lazyWalk f) ((W.lazyWalk^n) g) := ih _ _
      _ = inner ℝ f (W.lazyWalk ((W.lazyWalk^n) g)) := W.lazyWalk_symmetric _ _
      _ = _ := by rw [pow_succ',Module.End.mul_apply]

lemma walkState_double_at_one (n : ℕ) : W.walkState (2*n) 1=‖W.walkState n‖^2 := by
  have hh := W.walkPower_symmetric n (lp.single 2 (1:A) (1:ℝ)) (W.walkState n)
  rw [lp.inner_single_left] at hh
  have he : (W.lazyWalk^n) (W.walkState n)=W.walkState (2*n) := by
    simp only [walkState,←Module.End.mul_apply,←pow_add,two_mul]
  rw [he] at hh
  change inner ℝ (W.walkState n) (W.walkState n) = inner ℝ 1 (W.walkState (2*n) 1) at hh
  simpa only [real_inner_self_eq_norm_sq,Real.inner_apply,one_mul] using hh.symm

lemma walkState_norm_sq (n : ℕ) :
    ‖W.walkState n‖^2=∑ x∈W.ball n, (W.walkState n x)^2 := by
  rw [←real_inner_self_eq_norm_sq]
  change (∑' x : A, inner ℝ (W.walkState n x) (W.walkState n x))=_
  simp only [Real.inner_apply]
  rw [tsum_eq_sum (s := W.ball n)]
  · apply Finset.sum_congr rfl; intro x _; ring
  · intro x hx; rw [W.walkState_support n hx]; simp

lemma walkState_norm_lower (n : ℕ) :
    1≤((W.ball n).card:ℝ)*‖W.walkState n‖^2 := by
  have hmass : (∑ x∈W.ball n, W.walkState n x)=1 := by
    rw [←(W.walkState_mass n).tsum_eq]
    exact (tsum_eq_sum (f := fun x => W.walkState n x) (s := W.ball n)
      (fun x hx => W.walkState_support n (x := x) hx)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (W.ball n) (fun _ => (1:ℝ))
    (fun x => W.walkState n x)
  simpa only [one_mul,hmass,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,
    ←W.walkState_norm_sq] using hcs

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
