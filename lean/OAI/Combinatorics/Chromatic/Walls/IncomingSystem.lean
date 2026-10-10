import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusWallLeading

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries ElementaryPositivity.PowerSeriesSplit
noncomputable section

variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
local instance : @Module ℚ (Torus v Ω) _ (Torus.instRing v Ω).toAddCommMonoid := by
  let finsuppModule := (inferInstance : Module ℚ (M →₀ R))
  letI : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
  exact
    { smul := finsuppModule.smul
      one_smul := finsuppModule.one_smul
      mul_smul := finsuppModule.mul_smul
      smul_zero := finsuppModule.smul_zero
      smul_add := finsuppModule.smul_add
      add_smul := finsuppModule.add_smul
      zero_smul := finsuppModule.zero_smul }
attribute [local instance] Classical.propDecidable

lemma rootDegree_finite (n : ℕ) : {m | HasRootDegree C n m}.Finite := by
  let F : (I → Fin (n+1)) → M := fun d => C (fun i => (d i : ℤ))
  apply (Set.finite_range F).subset
  rintro m ⟨d,hd,hm⟩
  have hi : ∀i,d i≤n := by
    intro i
    rw [←hd]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
  exact ⟨fun i => ⟨d i,by have := hi i; omega⟩,hm⟩

def incomingCovector (r : M) : M →+ ℝ where
  toFun a := (Ω a r : ℝ)
  map_zero' := by simp
  map_add' := by intro a b; simp

def incomingMiddle (r : M) (f : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  zeroFactor (positiveProject v Ω (incomingCovector Ω r))
    (zeroProject v Ω (incomingCovector Ω r)) f

omit [Algebra ℚ R] in
lemma incomingMiddle_constant (r : M) (f : PowerSeries (Torus v Ω)) :
    constantCoeff (incomingMiddle v Ω r f)=1 :=
  left_constant _ _

omit [Algebra ℚ R] in
lemma incomingMiddle_coeff_congr (r : M) (f g : PowerSeries (Torus v Ω)) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) :
    coeff n (incomingMiddle v Ω r f)=coeff n (incomingMiddle v Ω r g) :=
  zero_coeff_congr _ _ _ _ _ h

def incomingCoefficient (n : ℕ) (f : PowerSeries (Torus v Ω)) : Torus v Ω :=
  Finsupp.onFinset (rootDegree_finite C n).toFinset
    (fun m => if HasRootDegree C n m then
      (coeff n (FormalLog.log (incomingMiddle v Ω m f))) m else 0)
    (by
      intro m hm
      rw [Set.Finite.mem_toFinset]
      change HasRootDegree C n m
      by_contra hn
      exact hm (ite_eq_right hn))

lemma incomingCoefficient_apply (n : ℕ) (f : PowerSeries (Torus v Ω)) (m : M) :
    incomingCoefficient v Ω C n f m = if HasRootDegree C n m then
      (coeff n (FormalLog.log (incomingMiddle v Ω m f))) m else 0 := rfl

lemma incomingCoefficient_graded (n : ℕ) (f : PowerSeries (Torus v Ω)) :
    incomingCoefficient v Ω C n f ∈ rootGrade v Ω C n := by
  intro m hm
  rw [incomingCoefficient_apply,ite_eq_right hm]

lemma incomingCoefficient_zero (f : PowerSeries (Torus v Ω)) :
    incomingCoefficient v Ω C 0 f=0 := by
  ext m
  rw [incomingCoefficient_apply]
  simp only [coeff_zero_eq_constantCoeff_apply,FormalLog.log_constant]
  split_ifs <;> rfl

lemma incomingCoefficient_congr (f g : PowerSeries (Torus v Ω)) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g) :
    incomingCoefficient v Ω C n f=incomingCoefficient v Ω C n g := by
  ext m
  rw [incomingCoefficient_apply,incomingCoefficient_apply]
  split_ifs with hm
  · congr 1
    apply FormalLog.log_coeff_congr
    intro j hj
    exact incomingMiddle_coeff_congr v Ω m f g j (fun k hk => h k (hk.trans hj))
  · rfl

omit [Algebra ℚ R] in
lemma torus_sub_apply (x y : Torus v Ω) (m : M) : (x-y) m=x m-y m := by
  rw [sub_eq_add_neg]
  change x m + -y m = x m-y m
  exact (sub_eq_add_neg _ _).symm

lemma incomingCoefficient_leading (hΩ : ∀m,Ω m m=0)
    (f g : PowerSeries (Torus v Ω)) (n : ℕ)
    (h : ∀k≤n,coeff k f=coeff k g)
    (hf : coeff (n+1) f∈rootGrade v Ω C (n+1))
    (hg : coeff (n+1) g∈rootGrade v Ω C (n+1)) :
    incomingCoefficient v Ω C (n+1) f-incomingCoefficient v Ω C (n+1) g =
      coeff (n+1) f-coeff (n+1) g := by
  classical
  ext m
  rw [torus_sub_apply,torus_sub_apply]
  rw [incomingCoefficient_apply,incomingCoefficient_apply]
  by_cases hm : HasRootDegree C (n+1) m
  · rw [ite_eq_left hm,ite_eq_left hm]
    have hlog := FormalLog.log_leading_difference (incomingMiddle v Ω m f)
      (incomingMiddle v Ω m g) n (incomingMiddle_constant v Ω m f)
      (incomingMiddle_constant v Ω m g)
      (fun k hk => incomingMiddle_coeff_congr v Ω m f g k (fun j hj => h j (hj.trans hk)))
    have hmid := zero_leading_difference (positiveProject v Ω (incomingCovector Ω m))
      (zeroProject v Ω (incomingCovector Ω m))
      (zero_positive_project v Ω (incomingCovector Ω m)) f g n h
    have he := congrArg (fun t : Torus v Ω => t m) (hlog.trans hmid)
    rw [torus_sub_apply] at he
    change _-_=(Finsupp.filter (fun x => incomingCovector Ω m x=0)
      (coeff (n+1) f-coeff (n+1) g)) m at he
    rw [Finsupp.filter_apply] at he
    have hzero : incomingCovector Ω m m=0 := by change (Ω m m : ℝ)=0; rw [hΩ,Int.cast_zero]
    rw [ite_eq_left hzero,torus_sub_apply] at he
    exact he
  · rw [ite_eq_right hm,ite_eq_right hm,hf m hm,hg m hm]

def incomingSolutionCoefficients (l : ℕ → Torus v Ω) : ℕ → Torus v Ω
  | 0 => 1
  | n+1 => l (n+1)-incomingCoefficient v Ω C (n+1)
    (PowerSeries.mk (fun k => if _ : k≤n then incomingSolutionCoefficients l k else 0))
termination_by n => n

def incomingSolution (l : ℕ → Torus v Ω) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (incomingSolutionCoefficients v Ω C l)

lemma incomingSolution_constant (l : ℕ → Torus v Ω) :
    constantCoeff (incomingSolution v Ω C l)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply]
  simp only [incomingSolution,coeff_mk,incomingSolutionCoefficients]

lemma incomingSolution_graded (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) (n : ℕ) :
    coeff n (incomingSolution v Ω C l)∈rootGrade v Ω C n := by
  cases n with
  | zero => simpa only [coeff_zero_eq_constantCoeff_apply,incomingSolution_constant] using rootGrade_one v Ω C
  | succ n =>
    simp only [incomingSolution,coeff_mk,incomingSolutionCoefficients]
    intro m hm
    rw [torus_sub_apply,hl _ m hm,incomingCoefficient_graded v Ω C _ _ m hm,sub_self]

def incomingTruncation (l : ℕ → Torus v Ω) (n : ℕ) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk (fun k => if k≤n then incomingSolutionCoefficients v Ω C l k else 0)

lemma incomingTruncation_lower (l : ℕ → Torus v Ω) (n k : ℕ) (hk : k≤n) :
    coeff k (incomingSolution v Ω C l)=coeff k (incomingTruncation v Ω C l n) := by
  simp only [incomingSolution,incomingTruncation,coeff_mk,ite_eq_left hk]

lemma incomingTruncation_top (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (incomingTruncation v Ω C l n)=0 := by
  simp only [incomingTruncation,coeff_mk,show ¬n+1≤n by omega,ite_false]

lemma incomingSolution_step (l : ℕ → Torus v Ω) (n : ℕ) :
    coeff (n+1) (incomingSolution v Ω C l)=
      l (n+1)-incomingCoefficient v Ω C (n+1) (incomingTruncation v Ω C l n) := by
  simp only [incomingSolution,coeff_mk,incomingSolutionCoefficients,incomingTruncation,dite_eq_ite]

lemma incomingSolution_prescription_difference (hΩ : ∀m,Ω m m=0) (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) (n : ℕ) :
    incomingCoefficient v Ω C (n+1) (incomingSolution v Ω C l)-
      incomingCoefficient v Ω C (n+1) (incomingTruncation v Ω C l n)=
      coeff (n+1) (incomingSolution v Ω C l)-0 := by
  have hpgrade : coeff (n+1) (incomingTruncation v Ω C l n)∈rootGrade v Ω C (n+1) := by
    intro m hm
    rw [incomingTruncation_top]
    rfl
  have H := incomingCoefficient_leading v Ω C hΩ
    (incomingSolution v Ω C l) (incomingTruncation v Ω C l n) n
    (incomingTruncation_lower v Ω C l n) (incomingSolution_graded v Ω C l hl _) hpgrade
  rw [incomingTruncation_top] at H
  exact H

lemma incomingSolution_prescription (hΩ : ∀m,Ω m m=0) (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) (n : ℕ) :
    incomingCoefficient v Ω C (n+1) (incomingSolution v Ω C l)=l (n+1) := by
  have H := incomingSolution_prescription_difference v Ω C hΩ l hl n
  rw [incomingSolution_step] at H
  ext m
  have he := congrArg (fun x : Torus v Ω => x m) H
  simp only [torus_sub_apply,Finsupp.zero_apply,sub_zero] at he
  exact sub_left_inj.mp he

theorem existsUnique_incoming (hΩ : ∀m,Ω m m=0) (l : ℕ → Torus v Ω)
    (hl : ∀n,l n∈rootGrade v Ω C n) :
    ∃! g : CompletedPositive v Ω C,
      ∀n,incomingCoefficient v Ω C (n+1) g.val=l (n+1) := by
  let g : CompletedPositive v Ω C := ⟨incomingSolution v Ω C l,
    incomingSolution_constant v Ω C l,incomingSolution_graded v Ω C l hl⟩
  refine ⟨g,fun n => incomingSolution_prescription v Ω C hΩ l hl n,?_⟩
  intro f hf
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,f.property.1,g.property.1]
    | succ n =>
      have H := incomingCoefficient_leading v Ω C hΩ f.val g.val n
        (fun k hk => ih k (by omega)) (f.property.2 _) (g.property.2 _)
      rw [hf n,incomingSolution_prescription v Ω C hΩ l hl n] at H
      ext m
      have he := congrArg (fun x : Torus v Ω => x m) H
      simp only [torus_sub_apply,sub_self] at he
      exact sub_eq_zero.mp he.symm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
