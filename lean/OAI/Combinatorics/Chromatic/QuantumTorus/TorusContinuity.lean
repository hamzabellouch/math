import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IncomingSystem
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentContinuity

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] Classical.propDecidable

def TorusConverges (f : ι → Torus v Ω) (F : Torus v Ω) : Prop :=
  ∀m,Converges l (fun i=>f i m) (F m)

lemma torusConverges_const (F : Torus v Ω) : TorusConverges v Ω l (fun _=>F) F :=
  fun m=>converges_const l (F m)

lemma TorusConverges.add {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G) :
    TorusConverges v Ω l (fun i=>f i+g i) (F+G) :=
  fun m=>(hf m).add l (hg m)

lemma TorusConverges.sub {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G) :
    TorusConverges v Ω l (fun i=>f i-g i) (F-G) := by
  intro m
  simp only [torus_sub_apply]
  exact (hf m).sub l (hg m)

lemma TorusConverges.sum {α : Type*} (s : Finset α)
    {f : α → ι → Torus v Ω} {F : α → Torus v Ω}
    (h : ∀a∈s,TorusConverges v Ω l (f a) (F a)) :
    TorusConverges v Ω l (fun i=>∑a∈s,f a i) (∑a∈s,F a) := by
  intro m
  simp only [Finsupp.finsetSum_apply]
  exact LaurentPrecision.Converges.sum l s (fun a ha=>h a ha m)

lemma torus_mul_finite (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) (m : M) :
    (f*g) m=∑x∈S,∑y∈T,
      (Finsupp.single (x+y) (f x*g y*(↑(v^(Ω x y)) : LaurentSeries ℚ)) : Torus v Ω) m := by
  change Torus.multiply v Ω f g m=_
  unfold Torus.multiply
  rw [Finsupp.sum_of_support_subset f hf _ (by intros; simp)]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finsupp.sum_of_support_subset g hg _ (by intros; simp),Finsupp.finsetSum_apply]

lemma TorusConverges.mul_of_support {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G)
    (S T : Finset M) (hS : ∀i,(f i).support⊆S) (hT : ∀i,(g i).support⊆T)
    (hSF : F.support⊆S) (hTG : G.support⊆T) :
    TorusConverges v Ω l (fun i=>f i*g i) (F*G) := by
  intro m
  simp only [torus_mul_finite v Ω S T _ _ (hS _) (hT _) m,
    torus_mul_finite v Ω S T F G hSF hTG m]
  apply LaurentPrecision.Converges.sum l S
  intro x hx
  apply LaurentPrecision.Converges.sum l T
  intro y hy
  by_cases hxy : x+y=m
  · simp only [hxy,Finsupp.single_eq_same]
    exact ((hf x).mul l (hg y)).mul l (converges_const l _)
  · simp only [Finsupp.single_eq_of_ne (Ne.symm hxy)]
    exact converges_const l 0

lemma rootGrade_support (n : ℕ) (f : Torus v Ω) (hf : f∈rootGrade v Ω C n) :
    f.support⊆(rootDegree_finite C n).toFinset := by
  intro m hm
  apply (rootDegree_finite C n).mem_toFinset.mpr
  by_contra h
  exact (Finsupp.mem_support_iff.mp hm) (hf m h)

lemma TorusConverges.mul_graded {f g : ι → Torus v Ω} {F G : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (hg : TorusConverges v Ω l g G)
    (n k : ℕ) (hfn : ∀i,f i∈rootGrade v Ω C n) (hgk : ∀i,g i∈rootGrade v Ω C k)
    (hFn : F∈rootGrade v Ω C n) (hGk : G∈rootGrade v Ω C k) :
    TorusConverges v Ω l (fun i=>f i*g i) (F*G) :=
  hf.mul_of_support v Ω l hg (rootDegree_finite C n).toFinset (rootDegree_finite C k).toFinset
    (fun i=>rootGrade_support v Ω C n _ (hfn i))
    (fun i=>rootGrade_support v Ω C k _ (hgk i))
    (rootGrade_support v Ω C n F hFn) (rootGrade_support v Ω C k G hGk)

lemma TorusConverges.filter {f : ι → Torus v Ω} {F : Torus v Ω}
    (hf : TorusConverges v Ω l f F) (p : M → Prop) :
    TorusConverges v Ω l (fun i=>(f i).filter p) (F.filter p) := by
  intro m
  by_cases h : p m
  · simpa only [Finsupp.filter_apply,ite_eq_left h] using hf m
  · simpa only [Finsupp.filter_apply,ite_eq_right h] using converges_const l (0 : LaurentSeries ℚ)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
