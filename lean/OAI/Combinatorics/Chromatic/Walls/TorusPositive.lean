import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RootProducts

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open LaurentPositive WallUnits PowerSeries
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ)
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def TorusPositive (f : Torus LaurentRay.vUnit Ω) : Prop := ∀m,Positive (f m)
def IntegralPositive (F : PowerSeries (Torus LaurentRay.vUnit Ω)) : Prop := ∀n,TorusPositive Ω (coeff n F)

lemma torusPositive_zero : TorusPositive Ω 0 := fun _=>positive_zero
lemma TorusPositive.add {f g : Torus LaurentRay.vUnit Ω}
    (hf : TorusPositive Ω f) (hg : TorusPositive Ω g) : TorusPositive Ω (f+g) :=
  fun m=>(hf m).add (hg m)
lemma TorusPositive.sum {A : Type*} (s : Finset A) (f : A → Torus LaurentRay.vUnit Ω)
    (h : ∀a∈s,TorusPositive Ω (f a)) : TorusPositive Ω (∑a∈s,f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact torusPositive_zero Ω
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add Ω (ih (fun b hb=>h b (Finset.mem_insert_of_mem hb)))
lemma torusPositive_monomial (m : M) (r : LaurentSeries ℚ) (hr : Positive r) :
    TorusPositive Ω (Torus.monomial LaurentRay.vUnit Ω m r) := by
  classical
  intro x
  change Positive ((Finsupp.single m r) x)
  by_cases h : m=x
  · subst x
    simpa only [Finsupp.single_eq_same] using hr
  · simpa only [Finsupp.single_eq_of_ne (Ne.symm h)] using positive_zero

lemma TorusPositive.mul {f g : Torus LaurentRay.vUnit Ω}
    (hf : TorusPositive Ω f) (hg : TorusPositive Ω g) : TorusPositive Ω (f*g) := by
  change TorusPositive Ω (Torus.multiply LaurentRay.vUnit Ω f g)
  unfold Torus.multiply Finsupp.sum
  apply TorusPositive.sum
  intro x hx
  apply TorusPositive.sum
  intro y hy
  apply torusPositive_monomial
  rw [LaurentRay.vUnit_zpow]
  exact ((hf x).mul (hg y)).mul (LaurentPositive.single _ _ natCoeff_one)

lemma completedPositive_C_X (m : M) : IntegralPositive Ω (C (Torus.X LaurentRay.vUnit Ω m)) := by
  intro n
  rw [coeff_C]
  split
  · exact torusPositive_monomial Ω _ _ positive_one
  · exact torusPositive_zero Ω

lemma IntegralPositive.mul {F G : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : IntegralPositive Ω F) (hG : IntegralPositive Ω G) : IntegralPositive Ω (F*G) := by
  intro n
  rw [coeff_mul]
  exact TorusPositive.sum Ω _ _ (fun p hp=>(hF p.1).mul Ω (hG p.2))

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [Fact (∀i,0<w i)] (P : (I→ℕ) →+ M)

omit [DecidableEq I] in
lemma push_positive (f : (I→ℕ) → LaurentSeries ℚ) (hf : ∀d,Positive (f d)) :
    IntegralPositive Ω (WeightedTorusSeries.push w LaurentRay.vUnit Ω P f) := by
  intro n
  simp only [WeightedTorusSeries.push,coeff_mk,WeightedTorusSeries.pushCoeff]
  exact TorusPositive.sum Ω _ _ (fun d hd=>torusPositive_monomial Ω _ _ (hf d.val))

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I→ℤ) →+ M) (l : Filter ι)
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] Classical.propDecidable

def sumSupport (S T : Finset M) : Finset M := (S×ˢT).image (fun p=>p.1+p.2)

lemma torus_mul_support (S T : Finset M) (f g : Torus v Ω)
    (hf : f.support⊆S) (hg : g.support⊆T) : (f*g).support⊆sumSupport S T := by
  intro m hm
  by_contra H
  apply Finsupp.mem_support_iff.mp hm
  rw [torus_mul_finite v Ω S T f g hf hg m]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finsupp.single_eq_of_ne
  intro Hxy
  apply H
  exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,Hxy.symm⟩

lemma SeriesConverges.mul_of_support {f g : ι → PowerSeries (Torus v Ω)}
    {F G : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hg : SeriesConverges v Ω l g G)
    (S T : ℕ → Finset M) (hs : ∀i n,(coeff n (f i)).support⊆S n)
    (ht : ∀i n,(coeff n (g i)).support⊆T n)
    (hS : ∀n,(coeff n F).support⊆S n) (hT : ∀n,(coeff n G).support⊆T n) :
    SeriesConverges v Ω l (fun i=>f i*g i) (F*G) := by
  intro n
  simp only [coeff_mul]
  apply TorusConverges.sum
  intro p hp
  exact (hf p.1).mul_of_support v Ω l (hg p.2) (S p.1) (T p.2)
    (fun i=>hs i p.1) (fun i=>ht i p.2) (hS p.1) (hT p.2)

lemma SeriesConverges.mul_C {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hfg : ∀i,SeriesGraded v Ω C (f i))
    (hF : SeriesGraded v Ω C F) (x : Torus v Ω) :
    SeriesConverges v Ω l (fun i=>f i*PowerSeries.C x) (F*PowerSeries.C x) := by
  intro n
  simp only [coeff_mul_C]
  exact (hf n).mul_of_support v Ω l (torusConverges_const v Ω l x)
    (rootDegree_finite C n).toFinset x.support
    (fun i=>rootGrade_support v Ω C n _ (hfg i n)) (fun _=>Finset.Subset.refl _)
    (rootGrade_support v Ω C n _ (hF n)) (Finset.Subset.refl _)

lemma SeriesGraded.mul_C_support {F : PowerSeries (Torus v Ω)}
    (hF : SeriesGraded v Ω C F) (x : Torus v Ω) (n : ℕ) :
    (coeff n (F*PowerSeries.C x)).support⊆sumSupport (rootDegree_finite C n).toFinset x.support := by
  rw [coeff_mul_C]
  exact torus_mul_support v Ω _ _ _ _ (rootGrade_support v Ω C n _ (hF n)) (Finset.Subset.refl _)

theorem SeriesConverges.adjoint {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) (x : Torus v Ω) :
    SeriesConverges v Ω l (fun i=>f i*PowerSeries.C x*invOfUnit (f i) 1)
      (F*PowerSeries.C x*invOfUnit F 1) := by
  exact (hf.mul_C v Ω C l hfg hF x).mul_of_support v Ω l
    (hf.inverse v Ω C l hfg hF)
    (fun n=>sumSupport (rootDegree_finite C n).toFinset x.support)
    (fun n=>(rootDegree_finite C n).toFinset)
    (fun i n=>(hfg i).mul_C_support v Ω C x n)
    (fun i n=>rootGrade_support v Ω C n _ ((hfg i).inverse v Ω C n))
    (fun n=>hF.mul_C_support v Ω C x n)
    (fun n=>rootGrade_support v Ω C n _ (hF.inverse v Ω C n))

variable [l.NeBot]
lemma IntegralPositive.of_converges {f : ι → PowerSeries (Torus WallUnits.LaurentRay.vUnit Ω)}
    {F : PowerSeries (Torus WallUnits.LaurentRay.vUnit Ω)}
    (hf : SeriesConverges WallUnits.LaurentRay.vUnit Ω l f F)
    (hp : ∀ᶠi in l,IntegralPositive Ω (f i)) : IntegralPositive Ω F := by
  intro n m
  exact LaurentPositive.of_converges l (hf n m) (hp.mono (fun i hi=>hi n m))

end
end ElementaryPositivity.QuantumTorus

end

end OAI
