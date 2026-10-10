import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.LazyWalkHilbert

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.HomogeneousAnalysis
open HarmonicAnalysis

variable {X : Type*}

def finiteHilbert : Submodule ℝ (RegularHilbert X) where
  carrier := {f | (Function.support (fun x => f x)).Finite}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    apply (hf.union hg).subset
    intro x hx
    by_contra hn
    have hx' : f x+g x≠0 := hx
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hx' (by rw [hn.1,hn.2]; ring)
  smul_mem' := by
    intro c f hf
    apply hf.subset
    intro x hx
    by_contra hn
    have hx' : c*f x≠0 := hx
    simp only [Function.mem_support,not_not] at hn
    exact hx' (by rw [hn,mul_zero])

abbrev FH (X : Type*) := ↥(finiteHilbert (X:=X))
namespace FH
instance : CoeFun (FH X) (fun _ => X → ℝ) := ⟨fun f => (f.val : X → ℝ)⟩
@[ext] lemma ext {f g : FH X} (h : ∀ x, f x=g x) : f=g :=
  Subtype.ext (by ext x; exact h x)

@[simp] lemma zero_apply (x : X) : (0 : FH X) x=0 := rfl
@[simp] lemma add_apply (f g : FH X) (x : X) : (f+g) x=f x+g x := rfl
@[simp] lemma sub_apply (f g : FH X) (x : X) : (f-g) x=f x-g x := rfl
@[simp] lemma smul_apply (c : ℝ) (f : FH X) (x : X) : (c • f) x=c*f x := rfl
lemma sum_apply {ι : Type*} (s : Finset ι) (f : ι → FH X) (x : X) :
    (∑ i∈s, f i) x=∑ i∈s, f i x := by
  simp only [Submodule.coe_sum,lp.coeFn_sum,Finset.sum_apply]

def support (f : FH X) : Finset X := f.property.toFinset
@[simp] lemma mem_support (f : FH X) (x : X) : x∈f.support ↔ f x≠0 :=
  f.property.mem_toFinset
lemma eq_zero_of_not_mem (f : FH X) {x : X} (h : x∉f.support) : f x=0 :=
  not_not.mp ((f.mem_support x).not.mp h)

def ofFunction (f : X → ℝ) (hf : (Function.support f).Finite) : FH X :=
  ⟨⟨f,(memℓp_zero_iff.mpr hf).of_exponent_ge (by norm_num)⟩,hf⟩
@[simp] lemma ofFunction_apply (f : X → ℝ) (hf : (Function.support f).Finite) (x : X) :
    ofFunction f hf x=f x := rfl

def delta (x : X) : FH X :=
  ofFunction (Pi.single x 1) ((Set.finite_singleton x).subset (by
    intro y hy
    by_contra hn
    simp only [Set.mem_singleton_iff] at hn
    exact hy (by simp [hn])))
@[simp] lemma delta_apply (x y : X) : delta x y=if y=x then 1 else 0 := by
  simp [delta,Pi.single_apply,eq_comm]
lemma delta_inner (x : X) (f : FH X) : inner ℝ (delta x) f=f x := by
  change inner ℝ (lp.single 2 x (1:ℝ)) f.val=f x
  rw [lp.inner_single_left]
  simp

lemma inner_eq_sum (f g : FH X) (F : Finset X) (hF : f.support⊆F) :
    inner ℝ f g=∑ x∈F, f x*g x := by
  change (∑' x, inner ℝ (f x) (g x))=_
  simp only [Real.inner_apply]
  apply tsum_eq_sum
  intro x hx
  rw [f.eq_zero_of_not_mem (fun h => hx (hF h)),zero_mul]
lemma norm_sq_eq_sum (f : FH X) (F : Finset X) (hF : f.support⊆F) :
    ‖f‖^2=∑ x∈F, (f x)^2 := by
  rw [←real_inner_self_eq_norm_sq,f.inner_eq_sum f F hF]
  simp only [pow_two]

lemma norm_coordinate_le (f : FH X) (x : X) : |f x|≤‖f‖ := by
  exact lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) f.val x

def transportLinear (g : Equiv.Perm X) : FH X ≃ₗ[ℝ] FH X where
  toFun f := ofFunction (fun x => f (g.symm x)) (by
    have he : Function.support (fun x => f (g.symm x))=g '' Function.support (fun x => f x) := by
      ext x; simp [Function.mem_support]
    rw [he]; exact f.property.image g)
  invFun f := ofFunction (fun x => f (g x)) (by
    have he : Function.support (fun x => f (g x))=g.symm '' Function.support (fun x => f x) := by
      ext x; simp [Function.mem_support]
    rw [he]; exact f.property.image g.symm)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl

def transport (g : Equiv.Perm X) : FH X ≃ₗᵢ[ℝ] FH X :=
  (transportLinear g).isometryOfInner (by
    intro f h
    change (∑' x, inner ℝ (f (g.symm x)) (h (g.symm x)))=∑' x, inner ℝ (f x) (h x)
    exact g.symm.tsum_eq (fun x => inner ℝ (f x) (h x)))
@[simp] lemma transport_apply (g : Equiv.Perm X) (f : FH X) (x : X) :
    transport g f x=f (g.symm x) := rfl
@[simp] lemma transport_one (f : FH X) : transport 1 f=f := by ext x; rfl
@[simp] lemma transport_mul (a b : Equiv.Perm X) (f : FH X) :
    transport (a*b) f=transport a (transport b f) := by ext x; rfl
@[simp] lemma transport_delta (g : Equiv.Perm X) (x : X) :
    transport g (delta x)=delta (g x) := by
  ext y
  simp only [transport_apply,delta_apply]
  congr 1
  exact propext g.symm_apply_eq

lemma delta_decomposition (f : FH X) :
    (∑ x∈f.support, f x • delta x)=f := by
  ext y
  rw [sum_apply]
  by_cases hy : y∈f.support
  · simp [delta_apply,hy]
  · simp [delta_apply,hy,f.eq_zero_of_not_mem hy]

lemma sum_sq_le_norm_sq (f : FH X) (F : Finset X) :
    (∑ x∈F, (f x)^2)≤‖f‖^2 := by
  rw [f.norm_sq_eq_sum (F∪f.support) Finset.subset_union_right]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by intros; positivity)

lemma summable (f : FH X) : Summable (fun x => f x) := summable_of_hasFiniteSupport f.property

def mass : FH X →ₗ[ℝ] ℝ where
  toFun f := ∑' x, f x
  map_add' f g := by simp only [add_apply]; exact Summable.tsum_add f.summable g.summable
  map_smul' c f := by simp only [smul_apply,RingHom.id_apply,smul_eq_mul,tsum_mul_left]
@[simp] lemma mass_delta (x : X) : mass (delta x)=1 := by
  change (∑' y, delta x y)=1
  simp only [delta_apply]
  exact tsum_ite_eq _ _
lemma hasSum_mass (f : FH X) : HasSum (fun x => f x) (mass f) := f.summable.hasSum

end FH
end CriticalPercolation.HomogeneousAnalysis
end
end

end OAI
