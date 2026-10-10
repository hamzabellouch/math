import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeFaithfulRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeFaithfulAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeFaithfulAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup

def FullHomogeneous (τ : M →+ ℤ) (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀n m,coeff n f m≠0 → τ m=(n:ℤ)

lemma regrade_coeff_eval (f : PowerSeries (Torus v Ω)) (d : ℕ) (m : M) :
    coeff d (regrade v Ω δ B f) m=
      if d=(δ m).toNat then ∑n∈Finset.range (B*d+1),coeff n f m else 0 := by
  classical
  rw [regrade_coeff,nonp_torus_eval_sum]
  simp_rw [homogenize_coeff]
  split_ifs <;> simp_all

lemma regrade_read (τ : M →+ ℤ) {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hτ : FullHomogeneous v Ω τ f)
    (n : ℕ) (m : M) (hm : τ m=(n:ℤ)) :
    coeff (δ m).toNat (regrade v Ω δ B f) m=coeff n f m := by
  classical
  rw [regrade_coeff_eval,ite_eq_left rfl]
  apply Finset.sum_eq_single n
  · intro j hj hne
    by_contra hz
    have H:=hτ j m hz
    have : j=n:=by omega
    exact hne this
  · intro hn
    by_contra hz
    have H:=(hf n m hz).2
    have HH : ¬n<B*(δ m).toNat+1:=by simpa only [Finset.mem_range] using hn
    omega

lemma regrade_injective_homogeneous (τ : M →+ ℤ) {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g)
    (hτf : FullHomogeneous v Ω τ f) (hτg : FullHomogeneous v Ω τ g)
    (he : regrade v Ω δ B f=regrade v Ω δ B g) : f=g := by
  apply PowerSeries.ext
  intro n
  ext m
  by_cases hm : τ m=(n:ℤ)
  · rw [←regrade_read v Ω δ B τ hf hτf n m hm,
      ←regrade_read v Ω δ B τ hg hτg n m hm,he]
  · have Hf : coeff n f m=0:=by by_contra hz; exact hm (hτf n m hz)
    have Hg : coeff n g m=0:=by by_contra hz; exact hm (hτg n m hz)
    rw [Hf,Hg]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeNegationRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeNegationAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeNegationAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma torus_neg_one_mul (f : Torus v Ω) : (-1 : Torus v Ω)*f= -f := by
  have H:=Torus.add_mul v Ω (-1) 1 f
  rw [neg_add_cancel,Torus.zero_mul,Torus.one_mul] at H
  exact eq_neg_of_add_eq_zero_left H.symm
lemma RegradeBound.invOfUnit {f : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f) :
    RegradeBound v Ω δ B (PowerSeries.invOfUnit f 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih=>
    intro m hm
    by_cases hn : n=0
    · subst n
      rw [coeff_invOfUnit,ite_eq_left rfl] at hm
      have hm0 : m=0:=by
        by_contra HH
        apply hm
        change Finsupp.single 0 (1:R) m=0
        exact Finsupp.single_eq_of_ne HH
      subst m
      simp
    · rw [coeff_invOfUnit,ite_eq_right hn] at hm
      simp only [inv_one,Units.val_one] at hm
      rw [torus_neg_one_mul] at hm
      change -(∑ab∈Finset.HasAntidiagonal.antidiagonal n,
        if ab.2<n then coeff ab.1 f*coeff ab.2 (PowerSeries.invOfUnit f 1) else 0) m≠0 at hm
      have HH:=neg_ne_zero.mp hm
      rw [nonp_torus_eval_sum] at HH
      obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero HH
      have hb : ab.2<n:=by by_contra hh; simp [hh] at hz
      rw [ite_eq_left hb] at hz
      obtain ⟨a,b,ha,hb',he⟩:=torus_product_nonzero v Ω _ _ m hz
      obtain ⟨ha0,han⟩:=hf ab.1 a ha
      obtain ⟨hb0,hbn⟩:=ih ab.2 hb b hb'
      have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rw [←he,_root_.map_add,Int.toNat_add ha0 hb0,mul_add]
      exact ⟨add_nonneg ha0 hb0,hsum ▸ Nat.add_le_add han hbn⟩

lemma homogenize_one : homogenize v Ω δ 1=1 := by
  change homogenize v Ω δ (Torus.monomial v Ω 0 1)=_
  rw [homogenize_monomial]
  simp only [_root_.map_zero,Int.toNat_zero,monomial_zero_eq_C]
  rfl
lemma regrade_zero : regrade v Ω δ B 0=0 := by
  apply PowerSeries.ext
  intro d
  rw [regrade_coeff]
  simp
lemma regrade_one : regrade v Ω δ B 1=1 := by
  classical
  apply PowerSeries.ext
  intro d
  rw [regrade_coeff,Finset.sum_eq_single 0]
  · rw [coeff_zero_eq_constantCoeff_apply,constantCoeff_one,homogenize_one]
  · intro n hn hn0
    rw [coeff_one,ite_eq_right hn0,_root_.map_zero,_root_.map_zero]
  · intro h
    simp at h

def boundedRegradeSubring : Subring (PowerSeries (Torus v Ω)) where
  carrier:=RegradeBound v Ω δ B
  zero_mem':=RegradeBound.zero v Ω δ B
  one_mem':=RegradeBound.one v Ω δ B
  add_mem':=fun hf hg=>hf.add v Ω δ B hg
  neg_mem':=fun hf=>hf.neg v Ω δ B
  mul_mem':=fun hf hg=>hf.mul v Ω δ B hg

def regradeHom : boundedRegradeSubring v Ω δ B →+* PowerSeries (Torus v Ω) where
  toFun f:=regrade v Ω δ B f.val
  map_zero':=regrade_zero v Ω δ B
  map_one':=regrade_one v Ω δ B
  map_add' f g:=regrade_add v Ω δ B f.property g.property
  map_mul' f g:=regrade_mul v Ω δ B f.property g.property

lemma regrade_inverse_mul {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hc : constantCoeff f=1) :
    regrade v Ω δ B (PowerSeries.invOfUnit f 1)*regrade v Ω δ B f=1 := by
  rw [←regrade_mul v Ω δ B (hf.invOfUnit v Ω δ B) hf,
    PowerSeries.invOfUnit_mul f 1 hc,regrade_one]
lemma regrade_mul_inverse {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hc : constantCoeff f=1) :
    regrade v Ω δ B f*regrade v Ω δ B (PowerSeries.invOfUnit f 1)=1 := by
  rw [←regrade_mul v Ω δ B hf (hf.invOfUnit v Ω δ B),
    PowerSeries.mul_invOfUnit f 1 hc,regrade_one]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
