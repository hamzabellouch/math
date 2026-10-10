import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpHomogenize

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance regradeSupportRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeSupportAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeSupportAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma torus_product_nonzero (f g : Torus v Ω) (r : M) (h : (f*g) r≠0) :
    ∃m n,f m≠0 ∧ g n≠0 ∧ m+n=r := by
  classical
  by_contra H
  apply h
  change Torus.multiply v Ω f g r=0
  simp only [Torus.multiply,Finsupp.sum,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  apply Finsupp.single_eq_of_ne
  intro hr
  exact H ⟨m,n,Finsupp.mem_support_iff.mp hm,Finsupp.mem_support_iff.mp hn,hr.symm⟩
lemma nonp_torus_eval_sum {A : Type*} (s : Finset A) (f : A → Torus v Ω) (r : M) :
    (∑a∈s,f a) r=∑a∈s,f a r := by
  classical
  induction s using Finset.induction_on with
  | empty=>rfl
  | @insert a s ha ih=>simp only [Finset.sum_insert ha,Finsupp.add_apply,ih]
lemma series_product_nonzero (f g : PowerSeries (Torus v Ω)) (j : ℕ) (r : M)
    (h : coeff j (f*g) r≠0) :
    ∃a b m n,a+b=j ∧ coeff a f m≠0 ∧ coeff b g n≠0 ∧ m+n=r := by
  classical
  rw [coeff_mul,nonp_torus_eval_sum] at h
  obtain ⟨ab,hab,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨m,n,hm,hn,he⟩:=torus_product_nonzero v Ω _ _ r hz
  exact ⟨ab.1,ab.2,m,n,Finset.HasAntidiagonal.mem_antidiagonal.mp hab,hm,hn,he⟩

def RegradeBound (δ : M →+ ℤ) (B : ℕ) (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀n m,coeff n f m≠0 → 0≤δ m ∧ n≤B*(δ m).toNat
variable (δ : M →+ ℤ) (B : ℕ)
lemma RegradeBound.zero : RegradeBound v Ω δ B 0 := by intro n m h; simp at h
lemma RegradeBound.one : RegradeBound v Ω δ B 1 := by
  intro n m hm
  have hn : n=0:=by by_contra hn; simp [coeff_one,hn] at hm
  subst n
  have hm0 : m=0:=by
    by_contra hm0
    apply hm
    rw [coeff_one,ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne hm0
  subst m
  simp
lemma RegradeBound.add {f g : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f)
    (hg : RegradeBound v Ω δ B g) : RegradeBound v Ω δ B (f+g) := by
  intro n m hm
  have H : coeff n f m≠0 ∨ coeff n g m≠0:=by
    by_contra hh
    push Not at hh
    simp [hh.1,hh.2] at hm
  exact H.elim (hf n m) (hg n m)
lemma RegradeBound.neg {f : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f) :
    RegradeBound v Ω δ B (-f) := by
  intro n m hm
  apply hf n m
  change -(coeff n f m)≠0 at hm
  exact neg_ne_zero.mp hm
lemma RegradeBound.mul {f g : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f)
    (hg : RegradeBound v Ω δ B g) : RegradeBound v Ω δ B (f*g) := by
  intro j r hr
  obtain ⟨a,b,m,n,hab,hm,hn,rfl⟩:=series_product_nonzero v Ω f g j r hr
  obtain ⟨hm0,hma⟩:=hf a m hm
  obtain ⟨hn0,hnb⟩:=hg b n hn
  refine ⟨by simpa only [map_add] using add_nonneg hm0 hn0,?_⟩
  rw [←hab,map_add,Int.toNat_add hm0 hn0,mul_add]
  exact Nat.add_le_add hma hnb

lemma RegradeBound.homogenize_vanish {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (d n : ℕ) (hn : B*d<n) :
    coeff d (homogenize v Ω δ (coeff n f))=0 := by
  ext m
  rw [homogenize_coeff]
  by_cases hd : d=(δ m).toNat
  · rw [ite_eq_left hd]
    by_contra hm
    have HH:=(hf n m hm).2
    rw [←hd] at HH
    exact Nat.not_lt_of_ge HH hn
  · simp [hd]
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def regrade (f : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk fun d=>∑n∈Finset.range (B*d+1),coeff d (homogenize v Ω δ (coeff n f))
lemma regrade_coeff (f : PowerSeries (Torus v Ω)) (d : ℕ) :
    coeff d (regrade v Ω δ B f)=
      ∑n∈Finset.range (B*d+1),coeff d (homogenize v Ω δ (coeff n f)) := coeff_mk _ _

section Topology
local instance regradeTopology : TopologicalSpace (Torus v Ω) := ⊥
local instance regradeDiscreteTopology : DiscreteTopology (Torus v Ω) := ⟨rfl⟩
open scoped PowerSeries.WithPiTopology

lemma regrade_hasSum {f : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f) :
    HasSum (fun n=>homogenize v Ω δ (coeff n f)) (regrade v Ω δ B f) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [regrade_coeff]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply hf.homogenize_vanish v Ω δ B d n
  have H : B*d+1≤n:=by simpa only [Finset.mem_range,not_lt] using hn
  omega

lemma regrade_product_summable {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g) :
    Summable (fun ab : ℕ×ℕ=>homogenize v Ω δ (coeff ab.1 f)*homogenize v Ω δ (coeff ab.2 g)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet ((Finset.range (B*d+1)).product (Finset.range (B*d+1)))).subset
  intro ab hab
  change coeff d (homogenize v Ω δ (coeff ab.1 f)*homogenize v Ω δ (coeff ab.2 g))≠0 at hab
  change ab∈(Finset.range (B*d+1)) ×ˢ (Finset.range (B*d+1))
  rw [Finset.mem_product,Finset.mem_range,Finset.mem_range]
  by_contra H
  apply hab
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro kl hkl
  have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  have hl : B*kl.1≤B*d:=Nat.mul_le_mul_left B (by omega)
  have hr : B*kl.2≤B*d:=Nat.mul_le_mul_left B (by omega)
  by_cases ha : ab.1<B*d+1
  · have hb : B*d<ab.2:=by omega
    rw [hg.homogenize_vanish v Ω δ B kl.2 ab.2 (lt_of_le_of_lt hr hb),Torus.mul_zero]
  · have ha' : B*d<ab.1:=by omega
    rw [hf.homogenize_vanish v Ω δ B kl.1 ab.1 (lt_of_le_of_lt hl ha'),Torus.zero_mul]

lemma regrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g) :
    regrade v Ω δ B (f*g)=regrade v Ω δ B f*regrade v Ω δ B g := by
  rw [←(regrade_hasSum v Ω δ B hf).tsum_eq,←(regrade_hasSum v Ω δ B hg).tsum_eq,
    (regrade_hasSum v Ω δ B hf).summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (regrade_hasSum v Ω δ B hg).summable (regrade_product_summable v Ω δ B hf hg),
    ←(regrade_hasSum v Ω δ B (hf.mul v Ω δ B hg)).tsum_eq]
  apply tsum_congr
  intro n
  rw [coeff_mul,_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  exact homogenize_mul v Ω δ _ _ (fun m hm=>(hf ab.1 m hm).1) (fun m hm=>(hg ab.2 m hm).1)

lemma regrade_add {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g) :
    regrade v Ω δ B (f+g)=regrade v Ω δ B f+regrade v Ω δ B g := by
  apply (regrade_hasSum v Ω δ B (hf.add v Ω δ B hg)).unique
  have H : (fun n=>homogenize v Ω δ (coeff n (f+g)))=
      (fun n=>homogenize v Ω δ (coeff n f)+homogenize v Ω δ (coeff n g)) := by
    funext n
    rw [_root_.map_add,_root_.map_add]
  rw [H]
  exact (regrade_hasSum v Ω δ B hf).add (regrade_hasSum v Ω δ B hg)
end Topology
end
end ElementaryPositivity.QuantumTorus

end

end OAI
