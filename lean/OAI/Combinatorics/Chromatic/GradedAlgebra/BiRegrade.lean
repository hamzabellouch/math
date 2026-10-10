import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalLaurentFaithful

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance biRegradeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance biRegradeAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance biRegradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def biRegrade (f : PowerSeries (Torus v Ω)) : PowerSeries (PowerSeries (Torus v Ω)) :=
  PowerSeries.mk fun d=>PowerSeries.mk fun e=>coeff e (coeff d (biHomogenize v Ω δ κ (coeff (d+e) f)))
lemma biRegrade_coeff (f : PowerSeries (Torus v Ω)) (d e : ℕ) :
    coeff e (coeff d (biRegrade v Ω δ κ f))=
      coeff e (coeff d (biHomogenize v Ω δ κ (coeff (d+e) f))) := by simp [biRegrade]

section Topology
local instance biRegradeTopology : TopologicalSpace (Torus v Ω) := ⊥
local instance biRegradeDiscreteTopology : DiscreteTopology (Torus v Ω) := ⟨rfl⟩
open scoped PowerSeries.WithPiTopology
lemma biRegrade_hasSum {f : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f) :
    HasSum (fun n=>biHomogenize v Ω δ κ (coeff n f)) (biRegrade v Ω δ κ f) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro e
  rw [biRegrade_coeff]
  have H : HasSum (fun n=>coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f))))
      (∑n∈({d+e}:Finset ℕ),coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))) :=
    hasSum_sum_of_ne_finset_zero (s:={d+e})
    (f:=fun n=>coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f))))
    (fun n hn=>hf.bi_vanish v Ω δ κ d e n (by simpa using hn))
  simpa using H
lemma biRegrade_product_summable {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g) :
    Summable (fun ab : ℕ×ℕ=>biHomogenize v Ω δ κ (coeff ab.1 f)*
      biHomogenize v Ω δ κ (coeff ab.2 g)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro e
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet ((Finset.range (d+e+1)).product (Finset.range (d+e+1)))).subset
  intro ab hab
  change coeff e (coeff d (biHomogenize v Ω δ κ (coeff ab.1 f)*
    biHomogenize v Ω δ κ (coeff ab.2 g)))≠0 at hab
  change ab∈(Finset.range (d+e+1)) ×ˢ (Finset.range (d+e+1))
  rw [Finset.mem_product,Finset.mem_range,Finset.mem_range]
  by_contra H
  exact hab (hf.bi_product_vanish v Ω δ κ hg d e ab.1 ab.2 (by omega))
lemma biRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g) :
    biRegrade v Ω δ κ (f*g)=biRegrade v Ω δ κ f*biRegrade v Ω δ κ g := by
  rw [←(biRegrade_hasSum v Ω δ κ hf).tsum_eq,←(biRegrade_hasSum v Ω δ κ hg).tsum_eq,
    (biRegrade_hasSum v Ω δ κ hf).summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (biRegrade_hasSum v Ω δ κ hg).summable (biRegrade_product_summable v Ω δ κ hf hg),
    ←(biRegrade_hasSum v Ω δ κ (hf.mul v Ω δ κ hg)).tsum_eq]
  apply tsum_congr
  intro n
  rw [coeff_mul,_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  exact biHomogenize_mul v Ω δ κ _ _ (fun m hm=>⟨(hf ab.1 m hm).1,(hf ab.1 m hm).2.1⟩)
    (fun m hm=>⟨(hg ab.2 m hm).1,(hg ab.2 m hm).2.1⟩)
end Topology
lemma biRegrade_add (f g : PowerSeries (Torus v Ω)) :
    biRegrade v Ω δ κ (f+g)=biRegrade v Ω δ κ f+biRegrade v Ω δ κ g := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  simp only [biRegrade_coeff,_root_.map_add]
  rw [_root_.map_add,_root_.map_add,_root_.map_add]
lemma biRegrade_one : biRegrade v Ω δ κ 1=1 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [biRegrade_coeff,coeff_one]
  by_cases hd : d=0
  · subst d
    by_cases he : e=0
    · subst e
      simp [biHomogenize_one]
    · simp [he]
  · have hde : d+e≠0:=by omega
    simp [hd]
lemma biRegrade_read (f : PowerSeries (Torus v Ω)) (d e : ℕ) (m : M)
    (hd : δ m=(d:ℤ)) (he : κ m=(e:ℤ)) :
    coeff e (coeff d (biRegrade v Ω δ κ f)) m=coeff (d+e) f m := by
  rw [biRegrade_coeff,biHomogenize_coeff,hd,he]
  simp
lemma biRegrade_injective {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g)
    (heq : biRegrade v Ω δ κ f=biRegrade v Ω δ κ g) : f=g := by
  apply PowerSeries.ext
  intro n
  ext m
  by_cases H : 0≤δ m ∧ 0≤κ m ∧ (n:ℤ)=δ m+κ m
  · have hn : n=(δ m).toNat+(κ m).toNat:=by omega
    rw [hn,←biRegrade_read v Ω δ κ f _ _ m (Int.toNat_of_nonneg H.1).symm
      (Int.toNat_of_nonneg H.2.1).symm,heq,
      biRegrade_read v Ω δ κ g _ _ m (Int.toNat_of_nonneg H.1).symm
        (Int.toNat_of_nonneg H.2.1).symm]
  · have Hf : coeff n f m=0:=by by_contra hz; exact H (hf n m hz)
    have Hg : coeff n g m=0:=by by_contra hz; exact H (hg n m hz)
    rw [Hf,Hg]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
