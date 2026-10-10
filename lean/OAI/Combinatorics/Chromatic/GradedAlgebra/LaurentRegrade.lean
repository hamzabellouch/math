import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentHomogenize
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)
local instance laurentRegradeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRegradeAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def LaurentBounded (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀ n m, coeff n f m ≠ 0 →
    0 ≤ δ m ∧ -(B : ℤ)*δ m ≤ κ m ∧ (n : ℤ) ≤ κ m + (B+1 : ℤ)*δ m

lemma LaurentBounded.zero : LaurentBounded v Ω δ κ B 0 := by
  intro n m h
  simp at h
lemma LaurentBounded.one : LaurentBounded v Ω δ κ B 1 := by
  intro n m hm
  have hn : n = 0 := by by_contra hn; simp [coeff_one, hn] at hm
  subst n
  have hm0 : m = 0 := by
    by_contra hm0
    apply hm
    rw [coeff_one, ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne hm0
  subst m
  simp
lemma LaurentBounded.add {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    LaurentBounded v Ω δ κ B (f+g) := by
  intro n m hm
  have H : coeff n f m ≠ 0 ∨ coeff n g m ≠ 0 := by
    by_contra hh
    push Not at hh
    simp [hh.1, hh.2] at hm
  exact H.elim (hf n m) (hg n m)
lemma LaurentBounded.neg {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) : LaurentBounded v Ω δ κ B (-f) := by
  intro n m hm
  apply hf n m
  intro hz
  apply hm
  change -(coeff n f m) = 0
  rw [hz, neg_zero]
lemma LaurentBounded.mul {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g) :
    LaurentBounded v Ω δ κ B (f*g) := by
  intro n r hr
  obtain ⟨a,b,m,l,hab,hm,hl,rfl⟩ := series_product_nonzero v Ω f g n r hr
  obtain ⟨hdm,hkm,hem⟩ := hf a m hm
  obtain ⟨hdl,hkl,hel⟩ := hg b l hl
  simp only [map_add]
  refine ⟨add_nonneg hdm hdl, ?_, ?_⟩
  · nlinarith
  · rw [←hab, Nat.cast_add]
    nlinarith

lemma LaurentBounded.laurent_vanish {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (d n : ℕ) (z : ℤ)
    (hz : z < -(B : ℤ)*(d : ℤ) ∨ z + (B+1 : ℤ)*(d : ℤ) < n) :
    (coeff d (laurentHomogenize v Ω δ κ (coeff n f))).coeff z = 0 := by
  ext m
  rw [laurentHomogenize_coeff]
  split_ifs with hh
  · by_contra hm
    obtain ⟨hd,hk,hn⟩ := hf n m hm
    have hD : δ m = (d : ℤ) := by rw [hh.1, Int.toNat_of_nonneg hd]
    rw [hD, ←hh.2] at hk hn
    rcases hz with hz | hz <;> omega
  · rfl

def laurentRegradeFamily (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) (d : ℕ) :
    HahnSeries.SummableFamily ℤ (Torus v Ω) ℕ where
  toFun n := coeff d (laurentHomogenize v Ω δ κ (coeff n f))
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨-(B : ℤ)*(d : ℤ), ?_⟩
    intro z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    by_contra h
    exact hn (hf.laurent_vanish v Ω δ κ B d n z (Or.inl (lt_of_not_ge h)))
  finite_co_support' z := by
    apply (Finset.finite_toSet (Finset.range ((z+(B+1 : ℤ)*(d : ℤ)).toNat+1))).subset
    intro n hn
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hn
    apply hf.laurent_vanish v Ω δ κ B d n z
    right
    omega

def laurentRegrade (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) : PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  PowerSeries.mk fun d => (laurentRegradeFamily v Ω δ κ B f hf d).hsum

lemma laurentRegrade_coeff (f : PowerSeries (Torus v Ω))
    (hf : LaurentBounded v Ω δ κ B f) (d : ℕ) (z : ℤ) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z =
      ∑ n ∈ Finset.range ((z+(B+1 : ℤ)*(d : ℤ)).toNat+1),
        (coeff d (laurentHomogenize v Ω δ κ (coeff n f))).coeff z := by
  rw [laurentRegrade, coeff_mk]
  apply HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hn (hf.laurent_vanish v Ω δ κ B d n z (Or.inr (by omega)))

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance laurentRegradeBiRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance laurentRegradeBiAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradeBiAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def BiBounded (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀ n m, coeff n f m ≠ 0 → 0 ≤ δ m ∧ 0 ≤ κ m ∧ (n : ℤ) ≤ δ m + κ m
lemma BiBounded.zero : BiBounded v Ω δ κ 0 := by intro n m h; simp at h
lemma BiBounded.one : BiBounded v Ω δ κ 1 := by
  intro n m hm
  have hn : n=0 := by by_contra hn; simp [coeff_one,hn] at hm
  subst n
  have hm0 : m=0 := by
    by_contra hm0
    apply hm
    rw [coeff_one,ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne hm0
  subst m
  simp
lemma BiBounded.add {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g) : BiBounded v Ω δ κ (f+g) := by
  intro n m hm
  have H : coeff n f m≠0 ∨ coeff n g m≠0 := by
    by_contra hh
    push Not at hh
    simp [hh.1,hh.2] at hm
  exact H.elim (hf n m) (hg n m)
lemma BiBounded.neg {f : PowerSeries (Torus v Ω)} (hf : BiBounded v Ω δ κ f) :
    BiBounded v Ω δ κ (-f) := by
  intro n m hm
  apply hf n m
  intro hz
  apply hm
  change -(coeff n f m)=0
  rw [hz,neg_zero]
lemma BiBounded.mul {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g) : BiBounded v Ω δ κ (f*g) := by
  intro j r hr
  obtain ⟨a,b,m,n,hab,hm,hn,rfl⟩ := series_product_nonzero v Ω f g j r hr
  obtain ⟨hdm,hkm,hem⟩ := hf a m hm
  obtain ⟨hdn,hkn,hen⟩ := hg b n hn
  simp only [map_add]
  refine ⟨add_nonneg hdm hdn,add_nonneg hkm hkn,?_⟩
  rw [←hab,Nat.cast_add]
  omega
lemma BiBounded.bi_vanish {f : PowerSeries (Torus v Ω)} (hf : BiBounded v Ω δ κ f)
    (d e n : ℕ) (hne : d+e<n) : coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))=0 := by
  ext m
  rw [biHomogenize_coeff]
  split_ifs with hh
  · by_contra hz
    obtain ⟨hd,hk,he⟩ := hf n m hz
    have hD : δ m=(d : ℤ) := by rw [hh.1,Int.toNat_of_nonneg hd]
    have hK : κ m=(e : ℤ) := by rw [hh.2,Int.toNat_of_nonneg hk]
    omega
  · rfl
lemma BiBounded.bi_product_vanish {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g)
    (d e a b : ℕ) (ha : d+e<a ∨ d+e<b) :
    coeff e (coeff d (biHomogenize v Ω δ κ (coeff a f)*
      biHomogenize v Ω δ κ (coeff b g)))=0 := by
  rw [coeff_mul,map_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro kl hkl
  have H1:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have H2:=Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rcases ha with ha|ha
  · rw [hf.bi_vanish v Ω δ κ ij.1 kl.1 a (by omega),Torus.zero_mul]
  · rw [hg.bi_vanish v Ω δ κ ij.2 kl.2 b (by omega),Torus.mul_zero]

def boundedBiRegrade (f : PowerSeries (Torus v Ω)) : PowerSeries (PowerSeries (Torus v Ω)) :=
  PowerSeries.mk fun d => PowerSeries.mk fun e =>
    ∑ n ∈ Finset.range (d+e+1), coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))
lemma boundedBiRegrade_coeff (f : PowerSeries (Torus v Ω)) (d e : ℕ) :
    coeff e (coeff d (boundedBiRegrade v Ω δ κ f)) =
      ∑ n ∈ Finset.range (d+e+1), coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f))) := by
  simp only [boundedBiRegrade,coeff_mk]

section Topology
local instance laurentRegradeTopology : TopologicalSpace (Torus v Ω) := ⊥
local instance laurentRegradeDiscreteTopology : DiscreteTopology (Torus v Ω) := ⟨rfl⟩
open scoped PowerSeries.WithPiTopology
lemma boundedBiRegrade_hasSum {f : PowerSeries (Torus v Ω)} (hf : BiBounded v Ω δ κ f) :
    HasSum (fun n => biHomogenize v Ω δ κ (coeff n f)) (boundedBiRegrade v Ω δ κ f) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro e
  rw [boundedBiRegrade_coeff]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply hf.bi_vanish v Ω δ κ d e n
  simp only [Finset.mem_range,not_lt] at hn
  omega
lemma boundedBiRegrade_product_summable {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g) :
    Summable (fun ab : ℕ×ℕ => biHomogenize v Ω δ κ (coeff ab.1 f)*
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
lemma boundedBiRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : BiBounded v Ω δ κ f) (hg : BiBounded v Ω δ κ g) :
    boundedBiRegrade v Ω δ κ (f*g) = boundedBiRegrade v Ω δ κ f*boundedBiRegrade v Ω δ κ g := by
  rw [←(boundedBiRegrade_hasSum v Ω δ κ hf).tsum_eq,
    ←(boundedBiRegrade_hasSum v Ω δ κ hg).tsum_eq,
    (boundedBiRegrade_hasSum v Ω δ κ hf).summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (boundedBiRegrade_hasSum v Ω δ κ hg).summable (boundedBiRegrade_product_summable v Ω δ κ hf hg),
    ←(boundedBiRegrade_hasSum v Ω δ κ (hf.mul v Ω δ κ hg)).tsum_eq]
  apply tsum_congr
  intro n
  rw [coeff_mul,_root_.map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  exact biHomogenize_mul v Ω δ κ _ _ (fun m hm => ⟨(hf ab.1 m hm).1,(hf ab.1 m hm).2.1⟩)
    (fun m hm => ⟨(hg ab.2 m hm).1,(hg ab.2 m hm).2.1⟩)
end Topology

lemma boundedBiRegrade_add (f g : PowerSeries (Torus v Ω)) :
    boundedBiRegrade v Ω δ κ (f+g) = boundedBiRegrade v Ω δ κ f+boundedBiRegrade v Ω δ κ g := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [_root_.map_add, _root_.map_add, boundedBiRegrade_coeff,
    boundedBiRegrade_coeff, boundedBiRegrade_coeff, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [_root_.map_add, _root_.map_add, _root_.map_add, _root_.map_add]
lemma boundedBiRegrade_one : boundedBiRegrade v Ω δ κ 1=1 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  rw [boundedBiRegrade_coeff]
  rw [Finset.sum_eq_single 0]
  · simp only [coeff_zero_one,biHomogenize_one]
  · intro n hn hne
    rw [coeff_one,ite_eq_right hne,_root_.map_zero,_root_.map_zero,_root_.map_zero]
  · intro hn
    exact (hn (by simp)).elim
lemma boundedBiRegrade_zero : boundedBiRegrade v Ω δ κ 0=0 := by
  apply PowerSeries.ext
  intro d
  apply PowerSeries.ext
  intro e
  simp only [boundedBiRegrade_coeff,_root_.map_zero,Finset.sum_const_zero]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
