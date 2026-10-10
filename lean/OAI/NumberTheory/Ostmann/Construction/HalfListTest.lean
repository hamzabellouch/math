import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.ExactGroupScalar
import OAI.NumberTheory.Ostmann.Construction.FavorableGiant

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

namespace FinitePrior

theorem pair_mean {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (ν : FinitePrior β) (f : α×β → ℝ) :
    (μ.pair ν).mean f=μ.mean (fun x => ν.mean (fun y => f (x,y))) := by
  simp only [mean,pair,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem mean_mul_const {α : Type*} [Fintype α]
    (μ : FinitePrior α) (f : α → ℝ) (c : ℝ) :
    μ.mean (fun x => f x*c)=μ.mean f*c := by
  simp only [mean,← mul_assoc,← Finset.sum_mul]

theorem mean_const_mul {α : Type*} [Fintype α]
    (μ : FinitePrior α) (c : ℝ) (f : α → ℝ) :
    μ.mean (fun x => c*f x)=c*μ.mean f := by
  simp only [mean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem pair_mean_product {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (ν : FinitePrior β) (f : α → ℝ) (g : β → ℝ) :
    (μ.pair ν).mean (fun x => f x.1*g x.2)=μ.mean f*ν.mean g := by
  rw [pair_mean]
  simp_rw [mean_const_mul,mean_mul_const]

end FinitePrior

def primeSourceTestMean (d : Decomposition) (S : PrimeSource) (n : ℤ) : ℝ :=
  S.law.mean (fun p => (residueTest d p (n:ZMod (p:ℕ))).re)

def primeGroupTestMean (d : Decomposition) (S : PrimeSource) (b : ℕ) (t : ℤ)
    (n : ℤ) : ℝ :=
  (primeGroupPrior S b).mean (fun x => Ostmann.smoothPartition (primeGroupLog S b x-t)*
    ∏i,(residueTest d (x i) (n:ZMod (x i:ℕ))).re)

def giantTestMean (d : Decomposition) (P : Finset ℕ) (giant : PrimeSource) (n : ℤ) : ℝ :=
  giant.law.mean (fun p => (favorableGiantResidueTest d P p (n:ZMod (p:ℕ))).re)

def halfListTest (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) (n : ℤ) : ℝ :=
  giantTestMean d P giant n*primeGroupTestMean d bulk b tb n*
    primeGroupTestMean d spectator s td n*∏i,primeSourceTestMean d (aux i) n

abbrev HalfListSample (giant bulk spectator : PrimeSource) {ι : Type*}
    (aux : ι → PrimeSource) (b s : ℕ) :=
  giant.Sample×(PrimeGroupSample bulk b×(PrimeGroupSample spectator s×∀i,(aux i).Sample))

def halfListPrior (giant bulk spectator : PrimeSource) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ) :
    FinitePrior (HalfListSample giant bulk spectator aux b s) :=
  giant.law.pair ((primeGroupPrior bulk b).pair
    ((primeGroupPrior spectator s).pair (dependentProductPrior (fun i => (aux i).law))))

def halfListTupleTest (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
    {ι : Type*} [Fintype ι] (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) (n : ℤ)
    (x : HalfListSample giant bulk spectator aux b s) : ℝ :=
  (favorableGiantResidueTest d P x.1 (n:ZMod (x.1:ℕ))).re *
    (Ostmann.smoothPartition (primeGroupLog bulk b x.2.1-tb)*
      ∏i,(residueTest d (x.2.1 i) (n:ZMod (x.2.1 i:ℕ))).re) *
    (Ostmann.smoothPartition (primeGroupLog spectator s x.2.2.1-td)*
      ∏i,(residueTest d (x.2.2.1 i) (n:ZMod (x.2.2.1 i:ℕ))).re) *
    ∏i,(residueTest d (x.2.2.2 i) (n:ZMod (x.2.2.2 i:ℕ))).re

theorem halfListTest_eq_tuple_mean (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) (n : ℤ) :
    halfListTest d P giant bulk spectator aux b s tb td n=
      (halfListPrior giant bulk spectator aux b s).mean
        (halfListTupleTest d P giant bulk spectator aux b s tb td n) := by
  have he : halfListTupleTest d P giant bulk spectator aux b s tb td n =
      fun x => (favorableGiantResidueTest d P x.1 (n:ZMod (x.1:ℕ))).re *
        ((Ostmann.smoothPartition (primeGroupLog bulk b x.2.1-tb)*
          ∏i,(residueTest d (x.2.1 i) (n:ZMod (x.2.1 i:ℕ))).re) *
        ((Ostmann.smoothPartition (primeGroupLog spectator s x.2.2.1-td)*
          ∏i,(residueTest d (x.2.2.1 i) (n:ZMod (x.2.2.1 i:ℕ))).re) *
          ∏i,(residueTest d (x.2.2.2 i) (n:ZMod (x.2.2.2 i:ℕ))).re)) := by
    funext x
    unfold halfListTupleTest
    ring
  rw [he]
  unfold halfListPrior
  rw [FinitePrior.pair_mean_product giant.law
    ((primeGroupPrior bulk b).pair ((primeGroupPrior spectator s).pair
      (dependentProductPrior (fun i => (aux i).law))))
    (fun p => (favorableGiantResidueTest d P p (n:ZMod (p:ℕ))).re)
    (fun x => (Ostmann.smoothPartition (primeGroupLog bulk b x.1-tb)*
      ∏i,(residueTest d (x.1 i) (n:ZMod (x.1 i:ℕ))).re)*
      ((Ostmann.smoothPartition (primeGroupLog spectator s x.2.1-td)*
      ∏i,(residueTest d (x.2.1 i) (n:ZMod (x.2.1 i:ℕ))).re)*
      ∏i,(residueTest d (x.2.2 i) (n:ZMod (x.2.2 i:ℕ))).re))]
  rw [FinitePrior.pair_mean_product (primeGroupPrior bulk b)
    ((primeGroupPrior spectator s).pair (dependentProductPrior (fun i => (aux i).law)))
    (fun x => Ostmann.smoothPartition (primeGroupLog bulk b x-tb)*
      ∏i,(residueTest d (x i) (n:ZMod (x i:ℕ))).re)
    (fun x => (Ostmann.smoothPartition (primeGroupLog spectator s x.1-td)*
      ∏i,(residueTest d (x.1 i) (n:ZMod (x.1 i:ℕ))).re)*
      ∏i,(residueTest d (x.2 i) (n:ZMod (x.2 i:ℕ))).re)]
  rw [FinitePrior.pair_mean_product (primeGroupPrior spectator s)
    (dependentProductPrior (fun i => (aux i).law))
    (fun x => Ostmann.smoothPartition (primeGroupLog spectator s x-td)*
      ∏i,(residueTest d (x i) (n:ZMod (x i:ℕ))).re)
    (fun x => ∏i,(residueTest d (x i) (n:ZMod (x i:ℕ))).re)]
  rw [dependentProductPrior_mean (fun i => (aux i).law)
    (fun i p => (residueTest d p (n:ZMod (p:ℕ))).re)]
  unfold halfListTest giantTestMean primeGroupTestMean primeSourceTestMean
  ring

theorem primeSourceTestMean_on_summand (d : Decomposition) (S : PrimeSource)
    {a : ℕ} (ha : a∈d.A) (hlarge : ∀ p : S.Sample,(p:ℕ)+d.cutoff<a) :
    primeSourceTestMean d S a=primeSourceScalar d S := by
  unfold primeSourceTestMean primeSourceScalar FinitePrior.mean
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only
  rw [Int.cast_natCast,residueTest_on_summand d (S.prime _ p.property) ha (hlarge p),Complex.ofReal_re]

theorem primeGroupTestMean_on_summand (d : Decomposition) (S : PrimeSource)
    (b : ℕ) (t : ℤ) {a : ℕ} (ha : a∈d.A)
    (hlarge : ∀ p : S.Sample,(p:ℕ)+d.cutoff<a) :
    primeGroupTestMean d S b t a=primeGroupScalar d S b t := by
  unfold primeGroupTestMean primeGroupScalar FinitePrior.mean
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  rw [Int.cast_natCast,residueTest_on_summand d (S.prime _ (x i).property) ha (hlarge (x i)),Complex.ofReal_re]

theorem halfListTest_on_summand (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s : ℕ) (tb td : ℤ) {a : ℕ} (ha : a∈d.A)
    (hb : ∀ p : bulk.Sample,(p:ℕ)+d.cutoff<a)
    (hs : ∀ p : spectator.Sample,(p:ℕ)+d.cutoff<a)
    (haux : ∀i,∀p : (aux i).Sample,(p:ℕ)+d.cutoff<a) :
    halfListTest d P giant bulk spectator aux b s tb td a=
      nongiantScalar d bulk spectator aux b s tb td*giantTestMean d P giant a := by
  unfold halfListTest nongiantScalar
  rw [primeGroupTestMean_on_summand d bulk b tb ha hb,
    primeGroupTestMean_on_summand d spectator s td ha hs]
  have he : (∏i,primeSourceTestMean d (aux i) (a:ℤ))=∏i,primeSourceScalar d (aux i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact primeSourceTestMean_on_summand d (aux i) ha (haux i)
  rw [he]
  ring

end Ostmann.Construction

end

end OAI
