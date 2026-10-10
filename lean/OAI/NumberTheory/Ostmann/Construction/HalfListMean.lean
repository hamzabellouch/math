import OAI.NumberTheory.Ostmann.Construction.HalfListTest

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators
open Ostmann.Preliminaries

theorem giantTestMean_window_average (d : Decomposition) (P : Finset ℕ)
    (giant : PrimeSource) (X : ℕ) :
    (∑a∈upperWindow d.A X,giantTestMean d P giant (a:ℤ))/((upperWindow d.A X).card:ℝ)=
      giant.law.mean (fun p => if (p:ℕ)∈P then giantEmpiricalMean d X p else 0) := by
  classical
  have hpoint (p : giant.Sample) (a : ℕ) :
      (favorableGiantResidueTest d P p ((a:ℤ):ZMod (p:ℕ))).re=
        if (p:ℕ)∈P then giantNatTest d p a else 0 := by
    let : NeZero (p:ℕ) := ⟨(giant.prime _ p.property).ne_zero⟩
    rw [Int.cast_natCast,favorableGiantResidueTest_nat_re]
  unfold giantTestMean FinitePrior.mean
  dsimp only
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hP : (p:ℕ)∈P
  · simp only [hP,ite_true,giantEmpiricalMean,mul_div_assoc]
  · simp only [hP,ite_false,Finset.sum_const_zero,mul_zero,zero_div]

def SourceWindowCoverage (d : Decomposition) (S : PrimeSource) (X : ℕ) : Prop :=
  ∀ p : S.Sample, ((p:ℕ)+d.cutoff:ℝ)<(X:ℝ)^(9/10:ℝ)

lemma SourceWindowCoverage.large (d : Decomposition) (S : PrimeSource) (X : ℕ)
    (hS : SourceWindowCoverage d S X) {a : ℕ} (ha : a∈upperWindow d.A X) :
    ∀p : S.Sample,(p:ℕ)+d.cutoff<a := by
  intro p
  have h := (hS p).trans_le (mem_upperWindow.mp ha).2.2
  exact_mod_cast h

theorem halfListTest_window_average (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s X : ℕ) (tb td : ℤ)
    (hb : SourceWindowCoverage d bulk X) (hs : SourceWindowCoverage d spectator X)
    (haux : ∀i,SourceWindowCoverage d (aux i) X) :
    (∑a∈upperWindow d.A X,halfListTest d P giant bulk spectator aux b s tb td (a:ℤ))/
        ((upperWindow d.A X).card:ℝ)=
      nongiantScalar d bulk spectator aux b s tb td*
        giant.law.mean (fun p => if (p:ℕ)∈P then giantEmpiricalMean d X p else 0) := by
  have he : (∑a∈upperWindow d.A X,halfListTest d P giant bulk spectator aux b s tb td (a:ℤ))=
      nongiantScalar d bulk spectator aux b s tb td*
        ∑a∈upperWindow d.A X,giantTestMean d P giant (a:ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact halfListTest_on_summand d P giant bulk spectator aux b s tb td
      (mem_upperWindow.mp ha).1 (hb.large d bulk X ha) (hs.large d spectator X ha)
      (fun i => (haux i).large d (aux i) X ha)
  rw [he,mul_div_assoc,giantTestMean_window_average]

theorem halfListTest_window_mean_lower (d : Decomposition) (P : Finset ℕ)
    (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s m X : ℕ) (tb td : ℤ) {g : ℝ} (hg : 0≤g)
    (hb : SourceWindowCoverage d bulk X) (hs : SourceWindowCoverage d spectator X)
    (haux : ∀i,SourceWindowCoverage d (aux i) X)
    (hscalar : Real.exp (-10*(m:ℝ)) ≤ nongiantScalar d bulk spectator aux b s tb td)
    (hgiant : g ≤ giant.law.mean (fun p => if (p:ℕ)∈P then giantEmpiricalMean d X p else 0)) :
    Real.exp (-10*(m:ℝ))*g ≤
      (∑a∈upperWindow d.A X,halfListTest d P giant bulk spectator aux b s tb td (a:ℤ))/
        ((upperWindow d.A X).card:ℝ) := by
  rw [halfListTest_window_average d P giant bulk spectator aux b s X tb td hb hs haux]
  exact mul_le_mul hscalar hgiant hg ((Real.exp_pos _).le.trans hscalar)

end Ostmann.Construction

end

end OAI
