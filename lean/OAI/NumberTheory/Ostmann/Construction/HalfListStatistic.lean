import OAI.NumberTheory.Ostmann.Construction.HalfListBounds
import OAI.NumberTheory.Ostmann.Construction.HalfListMean

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators
open Ostmann.Preliminaries

def integerUpperWindow (d : Decomposition) (X : ℕ) : Finset ℤ :=
  (upperWindow d.A X).map ⟨Int.ofNat,Int.ofNat_injective⟩

theorem halfListStatistic_lower : ∃ cψ : ℝ, 0<cψ ∧
    ∀ (d : Decomposition) (P : Finset ℕ) (giant bulk spectator : PrimeSource)
      {ι : Type} [Fintype ι] (aux : ι → PrimeSource) (b s m X : ℕ) (tb td : ℤ) (g : ℝ),
      0<X → 0≤g → (upperWindow d.A X).Nonempty →
      SourceWindowCoverage d bulk X → SourceWindowCoverage d spectator X →
      (∀i,SourceWindowCoverage d (aux i) X) →
      Real.exp (-10*(m:ℝ)) ≤ nongiantScalar d bulk spectator aux b s tb td →
      g ≤ giant.law.mean (fun p => if (p:ℕ)∈P then giantEmpiricalMean d X p else 0) →
      cψ*((upperWindow d.A X).card:ℝ)*(Real.exp (-10*(m:ℝ))*g)^2 ≤
        smoothedStatistic X (halfListTest d P giant bulk spectator aux b s tb td) := by
  obtain ⟨cψ,hc,hstat⟩ := exists_cutoff_statistic_constant
  refine ⟨cψ,hc,?_⟩
  intro d P giant bulk spectator ι inst aux b s m X tb td g hX hg hwindow hb hs haux hcL hgL
  have hcard : (0:ℝ)<(upperWindow d.A X).card := by exact_mod_cast hwindow.card_pos
  have hmean := halfListTest_window_mean_lower d P giant bulk spectator aux b s m X tb td hg hb hs haux hcL hgL
  have hsum := (le_div_iff₀ hcard).mp hmean
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hrange : ∀n∈integerUpperWindow d X, |(n:ℝ)/(X:ℝ)|≤1 := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hn
    have haX : (a:ℝ)≤X := by exact_mod_cast (mem_upperWindow.mp ha).2.1
    change |(a:ℝ)/(X:ℝ)|≤1
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg a) hXr.le)]
    exact (div_le_one hXr).mpr haX
  have hcardeq : (integerUpperWindow d X).card=(upperWindow d.A X).card := Finset.card_map _
  have hsum' : ((integerUpperWindow d X).card:ℝ)*(Real.exp (-10*(m:ℝ))*g)≤
      ∑n∈integerUpperWindow d X,halfListTest d P giant bulk spectator aux b s tb td n := by
    rw [hcardeq]
    simp only [integerUpperWindow,Finset.sum_map,Function.Embedding.coeFn_mk]
    change ((upperWindow d.A X).card:ℝ)*(Real.exp (-10*(m:ℝ))*g) ≤
      ∑a∈upperWindow d.A X,halfListTest d P giant bulk spectator aux b s tb td (a:ℤ)
    nlinarith
  have h := hstat (X:ℝ) (halfListBound giant bulk spectator aux b s)
    (Real.exp (-10*(m:ℝ))*g) (halfListTest d P giant bulk spectator aux b s tb td)
    (integerUpperWindow d X) hXr (halfListBound_nonneg giant bulk spectator aux b s)
    (halfListTest_abs_le d P giant bulk spectator aux b s tb td)
    (mul_nonneg (Real.exp_pos _).le hg) hrange hsum'
  rwa [hcardeq] at h

end Ostmann.Construction

end

end OAI
