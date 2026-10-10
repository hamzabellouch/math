import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolyZExtension

namespace OAI

/-! # Extensions of groups with torsion-free cyclic series -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G : Type} [Group G]

theorem TorsionFreeCyclicFactors.cons {H K L : Subgroup G} {n : ℕ}
    (s : CyclicStep H K) {c : CyclicSeries K L n}
    (hs : letI := s.normal; HasNoNontrivialTorsion (K ⧸ H.subgroupOf K))
    (hc : TorsionFreeCyclicFactors c) : TorsionFreeCyclicFactors (c.cons s) := by
  intro i hi
  cases i with
  | zero =>
    exact (cyclicStep_torsionFree_congr ((c.cons s).step 0 hi) s rfl c.first).mpr hs
  | succ i => exact hc i (by omega)

theorem TorsionFreeCyclicFactors.tail {H K : Subgroup G} {n : ℕ}
    {c : CyclicSeries H K (n + 1)} (hc : TorsionFreeCyclicFactors c) :
    TorsionFreeCyclicFactors c.tail := by
  intro i hi
  exact hc (i + 1) (by omega)

def cyclicSeriesJoin {H K L : Subgroup G} {n m : ℕ}
    (c : CyclicSeries H K n) (d : CyclicSeries K L m) : CyclicSeries H L (n + m) where
  group i := if i ≤ n then c.group i else d.group (i - n)
  first := by simpa using c.first
  last := by
    by_cases hm : m = 0
    · subst m
      simpa only [Nat.add_zero, ite_true, le_refl] using c.last.trans d.first.symm |>.trans d.last
    · simpa only [ite_false, show ¬ n + m ≤ n by omega, Nat.add_sub_cancel_left] using d.last
  step i hi := by
    by_cases hn : i < n
    · simpa only [ite_true, show i ≤ n by omega, show i + 1 ≤ n by omega] using c.step i hn
    · by_cases he : i = n
      · subst i
        simpa only [ite_true, le_refl, ite_false, show ¬ n + 1 ≤ n by omega,
          Nat.add_sub_cancel_left, c.last, d.first] using d.step 0 (by omega)
      · simpa only [ite_false, show ¬ i ≤ n by omega, show ¬ i + 1 ≤ n by omega,
          show i + 1 - n = (i - n) + 1 by omega] using d.step (i - n) (by omega)

theorem TorsionFreeCyclicFactors.join {H K L : Subgroup G} {n m : ℕ}
    {c : CyclicSeries H K n} {d : CyclicSeries K L m}
    (hc : TorsionFreeCyclicFactors c) (hd : TorsionFreeCyclicFactors d) :
    TorsionFreeCyclicFactors (cyclicSeriesJoin c d) := by
  intro i hi
  by_cases hn : i < n
  · apply (cyclicStep_torsionFree_congr ((cyclicSeriesJoin c d).step i hi)
      (c.step i hn) ?_ ?_).mpr (hc i hn)
    · simp only [cyclicSeriesJoin, ite_true, show i ≤ n by omega]
    · simp only [cyclicSeriesJoin, ite_true, show i + 1 ≤ n by omega]
  · by_cases he : i = n
    · subst i
      apply (cyclicStep_torsionFree_congr ((cyclicSeriesJoin c d).step n hi)
        (d.step 0 (by omega)) ?_ ?_).mpr (hd 0 (by omega))
      · simp only [cyclicSeriesJoin, ite_true, le_refl, c.last, d.first]
      · simp only [cyclicSeriesJoin, ite_false, show ¬ n + 1 ≤ n by omega,
          Nat.add_sub_cancel_left]
    · apply (cyclicStep_torsionFree_congr ((cyclicSeriesJoin c d).step i hi)
        (d.step (i - n) (by omega)) ?_ ?_).mpr (hd (i - n) (by omega))
      · simp only [cyclicSeriesJoin, ite_false, show ¬ i ≤ n by omega]
      · simp only [cyclicSeriesJoin, ite_false, show ¬ i + 1 ≤ n by omega,
          show i + 1 - n = (i - n) + 1 by omega]

theorem isPolyZ_of_normal_subgroup (N : Subgroup G) [N.Normal]
    (hN : IsPolyZ N) (hQ : IsPolyZ (G ⧸ N)) : IsPolyZ G := by
  obtain ⟨n, c, hc⟩ := hN
  obtain ⟨m, d, hd⟩ := hQ
  let cG := c.map N.subtype
  let cG' : CyclicSeries (⊥ : Subgroup G) N n :=
    { cG with
      first := by simpa only [Subgroup.map_bot] using cG.first
      last := by simpa only [← MonoidHom.range_eq_map, N.range_subtype] using cG.last }
  let dG := d.comap (QuotientGroup.mk' N)
  let dG' : CyclicSeries N ⊤ m :=
    { dG with
      first := by simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk'] using dG.first
      last := by simpa only [Subgroup.comap_top] using dG.last }
  have hcG : TorsionFreeCyclicFactors cG' := hc.map N.subtype N.subtype_injective
  have hdG : TorsionFreeCyclicFactors dG' := hd.comap (QuotientGroup.mk' N)
  exact ⟨n + m, cyclicSeriesJoin cG' dG', hcG.join hdG⟩

end PolycyclicRecognition

end

end OAI
