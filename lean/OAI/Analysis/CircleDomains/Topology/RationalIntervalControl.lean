import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Algebra.Order.Archimedean

namespace OAI

/-! Bounds on rational intervals extend to all compact interior intervals
by continuity from above. No pointwise continuity of a density is required. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

 theorem le_measure_Icc_of_rational_enclosures (μ : Measure ℝ)
    {a b x y : ℝ} (hax : a < x) (hyb : y < b)
    (hfin : μ (Icc a b) < ∞) (c : ℝ≥0∞)
    (h : ∀ p q : ℚ, a < (p : ℝ) → (p : ℝ) < x →
      y < (q : ℝ) → (q : ℝ) < b → c ≤ μ (Icc (p : ℝ) q)) :
    c ≤ μ (Icc x y) := by
  obtain ⟨p, hp, hpmem, hplim⟩ :=
    Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt Rat.cast_mono hax
  obtain ⟨q, hq, hqmem, hqlim⟩ :=
    Rat.denseRange_cast.exists_seq_strictAnti_tendsto_of_lt Rat.cast_mono hyb
  let V : ℕ → Set ℝ := fun n => Icc (p n : ℝ) (q n : ℝ)
  have hanti : Antitone V := fun i j hij =>
    Icc_subset_Icc (Rat.cast_mono (hp.monotone hij)) (Rat.cast_mono (hq.antitone hij))
  have hinter : (⋂ n, V n) = Icc x y := by
    ext z
    constructor
    · intro hz
      exact ⟨le_of_tendsto hplim (Eventually.of_forall fun n => (mem_iInter.mp hz n).1),
        ge_of_tendsto hqlim (Eventually.of_forall fun n => (mem_iInter.mp hz n).2)⟩
    · intro hz
      exact mem_iInter.mpr fun n =>
        ⟨(hpmem n).2.le.trans hz.1, hz.2.trans (hqmem n).1.le⟩
  have hVfin : μ (V 0) ≠ ∞ :=
    ((measure_mono (Icc_subset_Icc (hpmem 0).1.le (hqmem 0).2.le)).trans_lt hfin).ne
  rw [← hinter, hanti.measure_iInter (fun _ => measurableSet_Icc.nullMeasurableSet) ⟨0, hVfin⟩]
  exact le_iInf fun n => h (p n) (q n) (hpmem n).1 (hpmem n).2 (hqmem n).1 (hqmem n).2

end CircleDomainRigidity

end OAI
