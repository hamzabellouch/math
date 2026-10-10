import OAI.NumberTheory.Ostmann.Construction.InitialEtaPeriod
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsCenters
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationPriors

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction.InitialEta

theorem initial_tupleValues_min_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ)) →
      ∀x:JointSample C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2),
      (jointPrior C.giant C.bulk spectator C.auxiliary
        (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)).mass x≠0 →
      ∀i,Real.exp (Real.exp ((1/2000:ℝ)*L))≤(tupleValues x i:ℝ) := by
  filter_upwards [RepeatedPriorBounds.initial_cell_centers_eventually d Bs BD Bz hk,
    SourceRangeSeparation.broad_range_gaps_eventually k] with L hcenters hgap
  intro E C hG hGu hcl hcu hb hd spectator hspec x hm i
  have hL := hgap.1
  have hwidth := hgap.2.1
  have hr : Real.exp ((1/2000:ℝ)*L)≤favorableBlockWidth L/200 :=
    (Real.exp_le_exp.mpr (by linarith)).trans hgap.2.2.2.1.le
  have hc := hcenters E C hG hGu hcl hcu hb hd
  have hmass := tupleSample_mass_ne_zero C.giant C.bulk spectator C.auxiliary _ _ x hm
  apply (Real.le_log_iff_exp_le (by exact_mod_cast (tupleValues_prime x i).pos)).mp
  rcases i with ⟨h,i⟩
  rcases i with u | (j | (j | j))
  · cases u
    have hs := C.giant_log_support (halfAt x h).1 (hmass (h,.inl ()))
    change _≤Real.log ((halfAt x h).1:ℕ)
    have hs' := (abs_lt.mp hs).1
    linarith [hc.1.1]
  · have hs := (harmonicBand_log_support C.bulkPositive ((halfAt x h).2.1 j)).1
    change _≤Real.log ((halfAt x h).2.1 j:ℕ)
    exact (Real.exp_le_exp.mpr (by nlinarith)).trans hs
  · exact hspec ((halfAt x h).2.2.1 j)
  · cases j with
    | inl j =>
      have hs := C.cells.topSource_cell_support E C.deleted_card j
        ((halfAt x h).2.2.2 (.inl j)) (hmass (h,.inr (.inr (.inr (.inl j)))))
      have hlo := (hc.2 (.inl j)).1
      change favorableBlockWidth L/100≤(C.cells.top j:ℝ) at hlo
      change _≤Real.log ((halfAt x h).2.2.2 (.inl j):ℕ)
      have hs' := (abs_lt.mp hs).1
      linarith
    | inr ji =>
      have hs := C.cells.compSource_cell_support E C.deleted_card ji.1 ji.2
        ((halfAt x h).2.2.2 (.inr ji)) (hmass (h,.inr (.inr (.inr (.inr ji)))))
      have hlo := (hc.2 (.inr ji)).1
      change favorableBlockWidth L/100≤(C.cells.comp ji.1 ji.2:ℝ) at hlo
      change _≤Real.log ((halfAt x h).2.2.2 (.inr ji):ℕ)
      have hs' := (abs_lt.mp hs).1
      linarith

end Ostmann.Construction.InitialEta

end

end OAI
