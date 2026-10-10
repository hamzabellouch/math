import Mathlib
import OAI.Probability.Ballisticity.Estimates.UpperPairPatch

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma finiteLogExcess_eq_ciSup {Ω : Type*} (A : ℝ) (p : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    finiteLogExcess A p N ω = ⨆ n : Fin (N+1), max (-Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2)) 0 := by
  unfold finiteLogExcess
  rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal']

lemma finiteLogExcess_stability {Ω : Type*} (A : ℝ) (p q : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω)
    {ε : ℝ} (hε : 0 ≤ ε) (hpq : ∀ n ≤ N, |Real.log (p n ω)-Real.log (q n ω)| ≤ ε) :
    |finiteLogExcess A p N ω-finiteLogExcess A q N ω| ≤ ε := by
  have one_side (p q : ℕ → Ω → ℝ)
      (hpq : ∀ n ≤ N, |Real.log (p n ω)-Real.log (q n ω)| ≤ ε) :
      finiteLogExcess A p N ω ≤ finiteLogExcess A q N ω+ε := by
    rw [finiteLogExcess_eq_ciSup]
    apply ciSup_le
    intro n
    have hq : max (-Real.log (q n ω)-2*A*Real.log ((n:ℝ)+2)) 0 ≤ finiteLogExcess A q N ω := by
      rw [finiteLogExcess_eq_ciSup]
      exact le_ciSup (Set.finite_range (fun k : Fin (N+1) => max (-Real.log (q k ω)-2*A*Real.log ((k:ℝ)+2)) 0)).bddAbove n
    have hh := (abs_le.mp (hpq n (by omega))).1
    apply (max_le_max (by linarith : -Real.log (p n ω)-2*A*Real.log ((n:ℝ)+2) ≤
      -Real.log (q n ω)-2*A*Real.log ((n:ℝ)+2)+ε) (show (0:ℝ) ≤ 0+ε by linarith)).trans
    simpa only [max_add_add_right] using add_le_add_left hq ε
  have h₁ := one_side p q hpq
  have h₂ := one_side q p (fun n hn => by simpa only [abs_sub_comm] using hpq n hn)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma log_uniform_on_positive_interval {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : ℝ, c ≤ p → p ≤ 1 → c ≤ q → q ≤ 1 → |p-q| < δ →
      |Real.log p-Real.log q| < ε := by
  have hcont : ContinuousOn Real.log (Set.Icc c 1) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt (hc.trans_le hx.1))
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨δ,hδ,?_⟩
  intro p q hp hp1 hq hq1 hdif
  exact hd p ⟨hp,hp1⟩ q ⟨hq,hq1⟩ hdif
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma outwardKernelMass_le_one {d : ℕ} (e f : Direction d) (H : ℕ)
    (x : Lattice d × Lattice d) (ω : Environment d) : outwardKernelMass e f H x ω ≤ 1 := by
  have hh := ENNReal.toReal_mono ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)})).trans (rawPairEndpointLaw_total_le_one (realPosition (step e)) H ω x))
  simpa only [outwardKernelMass,ENNReal.toReal_one] using hh

lemma outwardLog_fixed_height_locality {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e f : Direction d) {H : ℕ} (hH : 0 < H) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (a : ℝ) (x : Lattice d × Lattice d), x ∈ PairAtHeight (realPosition (step e)) a →
      ∀ (ω : Environment d), (∀ y g, κ ≤ (ω y).1 g) →
      |Real.log (outwardKernelMass e f H x ω)-
        Real.log (outwardKernelMass e f H x (upperPairPatch e a x N ω))| < ε := by
  have hκr : 0 < (κ:ℝ) := by exact_mod_cast hκ
  obtain ⟨δ,hδ,hlog⟩ := log_uniform_on_positive_interval (pow_pos hκr (2*H)) hε
  obtain ⟨N,hN⟩ := rawPairEndpointLaw_upper_patch_locality hκ e hH
    (ENNReal.ofReal_pos.mpr (show 0 < δ/2 by linarith))
  refine ⟨N,?_⟩
  intro a x hx ω hω
  let η := upperPairPatch e a x N ω
  have hη := upperPairPatch_elliptic e a x N ω hω
  apply hlog _ _ (outwardKernelMass_lower e f H ω x (fun y => hω y e))
    (outwardKernelMass_le_one e f H x ω)
    (outwardKernelMass_lower e f H η x (fun y => hη y e))
    (outwardKernelMass_le_one e f H x η)
  let S := {y : Lattice d × Lattice d | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)}
  have hfin (ζ : Environment d) : rawPairEndpointLaw (realPosition (step e)) H ζ x S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((measure_mono (Set.subset_univ _)).trans (rawPairEndpointLaw_total_le_one _ _ _ _))
  have hh := hN a x hx ω hω S
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin η,ENNReal.ofReal_ne_top⟩) hh.1
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin ω,ENNReal.ofReal_ne_top⟩) hh.2
  rw [ENNReal.toReal_add (hfin η) ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by linarith : 0 ≤ δ/2)] at h₁
  rw [ENNReal.toReal_add (hfin ω) ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal (by linarith : 0 ≤ δ/2)] at h₂
  change outwardKernelMass e f H x ω ≤ outwardKernelMass e f H x η+δ/2 at h₁
  change outwardKernelMass e f H x η ≤ outwardKernelMass e f H x ω+δ/2 at h₂
  exact abs_lt.mpr ⟨by linarith,by linarith⟩
end DirectionalTransience

end

end

end OAI
