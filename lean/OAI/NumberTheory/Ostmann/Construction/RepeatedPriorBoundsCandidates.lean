import OAI.NumberTheory.Ostmann.Construction.BalancedCellScale
import OAI.NumberTheory.Ostmann.Construction.LogLogPrimeBands

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.RepeatedPriorBounds
open Filter

theorem nat_le_cellPrimeCutoff_of_log_le {L : ℝ} {p : ℕ} (hp : 0<p)
    (hlog : Real.log (p:ℝ)≤Real.exp L) : p≤cellPrimeCutoff L := by
  have hreal : (p:ℝ)≤Real.exp (Real.exp L) :=
    (Real.log_le_iff_le_exp (by exact_mod_cast hp)).mp hlog
  exact_mod_cast hreal.trans (Nat.le_ceil _)

theorem logCellPrimes_candidate_le_cutoff {L c : ℝ}
    (hc : c+1≤Real.exp L) {p : ℕ} (hp : p∈logCellPrimes c) :
    p≤cellPrimeCutoff L := by
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2.trans
    (Nat.ceil_mono (Real.exp_le_exp.mpr hc))

theorem logCellPrimeSource_candidate_le_cutoff {L c : ℝ} {E : Finset ℕ}
    (hZ : 0<logCellMass c E) (hc : c+1≤Real.exp L) {p : ℕ}
    (hp : p∈(logCellPrimeSource c E hZ).candidates) : p≤cellPrimeCutoff L := by
  exact logCellPrimes_candidate_le_cutoff hc (Finset.mem_sdiff.mp hp).1

theorem harmonicPrimeSource_candidate_le_cutoff {L : ℝ} {P : Finset ℕ}
    (hP : ∀p∈P,Nat.Prime p) (hZ : 0<harmonicPrimeMass P)
    (hlog : ∀p∈P,Real.log (p:ℝ)≤Real.exp L) {p : ℕ}
    (hp : p∈(harmonicPrimeSource P hP hZ).candidates) : p≤cellPrimeCutoff L := by
  exact nat_le_cellPrimeCutoff_of_log_le (hP p hp).pos (hlog p hp)

theorem harmonicPrimeMass_le_two_mul_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀p∈P,Nat.Prime p) →
      (∀p∈P,p≤cellPrimeCutoff L) → harmonicPrimeMass P≤2*L := by
  obtain ⟨C,hC,hM⟩ := Ostmann.Reuse.primeReciprocal_abs_error_bound
  filter_upwards [eventually_ge_atTop (C+1),eventually_ge_atTop (0:ℝ),
    cellPrimeCutoff_tendsto.eventually_ge_atTop 2] with L hLC hL hcut
  intro P hP hbound
  have hsub : P⊆primePrefix (cellPrimeCutoff L:ℝ) := by
    intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨(hP p hp).pos,?_⟩,hP p hp⟩
    simpa only [Nat.floor_natCast] using hbound p hp
  have hsum : harmonicPrimeMass P≤harmonicPrimeMass (primePrefix (cellPrimeCutoff L:ℝ)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  have hm := (abs_le.mp (hM (cellPrimeCutoff L:ℝ) (by exact_mod_cast hcut))).2
  change harmonicPrimeMass (primePrefix (cellPrimeCutoff L:ℝ))-
    Real.log (Real.log (cellPrimeCutoff L:ℝ))≤C at hm
  have hl := cellPrimeCutoff_loglog_upper hL
  linarith

theorem candidate_union_le_cutoff {ι : Type*} (I : Finset ι) (sources : ι→PrimeSource)
    {L : ℝ} (hcut : ∀i∈I,∀p∈(sources i).candidates,p≤cellPrimeCutoff L)
    {p : ℕ} (hp : p∈I.biUnion (fun i => (sources i).candidates)) :
    p≤cellPrimeCutoff L := by
  obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
  exact hcut i hi p hp

theorem candidate_union_harmonicMass_le_eventually {ι : Type*} :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Finset ι) (sources : ι→PrimeSource),
      (∀i∈I,∀p∈(sources i).candidates,p≤cellPrimeCutoff L) →
      harmonicPrimeMass (I.biUnion (fun i => (sources i).candidates))≤2*L := by
  filter_upwards [harmonicPrimeMass_le_two_mul_eventually] with L hL
  intro I sources hcut
  apply hL
  · intro p hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
    exact (sources i).prime p hp
  · intro p hp
    exact candidate_union_le_cutoff I sources hcut hp

end Ostmann.Construction.RepeatedPriorBounds

end

end OAI
