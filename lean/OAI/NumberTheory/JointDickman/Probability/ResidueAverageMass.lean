import OAI.NumberTheory.JointDickman.Probability.EndpointHistogramIdentity
import OAI.NumberTheory.JointDickman.Probability.SampledHistogram

namespace OAI

/-! # Residue averaging recovers the same logarithmic marginal for every modulus -/

namespace JointDickman
open Finset

open Classical in
theorem logResidueCell_sum {D : Type*} [DecidableEq D] {B q : ℕ} [NeZero q]
    (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (n : ℕ) (hn : n.Coprime q) (i : D) (c : ℝ) :
    (∑ r : (ZMod q)ˣ, if logResidueCell B q lower upper n = some (i,r) then c else 0) =
      if Real.log n/B ∈ Set.Ioc (lower i) (upper i) then c else 0 := by
  classical
  simp_rw [logResidueCell_eq_some B q lower upper hdisjoint]
  by_cases hi : Real.log n/B ∈ Set.Ioc (lower i) (upper i)
  · simp only [hi,true_and,ite_true]
    rw [sum_eq_single (ZMod.unitOfCoprime n hn)]
    · simp
    · intro r _ hr
      have hne : (n : ZMod q) ≠ (r : ZMod q) := by
        intro he
        apply hr
        exact Units.ext he.symm
      simp [hne]
    · simp
  · simp [hi]

noncomputable def logCellSignedMass (m B : ℕ)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (i : Fin (channelFineCount m B)) : ℝ :=
  ∑ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
    if Real.log n/B ∈ Set.Ioc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i) then
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n else 0

theorem manuscript_residue_average_mass {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (i : Fin (channelFineCount m B)) :
    channelMesh (channelFineCount m B)*
      finiteResidueAverage (fun r => manuscriptChannel m B q g (i,r)) =
      logCellSignedMass m B g i := by
  classical
  have havg : channelMesh (channelFineCount m B)*
      finiteResidueAverage (fun r => manuscriptChannel m B q g (i,r)) =
      ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q g (i,r) := by
    unfold finiteResidueAverage
    rw [← mul_sum]
    simp only [ZMod.card_units_eq_totient]
    ring
  rw [havg]
  simp_rw [← manuscriptChannel_cell_mass hm hB g]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  have hcop := primeSplitProductSupport_coprime (auxiliaryPrimes_prime B) (NeZero.ne q)
    (fun p hp => hcut.trans_lt (by exact_mod_cast (mem_filter.mp hp).2)) hn
  exact logResidueCell_sum (B := B) (q := q) _ _
    (channelCells_disjoint (channelFineCount_pos hm hB)) n hcop i
      (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n)

theorem manuscript_residue_average_independent {m B q d : ℕ} [NeZero q] [NeZero d]
    (hm : 0 < m) (hB : 0 < B) (hq : q ≤ auxiliaryCutoff B) (hd : d ≤ auxiliaryCutoff B)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (i : Fin (channelFineCount m B)) :
    finiteResidueAverage (fun r => manuscriptChannel m B q g (i,r)) =
      finiteResidueAverage (fun r => manuscriptChannel m B d g (i,r)) := by
  apply (mul_left_cancel₀ (channelMesh_pos (channelFineCount_pos hm hB)).ne')
  rw [manuscript_residue_average_mass hm hB hq,manuscript_residue_average_mass hm hB hd]

theorem sampledProjectedValue_log_mass {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    (J : Finset (Fin (channelFineCount m B))) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) :
    sampledProjectedValue m B q J g F =
      ∑ i ∈ J, (logCellSignedMass m B g i : ℂ)*F i := by
  unfold sampledProjectedValue
  apply sum_congr rfl
  intro i _
  rw [← Complex.ofReal_mul,manuscript_residue_average_mass hm hB hcut]

end JointDickman

end OAI
