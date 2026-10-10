import OAI.NumberTheory.Ostmann.Construction.InitialEtaCoordinates
import OAI.NumberTheory.Ostmann.Construction.InitialEtaPrior
import OAI.NumberTheory.Ostmann.Construction.InitialNominalGeometry
import OAI.NumberTheory.Ostmann.Construction.SelectedSourceSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta

lemma tupleSample_mass_ne_zero (giant bulk spectator : PrimeSource) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (aux : ι → PrimeSource) (b s : ℕ)
    (x : JointSample giant bulk spectator aux b s)
    (hm : (jointPrior giant bulk spectator aux b s).mass x≠0) (i : Position b s ι) :
    (tupleSource giant bulk spectator aux b s i).law.mass (tupleSample x i)≠0 := by
  classical
  rw [jointPrior_mass] at hm
  exact (Finset.prod_ne_zero_iff.mp hm) i (Finset.mem_univ i)

theorem initial_tuplePeriod_log_support {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (x : JointSample C.giant C.bulk spectator C.auxiliary
      (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2))
    (hm : (jointPrior C.giant C.bulk spectator C.auxiliary
      (Conclusion.bulkSize k L/2) (Conclusion.bulkSize k L/2)).mass x≠0)
    (hb : tupleBins C.bulkBin C.spectatorBin x≠0) :
    |Real.log (tuplePeriod x:ℝ)-(Real.log (C.scale:ℝ)+Conclusion.initialGap Bs k L)|≤14+6*(k:ℝ) := by
  classical
  have hmass := tupleSample_mass_ne_zero C.giant C.bulk spectator C.auxiliary _ _ x hm
  have hg (h : Bool) : |Real.log ((jointCoordinates x).giant h)-(C.giantCenter:ℝ)|≤1 := by
    exact (C.giant_log_support (halfAt x h).1 (hmass (h,.inl ()))).le
  have ht (h : Bool) (i : Fin 3) :
      |Real.log ((jointCoordinates x).top h i)-(C.cells.top i:ℝ)|≤1 := by
    exact (logCellPrimeSource_log_support _ E
      (C.cells.top_balanced i E C.deleted_card).choose ((halfAt x h).2.2.2 (.inl i))
      (hmass (h,.inr (.inr (.inr (.inl i)))))).le
  have hc (h : Bool) (j : Fin k) (i : Fin 2) :
      |Real.log ((jointCoordinates x).compensation h j i)-(C.cells.comp j i:ℝ)|≤1 := by
    exact (logCellPrimeSource_log_support _ E
      (C.cells.comp_balanced j i E C.deleted_card).choose ((halfAt x h).2.2.2 (.inr (j,i)))
      (hmass (h,.inr (.inr (.inr (.inr (j,i))))))).le
  have hb' : Arithmetic.realLeafBins (jointCoordinates x) C.bulkBin C.spectatorBin≠0 := by
    rwa [jointCoordinates_bins]
  obtain ⟨hbulk,hspec⟩ := Arithmetic.realLeafBins_support _ _ _ hb'
  have htop : |(∑_h:Bool,∑i,(C.cells.top i:ℝ))-
      (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin-2*C.bulkBin)|≤2 := by
    simpa only [Fintype.sum_bool,← two_mul] using C.cells.top_doubled_error.le
  have hcomp : |(∑_h:Bool,∑j,∑i,(C.cells.comp j i:ℝ))-
      (∑j:Fin k,nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j)|≤2*(k:ℝ) := by
    have he : (∑_h:Bool,∑j,∑i,(C.cells.comp j i:ℝ))-
        (∑j:Fin k,nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j) =
        ∑j:Fin k,(2*(∑i,(C.cells.comp j i:ℝ))-
          nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j) := by
      simp only [Fintype.sum_bool,Finset.sum_sub_distrib,← Finset.mul_sum]
      ring
    rw [he]
    calc
      _ ≤ ∑j:Fin k,|2*(∑i,(C.cells.comp j i:ℝ))-
          nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑_j:Fin k,(2:ℝ) := Finset.sum_le_sum fun j _ => (C.cells.comp_doubled_error j).le
      _ = _ := by simp [mul_comm]
  have hg' := initial_nominal_log_product_support (jointCoordinates x) (jointCoordinates_positive x)
    C.giantCenter C.bulkBin C.spectatorBin
    (nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin)
    (fun j => nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j)
    (fun _ i => (C.cells.top i:ℝ)) (fun _ j i => (C.cells.comp j i:ℝ))
    hg hbulk hspec ht hc 2 (2*k) htop hcomp
  rw [jointCoordinates_product] at hg'
  have hnom := nominalCompensation_total Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin
  rw [← Fin.sum_univ_eq_sum_range] at hnom
  change nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin+
      (∑j:Fin k,nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j)=
      Real.log (C.scale:ℝ)-2*C.giantCenter-2*C.spectatorBin+Conclusion.initialGap Bs k L at hnom
  have he : 2*(C.giantCenter:ℝ)+2*C.spectatorBin+
      nominalJ Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin+
      (∑j:Fin k,nominalCompensation Bs BD Bz k L C.blockBase C.giantCenter C.spectatorBin j)=
      Real.log (C.scale:ℝ)+Conclusion.initialGap Bs k L := by linarith
  rw [he] at hg'
  convert hg' using 1; ring

end Ostmann.Construction.InitialEta

end

end OAI
