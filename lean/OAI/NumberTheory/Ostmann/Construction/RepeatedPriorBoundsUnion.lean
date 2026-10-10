import OAI.NumberTheory.Ostmann.Construction.InitialEtaDefs
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsCandidates
import OAI.NumberTheory.Ostmann.Construction.RepeatedPriorBoundsCenters

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Filter
open RepeatedPriorBounds

namespace InitialEta

def candidateValues (giant bulk spectator : PrimeSource) {ι : Type*} [Fintype ι]
    (aux : ι → PrimeSource) (b s : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i : Position b s ι => (tupleSource giant bulk spectator aux b s i).candidates)

theorem tupleValues_mem_candidateValues {giant bulk spectator : PrimeSource} {ι : Type*}
    [Fintype ι] {aux : ι → PrimeSource} {b s : ℕ}
    (x : JointSample giant bulk spectator aux b s) (i : Position b s ι) :
    tupleValues x i∈candidateValues giant bulk spectator aux b s := by
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,(tupleSample x i).property⟩

end InitialEta

theorem initial_candidate_cutoff_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀p : spectator.Sample, Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀ b s : ℕ,∀ i : InitialEta.Position b s (AuxiliaryIndex k),
      ∀p∈(InitialEta.tupleSource C.giant C.bulk spectator C.auxiliary b s i).candidates,
        p≤cellPrimeCutoff L := by
  filter_upwards [initial_cell_centers_eventually d Bs BD Bz hk,
    cell_center_ranges_eventually hk] with L hc hr
  intro E C hG hGu hcl hcu hb hd spectator hspec b s i p hp
  have hc := hc E C hG hGu hcl hcu hb hd
  have hL : 0≤L := by linarith [hr.1]
  have hhalf : 1≤Real.exp L/2 := hr.2.2.2.2.1
  have hgc : (C.giantCenter:ℝ)+1≤Real.exp L := by linarith [hc.1.2]
  have hac (i : AuxiliaryIndex k) : auxiliaryCenter C i+1≤Real.exp L := by
    linarith [(hc.2 i).2]
  rcases i with ⟨h,i⟩
  rcases i with u | (j | (j | j))
  · exact logCellPrimeSource_candidate_le_cutoff C.giantPositive hgc hp
  · have hlog := (harmonicBand_log_support C.bulkPositive (⟨p,hp⟩ : C.bulk.Sample)).2
    have hlog' : Real.log (p:ℝ)≤Real.exp L :=
      hlog.trans (Real.exp_le_exp.mpr (by nlinarith))
    exact nat_le_cellPrimeCutoff_of_log_le (C.bulk.prime p hp).pos hlog'
  · exact nat_le_cellPrimeCutoff_of_log_le (spectator.prime p hp).pos
      ((hspec ⟨p,hp⟩).trans (Real.exp_le_exp.mpr (by nlinarith)))
  · cases j with
    | inl j => exact logCellPrimeSource_candidate_le_cutoff _ (hac (.inl j)) hp
    | inr ji => exact logCellPrimeSource_candidate_le_cutoff _ (hac (.inr ji)) hp

theorem initial_candidate_harmonicMass_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀p : spectator.Sample, Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀ b s : ℕ,
        harmonicPrimeMass (InitialEta.candidateValues C.giant C.bulk spectator C.auxiliary b s)≤2*L := by
  filter_upwards [initial_candidate_cutoff_eventually d Bs BD Bz hk,
    harmonicPrimeMass_le_two_mul_eventually] with L hc hm
  intro E C hG hGu hcl hcu hb hd spectator hspec b s
  apply hm
  · intro p hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
    exact (InitialEta.tupleSource C.giant C.bulk spectator C.auxiliary b s i).prime p hp
  · intro p hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
    exact hc E C hG hGu hcl hcu hb hd spectator hspec b s i p hp

end Ostmann.Construction

end

end OAI
