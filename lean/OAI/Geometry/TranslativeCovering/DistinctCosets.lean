import OAI.Geometry.TranslativeCovering.PeriodicDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory
open scoped ENNReal Classical
noncomputable def PeriodicCover.coset {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K)
    (i : Fin P.m) : Space n ⧸ P.lattice := Submodule.Quotient.mk (P.offsets i)

def PeriodicCover.Distinct {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) : Prop :=
  Function.Injective P.coset

noncomputable def thetaPer {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ P : {P : PeriodicCover K // P.Distinct},volume K*P.val.intensity

lemma PeriodicCover.remove_repeats {n : ℕ} {K : Set (Space n)} (P : PeriodicCover K) :
    ∃ Q : PeriodicCover K,Q.Distinct ∧ Q.intensity≤P.intensity := by
  let S : Finset (Space n ⧸ P.lattice) := Finset.univ.image P.coset
  have hex (s : S) : ∃ i : Fin P.m,P.coset i=s.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp s.property
    exact ⟨i,hi⟩
  let r : S → Fin P.m := fun s => Classical.choose (hex s)
  have hr (s : S) : P.coset (r s)=s.val := Classical.choose_spec (hex s)
  let e := Finset.equivFin S
  let Q : PeriodicCover K := {
    lattice := P.lattice
    discrete := P.discrete
    fullrank := P.fullrank
    m := S.card
    offsets := fun j => P.offsets (r (e.symm j))
    covers := by
      intro y
      obtain ⟨i,l,hy⟩ := P.covers y
      let s : S := ⟨P.coset i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩
      have heq : P.coset i=P.coset (r s) := (hr s).symm
      have hmem : P.offsets i-P.offsets (r s) ∈ P.lattice := (Submodule.Quotient.eq P.lattice).mp heq
      refine ⟨e s,⟨P.offsets i-P.offsets (r s)+l.val,P.lattice.add_mem hmem l.property⟩,?_⟩
      simp only [Equiv.symm_apply_apply]
      have he : y - P.offsets (r s) - (P.offsets i - P.offsets (r s) + l.val) =
          y - P.offsets i - l.val := by abel
      simpa only [he] using hy }
  refine ⟨Q,?_,?_⟩
  · intro j k hjk
    change P.coset (r (e.symm j))=P.coset (r (e.symm k)) at hjk
    rw [hr,hr] at hjk
    exact e.symm.injective (Subtype.ext hjk)
  · change (S.card:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)≤
      (P.m:ℝ≥0∞)/ENNReal.ofReal (ZLattice.covolume P.lattice volume)
    apply ENNReal.div_le_div_right
    have hc : S.card≤P.m := by simpa only [S,Finset.card_univ,Fintype.card_fin] using (Finset.card_image_le (s:=Finset.univ) (f:=P.coset))
    exact_mod_cast hc

lemma listed_eq_distinct {n : ℕ} (K : Set (Space n)) : thetaPerListed K=thetaPer K := by
  apply le_antisymm
  · apply le_iInf
    intro P
    exact iInf_le (fun Q : PeriodicCover K => volume K*Q.intensity) P.val
  · apply le_iInf
    intro P
    obtain ⟨Q,hQ,hQP⟩ := P.remove_repeats
    exact (iInf_le (fun Q : {P : PeriodicCover K // P.Distinct} => volume K*Q.val.intensity) ⟨Q,hQ⟩).trans
      (mul_le_mul le_rfl hQP bot_le bot_le)

theorem periodization_exact {n : ℕ} {K : Set (Space n)} (hK : ConvexBody K) :
    thetaT K=thetaPer K := (periodization_all hK).trans (listed_eq_distinct K)
end TranslativeCovering

end OAI
