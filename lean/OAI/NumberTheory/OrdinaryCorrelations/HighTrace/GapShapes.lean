import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Edges

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace NumericalLine
variable (w : NumericalLine D h ℓ)

def gapShapes (a : S.FixedResidues w.line) (L : ℕ) : Finset (Finset (Fin ℓ)) :=
  w.line.treeSteps.powerset.filter fun E => ∃ (P : TreePath w L) (p : S.FixedIndex w.line),
    P.edges=E ∧ P.IsGap a p ∧ ∀ i,P.edge i ∈ uncutTreeEdges w.line a

lemma mem_gapShapes (a : S.FixedResidues w.line) {E : Finset (Fin ℓ)} :
    E ∈ w.gapShapes a L ↔ ∃ (P : TreePath w L) (p : S.FixedIndex w.line),
      P.edges=E ∧ P.IsGap a p ∧ ∀ i,P.edge i ∈ uncutTreeEdges w.line a := by
  constructor
  · exact fun he => (mem_filter.mp he).2
  · rintro ⟨P,p,rfl,hg,hu⟩
    exact mem_filter.mpr ⟨mem_powerset.mpr P.edges_subset,⟨P,p,rfl,hg,hu⟩⟩

lemma gapFamily_of_packing (a : S.FixedResidues w.line) (𝓠 : Finset (Finset (Fin ℓ)))
    (hQ : 𝓠 ⊆ w.gapShapes a L)
    (hdis : ∀ E ∈ 𝓠,∀ F ∈ 𝓠,E≠F → Disjoint E F) (ht : t ≤ 𝓠.card) :
    Nonempty (GapFamily w a L t) := by
  have hc : Fintype.card (Fin t) ≤ Fintype.card ↥𝓠 := by simpa using ht
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  have hw (E : ↥𝓠) := (w.mem_gapShapes a).mp (hQ E.property)
  choose P p hE hg hu using hw
  refine ⟨{
    path := fun j => P (f j)
    modulus := fun j => p (f j)
    gap := fun j => hg (f j)
    uncut := fun j => hu (f j)
    disjoint := ?_ }⟩
  intro j k hjk i n he
  have hne : (f j).val≠(f k).val := fun he => hjk (f.injective (Subtype.ext he))
  apply (disjoint_left.mp (hdis _ (f j).property _ (f k).property hne))
    (a := (P (f j)).edge i)
  · rw [←hE (f j)]
    exact (P (f j)).edge_mem i
  · rw [he,←hE (f k)]
    exact (P (f k)).edge_mem n

theorem gap_hitting (hh : 0<h) (a : S.FixedResidues w.line)
    (hpack : ¬Nonempty (GapFamily w a L t)) :
    ∃ H : Finset (Fin ℓ), H ⊆ uncutTreeEdges w.line a ∧ H.card<2*t ∧
      ∀ (P : TreePath w L) (p : S.FixedIndex w.line), P.IsGap a p →
        (∀ i,P.edge i ∈ uncutTreeEdges w.line a) → ∃ i,P.edge i ∈ H := by
  have hpaths : ∀ E ∈ w.gapShapes a L,
      E.Nonempty ∧ Grows w.line (pathTop w.line E) E ∧ (topMarks w.line E).card ≤ 2 := by
    intro E he
    obtain ⟨P,p,rfl,hg,hu⟩ := (w.mem_gapShapes a).mp he
    exact ⟨P.edges_nonempty,P.grows hh,P.topMarks_card_le_two⟩
  obtain ⟨𝓠,H,hQ,hdis,hcard,hhit,hsub⟩ := chronological_path_hitting w.line (w.gapShapes a L) hpaths
  have ht : 𝓠.card<t := lt_of_not_ge (fun ht => hpack (w.gapFamily_of_packing a 𝓠 hQ hdis ht))
  refine ⟨H,?_,by omega,?_⟩
  · intro e he
    obtain ⟨E,hE,heE⟩ := mem_biUnion.mp (hsub he)
    obtain ⟨P,p,rfl,hg,hu⟩ := (w.mem_gapShapes a).mp hE
    obtain ⟨i,hi,rfl⟩ := mem_image.mp heE
    exact hu i
  · intro P p hg hu
    have he : P.edges ∈ w.gapShapes a L := (w.mem_gapShapes a).mpr ⟨P,p,rfl,hg,hu⟩
    obtain ⟨e,heH,heE⟩ := hhit P.edges he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp heE
    exact ⟨i,heH⟩

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
