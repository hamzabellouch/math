import OAI.MeasureTheory.Falconer.Incidence.RetainedCoarseIncidences
import OAI.MeasureTheory.Falconer.Measures.CellRefinementMass

namespace OAI

/-! Simultaneous fine-point and pencil refinement in the retained coarse
cells, with global mass and local regularity inherited from the originals. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem retained_regular_cells {δ Δ s t K m M H B b J L w : ℝ}
    (hδ : 0 ≤ δ) (hΔ : 0 ≤ Δ) (hK : 1 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (hH : 0 < H) (hB : 0 < B) (hb : 0 < b) (hJ : 0 ≤ J) (hL : 0 ≤ L) (hw : 0 ≤ w)
    (P C R : Finset (Space 2)) (q : Space 2 → Space 2)
    (T U : Space 2 → Finset (Space 2)) (ql X : Space 2 → Space 2 → Space 2)
    (hR : R.Nonempty) (hRC : R ⊆ C)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hmass : (P.card:ℝ) ≤ J*∑ c ∈ C, ((P.filter fun p => q p = c).card:ℝ))
    (hband : ∀ c ∈ C, w ≤ ((P.filter fun p => q p = c).card:ℝ) ∧
      ((P.filter fun p => q p = c).card:ℝ) ≤ 2*w)
    (hcount : (C.card:ℝ) ≤ L*(R.card:ℝ))
    (hcell : ∀ c ∈ R, (P.filter fun p => q p = c).Nonempty ∧
      Function.Injective (X c) ∧
      NormalizedFiniteBallBound Δ t K ((P.filter fun p => q p = c).image (X c)))
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p))
    (hU : ∀ c ∈ R, b ≤ ((U c).card:ℝ) ∧
      ∀ a ∈ U c, (∑ p ∈ P.filter (fun p => q p = c), ((T p).card:ℝ)) ≤
        H*B*(coarsePencilWeight (P.filter (fun p => q p = c)) T (ql c) a:ℝ)) :
    let E := H*B/b
    let F := 2*E*M/m
    let V := fun p => (T p).filter fun l => ql (q p) l ∈ U (q p)
    ∃ A : Space 2 → Finset (Space 2),
      (∀ c ∈ R, A c ⊆ P.filter (fun p => q p = c) ∧ (A c).Nonempty ∧
        ((P.filter fun p => q p = c).card:ℝ) ≤ F*((A c).card:ℝ) ∧
        NormalizedFiniteBallBound Δ t (K*F) ((A c).image (X c)) ∧
        ∀ p ∈ A c, V p ⊆ T p ∧ m/(2*E) ≤ ((V p).card:ℝ) ∧
          ((V p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (V p) ∧
          ∀ l ∈ V p, ql c l ∈ U c) ∧
      R.biUnion A ⊆ P ∧ (R.biUnion A).Nonempty ∧
      (P.card:ℝ) ≤ (2*J*L*F)*((R.biUnion A).card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*(2*J*L*F)) (R.biUnion A) := by
  let S := fun c => P.filter fun p => q p = c
  let E := H*B/b
  let F := 2*E*M/m
  let V := fun p => (T p).filter fun l => ql (q p) l ∈ U (q p)
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hF : 0 ≤ F := by dsimp [F,E]; positivity
  have hzero (c : Space 2) : NormalizedFiniteBallBound δ 0 K (S c) := by
    intro z r _ _
    simp only [Real.rpow_zero,mul_one]
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
      (le_mul_of_one_le_left (Nat.cast_nonneg _) hK)
  have hchoice (c : Space 2) (hc : c ∈ R) := retain_coarse_incidences hδ hK0 hm hM hH hB hb
    (S c) (U c) T (ql c) (hcell c hc).1 (hU c hc).1 (hzero c)
    (fun p hp => hT p (Finset.mem_filter.mp hp).1) (hU c hc).2
  let A := fun c => if hc : c ∈ R then Classical.choose (hchoice c hc) else ∅
  have hdata (c : Space 2) (hc : c ∈ R) :
      A c ⊆ S c ∧ (A c).Nonempty ∧ ((S c).card:ℝ) ≤ F*((A c).card:ℝ) ∧
      NormalizedFiniteBallBound Δ t (K*F) ((A c).image (X c)) ∧
      ∀ p ∈ A c, V p ⊆ T p ∧ m/(2*E) ≤ ((V p).card:ℝ) ∧
        ((V p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (V p) ∧
        ∀ l ∈ V p, ql c l ∈ U c := by
    have hh := Classical.choose_spec (hchoice c hc)
    have he : A c = Classical.choose (hchoice c hc) := dite_eq_left hc
    rw [← he] at hh
    obtain ⟨hAS,hA,hsize,_,hfine⟩ := hh
    refine ⟨hAS,hA,hsize,?_,?_⟩
    · have hi := (hcell c hc).2.1
      have himage : (((S c).image (X c)).card:ℝ) ≤ F*(((A c).image (X c)).card:ℝ) := by
        simpa only [Finset.card_image_of_injective _ hi] using hsize
      exact normalized_finite_ball_bound_subset hΔ hK0 (Finset.image_subset_image hAS)
        himage (hcell c hc).2.2
    · intro p hp
      have hpc : q p = c := (Finset.mem_filter.mp (hAS hp)).2
      have hv : V p = (T p).filter (fun l => ql c l ∈ U c) := by dsimp [V]; rw [hpc]
      rw [hv]
      obtain ⟨hsub,hlo,hup,hreg⟩ := hfine p hp
      exact ⟨hsub,hlo,hup,hreg,fun l hl => (Finset.mem_filter.mp hl).2⟩
  obtain ⟨hsub,hmass'⟩ := cell_refinement_mass hJ hL hF hw P C R q A hRC hmass hband hcount
    (fun c hc => ⟨(hdata c hc).1,(hdata c hc).2.2.1⟩)
  have hne : (R.biUnion A).Nonempty := by
    obtain ⟨c,hc⟩ := hR
    obtain ⟨p,hp⟩ := (hdata c hc).2.1
    exact ⟨p,Finset.mem_biUnion.mpr ⟨c,hc,hp⟩⟩
  exact ⟨A,hdata,hsub,hne,hmass',normalized_finite_ball_bound_subset hδ hK0 hsub hmass' hPball⟩

end Falconer

end OAI
