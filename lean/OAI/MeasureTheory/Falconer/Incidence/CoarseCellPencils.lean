import OAI.MeasureTheory.Falconer.Incidence.IncidentCoarsePencils

namespace OAI

/-! Construct all coarse cell pencils from the original fine incidences,
with one common logarithmic loss and their original fine witnesses. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem coarse_cell_pencils {δ ρ s K : ℝ}
    (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/2) (hδρ : δ ≤ ρ)
    (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P C : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (q : Space 2 → Space 2) (hC : C ⊆ P.image q)
    (hnear : ∀ p ∈ P, dist p (q p) ≤ ρ)
    (hchart : ∀ c ∈ C, |c 0| ≤ 1/4 ∧ |c 1| ≤ 1/4)
    (hV : ∀ p ∈ P, (V p).Nonempty ∧ NormalizedFiniteBallBound δ s K (V p) ∧
      ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) :
    let S := fun c => P.filter fun p => q p = c
    let ql := fun c (l : Space 2) => roundedIncidentLine ρ c (l 0)
    let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
    ∃ T : Space 2 → Finset (Space 2), ∀ c ∈ C,
      T c ⊆ ((S c).biUnion V).image (ql c) ∧ (T c).Nonempty ∧
      InBoundedLineChart (T c) ∧ FiniteSeparatedAt ρ (T c) ∧
      NormalizedFiniteBallBound ρ s (2*(K*(7:ℝ)^s)*(J:ℝ)) (T c) ∧
      (∀ a ∈ T c, TubeIncident ρ c a ∧
        ((∑ p ∈ S c, (V p).card):ℝ) ≤ 2*(J:ℝ)*((T c).card:ℝ)*
          (coarsePencilWeight (S c) V (ql c) a:ℝ)) ∧
      ∀ p ∈ S c, ∀ l ∈ V p, dist l (ql c l) ≤ 6*ρ := by
  dsimp only
  let S := fun c => P.filter fun p => q p = c
  let ql := fun c (l : Space 2) => roundedIncidentLine ρ c (l 0)
  let J := Nat.log 2 (∑ p ∈ P, (V p).card)+1
  have hS (c : Space 2) (hc : c ∈ C) : (S c).Nonempty := by
    obtain ⟨p,hp,hpc⟩ := Finset.mem_image.mp (hC hc)
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,hpc⟩⟩
  have hcell (c : Space 2) (p : Space 2) (hp : p ∈ S c) : dist p c ≤ ρ := by
    obtain ⟨hp,hpc⟩ := Finset.mem_filter.mp hp
    simpa only [hpc] using hnear p hp
  have hchoice (c : Space 2) (hc : c ∈ C) := incident_regular_coarse_pencil hδ hρ hρ1 hδρ hs hK
    (S c) V (hS c hc) c (hchart c hc).1 (hchart c hc).2 (hcell c)
    (fun p hp => hV p (Finset.mem_filter.mp hp).1)
  let T := fun c => if hc : c ∈ C then Classical.choose (hchoice c hc) else ∅
  refine ⟨T,?_⟩
  intro c hc
  have hh := Classical.choose_spec (hchoice c hc)
  have he : T c = Classical.choose (hchoice c hc) := dite_eq_left hc
  rw [← he] at hh
  obtain ⟨hsub,hne,hch,hsep,hreg,hweight⟩ := hh
  have hsum : ∑ p ∈ S c, (V p).card ≤ ∑ p ∈ P, (V p).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hJ : (Nat.log 2 (∑ p ∈ S c, (V p).card)+1:ℕ) ≤ J :=
    Nat.add_le_add_right (Nat.log_mono_right hsum) 1
  have hJR : ((Nat.log 2 (∑ p ∈ S c, (V p).card)+1:ℕ):ℝ) ≤ (J:ℝ) := Nat.cast_le.mpr hJ
  refine ⟨hsub,hne,hch,hsep,?_,?_,?_⟩
  · intro z r hr hr1
    have hr0 : 0 ≤ r := hρ.le.trans hr
    exact (hreg z r hr hr1).trans (by gcongr)
  · intro a ha
    refine ⟨(hweight a ha).1,?_⟩
    have hw : (∑ p ∈ S c, ((V p).card:ℝ)) ≤
        2*((Nat.log 2 (∑ p ∈ S c, (V p).card)+1:ℕ):ℝ)*((T c).card:ℝ)*
          (coarsePencilWeight (S c) V (ql c) a:ℝ) := by
      simpa only [Nat.cast_sum,ql] using (hweight a ha).2
    have hb : (∑ p ∈ S c, ((V p).card:ℝ)) ≤ 2*(J:ℝ)*((T c).card:ℝ)*
        (coarsePencilWeight (S c) V (ql c) a:ℝ) := by
      calc
        _ ≤ _ := hw
        _ ≤ _ := by gcongr
    simpa only [S,ql,Nat.cast_sum] using hb
  · intro p hp l hl
    have ht := (hV p (Finset.mem_filter.mp hp).1).2.2 l hl
    exact rounded_incident_near_line hρ c l ((hchart c hc).1.trans (by norm_num))
      (moved_point_residual hδ hρ hδρ p c l (hcell c p hp) (ht.1.trans (by norm_num)) ht.2)

end Falconer

end OAI
