import OAI.MeasureTheory.Falconer.Incidence.CoarserPencilDirections
import OAI.MeasureTheory.Falconer.Estimates.GeometricRegularFiber

namespace OAI

/-! A single original coarse tube with a regular family of incident cells,
all of whose local point sets have good transverse projected energy. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem packet_good_regular_fiber (N : ℕ) {s t K KP m M L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hKP : 1 ≤ KP)
    (hm : 0 < m) (hL : 0 < L)
    (C : Finset (Space 2)) (T Q : Space 2 → Finset (Space 2)) (hC : C.Nonempty)
    (hCchart : InBoundedLineChart C)
    (hCball : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t K C)
    (hT : ∀ x ∈ C, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^(N+3)) x l)
    (hQ : ∀ x ∈ C, (Q x).Nonempty ∧ InBoundedLineChart (Q x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP (Q x))
    (hunion : ((C.biUnion T).card:ℝ) ≤ L) :
    ∃ l ∈ C.biUnion T, ∃ S ⊆ C, S.Nonempty ∧
      m*(C.card:ℝ)/(400*L) ≤ (S.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) (t-s)
        (4*pencilEnergyCutoff (N+3) s t (50*K) M (m/50) C*
          (4*L/((m/50)*(C.card:ℝ)))^2*(2:ℝ)^(t-s)) S ∧
      ∀ x ∈ S, l ∈ T x ∧
        planarProjectionEnergy N s (-l 0) (Q x) ≤
          2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*((Q x).card:ℝ)^2 := by
  have hchoice (x : Space 2) (hx : x ∈ C) := good_pencil_projection_directions_coarser N hs hst
    hK hKP x (hCchart x hx).1 (T x)
    (Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le (hT x hx).1)))
    (hT x hx).2.2.2.1 (hT x hx).2.2.1 (hT x hx).2.2.2.2.2
    (hT x hx).2.2.2.2.1 (Q x) (hQ x hx).1 (hQ x hx).2.1 (hQ x hx).2.2
  let U := fun x => if hx : x ∈ C then Classical.choose (hchoice x hx) else ∅
  have hU (x : Space 2) (hx : x ∈ C) :
      U x ⊆ T x ∧ (U x).Nonempty ∧ ((T x).card:ℝ) ≤ 50*((U x).card:ℝ) ∧
      FiniteSeparatedAt (1/(2:ℝ)^(N+3)) (U x) ∧ InBoundedLineChart (U x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) s (50*K) (U x) ∧
      ∀ l ∈ U x, planarProjectionEnergy N s (-l 0) (Q x) ≤
        2*projectionEnergyBudget N s t (25*K*(4:ℝ)^s) KP*((Q x).card:ℝ)^2 := by
    simpa only [U,dite_eq_left hx] using Classical.choose_spec (hchoice x hx)
  have hUU : C.biUnion U ⊆ C.biUnion T := by
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hx,(hU x hx).1 hl⟩
  have hK' : 1 ≤ 50*K := by linarith only [hK]
  have hCb : NormalizedFiniteBallBound (1/(2:ℝ)^(N+3)) t (50*K) C := by
    intro z r hr hr1
    have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^(N+3) by positivity).trans hr
    exact (hCball z r hr hr1).trans (by
      gcongr
      linarith only [hK])
  obtain ⟨l,hl,S,hSC,hS,hsize,hinc,hreg⟩ := geometric_regular_fiber (N+3) hs hst hK'
    (show 0 < m/50 by positivity) hL C U hC hCchart hCb (by
      intro x hx
      have hu := hU x hx
      refine ⟨?_,?_,hu.2.2.2.2.1,hu.2.2.2.2.2.1,?_⟩
      · have hh := (hT x hx).1
        linarith only [hh,hu.2.2.1]
      · exact (Nat.cast_le.mpr (Finset.card_le_card hu.1)).trans (hT x hx).2.1
      · exact fun a ha => (hT x hx).2.2.2.2.2 a (hu.1 ha))
    ((Nat.cast_le.mpr (Finset.card_le_card hUU)).trans hunion)
  refine ⟨l,hUU hl,S,hSC,hS,?_,hreg,?_⟩
  · convert hsize using 1
    ring
  · intro x hx
    exact ⟨(hU x (hSC hx)).1 (hinc x hx),(hU x (hSC hx)).2.2.2.2.2.2 l (hinc x hx)⟩

end Falconer

end OAI
