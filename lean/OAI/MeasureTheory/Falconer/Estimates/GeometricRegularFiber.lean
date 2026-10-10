import OAI.MeasureTheory.Falconer.Estimates.SelectedRegularFiber

namespace OAI

/-! The selected regular fiber with all energy and incidence estimates
supplied by the original geometric configuration. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem geometric_regular_fiber (N : ℕ) {s t K M m L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 < m) (hL : 0 < L)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ L) :
    ∃ l ∈ P.biUnion T, ∃ S ⊆ P, S.Nonempty ∧
      m*(P.card:ℝ)/(8*L) ≤ (S.card:ℝ) ∧ (∀ x ∈ S, l ∈ T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) (t-s)
        (4*pencilEnergyCutoff N s t K M m P*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s)) S := by
  let Q := pencilEnergyCutoff N s t K M m P
  let U := fun x => (T x).filter fun l => pencilFiberEnergy N (t-s) P T l ≤ Q
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨p,hp⟩ := hP.exists_mem
  have hM : 0 < M := hm.trans_le ((hT p hp).1.trans (hT p hp).2.1)
  have hpot : 0 < planarPotentialConstant s t := planarPotentialConstant_pos hst
  have hcrit : 0 < planarCriticalConstant N t := by unfold planarCriticalConstant; positivity
  have hQ : 0 < Q := by
    dsimp [Q,pencilEnergyCutoff,pencilEnergyBudget,pencilMomentBudget]
    positivity
  obtain ⟨R,hRP,hR,hhalf,_,hgood⟩ := prune_pencil_fiber_energy N hs hst hK hm
    P T hP hPchart hPball hT
  have hUR : R.biUnion U ⊆ P.biUnion T := by
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hRP hx,(Finset.mem_filter.mp hl).1⟩
  have hRcard : 0 < (R.card:ℝ) := Nat.cast_pos.mpr hR.card_pos
  obtain ⟨l,hl,S,hSR,hS,hsize,hinc,hreg⟩ := regular_fiber_of_pencil_degree N
    (sub_nonneg.mpr hst.le) (show 0 < m/2 by positivity) hL hQ R U hR
    (fun x hx => (hgood x hx).1)
    ((Nat.cast_le.mpr (Finset.card_le_card hUR)).trans hunion) (by
      intro l hl
      obtain ⟨x,hx,hlx⟩ := Finset.mem_biUnion.mp hl
      exact (pencilFiberEnergy_mono N (t-s) P R T U hRP
        (fun _ _ => Finset.filter_subset _ _) l).trans (Finset.mem_filter.mp hlx).2)
  refine ⟨l,hUR hl,S,hSR.trans hRP,hS,?_,?_,?_⟩
  · apply le_trans _ hsize
    apply (div_le_div_iff₀ (by positivity : 0 < 8*L) (by positivity : 0 < 2*L)).2
    have hh := mul_le_mul_of_nonneg_left hhalf hm.le
    nlinarith only [hh,hL]
  · exact fun x hx => (Finset.mem_filter.mp (hinc x hx)).1
  · have hd : m*(P.card:ℝ)/4 ≤ (m/2)*(R.card:ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hhalf hm.le
      linarith only [hh]
    have hratio : L/((m/2)*(R.card:ℝ)) ≤ 4*L/(m*(P.card:ℝ)) := by
      calc
        _ ≤ L/(m*(P.card:ℝ)/4) := div_le_div_of_nonneg_left hL.le (by positivity) hd
        _ = _ := by field_simp
    have hC : 4*Q*(L/((m/2)*(R.card:ℝ)))^2*(2:ℝ)^(t-s) ≤
        4*Q*(4*L/(m*(P.card:ℝ)))^2*(2:ℝ)^(t-s) := by gcongr
    intro z r hr hr1
    have hr0 : 0 ≤ r := (show 0 ≤ 1/(2:ℝ)^N by positivity).trans hr
    exact (hreg z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))

end Falconer

end OAI
