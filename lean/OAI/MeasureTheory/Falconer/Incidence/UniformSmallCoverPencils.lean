import OAI.MeasureTheory.Falconer.Incidence.CoarsePencilSize

namespace OAI

/-! A small total cover forces comparable pencils to have the critical
cardinality. The point restriction and all geometric properties are retained. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem uniform_small_cover_pencils (N : ℕ) {s t K L : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (hunion : ((P.biUnion T).card:ℝ) ≤ L) :
    let J := Nat.log 2 (P.biUnion T).card+1
    ∃ k : ℕ, ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ (J:ℝ)*(R.card:ℝ) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) t (K*(J:ℝ)) R ∧
      1/(2*K*(1/(2:ℝ)^N)^s) ≤ (2:ℝ)^k ∧
      (2:ℝ)^k ≤ 2*L*(K*(J:ℝ))*(80*(1/(2:ℝ)^N))^s*
        (1+(K*(J:ℝ))*planarPotentialConstant s t) ∧
      ∀ x ∈ R, (2:ℝ)^k ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ 2*(2:ℝ)^k := by
  let J := Nat.log 2 (P.biUnion T).card+1
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have hδ1 : 1/(2:ℝ)^N ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ : (1:ℝ) ≤ J := by dsimp [J]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hKJ : 1 ≤ K*(J:ℝ) := hK.trans (le_mul_of_one_le_right hK0 hJ)
  obtain ⟨k,R,hRP,hR,hsize,hRball,hband⟩ := uniform_pencil_size_band hδ.le hK0 P T hP hPball
    (fun x hx => (hT x hx).1)
  have hTball (x : Space 2) (hx : x ∈ R) :
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s (K*(J:ℝ)) (T x) := by
    intro z r hr hr1
    have hr0 : 0 ≤ r := hδ.le.trans hr
    have hk : K ≤ K*(J:ℝ) := le_mul_of_one_le_right hK0 hJ
    exact ((hT x (hRP hx)).2.2.1 z r hr hr1).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))
  have hlarge := comparable_pencil_size_upper N hs hst hKJ (by positivity : 0 < (2:ℝ)^k) hL
    R T hR (fun x hx => hPchart x (hRP hx)) hRball (by
      intro x hx
      exact ⟨(hband x hx).1,(hband x hx).2,(hT x (hRP hx)).2.1,hTball x hx,(hT x (hRP hx)).2.2.2⟩)
    ((Nat.cast_le.mpr (Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left T hRP))).trans hunion)
  refine ⟨k,R,hRP,hR,hsize,hRball,?_,hlarge,hband⟩
  obtain ⟨x,hx⟩ := hR
  have hlow := finite_ball_bound_card_lower hδ hδ1 (hT x (hRP hx)).1 (hT x (hRP hx)).2.2.1
  have hh := mul_le_mul_of_nonneg_left (hband x hx).2 (show 0 ≤ K*(1/(2:ℝ)^N)^s by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2*K*(1/(2:ℝ)^N)^s)).2
  nlinarith only [hlow,hh]

end Falconer

end OAI
