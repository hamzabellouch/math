import OAI.MeasureTheory.Falconer.Estimates.LocalCellLines

namespace OAI

/-! The fine union inside a regular coarse cell retains the original pencil
size in the elementary incidence bound. This is the local factor needed
in the scale-combination argument. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem local_cell_variable_incidence (N : ℕ) {s t K m M y a : ℝ}
    (hN : 3 ≤ N) (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hy : |y| ≤ 1) (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ (1/(2:ℝ)^N)/4 ∧ |p 1-a| ≤ (1/(2:ℝ)^N)/4)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K
      (P.image (localPacketPoint (1/(2:ℝ)^N) y a)))
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^N)^2) s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^N)^2) p l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      (((K*3^s)*(80*(1/(2:ℝ)^N))^s*M)*(1+(K*3^s)*planarPotentialConstant s t)) := by
  let Δ := 1/(2:ℝ)^N
  let F := localPacketPoint Δ y a
  let L := localCellLine Δ y a
  let R := P.image F
  let V := fun q => (T (Δ • q+rowPoint y a)).image L
  let C := K*3^s
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔsmall : Δ ≤ 1/8 := by
    change 1/(2:ℝ)^N ≤ 1/8
    have hp : (2:ℝ)^3 ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hN
    norm_num at hp
    exact (div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by norm_num)).2 hp
  have hΔ1 : Δ ≤ 1 := hΔsmall.trans (by norm_num)
  have hinv (p : Space 2) : Δ • F p+rowPoint y a = p := by
    apply localPacketPoint_injective hΔ y a
    exact localPacketPoint_inverse hΔ y a (F p)
  have hV (p : Space 2) : V (F p) = (T p).image L := by
    change (T (Δ • F p+rowPoint y a)).image L = _
    rw [hinv]
  have hC : 1 ≤ C := by
    have hh : 1 ≤ (3:ℝ)^s := Real.one_le_rpow (by norm_num) hs
    dsimp [C]
    nlinarith only [hh,hK]
  have hKC : K ≤ C := by
    dsimp [C]
    exact le_mul_of_one_le_right (zero_le_one.trans hK) (Real.one_le_rpow (by norm_num) hs)
  have hRb : NormalizedFiniteBallBound Δ t C R := by
    intro z r hr hr1
    exact (hPball z r hr hr1).trans (by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (hΔ.le.trans hr) _))
  have hRchart : InBoundedLineChart R := localPacketPoint_chart hΔ P (fun p hp =>
    ⟨(hcell p hp).1.trans (by linarith only [hΔ]),
      (hcell p hp).2.trans (by linarith only [hΔ])⟩)
  have hdata (q : Space 2) (hq : q ∈ R) :
      m ≤ ((V q).card:ℝ) ∧ ((V q).card:ℝ) ≤ M ∧ InBoundedLineChart (V q) ∧
      NormalizedFiniteBallBound Δ s C (V q) ∧ ∀ l ∈ V q, TubeIncident Δ q l := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [hV]
    have hcard : ((T p).image L).card = (T p).card :=
      Finset.card_image_of_injective _ (localCellLine_injective hΔ y a)
    refine ⟨by simpa only [hcard] using (hT p hp).1,
      by simpa only [hcard] using (hT p hp).2.1,?_,?_,?_⟩
    · intro l hl
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
      exact localCellLine_chart hΔ hΔsmall p b (hcell p hp).1 (hcell p hp).2
        ((hT p hp).2.2.2 b hb).1 ((hT p hp).2.2.2 b hb).2
    · exact localCellLine_regular hΔ hΔ1 hy (by nlinarith only [hΔ1,hΔ]) hs hK
        (T p) (hT p hp).2.2.1
    · intro l hl
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
      have hi := localCellLine_incident hΔ y a p b ((hT p hp).2.2.2 b hb).2
      change TubeIncident (Δ^2/Δ) (F p) (L b) at hi
      simpa only [sq, mul_div_cancel_right₀ _ hΔ.ne'] using hi
  have hU : R.biUnion V ⊆ (P.biUnion T).image L := by
    intro l hl
    obtain ⟨q,hq,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [hV] at hl
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨p,hp,hb⟩)
  have hcount : ((R.biUnion V).card:ℝ) ≤ ((P.biUnion T).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hU).trans Finset.card_image_le
  have hconst : 0 ≤ (C*(80*Δ)^s*M)*(1+C*planarPotentialConstant s t) := by
    obtain ⟨p,hp⟩ := hP
    have hM : 0 ≤ M := (Nat.cast_nonneg _).trans (hT p hp).2.1
    have hpot := planarPotentialConstant_pos hst
    have hc0 := zero_le_one.trans hC
    positivity
  exact (planar_variable_baseline_incidence N hs hst hC hm R V (hP.image F)
    hRchart hRb hdata).trans (mul_le_mul_of_nonneg_right hcount hconst)

end Falconer

end OAI
