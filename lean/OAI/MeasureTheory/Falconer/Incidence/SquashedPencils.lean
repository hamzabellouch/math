import OAI.MeasureTheory.Falconer.Geometry.SquashCover
import OAI.MeasureTheory.Falconer.Estimates.SeparatedThinning

namespace OAI

/-! Original bounded-chart pencils, thinned by a fixed factor and moved
to the slope chart required by the regular incidence estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def squashedPencils (V : Space 2 → Finset (Space 2)) (z : Space 2) :
    Finset (Space 2) := (V (planarUnsquash z)).image planarSquash

theorem squashedPencils_at (V : Space 2 → Finset (Space 2)) (p : Space 2) :
    squashedPencils V (planarSquash p) = (V p).image planarSquash := by
  rw [squashedPencils,planarSquash_leftInverse]

theorem squashedPencils_union (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    (P.image planarSquash).biUnion (squashedPencils V) = (P.biUnion V).image planarSquash := by
  ext l
  constructor
  · intro hl
    obtain ⟨z,hz,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [squashedPencils_at] at hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨p,hp,ha⟩)
  · intro hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
    refine Finset.mem_biUnion.mpr ⟨planarSquash p,Finset.mem_image_of_mem _ hp,?_⟩
    rw [squashedPencils_at]
    exact Finset.mem_image_of_mem _ ha

theorem squashedPencils_union_card (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    ((P.image planarSquash).biUnion (squashedPencils V)).card = (P.biUnion V).card := by
  rw [squashedPencils_union,Finset.card_image_of_injective _ planarSquash_injective]

theorem squashed_pencil_configuration {δ s t K m M : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hs2 : s ≤ 2) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) (hPchart : InBoundedLineChart P) (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hV : ∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ M ∧
      InBoundedLineChart (V p) ∧ FiniteSeparatedAt δ (V p) ∧
      NormalizedFiniteBallBound δ s K (V p) ∧ ∀ l ∈ V p, TubeIncident δ p l) :
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ 81*(R.card:ℝ) ∧
      let Q := R.image planarSquash
      InBoundedLineChart Q ∧ FiniteSeparatedAt (δ/4) Q ∧
      NormalizedFiniteBallBound (δ/4) t (20736*K) Q ∧
      ∃ W : Space 2 → Finset (Space 2),
        (∀ p ∈ R, W p ⊆ V p) ∧
        (∀ q ∈ Q, m/81 ≤ ((squashedPencils W q).card:ℝ) ∧
          ((squashedPencils W q).card:ℝ) ≤ M ∧
          InBoundedLineChart (squashedPencils W q) ∧
          FiniteSeparatedAt (δ/4) (squashedPencils W q) ∧
          NormalizedFiniteBallBound (δ/4) s (20736*K) (squashedPencils W q) ∧
          ∀ l ∈ squashedPencils W q, |l 0| ≤ 1/2 ∧ TubeIncident (δ/4) q l) ∧
        (((Q.biUnion (squashedPencils W)).card:ℝ) ≤ ((P.biUnion V).card:ℝ)) := by
  obtain ⟨R,hRP,hR,hRsep,hRcard⟩ := quadruple_separated_subset hδ P hP hPsep
  have hselect : ∀ p, ∃ S : Finset (Space 2), p ∈ R →
      S ⊆ V p ∧ S.Nonempty ∧ FiniteSeparatedAt (4*δ) S ∧ ((V p).card:ℝ) ≤ 81*(S.card:ℝ) := by
    intro p
    by_cases hp : p ∈ R
    · have hv := hV p (hRP hp)
      have hn : (V p).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le hv.1))
      obtain ⟨S,hS⟩ := quadruple_separated_subset hδ (V p) hn hv.2.2.2.1
      exact ⟨S,fun _ => hS⟩
    · exact ⟨∅,fun h => False.elim (hp h)⟩
  choose W hW using hselect
  have h81 : 1 ≤ K*81 := by linarith only [hK]
  have hpow (u : ℝ) (hu : u ≤ 2) : (K*81)*(16:ℝ)^u ≤ 20736*K := by
    have hh : (16:ℝ)^u ≤ 256 := by
      calc
        _ ≤ (16:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hu
        _ = 256 := by norm_num
    nlinarith only [mul_le_mul_of_nonneg_left hh (by linarith only [hK] : 0 ≤ K*81)]
  have mono {u A B : ℝ} {S : Finset (Space 2)} (hAB : A ≤ B)
      (hball : NormalizedFiniteBallBound (δ/4) u A S) :
      NormalizedFiniteBallBound (δ/4) u B S := by
    intro z r hr hr1
    exact (hball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (by linarith only [hr,hδ]) _))
        (Nat.cast_nonneg _))
  refine ⟨R,hRP,hR,hRcard,planarSquash_chart R (fun p hp => hPchart p (hRP hp)),
    planarSquash_separated R hRsep,?_,W,(fun p hp => (hW p hp).1),?_,?_⟩
  · exact mono (hpow t ht2) (planarSquash_regular hδ ht h81 R
      (normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK) hRP hRcard hPball))
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [squashedPencils_at,Finset.card_image_of_injective _ planarSquash_injective]
    obtain ⟨hWV,hWne,hWsep,hWcard⟩ := hW p hp
    have hv := hV p (hRP hp)
    refine ⟨?_,?_,planarSquash_chart (W p) (fun l hl => hv.2.2.1 l (hWV hl)),
      planarSquash_separated (W p) hWsep,?_,?_⟩
    · exact (div_le_iff₀ (by norm_num : (0:ℝ) < 81)).2 (by linarith only [hv.1,hWcard])
    · exact (Nat.cast_le.mpr (Finset.card_le_card hWV)).trans hv.2.1
    · exact mono (hpow s hs2) (planarSquash_regular hδ hs h81 (W p)
        (normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK) hWV hWcard hv.2.2.2.2.1))
    · intro l hl
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨planarSquash_slope (hv.2.2.1 a (hWV ha)).1,
        planarSquash_incident hδ.le (hv.2.2.2.2.2 a (hWV ha))⟩
  · rw [squashedPencils_union_card]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨p,hRP hp,(hW p hp).1 hl⟩

end Falconer

end OAI
