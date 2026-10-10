import OAI.MeasureTheory.Falconer.Incidence.SquashedPencils
import OAI.MeasureTheory.Falconer.Estimates.ScaleThinning
import OAI.MeasureTheory.Falconer.Geometry.ProjectionCube

namespace OAI

/-! Prepare original bounded-chart pencils at the chosen terminal grid scale.
All losses are fixed packing factors in the scale ratio. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem planarSquash_in_centeredUnitCube {p : Space 2} (hp : |p 0| ≤ 1 ∧ |p 1| ≤ 1) :
    planarSquash p ∈ (centeredUnitCube 2).carrier := by
  intro i
  change -(1/2:ℝ) ≤ planarSquash p i ∧ planarSquash p i < -(1/2:ℝ)+1
  fin_cases i
  · change -(1/2:ℝ) ≤ p 0/4 ∧ p 0/4 < -(1/2:ℝ)+1
    rcases abs_le.mp hp.1 with ⟨hl,hu⟩
    constructor <;> linarith
  · change -(1/2:ℝ) ≤ p 1/16 ∧ p 1/16 < -(1/2:ℝ)+1
    rcases abs_le.mp hp.2 with ⟨hl,hu⟩
    constructor <;> linarith

theorem coarse_squashed_pencil_configuration {δ ρ s t K a b : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hs : 0 ≤ s) (hs2 : s ≤ 2) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hK : 1 ≤ K) (ha : 0 < a)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) (hPchart : InBoundedLineChart P) (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hV : ∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
      InBoundedLineChart (V x) ∧ FiniteSeparatedAt δ (V x) ∧
      NormalizedFiniteBallBound δ s K (V x) ∧ ∀ l ∈ V x, TubeIncident δ x l) :
    let F := (16*ρ/δ+1)^2;
    ∃ R : Finset (Space 2), R.Nonempty ∧ (∀ x ∈ R, x ∈ (centeredUnitCube 2).carrier) ∧
      FiniteSeparatedAt (2*ρ) R ∧ NormalizedFiniteBallBound (δ/4) t (20736*K*F) R ∧
    ∃ U : Space 2 → Finset (Space 2),
      (∀ x ∈ R, a/(81*F) ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ b ∧
        InBoundedLineChart (U x) ∧ FiniteSeparatedAt ρ (U x) ∧
        NormalizedFiniteBallBound (δ/4) s (20736*K*F) (U x) ∧
        ∀ l ∈ U x, |l 0| ≤ 1/2 ∧ TubeIncident (δ/4) x l) ∧
      ((R.biUnion U).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := by
  obtain ⟨P0,hP0P,hP0,_,hchart,hsep,hball,V0,_,hV0,hunion⟩ :=
    squashed_pencil_configuration hδ hs hs2 ht ht2 hK ha P V hP hPchart hPsep hPball hV
  let Q := P0.image planarSquash
  let T := squashedPencils V0
  let F := (16*ρ/δ+1)^2
  let E := (2*ρ/(δ/4)+1)^2
  have hδ4 : 0 < δ/4 := by positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hK0 : 1 ≤ 20736*K := by linarith
  obtain ⟨R,hRQ,hR,hRsep,hRcard⟩ := planar_separated_subset_at hδ4
    (show 0 ≤ 2*ρ by positivity) Q (hP0.image planarSquash) hsep
  have hFformula : (2*(2*ρ)/(δ/4)+1)^2 = F := by dsimp [F]; field_simp; ring
  rw [hFformula] at hRcard
  have hEF : E ≤ F := by
    change (2*ρ/(δ/4)+1)^2 ≤ (16*ρ/δ+1)^2
    apply pow_le_pow_left₀ (by positivity)
    have he : 2*ρ/(δ/4) = 8*ρ/δ := by field_simp; ring
    rw [he]
    have hh : 8*ρ/δ ≤ 16*ρ/δ := div_le_div_of_nonneg_right (by linarith) hδ.le
    linarith
  have hdata : ∀ x ∈ R, a/81 ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ b ∧
      FiniteSeparatedAt (δ/4) (T x) ∧ NormalizedFiniteBallBound (δ/4) s (20736*K) (T x) := by
    intro x hx
    have hh := hV0 x (hRQ hx)
    exact ⟨hh.1,hh.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩
  obtain ⟨U,hU⟩ := thin_pencils_to_scale hδ4 hρ hK0 (show 0 < a/81 by positivity) R T hdata
  refine ⟨R,hR,?_,hRsep,?_,U,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hRQ hx)
    exact planarSquash_in_centeredUnitCube (hPchart p (hP0P hp))
  · exact normalized_finite_ball_bound_subset hδ4.le (by linarith) hRQ hRcard hball
  · intro x hx
    obtain ⟨hUT,hlo,hhi,hsep',hball'⟩ := hU x hx
    have hh := hV0 x (hRQ hx)
    refine ⟨?_,hhi,(fun l hl => hh.2.2.1 l (hUT hl)),hsep',?_,
      (fun l hl => hh.2.2.2.2.2 l (hUT hl))⟩
    · calc
        a/(81*F) ≤ a/(81*E) := div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
        _ = (a/81)/E := by rw [div_mul_eq_div_div]
        _ ≤ ((U x).card:ℝ) := hlo
    · intro z r hr hr1
      have hb := hball' z r hr hr1
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEF (by linarith))
          (Real.rpow_nonneg (hδ4.le.trans hr) _)) (Nat.cast_nonneg _))
  · apply le_trans _ hunion
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hRQ hx,(hU x hx).1 hl⟩

end Falconer

end OAI
