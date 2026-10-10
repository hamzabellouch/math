import OAI.MeasureTheory.Falconer.Estimates.TubeUniformization
import OAI.MeasureTheory.Falconer.Estimates.Packing
import OAI.MeasureTheory.Falconer.Geometry.TwoPointTubeGeometry

namespace OAI

/-! Equalize the original pencils before the fixed geometric preparation.
Only a logarithmic fraction of the original point set is lost. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem original_pencil_equalization {δ s t K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 1 ≤ K) (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) (hPchart : InBoundedLineChart P) (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hV : ∀ x ∈ P, (V x).Nonempty ∧ InBoundedLineChart (V x) ∧
      FiniteSeparatedAt δ (V x) ∧ NormalizedFiniteBallBound δ s K (V x) ∧
      ∀ l ∈ V x, TubeIncident δ x l) :
    let M := Nat.ceil ((4/δ+1)^2)
    let J : ℝ := (Nat.log 2 M+1:ℕ)
    ∃ k : ℕ, ∃ R : Finset (Space 2), ∃ U : Space 2 → Finset (Space 2),
      R.Nonempty ∧ R ⊆ P ∧ InBoundedLineChart R ∧ FiniteSeparatedAt δ R ∧
      NormalizedFiniteBallBound δ t (K*J) R ∧
      1 ≤ 2*K*δ^s*(2:ℝ)^k ∧
      (∀ x ∈ R, (U x).card = 2^k ∧ InBoundedLineChart (U x) ∧
        FiniteSeparatedAt δ (U x) ∧ NormalizedFiniteBallBound δ s (2*K) (U x) ∧
        ∀ l ∈ U x, TubeIncident δ x l) ∧
      ((R.biUnion U).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := by
  dsimp only
  let M := Nat.ceil ((4/δ+1)^2)
  let J : ℝ := (Nat.log 2 M+1:ℕ)
  have hmax (x : Space 2) (hx : x ∈ P) : (V x).card ≤ M := by
    have hbound : ∀ l ∈ V x, dist l 0 ≤ 2 := by
      intro l hl
      have hb := (hV x hx).2.1 l hl
      have hd := planar_dist_le_coordinate_sum l 0
      simp only [PiLp.zero_apply,sub_zero] at hd
      linarith only [hd,hb.1,hb.2]
    have hh := separated_ball_card (V x) 0 hδ (by norm_num : (0:ℝ) ≤ 2)
      ((hV x hx).2.2.1) hbound
    norm_num only [show (2:ℝ)*2 = 4 by norm_num] at hh
    exact Nat.cast_le.mp (hh.trans (Nat.le_ceil _))
  obtain ⟨k,R,U,hR,hRP,hsize,hU⟩ := exists_equal_size_tube_pencils P V hP
    (fun x hx => (hV x hx).1) hmax
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hUsize (x : Space 2) (hx : x ∈ R) : ((V x).card:ℝ) ≤ 2*((U x).card:ℝ) := by
    exact_mod_cast (hU x hx).2.2
  have hnumber : 1 ≤ 2*K*δ^s*(2:ℝ)^k := by
    obtain ⟨x,hx⟩ := hR
    have hh := finite_ball_bound_card_lower hδ hδ1 (hV x (hRP hx)).1
      (hV x (hRP hx)).2.2.2.1
    have hcard : ((U x).card:ℝ) = (2:ℝ)^k := by exact_mod_cast (hU x hx).2.1
    have hc := mul_le_mul_of_nonneg_left (hUsize x hx) (mul_nonneg hK0 (Real.rpow_nonneg hδ.le s))
    rw [hcard] at hc
    nlinarith only [hh,hc]
  refine ⟨k,R,U,hR,hRP,(fun x hx => hPchart x (hRP hx)),finiteSeparatedAt_subset hRP hPsep,
    normalized_finite_ball_bound_subset hδ.le hK0 hRP hsize hPball,hnumber,?_,?_⟩
  · intro x hx
    have hu := hU x hx
    have hv := hV x (hRP hx)
    refine ⟨hu.2.1,(fun l hl => hv.2.1 l (hu.1 hl)),finiteSeparatedAt_subset hu.1 hv.2.2.1,?_,
      (fun l hl => hv.2.2.2.2 l (hu.1 hl))⟩
    have hb := normalized_finite_ball_bound_subset hδ.le hK0 hu.1 (hUsize x hx) hv.2.2.2.1
    simpa only [mul_comm K 2] using hb
  · apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hRP hx,(hU x hx).1 hl⟩

end Falconer

end OAI
