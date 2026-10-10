import OAI.MeasureTheory.Falconer.Incidence.CoarsePacketPoints
import OAI.MeasureTheory.Falconer.Incidence.FrozenPacketRegularity

namespace OAI

/-! Retain the original fine pencils whose coarse labels survive a packet
selection. The point and pencil losses follow from the actual weighted
incidences, rather than being extra regularity assumptions. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem retain_coarse_incidences {δ s t K m M H B b : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (hH : 0 < H) (hB : 0 < B) (hb : 0 < b)
    (P D : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (q : Space 2 → Space 2)
    (hP : P.Nonempty) (hD : b ≤ (D.card:ℝ))
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p))
    (hw : ∀ a ∈ D, (∑ p ∈ P, ((T p).card:ℝ)) ≤
      H*B*(coarsePencilWeight P T q a:ℝ)) :
    let E := H*B/b
    let F := 2*E*M/m
    let V := fun p => (T p).filter fun l => q l ∈ D
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*F) R ∧
      ∀ p ∈ R, V p ⊆ T p ∧ m/(2*E) ≤ ((V p).card:ℝ) ∧
        ((V p).card:ℝ) ≤ M ∧ NormalizedFiniteBallBound δ s (K*F) (V p) := by
  let E := H*B/b
  let F := 2*E*M/m
  let V := fun p => (T p).filter fun l => q l ∈ D
  have hE : 0 < E := by dsimp [E]; positivity
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  let I := ∑ p ∈ P, ((T p).card:ℝ)
  have hIlow : m*(P.card:ℝ) ≤ I := by
    calc
      _ = ∑ _p ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun p hp => (hT p hp).1
  have hI0 : 0 ≤ I := (mul_pos hm hPc).le.trans hIlow
  have hsum : b*I ≤ (H*B)*∑ a ∈ D, (coarsePencilWeight P T q a:ℝ) := by
    calc
      _ ≤ (D.card:ℝ)*I := mul_le_mul_of_nonneg_right hD hI0
      _ = ∑ _a ∈ D, I := by simp
      _ ≤ ∑ a ∈ D, H*B*(coarsePencilWeight P T q a:ℝ) := Finset.sum_le_sum hw
      _ = _ := by rw [Finset.mul_sum]
  have hcounts : (∑ a ∈ D, (coarsePencilWeight P T q a:ℝ)) =
      ∑ p ∈ P, ((V p).card:ℝ) := by
    exact_mod_cast sum_coarsePencilWeight P D T q
  have hretain : (m/E)*(P.card:ℝ) ≤ ∑ p ∈ P, ((V p).card:ℝ) := by
    have hrel : I ≤ E*∑ p ∈ P, ((V p).card:ℝ) := by
      rw [hcounts] at hsum
      calc
        I ≤ ((H*B)*∑ p ∈ P, ((V p).card:ℝ))/b :=
          (le_div_iff₀ hb).2 (by simpa only [mul_comm I b] using hsum)
        _ = _ := by dsimp [E]; ring
    calc
      (m/E)*(P.card:ℝ) = (m*(P.card:ℝ))/E := by ring
      _ ≤ _ := (div_le_iff₀ hE).2 (by simpa only [mul_comm E] using hIlow.trans hrel)
  obtain ⟨R,hRP,hR,hRsize,hRV⟩ := finite_large_weight_subset P
    (fun p => ((V p).card:ℝ)) hP (mul_pos (div_pos hm hE) hPc) hM
    (fun p hp => (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hT p hp).2.1) hretain
  have hsize : (P.card:ℝ) ≤ F*(R.card:ℝ) := by
    have hh := (div_le_iff₀ (mul_pos (by norm_num) hM)).1 hRsize
    have hh' := mul_le_mul_of_nonneg_left hh hE.le
    have hc : m*(P.card:ℝ) ≤ (2*E*M)*(R.card:ℝ) := by
      convert hh' using 1 <;> field_simp
    calc
      (P.card:ℝ) = (m*(P.card:ℝ))/m := by field_simp
      _ ≤ ((2*E*M)*(R.card:ℝ))/m := div_le_div_of_nonneg_right hc hm.le
      _ = _ := by dsimp [F]; ring
  refine ⟨R,hRP,hR,hsize,normalized_finite_ball_bound_subset hδ hK hRP hsize hPball,?_⟩
  intro p hp
  have hlo : m/(2*E) ≤ ((V p).card:ℝ) := by
    have hh := hRV p hp
    convert hh using 1
    field_simp
  have hcard : ((T p).card:ℝ) ≤ F*((V p).card:ℝ) := by
    have hh := (div_le_iff₀ (mul_pos (by norm_num) hE)).1 hlo
    have hh' := mul_le_mul_of_nonneg_left hh hM.le
    apply (hT p (hRP hp)).2.1.trans
    have hc : m*M ≤ (2*E*M)*((V p).card:ℝ) := by
      convert hh' using 1 <;> ring
    calc
      M = (m*M)/m := by field_simp
      _ ≤ ((2*E*M)*((V p).card:ℝ))/m := div_le_div_of_nonneg_right hc hm.le
      _ = _ := by dsimp [F]; ring
  exact ⟨Finset.filter_subset _ _,hlo,
    (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hT p (hRP hp)).2.1,
    normalized_finite_ball_bound_subset hδ hK (Finset.filter_subset _ _) hcard
      (hT p (hRP hp)).2.2⟩

end Falconer

end OAI
