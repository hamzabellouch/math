import Mathlib
import OAI.Probability.Ballisticity.Estimates.OutwardCanonical

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma wordCylinder_signed_up_disjoint_stay {d : ℕ} (e : Direction d)
    (x y : Lattice d) (H : ℕ) :
    Disjoint (wordCylinder y (List.replicate H e))
      (StayUntil (Strip (realPosition (step e)) x H) H) := by
  apply Set.disjoint_left.mpr
  intro X hw hS
  have hb := (hS 0 (Nat.zero_le H)).1
  have ht := (hS H le_rfl).2
  have hzero := hw 0 (by simp)
  have hend := hw H (by simp)
  rw [wordPath_replicate] at hend
  rw [hzero,wordPath_zero] at hb
  rw [hend,dot_realPosition_add,dot_realPosition_nsmul,dot_signed_direction e (step e),signedCoordinate_step_self,mul_one] at ht
  linarith

lemma quenched_signed_strip_block {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x y : Lattice d) (H : ℕ) :
    quenchedKernel (ω,y) (StayUntil (Strip (realPosition (step e)) x H) H) ≤
      1-(κ:ℝ≥0∞)^H := by
  have hsub := (wordCylinder_signed_up_disjoint_stay e x y H).subset_compl_left
  calc
    _ ≤ quenchedKernel (ω,y) (wordCylinder y (List.replicate H e))ᶜ := measure_mono hsub
    _ = 1-ENNReal.ofReal (wordWeight ω y (List.replicate H e)) := by
      rw [measure_compl (measurableSet_wordCylinder _ _) (measure_ne_top _ _),measure_univ,quenched_wordCylinder]
    _ ≤ 1-(κ:ℝ≥0∞)^H := by
      apply tsub_le_tsub_left
      have hs := ENNReal.ofReal_le_ofReal (wordWeight_lower ω hκ y (List.replicate H e))
      simpa only [List.length_replicate,ENNReal.ofReal_pow κ.coe_nonneg,ENNReal.ofReal_coe_nnreal] using hs

lemma quenched_signed_strip_geometric {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x y : Lattice d) (H k : ℕ) :
    quenchedKernel (ω,y) (StayUntil (Strip (realPosition (step e)) x H) (k*H)) ≤
      (1-(κ:ℝ≥0∞)^H)^k :=
  quenched_stayUntil_block_bound ω _ H _ (fun y => quenched_signed_strip_block ω hκ e x y H) y k

lemma truncatedEndpointLaw_mass_error {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (k : ℕ) :
    hitKernel (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) (ω,x) Set.univ ≤
      truncatedEndpointLaw e H (k*H) ω x Set.univ+(1-(κ:ℝ≥0∞)^H)^k := by
  rw [truncatedEndpointLaw_apply e hH,Set.inter_univ,hitKernel_total (disjoint_strip_upper _ _ _)]
  exact (quenched_hit_truncation ω x _ _ _).trans
    (add_le_add le_rfl (quenched_signed_strip_geometric ω hκ e x x H k))
end DirectionalTransience

end

end

end OAI
