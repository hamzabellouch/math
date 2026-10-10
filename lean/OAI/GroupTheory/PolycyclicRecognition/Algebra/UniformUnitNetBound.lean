import OAI.GroupTheory.PolycyclicRecognition.Analysis.UnitSeparatedNet
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Set.Card

namespace OAI

/-! # Uniform multiplicity of the unit-net cover

A finite cover of a compact ball at the identity bounds the number of
separated centers at every translate. This proves the multiplicity estimate
without needing a Haar-volume comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsIsometricSMul G G]

theorem exists_uniform_unit_net_card (R : ℝ) :
    ∃ M : ℕ, ∀ V : Set G, V.Pairwise (fun x y => 1 < dist x y) →
      ∀ x : G, (V ∩ closedBall x R).ncard ≤ M := by
  classical
  obtain ⟨C, hC, hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_closedBall (1 : G) R).totallyBounded (1 / 3 : ℝ) (by norm_num)
  refine ⟨C.ncard, ?_⟩
  intro V hV x
  let U := V ∩ closedBall x R
  have hc (v : U) : ∃ c : C, dist (x⁻¹ * (v : G)) c < 1 / 3 := by
    have hv : x⁻¹ * (v : G) ∈ closedBall (1 : G) R := by
      change dist (x⁻¹ * (v : G)) 1 ≤ R
      calc
        _ = dist (v : G) x := by
          simpa only [inv_mul_cancel] using dist_mul_left x⁻¹ (v : G) x
        _ ≤ R := v.property.2
    rcases mem_iUnion.mp (hcover hv) with ⟨c, hc⟩
    rcases mem_iUnion.mp hc with ⟨hc, hv⟩
    exact ⟨⟨c, hc⟩, mem_ball.mp hv⟩
  choose c hc using hc
  have hinj : Function.Injective c := by
    intro v w he
    apply Subtype.ext
    by_contra hne
    have hsep := hV v.property.1 w.property.1 hne
    have ht := dist_triangle (x⁻¹ * (v : G)) (c v : G) (x⁻¹ * (w : G))
    have hv := hc v
    have hw := hc w
    rw [← he] at hw
    rw [dist_comm (c v : G) (x⁻¹ * (w : G)), dist_mul_left] at ht
    linarith
  let : Finite C := hC.to_subtype
  have hcard := Nat.card_le_card_of_injective c hinj
  simpa only [Nat.card_coe_set_eq] using hcard

end PolycyclicRecognition

end

end OAI
