import OAI.GroupTheory.PolycyclicRecognition.Analysis.LipschitzPairReplacement
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricQuasiEquivalence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TransferredAction

namespace OAI

/-! # Constructed Lipschitz pairs for the transferred action -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem MetricQuasiEquivalence.exists_transferred_pair_representatives
    {J G : Type*} [Group J] [MetricSpace J] [IsIsometricSMul J J]
    [Group G] [MetricSpace G] [ProperSpace G] [IsIsometricSMul G G]
    (u : MetricQuasiEquivalence J G) (c : ControlledContraction G)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ s) ≤ dist 1 g * |t - s|) :
    ∃ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) ∧ ∃ E : ℝ, 0 ≤ E ∧
      ∃ rep : J → C(G, G) × C(G, G),
        (∀ h, LipschitzPairBounds G Λ (rep h)) ∧
        (∀ h x, dist ((rep h).1 x) (transferredMap u.toFun u.invFun h x) ≤ E) ∧
        (∀ h x, dist ((rep h).2 x) (transferredMap u.toFun u.invFun h⁻¹ x) ≤ E) := by
  obtain ⟨Kf, Cf, hKf, hCf, hf⟩ := u.toFun_control
  obtain ⟨Kr, Cr, hKr, hCr, hr⟩ := u.invFun_control
  obtain ⟨A, hA, ha⟩ := u.left_close
  obtain ⟨B, hB, hb⟩ := u.right_close
  let F := transferredMap u.toFun u.invFun
  have hu : ∀ h x y, dist (F h x) (F h y) ≤ (Kf * Kr) * dist x y + (Kf * Cr + Cf) :=
    transferredMap_coarse_upper u.toFun u.invFun (fun h x y => dist_mul_left h x y)
      Kf Cf Kr Cr hKf hf hr
  have hcomp : ∀ h k x, dist (F h (F k x)) (F (h * k) x) ≤ Kf * A + Cf := by
    intro h k x
    exact transferredMap_mul_close u.toFun u.invFun (fun h x y => dist_mul_left h x y)
      Kf Cf A hKf hf (fun j => by simpa only [dist_comm] using ha j) h k x
  have hidentity : ∀ x, dist (F 1 x) x ≤ B := by
    intro x
    exact transferredMap_one_close u.toFun u.invFun B (fun x => by simpa only [dist_comm] using hb x) x
  have hinv : ∀ h x, dist (F h⁻¹ (F h x)) x ≤ Kf * A + Cf + B := by
    intro h x
    have he := hcomp h⁻¹ h x
    rw [inv_mul_cancel] at he
    exact (dist_triangle _ (F 1 x) x).trans (add_le_add he (hidentity x))
  obtain ⟨Λ, hΛ, E, hE, hreplace⟩ := exists_lipschitz_pair_replacement_constants c hpath
    (A := Kf * A + Cf + B) (mul_nonneg hKf hKr) (add_nonneg (mul_nonneg hKf hCr) hCf)
  have hex (h : J) : ∃ p : C(G, G) × C(G, G), LipschitzPairBounds G Λ p ∧
      (∀ x, dist (p.1 x) (F h x) ≤ E) ∧ (∀ x, dist (p.2 x) (F h⁻¹ x) ≤ E) := by
    apply hreplace (F h) (F h⁻¹) (hu h) (hu h⁻¹) (hinv h)
    simpa only [inv_inv] using hinv h⁻¹
  choose rep hrep hforward hbackward using hex
  exact ⟨Λ, hΛ, E, hE, rep, hrep, hforward, hbackward⟩

end PolycyclicRecognition

end

end OAI
