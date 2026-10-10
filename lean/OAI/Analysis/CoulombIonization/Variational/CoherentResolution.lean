import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoherentPackets

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

namespace CoulombAtom

lemma coherentOverlap_continuous {g u : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g)
    (hu : Continuous u) (hcu : HasCompactSupport u) :
    Continuous (fun q : Space × Space => coherentOverlap g u q.1 q.2) := by
  obtain ⟨C,hC⟩ := hg.norm.exists_forall_ge_of_hasCompactSupport hcg.norm
  apply continuous_of_dominated (bound := fun x => ‖g C‖ * ‖u x‖)
  · intro q
    unfold coherentPacket
    fun_prop
  · intro q
    filter_upwards [] with x
    rw [norm_mul,Complex.norm_conj,coherentPacket_norm]
    exact mul_le_mul_of_nonneg_right (hC (x-q.1)) (norm_nonneg _)
  · exact (hu.norm.integrable_of_hasCompactSupport hcu.norm).const_mul ‖g C‖
  · filter_upwards [] with x
    unfold coherentPacket
    fun_prop

lemma coherentOverlap_momentum_integrable {g u : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) (z : Space) :
    Integrable (fun p : Space => ‖coherentOverlap g u z p‖^2) := by
  rw [← integrable_comp_smul_iff volume (fun p : Space => ‖coherentOverlap g u z p‖^2)
    (show 2*Real.pi ≠ 0 by positivity)]
  simp_rw [coherentOverlap_fourier]
  have hc : HasCompactSupport (fun x : Space => conj (g (x-z))*u x) := hcu.mul_left
  have hd : ContDiff ℝ ∞ (fun x : Space => conj (g (x-z))*u x) :=
    (Complex.conjCLE.contDiff.comp (hg.comp (contDiff_id.sub contDiff_const))).mul hu
  have hi := ((𝓕 (hc.toSchwartzMap hd)).memLp 2 volume).norm.integrable_sq
  change Integrable (fun x : Space => ‖𝓕 (fun x : Space => conj (g (x-z))*u x) x‖^2) at hi
  exact hi

lemma coherent_position_integrable {g u : Space → ℂ}
    (hg : Continuous g) (hcg : HasCompactSupport g)
    (hu : Continuous u) (hcu : HasCompactSupport u) :
    Integrable (fun q : Space × Space => ‖g (q.2-q.1)‖^2 * ‖u q.2‖^2) := by
  have hgs : Integrable (fun z : Space => ‖g z‖^2) :=
    (hg.memLp_of_hasCompactSupport hcg (p := 2)).norm.integrable_sq
  have hus : Integrable (fun z : Space => ‖u z‖^2) :=
    (hu.memLp_of_hasCompactSupport hcu (p := 2)).norm.integrable_sq
  apply (integrable_prod_iff' (by fun_prop)).mpr
  constructor
  · filter_upwards [] with x
    exact (hgs.comp_sub_left x).mul_const _
  · have he (x : Space) :
        (∫ z : Space, ‖‖g (x-z)‖^2 * ‖u x‖^2‖) = (∫ z : Space, ‖g z‖^2) * ‖u x‖^2 := by
      simp_rw [norm_mul,norm_pow,Real.norm_of_nonneg (norm_nonneg _)]
      rw [integral_mul_const,integral_sub_left_eq_self (fun t : Space => ‖g t‖^2) volume x]
    change Integrable (fun x : Space => ∫ z : Space, ‖‖g (x-z)‖^2 * ‖u x‖^2‖)
    simp_rw [he]
    exact hus.const_mul _

lemma coherentOverlap_resolution {g u : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) :
    ((2*Real.pi)^3)⁻¹ * (∫ z : Space, ∫ p : Space, ‖coherentOverlap g u z p‖^2) =
      (∫ z : Space, ‖g z‖^2) * (∫ x : Space, ‖u x‖^2) := by
  rw [← integral_const_mul]
  simp_rw [coherentOverlap_momentum hg hu hcu]
  rw [integral_integral_swap (coherent_position_integrable hg.continuous hcg hu.continuous hcu)]
  simp_rw [integral_mul_const,integral_sub_left_eq_self (fun t : Space => ‖g t‖^2) volume]
  rw [integral_const_mul]

lemma coherentOverlap_integrable {g u : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) :
    Integrable (fun q : Space × Space => ‖coherentOverlap g u q.1 q.2‖^2) := by
  apply (integrable_prod_iff ((coherentOverlap_continuous hg.continuous hcg hu.continuous hcu).norm.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (coherentOverlap_momentum_integrable hg hu hcu)
  · have he (z : Space) : (∫ p : Space, ‖‖coherentOverlap g u z p‖^2‖) =
        (2*Real.pi)^3 * (∫ x : Space, ‖g (x-z)‖^2 * ‖u x‖^2) := by
      simp_rw [norm_pow,Real.norm_of_nonneg (norm_nonneg _)]
      have h := coherentOverlap_momentum hg hu hcu z
      have hn : (2*Real.pi)^3 ≠ 0 := by positivity
      calc
        _ = (2*Real.pi)^3 * (((2*Real.pi)^3)⁻¹ * _) := by field_simp
        _ = _ := by rw [h]
    change Integrable (fun z : Space => ∫ p : Space, ‖‖coherentOverlap g u z p‖^2‖)
    simp_rw [he]
    exact (coherent_position_integrable hg.continuous hcg hu.continuous hcu).integral_prod_left.const_mul _

end CoulombAtom

end

end OAI
