import OAI.Analysis.LipschitzHilbert.Phase.SourceLabeledAngularErrorData
import OAI.Analysis.LipschitzHilbert.Estimates.CoefficientDecomposition

namespace OAI

/-! The original labeled physical coefficient splits into its centered
frozen selector and angular error, without changing synthesis packets. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physical_multiplier_analyzing_integrable (t : ℝ) (m : ℝ×ℝ → ℂ)
    (hm : Measurable m) (hm1 : ∀ z, ‖m z‖ ≤ 1)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) :
    Integrable (fun z => g z k*conj (m z*P.physicalPacket t j l u k z))
      (volume.prod volume) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.physicalPacket t j l u k).integrable.norm.mono'
    (hgm.mul (continuous_star.measurable.comp
      (hm.mul (P.physicalPacket t j l u k).continuous.measurable))).aestronglyMeasurable
  filter_upwards [] with z
  change ‖g z k*conj (m z*P.physicalPacket t j l u k z)‖ ≤ ‖P.physicalPacket t j l u k z‖
  rw [norm_mul,Complex.norm_conj,norm_mul]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  calc
    _ ≤ 1*(1*‖P.physicalPacket t j l u k z‖) := mul_le_mul hgk
      (mul_le_mul_of_nonneg_right (hm1 z) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

def physicalMultiplierCoefficient (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun u k z => b j l k (v z)*P.physicalPacket t j l u k z) g u

def physicalFrozenCenteredCoefficient (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (u : Item j l) : EuclideanSpace ℂ κ :=
  analyzingCoefficient (volume.prod volume) (fun _ : Item j l => P.length j*P.width)
    (fun u k z => if |v z-t| ≤ a*(2:ℝ)^j.val then
      b j l k t*P.physicalPacket t j l u k z else 0) g u

theorem physicalMultiplierCoefficient_split (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (hb : ∀ j l k, Measurable (b j l k))
    (hb1 : ∀ j l k s, ‖b j l k s‖ ≤ 1)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (l : P.labels j) (u : Item j l) :
    P.physicalMultiplierCoefficient t b v g j l u =
      P.physicalFrozenCenteredCoefficient t a b v g j l u+
        P.physicalAngularErrorCoefficient t a b v g j l u := by
  apply angularCoefficient_decomposition (fun _ : Item j l => P.length j*P.width)
    (fun _ k => b j l k) (fun u k => P.physicalPacket t j l u k) v t (a*(2:ℝ)^j.val) g
  · intro u k
    exact P.physical_multiplier_analyzing_integrable t (fun z => b j l k (v z))
      ((hb j l k).comp hv) (fun z => hb1 j l k (v z)) g hg hg1 j l u k
  · intro u k
    have hdist : Measurable (fun z => |v z-t|) := by
      simpa only [Real.norm_eq_abs] using (hv.sub_const t).norm
    have hm : Measurable (fun z : ℝ×ℝ =>
        if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0) :=
      Measurable.ite (measurableSet_le hdist measurable_const)
        measurable_const measurable_const
    have hm1 (z : ℝ×ℝ) :
        ‖if |v z-t| ≤ a*(2:ℝ)^j.val then b j l k t else 0‖ ≤ 1 := by
      split_ifs
      · exact hb1 j l k t
      · simp only [norm_zero,zero_le_one]
    have h := P.physical_multiplier_analyzing_integrable t _ hm hm1 g hg hg1 j l u k
    simpa only [Measure.volume_eq_prod,ite_mul,zero_mul] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
