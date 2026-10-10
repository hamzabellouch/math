import OAI.Geometry.NodalSets.Elliptic.CompactWeightedWeakEquation

namespace OAI

namespace Yau
open MeasureTheory
open scoped ContDiff
noncomputable section
variable {n : ℕ}

lemma real_pairing_compact (u : Coord n → ℝ) (V : Coord n → Coord n)
    (hc : HasCompactSupport u) : HasCompactSupport (pairing u V) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦
    (hc.fderiv_apply ℝ (Pi.single i 1)).mul_right (f' := fun x ↦ V x i))
  convert h using 1; first | rfl | (ext x; simp [pairing,coordPartial])

lemma real_pairing_mul (u v : Coord n → ℝ) (V : Coord n → Coord n)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : Coord n) :
    pairing (fun y ↦ u y*v y) V x =
      v x*pairing u V x + u x*pairing v V x := by
  simp only [pairing,real_coordPartial_mul _ _ hu hv,add_mul,
    Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

def weightedSkewTransport (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (w : Coord n → ℝ) (x : Coord n) : ℝ :=
  2*pairing w V x + weightedDiv gamma V x*w x

lemma weightedSkewTransport_smooth (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (w : Coord n → ℝ) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (weightedSkewTransport gamma V w) :=
  (contDiff_const.mul (pairing_smooth hw hV)).add ((weightedDiv_smooth hg hgn hV).mul hw)

lemma weightedSkewTransport_compact (gamma : Coord n → ℝ) (V : Coord n → Coord n)
    (w : Coord n → ℝ) (hc : HasCompactSupport w) :
    HasCompactSupport (weightedSkewTransport gamma V w) :=
  ((real_pairing_compact w V hc).mul_left).add hc.mul_left

lemma compact_weighted_product_integrable (gamma u v : Coord n → ℝ)
    (hg : Continuous gamma) (hu : Continuous u) (hv : Continuous v)
    (hc : HasCompactSupport u) : Integrable (fun x ↦ gamma x*u x*v x) :=
  ((hg.mul hu).mul hv).integrable_of_hasCompactSupport hc.mul_left.mul_right

theorem weighted_transport_green (gamma u v : Coord n → ℝ)
    (V : Coord n → Coord n) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport u)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    (∫ x, gamma x*u x*weightedSkewTransport gamma V v x) =
      -(∫ x, gamma x*weightedSkewTransport gamma V u x*v x) := by
  have hD := weightedDiv_smooth hg hgn hV
  have hpu := pairing_smooth hu hV
  have hpv := pairing_smooth hv hV
  have hi1 := compact_weighted_product_integrable gamma u (pairing v V)
    hg.continuous hu.continuous hpv.continuous hc
  have hi2 := compact_weighted_product_integrable gamma (pairing u V) v
    hg.continuous hpu.continuous hv.continuous (real_pairing_compact u V hc)
  have hi3 := compact_weighted_product_integrable gamma u (fun x ↦ v x*weightedDiv gamma V x)
    hg.continuous hu.continuous (hv.mul hD).continuous hc
  have he := (compact_weighted_integration_by_parts gamma (fun x ↦ u x*v x)
    hg hgn (hu.mul hv) hc.mul_right V hV).2.2
  have hpoint : (fun x ↦ gamma x*pairing (fun y ↦ u y*v y) V x) =
      (fun x ↦ gamma x*pairing u V x*v x + gamma x*u x*pairing v V x) := by
    funext x
    rw [real_pairing_mul u v V hu hv]
    ring
  rw [hpoint,integral_add hi2 hi1] at he
  have hpoint1 : (fun x ↦ gamma x*u x*weightedSkewTransport gamma V v x) =
      (fun x ↦ 2*(gamma x*u x*pairing v V x) + gamma x*u x*(v x*weightedDiv gamma V x)) := by
    funext x; unfold weightedSkewTransport; ring
  have hpoint2 : (fun x ↦ gamma x*weightedSkewTransport gamma V u x*v x) =
      (fun x ↦ 2*(gamma x*pairing u V x*v x) + gamma x*u x*(v x*weightedDiv gamma V x)) := by
    funext x; unfold weightedSkewTransport; ring
  rw [hpoint1,hpoint2,integral_add (hi1.const_mul 2) hi3,
    integral_add (hi2.const_mul 2) hi3,integral_const_mul,integral_const_mul]
  have heq : (fun x ↦ gamma x*(u x*v x)*weightedDiv gamma V x) =
      (fun x ↦ gamma x*u x*(v x*weightedDiv gamma V x)) := by funext x; ring
  rw [heq] at he
  linarith only [he]

lemma weightedSkewTransport_mul (gamma q v : Coord n → ℝ)
    (V : Coord n → Coord n) (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v)
    (x : Coord n) :
    weightedSkewTransport gamma V (fun y ↦ q y*v y) x =
      q x*weightedSkewTransport gamma V v x + 2*pairing q V x*v x := by
  unfold weightedSkewTransport
  rw [real_pairing_mul q v V hq hv]
  ring

theorem weighted_transport_multiplier (gamma q v : Coord n → ℝ)
    (V : Coord n → Coord n) (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    (∫ x, gamma x*q x*v x*weightedSkewTransport gamma V v x) =
      -(∫ x, gamma x*pairing q V x*v x^2) := by
  have hT := weightedSkewTransport_smooth gamma V v hg hgn hV hv
  have hi1 := compact_weighted_product_integrable gamma (fun x ↦ q x*v x)
    (weightedSkewTransport gamma V v) hg.continuous (hq.mul hv).continuous hT.continuous hc.mul_left
  have hi2 := compact_weighted_product_integrable gamma (fun x ↦ v x*v x)
    (pairing q V) hg.continuous (hv.mul hv).continuous (pairing_smooth hq hV).continuous hc.mul_right
  have he := weighted_transport_green gamma (fun x ↦ q x*v x) v V hg hgn
    (hq.mul hv) hv hc.mul_left hV
  have heq : (fun x ↦ gamma x*weightedSkewTransport gamma V (fun y ↦ q y*v y) x*v x) =
      (fun x ↦ gamma x*(q x*v x)*weightedSkewTransport gamma V v x +
        2*(gamma x*(v x*v x)*pairing q V x)) := by
    funext x
    rw [weightedSkewTransport_mul gamma q v V hq hv]
    ring
  rw [heq,integral_add hi1 (hi2.const_mul 2),integral_const_mul] at he
  have heq1 : (fun x ↦ gamma x*q x*v x*weightedSkewTransport gamma V v x) =
      (fun x ↦ gamma x*(q x*v x)*weightedSkewTransport gamma V v x) := by funext x; ring
  have heq2 : (fun x ↦ gamma x*pairing q V x*v x^2) =
      (fun x ↦ gamma x*(v x*v x)*pairing q V x) := by funext x; ring
  rw [heq1,heq2]
  linarith only [he]

end
end Yau

end OAI
