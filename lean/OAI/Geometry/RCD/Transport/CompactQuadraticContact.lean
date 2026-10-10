import OAI.Geometry.RCD.Sobolev.CoerciveQuadraticEnvelope
import OAI.Geometry.RCD.Sobolev.CompactCoerciveTruncation
import OAI.Geometry.RCD.Transport.CompactContactCompletion

namespace OAI

/-! # Compact Sobolev contact potentials for a local quadratic envelope -/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [ProperSpace X]

theorem compact_quadratic_contact (hgeo : IsGeodesicSpace X)
    (p : X) (point : Y → X) (F : Y → ℝ) {R t B A : ℝ}
    (hR : 0 ≤ R) (ht : 0 < t) (hF : ∀ a, F a ≤ B)
    (hd : ∀ a, dist p (point a) ≤ R) (Φ : X → ℝ)
    (hupper : ∀ x a, Φ x ≤ dist x (point a)^2/2-t*F a+t*A)
    (hexact : ∀ x, ∃ a, Φ x = dist x (point a)^2/2-t*F a+t*A)
    (hlip : ∀ r : ℝ, 0 < r → ∃ L : ℝ≥0, LipschitzOnWith L Φ (closedBall p r))
    {r₀ : ℝ} (hr₀ : 0 ≤ r₀) :
    ∃ (M r : ℝ) (ψ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L ψ ∧ HasCompactSupport ψ ∧
      (∀ x, r < dist p x → ψ x = 0) ∧
      LipschitzWith L (hopfLax (-ψ) 1) ∧ HasCompactSupport (hopfLax (-ψ) 1) ∧
      (∀ x y, hopfLax (-ψ) 1 x+ψ y ≤ dist x y^2/2) ∧
      (∀ x ∈ closedBall p r₀, hopfLax (-ψ) 1 x = Φ x-M) ∧
      ∀ x ∈ closedBall p r₀, ∀ a,
        Φ x = dist x (point a)^2/2-t*F a+t*A →
        hopfLax (-ψ) 1 x+ψ (point a) = dist x (point a)^2/2 := by
  have hcoerce := quadratic_envelope_coercive p hR ht point F hF hd Φ hexact
  obtain ⟨M,r,L,_,hf,hfs,hfzero,hlocal⟩ :=
    compact_coercive_truncation p Φ hlip hcoerce hr₀
  let f : X → ℝ := fun x => min (Φ x) M-M
  obtain ⟨ψ,s,hψ,hψs,hψzero,hχ,hχs,had,_,hc⟩ :=
    compact_contact_completion hgeo p hf hfzero
  have hbound (a : Y) (z : X) :
      f z+(t*F a-t*A+M) ≤ dist z (point a)^2/2 := by
    have hm := min_le_left (Φ z) M
    have hu := hupper z a
    dsimp [f]
    linarith
  have hcontact (x : X) (hx : x ∈ closedBall p r₀) (a : Y)
      (ha : Φ x = dist x (point a)^2/2-t*F a+t*A) :
      hopfLax (-ψ) 1 x = Φ x-M ∧ ψ (point a) = t*F a-t*A+M := by
    have he : f x+(t*F a-t*A+M) = dist x (point a)^2/2 := by
      change (min (Φ x) M-M)+(t*F a-t*A+M) = _
      rw [hlocal x hx,ha]
      ring
    obtain ⟨heq,hψeq⟩ := hc x (point a) (t*F a-t*A+M) (hbound a) he
    exact ⟨heq.trans (hlocal x hx),hψeq⟩
  refine ⟨M,s,ψ,L,hψ,hψs,hψzero,hχ,hχs,had,?_,?_⟩
  · intro x hx
    obtain ⟨a,ha⟩ := hexact x
    exact (hcontact x hx a ha).1
  · intro x hx a ha
    obtain ⟨he,hψeq⟩ := hcontact x hx a ha
    rw [he,hψeq,ha]
    ring

end RegularPointCoordinates

end

end OAI
