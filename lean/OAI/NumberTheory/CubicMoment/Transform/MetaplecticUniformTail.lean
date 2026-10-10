import OAI.NumberTheory.CubicMoment.Transform.MetaplecticDualTailWeights
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformWeights

namespace OAI

/-! Far-left truncation of the literal angular Voronoi series. The
absolute coefficient mass is derived from the published theta support,
and the height growth is derived from finite Gamma recurrence. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem UniformLogWeights.metaplectic_twisted_tail_bound
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W) (ℓ : ℤ) (m : ℕ)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hm : σ ≤ (m:ℝ)-1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ X J : ℝ, 0 < X → 0 < J → ∀ t : ℝ,
      ‖∑' nd, metaplecticFarTailTerm a r ℓ (fun x => W i x*mellinPhase t x)
          ((m:ℝ)-1/2) X J nd‖ ≤
        C*norm r^(ε+2*((m:ℝ)-1/2))*X^(-((m:ℝ)-1/2))*
          J^(-(((m:ℝ)-1/2)-σ))*(1+|t|)^(4*m) := by
  obtain ⟨Cw,hCw,hfar⟩ := h.metaplecticTransform_twisted_far_left ℓ m
  obtain ⟨M,hM,hmass⟩ := metaplectic_coefficient_mass_small_power ha hε hσ
  let A : ℝ := (m:ℝ)-1/2
  let S : ℝ := ∑' d : PrimaryArgument, norm d^(-5/2-3*σ)
  have hS : 0 ≤ S := tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _)
  let C : ℝ := Cw*(2*Real.pi)^(-4*A)*M*S
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro i r hr hsr X J hX hJ t
  have ht : 0 ≤ Cw*(1+|t|)^(4*m) := mul_nonneg hCw (by positivity)
  have htransform (v : ℝ) (hv : 0 < v) :
      ‖metaplecticTransform ℓ (fun x => W i x*mellinPhase t x) A v‖ ≤
        (Cw*(1+|t|)^(4*m))*v^(-A) := by
    have he : 1/2-(m:ℝ) = -A := by dsimp [A]; ring
    simpa only [he,mul_right_comm] using hfar i v hv t
  have hb := metaplecticFarTail_norm_bound a hr ℓ (fun x => W i x*mellinPhase t x)
    hσ hm hX hJ ht htransform (hmass r hr hsr).1 (hmass r hr hsr).2
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hRe : norm r^(2*A)*norm r^ε = norm r^(ε+2*A) := by
    rw [←Real.rpow_add hR]
    congr 1
    ring
  calc
    _ ≤ (Cw*(1+|t|)^(4*m)*((2*Real.pi)^(-4*A)*X^(-A)*norm r^(2*A)))*
        J^(-(A-σ))*(M*norm r^ε)*S := hb
    _ = C*(norm r^(2*A)*norm r^ε)*X^(-A)*J^(-(A-σ))*(1+|t|)^(4*m) := by
      dsimp [C]
      ring
    _ = _ := by rw [hRe]

end CubicFirstMoment

end

end OAI
