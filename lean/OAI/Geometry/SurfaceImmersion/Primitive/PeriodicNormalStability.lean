import OAI.Geometry.SurfaceImmersion.Geometry.CompactNormalTriple
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFamilies

namespace OAI

/-! Uniform normal margins over the compact position-period domain. -/
noncomputable section
open Set
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes CovarianceCorrector

variable {A : Type} [TopologicalSpace A]

/-- A full real fast phase costs no compactness: periodicity reduces the
normal estimate to one compact period. -/
theorem periodic_leading_normal_stability {K : Set A} (hK : IsCompact K)
    {X Y C : A → Vec} (hX : Continuous X) (hY : Continuous Y) (hC : Continuous C)
    (V : A → C(Period, Vec))
    (hVs : Continuous (fun p : A × ℝ => V p.1 (p.2 : Period)))
    (hD : ∀ p ∈ K, gramDet (Y p) (C p) ≠ 0)
    (hYV : ∀ p ∈ K, ∀ θ : Period, Y p ⬝ᵥ V p θ = 0)
    (hCV : ∀ p ∈ K, ∀ θ : Period, C p ⬝ᵥ V p θ = 0)
    (hV0 : ∀ p ∈ K, ∀ θ : Period, V p θ ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ p ∈ K, ∀ t : ℝ, ∀ H : NormalTriple,
      ‖H-![leadingTangent (X p) (Y p) (C p) (V p (t : Period)),Y p,C p]‖ < ε →
      gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖realNormalPart (H 0) (H 1) (H 2)‖ := by
  obtain ⟨ε,c,hε,hc,hh⟩ := compact_leading_normal_stability
    (hK.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)))
    (hX.comp continuous_fst).continuousOn (hY.comp continuous_fst).continuousOn
    (hC.comp continuous_fst).continuousOn hVs.continuousOn
    (fun p hp => hD p.1 hp.1) (fun p hp => hYV p.1 hp.1 (p.2 : Period))
    (fun p hp => hCV p.1 hp.1 (p.2 : Period))
    (fun p hp => hV0 p.1 hp.1 (p.2 : Period))
  refine ⟨ε,c,hε,hc,?_⟩
  intro p hp t H hH
  let a : ℝ := AddCircle.equivIco 1 0 (t : Period)
  have ha : a ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIco 1 0 (t : Period)).property
  have he : (a : Period) = (t : Period) := AddCircle.coe_equivIco
  apply hh (p,a) ⟨hp,ha.1,ha.2.le⟩ H
  simpa only [he,Function.comp_apply] using hH

/-- Componentwise `O(z)` errors in x, y and yy preserve a uniform normal
margin for all sufficiently small fast scales. -/
theorem periodic_normal_stability_of_linear_error {K : Set A} (hK : IsCompact K)
    {X Y C : A → Vec} (hX : Continuous X) (hY : Continuous Y) (hC : Continuous C)
    (V : A → C(Period, Vec))
    (hVs : Continuous (fun p : A × ℝ => V p.1 (p.2 : Period)))
    (hD : ∀ p ∈ K, gramDet (Y p) (C p) ≠ 0)
    (hYV : ∀ p ∈ K, ∀ θ : Period, Y p ⬝ᵥ V p θ = 0)
    (hCV : ∀ p ∈ K, ∀ θ : Period, C p ⬝ᵥ V p θ = 0)
    (hV0 : ∀ p ∈ K, ∀ θ : Period, V p θ ≠ 0)
    (D : ℝ) (hD0 : 0 ≤ D) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ z : ℝ, 0 < z → z < η →
      ∀ p ∈ K, ∀ t : ℝ, ∀ x y b : Vec,
      ‖x-leadingTangent (X p) (Y p) (C p) (V p (t : Period))‖ ≤ D*z →
      ‖y-Y p‖ ≤ D*z → ‖b-C p‖ ≤ D*z →
      gramDet x y ≠ 0 ∧ c < ‖realNormalPart x y b‖ := by
  obtain ⟨ε,c,hε,hc,hh⟩ := periodic_leading_normal_stability hK hX hY hC V hVs hD hYV hCV hV0
  refine ⟨ε/(D+1),c,div_pos hε (by linarith),hc,?_⟩
  intro z hz hzη p hp t x y b hx hy hb
  have hsmall : D*z < ε := by
    have hh := (lt_div_iff₀ (show 0 < D+1 by linarith)).mp hzη
    nlinarith
  apply hh p hp t ![x,y,b]
  apply lt_of_le_of_lt _ hsmall
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hD0 hz.le)).mpr
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hb

end ClosedSurfaceR4.VelocityFrame

end

end OAI
