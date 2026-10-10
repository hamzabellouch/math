import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.CoordinateBalls

namespace OAI

/-! Coordinate Ellipticity. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory Matrix
open scoped ContDiff InnerProductSpace ComplexOrder Matrix.Norms.Elementwise
namespace PotentialABP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)
local instance ellipticityRealIP (d : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin d))

lemma matrix_quadratic_pos {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.PosDef)
    {v : E} (hv : v ≠ 0) : 0 < inner ℝ (H.toEuclideanLin v) v := by
  rw [real_inner_comm, real_inner_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct]
  rw [dotProduct_comm]
  apply hH.re_dotProduct_pos
  intro h
  apply hv
  exact (EuclideanSpace.equiv (Fin d) ℂ).injective (by simpa using h)

 

lemma compact_matrix_lower_bound {K : Set E} (hK : IsCompact K)
    {G : E → Matrix (Fin d) (Fin d) ℂ}
    (hcont : ContinuousOn (fun x => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) (G x)) K)
    (hpos : ∀ x ∈ K, (G x).PosDef) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ v : E,
      δ*‖v‖^2 ≤ inner ℝ ((G x).toEuclideanLin v) v := by
  let Q : E × E → ℝ := fun z => inner ℝ ((G z.1).toEuclideanLin z.2) z.2
  let L := K ×ˢ sphere (0:E) 1
  have hLc : IsCompact L := hK.prod (isCompact_sphere _ _)
  have hQc : ContinuousOn Q L := by
    have hc := hcont.comp continuous_fst.continuousOn (show MapsTo Prod.fst L K from fun z hz => hz.1)
    exact (hc.clm_apply continuous_snd.continuousOn).inner continuous_snd.continuousOn
  have hp : ∀ z ∈ L, 0 < Q z := by
    rintro ⟨x,v⟩ ⟨hx,hv⟩
    apply matrix_quadratic_pos (hpos x hx)
    intro hv0
    change v = 0 at hv0
    have hw : ‖v‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hv
    rw [hv0, norm_zero] at hw
    norm_num at hw
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ L, δ ≤ Q z := by
    by_cases hn : L.Nonempty
    · obtain ⟨z, hz, hzmin⟩ := hLc.exists_isMinOn hn hQc
      exact ⟨Q z, hp z hz, fun y hy => hzmin hy⟩
    · exact ⟨1, by norm_num, fun z hz => (hn ⟨z,hz⟩).elim⟩
  obtain ⟨δ,hδ,hbound⟩ := hδ
  refine ⟨δ,hδ,?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hb := hbound (x,(‖v‖⁻¹ : ℝ) • v) ⟨hx, by simpa [mem_sphere, dist_zero_right] using hw⟩
  have he : Q (x,(‖v‖⁻¹ : ℝ) • v) = ‖v‖⁻¹*‖v‖⁻¹ * inner ℝ ((G x).toEuclideanLin v) v := by
    dsimp only [Q]
    have hmap : (G x).toEuclideanLin ((‖v‖⁻¹ : ℝ) • v) =
        (‖v‖⁻¹ : ℝ) • (G x).toEuclideanLin v :=
      ((G x).toEuclideanLin.restrictScalars ℝ).map_smul _ _
    rw [hmap, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [he] at hb
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖v‖)
  have hc : ‖v‖^2 * (‖v‖⁻¹ * ‖v‖⁻¹ * inner ℝ ((G x).toEuclideanLin v) v) =
      inner ℝ ((G x).toEuclideanLin v) v := by field_simp
  rw [hc] at hh
  nlinarith
end PotentialABP

namespace Anticanonical.SourceSmooth
open EllipticKernel PotentialABP
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local instance coordinateEllipticityRealIP (d : ℕ) : InnerProductSpace ℝ (EC d) :=
  InnerProductSpace.rclikeToReal ℂ (EC d)
namespace CoordinateBall
variable (p : CoordinateBall A)

lemma metric_continuousOn (g : KaehlerMetric A) :
    ContinuousOn (fun z : EC d =>
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) (g.matrix p.index (coordinateEquiv d z)))
      (closedBall p.center (3*p.radius)) := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.comp_continuousOn
  have hs : ContinuousOn (fun z : EC d => g.matrix p.index (coordinateEquiv d z))
      (A.euclideanChart p.index).target := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    have hij := (contDiffOn_pi.mp (contDiffOn_pi.mp (g.smooth p.index) i) j).continuousOn
    rw [ComplexAtlas.euclideanChart_target]
    convert hij.comp (coordinateEquiv d).continuous.continuousOn
      (show Set.MapsTo (coordinateEquiv d)
        ((coordinateEquiv d) ⁻¹' (A.chart p.index).target) (A.chart p.index).target from
          fun _ hz => hz) using 1
    rfl
  exact hs.mono (fun z hz => p.closure_sub
    (closedBall_subset_closedBall (by linarith [p.radius_pos]) hz))

lemma metric_lower_bound (g : KaehlerMetric A) : ∃ δ : ℝ, 0 < δ ∧
    ∀ z ∈ closedBall p.center (3*p.radius), ∀ v : EC d,
      δ*‖v‖^2 ≤ inner ℝ ((g.matrix p.index (coordinateEquiv d z)).toEuclideanLin v) v := by
  apply compact_matrix_lower_bound (isCompact_closedBall _ _) (p.metric_continuousOn g)
  intro z hz
  apply g.positive
  have ht := p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) hz)
  simpa only [ComplexAtlas.euclideanChart_target, mem_preimage] using ht
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
