import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVPlaneAreaCoordinates

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma prismRadialFlux_eq_sub {X Y : PrismCoordinates → ℝ}
    (hX : Continuous X) (hY : Continuous Y) (a c b l u : ℝ) :
    prismRadialFlux X Y a c b l u =
      (∫ t in a..c, ∫ s in (0 : ℝ)..b, X (t,(s*u,s))-u*Y (t,(s*u,s))) -
      (∫ t in a..c, ∫ s in (0 : ℝ)..b, X (t,(s*l,s))-l*Y (t,(s*l,s))) := by
  have hc (k : ℝ) : Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..b,
      X (t,(s*k,s))-k*Y (t,(s*k,s))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) _ _
  have he (t : ℝ) : (∫ s in (0 : ℝ)..b,
      (X (t,(s*u,s))-u*Y (t,(s*u,s)))-(X (t,(s*l,s))-l*Y (t,(s*l,s)))) =
      (∫ s in (0 : ℝ)..b, X (t,(s*u,s))-u*Y (t,(s*u,s))) -
      (∫ s in (0 : ℝ)..b, X (t,(s*l,s))-l*Y (t,(s*l,s))) :=
    intervalIntegral.integral_sub ((by fun_prop : Continuous (fun s : ℝ ↦
      X (t,(s*u,s))-u*Y (t,(s*u,s)))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun s : ℝ ↦
      X (t,(s*l,s))-l*Y (t,(s*l,s)))).intervalIntegrable _ _)
  simp only [prismRadialFlux,he]
  exact intervalIntegral.integral_sub ((hc u).intervalIntegrable _ _) ((hc l).intervalIntegrable _ _)

theorem blowup_radial_faces_remainder_le
    {a c b l u l₀ l₁ u₀ u₁ : ℝ} (hac : a ≤ c) (hb : 0 ≤ b)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    {A O : Set Cover} (hA : MeasurableSet A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c b l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c b u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hO : tsupport F ⊆ O) (hnF : ∀ x, ‖F x‖ ≤ 1) :
    (∫ x in A, divergence F x) -
      prismRadialFlux (fun w ↦ F (coverPrismCoordinates.symm w) 1)
        (fun w ↦ F (coverPrismCoordinates.symm w) 2) a c b l u ≤
    (coverLocalPerimeter A O).toReal -
      (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)) := by
  have hnL : ‖-radialFaceNormal l‖ = 1 := by rw [norm_neg,radialFaceNormal_norm]
  have hpL (y : Plane) : ⟪-radialFaceNormal l,radialFaceIsometry l y⟫ = 0 := by
    rw [inner_neg_left,radialFaceIsometry_perp,neg_zero]
  have hmL := measurableSet_strictPatchOpen
    (fun i ↦ (radialPatchInequalities_contDiff a c b l₀ l₁ i).continuous)
  have hmU := measurableSet_strictPatchOpen
    (fun i ↦ (radialPatchInequalities_contDiff a c b u₀ u₁ i).continuous)
  have h := blowup_two_polytope_patches_remainder_le
    (radialPatchInequalities_contDiff a c b l₀ l₁)
    (radialPatchInequalities_contDiff a c b u₀ u₁)
    (radialPatchClosed_isCompact a c b l₀ l₁) (radialPatchClosed_isCompact a c b u₀ u₁)
    (radialPatchOpen_disjoint hsep) hA hnL (radialFaceNormal_norm u)
    hflatL hflatU hLO hUO heq hflux hF hs hO hnF
  rw [neg_radial_face_flux hac hb hl₀ hl₁ hF.continuous,
    radial_face_flux hac hb hu₀ hu₁ hF.continuous,
    real_volume_normalPlane_eq_isometry hnL (radialFaceIsometry l) hpL hmL,
    real_volume_normalPlane_eq_isometry (radialFaceNormal_norm u)
      (radialFaceIsometry u) (radialFaceIsometry_perp u) hmU,
    radial_face_patch_area hac hb hl₀ hl₁,radial_face_patch_area hac hb hu₀ hu₁] at h
  rw [prismRadialFlux_eq_sub (prism_component_contDiff hF 1).continuous
    (prism_component_contDiff hF 2).continuous]
  simp only [coverPrismCoordinates_symm_apply] at ⊢
  have he (t s k : ℝ) : WithLp.toLp 2 ![t,s*k,s] = WithLp.toLp 2 ![t,k*s,s] := by rw [mul_comm s k]
  simp_rw [he]
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem coverLocalPerimeter_prism_surgery_lt
    {a c b l u l₀ l₁ u₀ u₁ : ℝ} (hac : a < c) (hb : 0 < b)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    (hsmall : (c-a)*b*(u-l)+b^2*(u-l) <
      (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)))
    {A O : Set Cover} (hA : MeasurableSet A)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c b l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c b u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) :
    coverLocalPerimeter (A \ euclideanPrism a c b l u) O < coverLocalPerimeter A O := by
  have hlu : l ≤ u := (hl₁.trans_le hsep).trans hu₀ |>.le
  let area := (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2))
  have harea : 0 < area := by
    dsimp [area]
    have hlp : 0 < Real.sqrt (1+l^2) := Real.sqrt_pos.mpr (by positivity)
    have hup : 0 < Real.sqrt (1+u^2) := Real.sqrt_pos.mpr (by positivity)
    exact mul_pos (mul_pos (sub_pos.mpr hac) hb) (add_pos hlp hup)
  have hrem (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : HasCompactSupport F) (hO : tsupport F ⊆ O) (hn : ∀ x, ‖F x‖ ≤ 1) :=
    blowup_radial_faces_remainder_le hac.le hb.le hl₀ hl₁ hu₀ hu₁ hsep hA hflatL hflatU
      hLO hUO heq hflux hF hs hO hn
  have hpa : area ≤ (coverLocalPerimeter A O).toReal := by
    have hz := hrem (fun _ ↦ 0) contDiff_const (by simp [HasCompactSupport])
      (by simp) (by simp)
    simp [area,divergence,prismRadialFlux] at hz ⊢
    linarith
  have hp : 0 < (coverLocalPerimeter A O).toReal := harea.trans_le hpa
  have hfin : coverLocalPerimeter A O ≠ ⊤ := by rw [heq]; exact measure_ne_top _ _
  have hbound := coverLocalPerimeter_prism_surgery_le hac.le hb.le hlu hPA hrem
  apply hbound.trans_lt
  apply lt_of_lt_of_eq ?_ (ENNReal.ofReal_toReal hfin)
  apply (ENNReal.ofReal_lt_ofReal_iff hp).mpr
  dsimp [area] at *
  linarith

theorem no_minimizing_strict_prism_sector
    {a c b l u l₀ l₁ u₀ u₁ : ℝ} (hac : a < c) (hb : 0 < b)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    (hsmall : (c-a)*b*(u-l)+b^2*(u-l) <
      (c-a)*b*(Real.sqrt (1+l^2)+Real.sqrt (1+u^2)))
    {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hPK : euclideanPrism a c b l u ⊆ K)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c b l u → x ∈ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c b u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c b l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c b u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  have hlt := coverLocalPerimeter_prism_surgery_lt hac hb hl₀ hl₁ hu₀ hu₁ hsep hsmall hA
    hPA hflatL hflatU hLO hUO heq hflux
  have hle := hmin (A \ euclideanPrism a c b l u)
    (hA.diff (measurableSet_euclideanPrism a c b l u))
    ((prism_surgery_symmDiff_subset A a c b l u).trans hPK)
  exact not_lt_of_ge hle hlt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma exists_normal_sphere_null_radius (ν : FiniteMeasure BlowupNormalBundle)
    {a b : ℝ} (hab : a < b) :
    ∃ r : ℝ, a < r ∧ r < b ∧ (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0 := by
  have hc := Measure.countable_meas_level_set_pos
    (μ := (ν : Measure BlowupNormalBundle)) (g := fun z : BlowupNormalBundle ↦ ‖z.1‖)
    (by fun_prop)
  obtain ⟨r,hr,hrab⟩ := (hc.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hab)
  refine ⟨r,hrab.1,hrab.2,?_⟩
  exact le_antisymm (not_lt.mp hr) bot_le

lemma normal_closedBall_ae_eq_ball {ν : FiniteMeasure BlowupNormalBundle} {r : ℝ}
    (hr : (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0) :
    {z : BlowupNormalBundle | z.1 ∈ Metric.closedBall (0 : Cover) r} =ᵐ[(ν : Measure BlowupNormalBundle)]
      {z : BlowupNormalBundle | z.1 ∈ Metric.ball (0 : Cover) r} := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hr] with z hz
  apply propext
  simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right]
  exact ⟨fun h ↦ lt_of_le_of_ne h hz,le_of_lt⟩

theorem coverLocalPerimeter_closedBall_eq_ball_of_normal
    {A : Set Cover} {ν : FiniteMeasure BlowupNormalBundle} {r : ℝ} (hr1 : r ≤ 1)
    (hr : (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0)
    (heq : coverLocalPerimeter A (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) :
    coverLocalPerimeter A (Metric.closedBall (0 : Cover) r) =
      coverLocalPerimeter A (Metric.ball (0 : Cover) r) := by
  apply le_antisymm
  · have hh := coverLocalPerimeter_le_normal Metric.isClosed_closedBall.measurableSet
      (Metric.closedBall_subset_closedBall hr1) hflux
    exact hh.trans_eq ((measure_congr (normal_closedBall_ae_eq_ball hr)).trans heq.symm)
  · exact coverLocalPerimeter_mono A Metric.ball_subset_closedBall

theorem normal_radius_local_minimizing {A : Set Cover} {ν : FiniteMeasure BlowupNormalBundle}
    {a r : ℝ} (ha : 0 < a) (har : a < r) (hr1 : r ≤ 1)
    (hr : (ν : Measure BlowupNormalBundle) {z | ‖z.1‖ = r} = 0)
    (heq : coverLocalPerimeter A (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      A ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b)) :
    ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter A (Metric.closedBall (0 : Cover) r) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) r) := by
  intro D hD hAD
  rw [coverLocalPerimeter_closedBall_eq_ball_of_normal hr1 hr heq hflux]
  exact hmin D hD a r ha har hr1 hAD

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma euclideanPrism_mono_height {a c b d l u : ℝ} (hbd : b ≤ d) :
    euclideanPrism a c b l u ⊆ euclideanPrism a c d l u := by
  intro x hx
  exact ⟨hx.1,⟨hx.2.1.1,hx.2.1.2.trans hbd⟩,hx.2.2⟩

lemma radialPatchOpen_mono_height {a c b d l u : ℝ} (hbd : b ≤ d) :
    strictPatchOpen (radialPatchInequalities a c b l u) ⊆
      strictPatchOpen (radialPatchInequalities a c d l u) := by
  intro x hx
  obtain ⟨ha,hc,h0,hb,hl,hu⟩ := (mem_radialPatchOpen a c b l u x).mp hx
  exact (mem_radialPatchOpen a c d l u x).mpr ⟨ha,hc,h0,hb.trans_le hbd,hl,hu⟩

theorem no_minimizing_small_radial_sector
    {a c ε l u l₀ l₁ u₀ u₁ : ℝ} (hac : a < c) (hε : 0 < ε)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hPK : euclideanPrism a c ε l u ⊆ K)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c ε l u → x ∈ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  have hlu : l < u := (hl₁.trans_le hsep).trans hu₀
  obtain ⟨b,hb,hbε,hsmall⟩ := exists_strict_prism_replacement_scale hac hlu hε
  have hPL := radialPatchOpen_mono_height (a := a) (c := c) (l := l₀) (u := l₁) hbε.le
  have hPU := radialPatchOpen_mono_height (a := a) (c := c) (l := u₀) (u := u₁) hbε.le
  have hP := euclideanPrism_mono_height (a := a) (c := c) (l := l) (u := u) hbε.le
  exact no_minimizing_strict_prism_sector hac hb hl₀ hl₁ hu₀ hu₁ hsep hsmall hA hmin
    (hP.trans hPK) (hPA.mono (fun _ hx hy ↦ hx (hP hy)))
    (hflatL.mono (fun _ hx hy ↦ hx (hPL hy)))
    (hflatU.mono (fun _ hx hy ↦ hx (hPU hy))) (hPL.trans hLO) (hPU.trans hUO) heq hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma integral_cover_divergence_zero {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x : Cover, divergence F x) = 0 := by
  let ψ : Fin 3 → Cover → ℝ := fun i x ↦ F x i
  have hp (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hps (i : Fin 3) : HasCompactSupport (ψ i) := hs.comp_left
    (show (EuclideanSpace.proj i) (0 : Cover) = 0 by simp)
  have hd (x : Cover) : divergence F x = ∑ i : Fin 3,
      fderiv ℝ (ψ i) x (EuclideanSpace.single i 1) := by
    unfold divergence
    apply Finset.sum_congr rfl
    intro i _
    have hh := (((EuclideanSpace.proj i).hasFDerivAt).comp x
      ((hF.differentiable (by simp)) x).hasFDerivAt).fderiv
    change fderiv ℝ (ψ i) x = _ at hh
    rw [hh]
    rfl
  simp_rw [hd]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    exact integral_compact_fderiv_zero (hp i) (hps i) _
  · intro i _
    exact (((hp i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hps i).fderiv_apply ℝ _)

lemma integral_cover_divergence_compl {A : Set Cover} (hA : MeasurableSet A)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F) :
    (∫ x in Aᶜ, divergence F x) = -(∫ x in A, divergence F x) := by
  have hi : Integrable (divergence F) (volume : Measure Cover) :=
    (continuous_divergence hF).integrable_of_hasCompactSupport
    (hs.of_isClosed_subset isClosed_closure (divergence_tsupport_subset F))
  have hh := integral_add_compl hA hi
  rw [integral_cover_divergence_zero hF hs] at hh
  linarith

theorem coverLocalPerimeter_compl {A : Set Cover} (hA : MeasurableSet A) (O : Set Cover) :
    coverLocalPerimeter Aᶜ O = coverLocalPerimeter A O := by
  have hle {A : Set Cover} (hA : MeasurableSet A) :
      coverLocalPerimeter Aᶜ O ≤ coverLocalPerimeter A O := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hnorm
    have hFn : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ -F x) := hF.neg
    have hsFn : HasCompactSupport (fun x ↦ -F x) := hs.neg
    have hOFn : tsupport (fun x ↦ -F x) ⊆ O := by
      change tsupport (-F) ⊆ O
      simpa only [tsupport_neg] using hO
    have hnFn (x) : ‖-F x‖ ≤ 1 := by simpa using hnorm x
    have he : (∫ x in Aᶜ, divergence F x) = ∫ x in A, divergence (fun y ↦ -F y) x := by
      rw [integral_cover_divergence_compl hA hF hs]
      simp only [divergence_neg,integral_neg]
    rw [he]
    exact le_iSup_of_le (fun x ↦ -F x) (le_iSup_of_le hFn (le_iSup_of_le hsFn
      (le_iSup_of_le hOFn (le_iSup_of_le hnFn le_rfl))))
  exact le_antisymm (hle hA) (by simpa only [compl_compl] using hle hA.compl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def reverseBlowupNormal (z : BlowupNormalBundle) : BlowupNormalBundle :=
  (z.1,⟨-(z.2 : Cover),by simpa only [norm_neg] using z.2.property⟩)

lemma continuous_reverseBlowupNormal : Continuous reverseBlowupNormal :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

lemma reverseBlowupNormal_spatial_mass (ν : FiniteMeasure BlowupNormalBundle)
    {O : Set Cover} (hO : MeasurableSet O) :
    (ν.map reverseBlowupNormal : Measure BlowupNormalBundle) {z | z.1 ∈ O} =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [FiniteMeasure.toMeasure_map,Measure.map_apply continuous_reverseBlowupNormal.measurable
    (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ O} from hO.preimage measurable_fst)]
  rfl

lemma reverseBlowupNormal_flux {A O : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hFO : tsupport F ⊆ O) (hFn : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν.map reverseBlowupNormal : Measure BlowupNormalBundle)) =
      ∫ x in Aᶜ, divergence F x := by
  rw [FiniteMeasure.toMeasure_map,integral_map continuous_reverseBlowupNormal.measurable.aemeasurable
    (continuous_blowupFluxTest hF.continuous).aestronglyMeasurable]
  change (∫ z, ⟪-(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = _
  simp_rw [inner_neg_left,integral_neg]
  rw [integral_cover_divergence_compl hA hF hs,hflux F hF hs hFO hFn]

lemma coverLocalPerimeter_normal_compl {A O : Set Cover} (hA : MeasurableSet A)
    (hO : MeasurableSet O) {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O}) :
    coverLocalPerimeter Aᶜ O =
      (ν.map reverseBlowupNormal : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [coverLocalPerimeter_compl hA,reverseBlowupNormal_spatial_mass ν hO,heq]

lemma coverLocalPerimeter_compl_minimizing {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O) :
    ∀ D : Set Cover, MeasurableSet D → Aᶜ ∆ D ⊆ K →
      coverLocalPerimeter Aᶜ O ≤ coverLocalPerimeter D O := by
  intro D hD hAD
  rw [coverLocalPerimeter_compl hA]
  have hsub : A ∆ Dᶜ ⊆ K := by
    intro x hx
    apply hAD
    simp only [mem_symmDiff,mem_compl_iff] at hx ⊢
    tauto
  simpa only [coverLocalPerimeter_compl hD] using hmin Dᶜ hD.compl hsub

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem no_minimizing_small_empty_radial_sector
    {a c ε l u l₀ l₁ u₀ u₁ : ℝ} (hac : a < c) (hε : 0 < ε)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    {A O K : Set Cover} (hA : MeasurableSet A) (hO : MeasurableSet O)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hPK : euclideanPrism a c ε l u ⊆ K)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c ε l u → x ∉ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) →
      (x ∉ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) →
      (x ∉ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) ⊆ O)
    (hUO : strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) ⊆ O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  exact no_minimizing_small_radial_sector hac hε hl₀ hl₁ hu₀ hu₁ hsep hA.compl
    (coverLocalPerimeter_compl_minimizing hA hmin) hPK hPA hflatL hflatU hLO hUO
    (coverLocalPerimeter_normal_compl hA hO heq)
    (fun F hF hs hFO hFn ↦ reverseBlowupNormal_flux hA hflux hF hs hFO hFn)

theorem no_moving_tangent_small_radial_sector
    {a c ε l u l₀ l₁ u₀ u₁ ρ : ℝ} (hac : a < c) (hε : 0 < ε)
    (hl₀ : l₀ < l) (hl₁ : l < l₁) (hu₀ : u₀ < u) (hu₁ : u < u₁) (hsep : l₁ ≤ u₀)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    {A : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      A ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hPK : euclideanPrism a c ε l u ⊆ Metric.ball (0 : Cover) ρ)
    (hPA : ∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c ε l u → x ∈ A)
    (hflatL : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l)))
    (hflatU : ∀ᵐ x : Cover ∂volume, x ∈ strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u)))
    (hLO : strictPatchOpen (radialPatchInequalities a c ε l₀ l₁) ⊆ Metric.ball (0 : Cover) ρ)
    (hUO : strictPatchOpen (radialPatchInequalities a c ε u₀ u₁) ⊆ Metric.ball (0 : Cover) ρ)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter A (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  obtain ⟨r,hρr,hr1,hr⟩ := exists_normal_sphere_null_radius ν hρ1
  have hr0 : 0 < r := hρ.trans hρr
  have hpr := heq r hr0 hr1.le
  have hclosed := coverLocalPerimeter_closedBall_eq_ball_of_normal hr1.le hr hpr hflux
  have hmass : coverLocalPerimeter A (Metric.closedBall (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.closedBall (0 : Cover) r} := by
    rw [hclosed,hpr,measure_congr (normal_closedBall_ae_eq_ball hr)]
  have hinner : Metric.ball (0 : Cover) ρ ⊆ Metric.closedBall (0 : Cover) r :=
    (Metric.ball_subset_ball hρr.le).trans Metric.ball_subset_closedBall
  exact no_minimizing_small_radial_sector hac hε hl₀ hl₁ hu₀ hu₁ hsep hA
    (normal_radius_local_minimizing hρ hρr hr1.le hr hpr hflux hmin)
    hPK hPA hflatL hflatU (hLO.trans hinner) (hUO.trans hinner) hmass
    (fun F hF _ hFO _ ↦ hflux F hF (hFO.trans (Metric.closedBall_subset_closedBall hr1.le)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma prismSlope_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun x : Cover ↦ (x 2)⁻¹*x 1) volume volume := by
  have hp := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp
    prismColumnCoordinates_measurePreserving.quasiMeasurePreserving
  have hw := planarWedgeCoordinates_quasiMeasurePreserving.comp hp
  have hs := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp hw
  convert! hs using 1
  ext x
  simp [planarWedgeCoordinates]

lemma mem_negative_radial_halfspace {v : ℝ} {x : Cover} (hx : 0 < x 2) :
    x ∈ coverHalfspace (-radialFaceNormal v) ↔ v < (x 2)⁻¹*x 1 := by
  change ⟪-radialFaceNormal v,x⟫ < 0 ↔ _
  rw [inner_neg_left,inner_radialFaceNormal]
  have hd : 0 < Real.sqrt (1+v^2) := Real.sqrt_pos.mpr (by positivity)
  rw [neg_lt_zero,div_pos_iff_of_pos_right hd,sub_pos,← div_eq_inv_mul,lt_div_iff₀ hx]

lemma mem_radial_halfspace {v : ℝ} {x : Cover} (hx : 0 < x 2) :
    x ∈ coverHalfspace (radialFaceNormal v) ↔ (x 2)⁻¹*x 1 < v := by
  change ⟪radialFaceNormal v,x⟫ < 0 ↔ _
  rw [inner_radialFaceNormal]
  have hd : 0 < Real.sqrt (1+v^2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_lt_iff₀ hd,zero_mul,sub_lt_zero,← div_eq_inv_mul,div_lt_iff₀ hx]

theorem slope_interval_radial_models
    {A : Set Cover} {a c ε l u δ : ℝ} (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hmodel : ∀ᵐ x : Cover ∂volume, x 0 ∈ Ioc a c → x 2 ∈ Ioc 0 ε →
      (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u)) :
    (∀ᵐ x : Cover ∂volume, x ∈ euclideanPrism a c ε l u → x ∈ A) ∧
    (∀ᵐ x : Cover ∂volume,
      x ∈ strictPatchOpen (radialPatchInequalities a c ε (l-δ) (l+δ)) →
      (x ∈ A ↔ x ∈ coverHalfspace (-radialFaceNormal l))) ∧
    (∀ᵐ x : Cover ∂volume,
      x ∈ strictPatchOpen (radialPatchInequalities a c ε (u-δ) (u+δ)) →
      (x ∈ A ↔ x ∈ coverHalfspace (radialFaceNormal u))) := by
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ l ∧ t ≠ u := by
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ l by rw [ae_iff]; simp,
      show ∀ᵐ t : ℝ ∂volume, t ≠ u by rw [ae_iff]; simp] with t hl hu
    exact ⟨hl,hu⟩
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hmodel,prismSlope_quasiMeasurePreserving.ae hne] with x hm hn hx
    change x 0 ∈ Ioc a c ∧ x 2 ∈ Ioc 0 ε ∧ x 1 ∈ Ioc (x 2*l) (x 2*u) at hx
    have ht : (x 2)⁻¹*x 1 ∈ Ioo l u := by
      rw [← div_eq_inv_mul]
      constructor
      · apply lt_of_le_of_ne ((le_div_iff₀ hx.2.1.1).mpr (by nlinarith [hx.2.2.1]))
        simpa only [div_eq_inv_mul] using hn.1.symm
      · apply lt_of_le_of_ne ((div_le_iff₀ hx.2.1.1).mpr (by nlinarith [hx.2.2.2]))
        simpa only [div_eq_inv_mul] using hn.2
    exact (hm hx.1 hx.2.1 ⟨by linarith [ht.1],by linarith [ht.2]⟩).mpr ht
  · filter_upwards [hmodel] with x hm hx
    obtain ⟨ha,hc,h0,hε,hl,hu⟩ := (mem_radialPatchOpen a c ε (l-δ) (l+δ) x).mp hx
    have htL : l-δ < (x 2)⁻¹*x 1 := by rw [← div_eq_inv_mul,lt_div_iff₀ h0]; exact hl
    have htU : (x 2)⁻¹*x 1 < l+δ := by rw [← div_eq_inv_mul,div_lt_iff₀ h0]; exact hu
    rw [hm ⟨ha,hc.le⟩ ⟨h0,hε.le⟩ ⟨htL,by linarith⟩,mem_negative_radial_halfspace h0]
    exact and_iff_left (by linarith)
  · filter_upwards [hmodel] with x hm hx
    obtain ⟨ha,hc,h0,hε,hl,hu⟩ := (mem_radialPatchOpen a c ε (u-δ) (u+δ) x).mp hx
    have htL : u-δ < (x 2)⁻¹*x 1 := by rw [← div_eq_inv_mul,lt_div_iff₀ h0]; exact hl
    have htU : (x 2)⁻¹*x 1 < u+δ := by rw [← div_eq_inv_mul,div_lt_iff₀ h0]; exact hu
    rw [hm ⟨ha,hc.le⟩ ⟨h0,hε.le⟩ ⟨by linarith,htU⟩,mem_radial_halfspace h0]
    exact and_iff_right (by linarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_norm_le_coordinates (x : Cover) : ‖x‖ ≤ |x 0|+|x 1|+|x 2| := by
  have he : x = (EuclideanSpace.single 0 (x 0) : Cover)+(EuclideanSpace.single 1 (x 1) : Cover)+(EuclideanSpace.single 2 (x 2) : Cover) := by
    ext i
    fin_cases i <;> simp
  calc
    ‖x‖ = ‖(EuclideanSpace.single 0 (x 0) : Cover)+(EuclideanSpace.single 1 (x 1) : Cover)+(EuclideanSpace.single 2 (x 2) : Cover)‖ := congrArg norm he
    _ ≤ ‖(EuclideanSpace.single 0 (x 0) : Cover)‖+‖(EuclideanSpace.single 1 (x 1) : Cover)‖+‖(EuclideanSpace.single 2 (x 2) : Cover)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by simp

lemma radialPatchClosed_coordinate_bounds {h b l u : ℝ} (hb : 0 ≤ b) {x : Cover}
    (hx : x ∈ strictPatchClosed (radialPatchInequalities (-h) h b l u)) :
    |x 0| ≤ h ∧ |x 1| ≤ b*(|l|+|u|) ∧ |x 2| ≤ b := by
  obtain ⟨ha,hc,h0,hb',hl,hu⟩ := (mem_radialPatchClosed (-h) h b l u x).mp hx
  refine ⟨abs_le.mpr ⟨ha,hc⟩,abs_le.mpr ⟨?_,?_⟩,by rwa [abs_of_nonneg h0]⟩
  · have hp := mul_le_mul_of_nonneg_left hb' (abs_nonneg l)
    have hq := mul_le_mul_of_nonneg_right (neg_abs_le l) h0
    have hr := mul_nonneg hb (abs_nonneg u)
    nlinarith
  · have hp := mul_le_mul_of_nonneg_left hb' (abs_nonneg u)
    have hq := mul_le_mul_of_nonneg_right (le_abs_self u) h0
    have hr := mul_nonneg hb (abs_nonneg l)
    nlinarith

lemma radialPatchClosed_norm_le {h b l u : ℝ} (hb : 0 ≤ b) {x : Cover}
    (hx : x ∈ strictPatchClosed (radialPatchInequalities (-h) h b l u)) :
    ‖x‖ ≤ h+b*(|l|+|u|+1) := by
  obtain ⟨h0,h1,h2⟩ := radialPatchClosed_coordinate_bounds hb hx
  have hn := cover_norm_le_coordinates x
  nlinarith

lemma euclideanPrism_subset_radialPatchClosed (a c b l u : ℝ) :
    euclideanPrism a c b l u ⊆ strictPatchClosed (radialPatchInequalities a c b l u) := by
  intro x hx
  change x 0 ∈ Ioc a c ∧ x 2 ∈ Ioc 0 b ∧ x 1 ∈ Ioc (x 2*l) (x 2*u) at hx
  apply (mem_radialPatchClosed a c b l u x).mpr
  exact ⟨hx.1.1.le,hx.1.2,hx.2.1.1.le,hx.2.1.2,by nlinarith [hx.2.2.1],by nlinarith [hx.2.2.2]⟩

lemma radialPatchOpen_subset_closed (a c b l u : ℝ) :
    strictPatchOpen (radialPatchInequalities a c b l u) ⊆
      strictPatchClosed (radialPatchInequalities a c b l u) := by
  intro x hx i
  exact (hx i).le

theorem exists_small_sector_geometry {ρ η b l u δ : ℝ}
    (hρ : 0 < ρ) (hη : 0 < η) (hb : 0 < b) (hδ : 0 < δ) :
    ∃ h ε : ℝ, 0 < h ∧ h < η ∧ 0 < ε ∧ ε < b ∧
      (∀ s t : ℝ, |s|+|t| ≤ 2*(|l|+|u|+δ) →
        strictPatchClosed (radialPatchInequalities (-h) h ε s t) ⊆ Metric.ball (0 : Cover) ρ) ∧
      (∀ x : Cover, x 2 ∈ Ioc 0 ε → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
        ‖planeProductCoordinates.symm (x 2,x 1)‖ < η) := by
  let N : ℝ := ‖planeProductCoordinates.symm.toContinuousLinearMap‖
  let M : ℝ := |l|+|u|+δ+1
  let h : ℝ := min (η/2) (ρ/4)
  let ε : ℝ := min (b/2) (min (ρ/(8*M)) (η/(4*(N+1)*M)))
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 0 ≤ N := norm_nonneg _
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have he : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have heρ : ε ≤ ρ/(8*M) := (min_le_right _ _).trans (min_le_left _ _)
  have heη : ε ≤ η/(4*(N+1)*M) := (min_le_right _ _).trans (min_le_right _ _)
  have heρ' := (le_div_iff₀ (show 0 < 8*M by positivity)).mp heρ
  have heη' := (le_div_iff₀ (show 0 < 4*(N+1)*M by positivity)).mp heη
  refine ⟨h,ε,hh,(min_le_left _ _).trans_lt (by linarith),he,
    (min_le_left _ _).trans_lt (by linarith),?_,?_⟩
  · intro s t hst x hx
    have hn := radialPatchClosed_norm_le he.le hx
    have hcoeff : |s|+|t|+1 ≤ 2*M := by dsimp [M]; linarith
    have hecoeff := mul_le_mul_of_nonneg_left hcoeff he.le
    rw [Metric.mem_ball,dist_zero_right]
    have hhr : h ≤ ρ/4 := min_le_right _ _
    nlinarith
  · intro x hx ht
    have hx0 : 0 < x 2 := hx.1
    have hlo : (l-δ)*x 2 < x 1 := by
      have hh := ht.1
      rw [← div_eq_inv_mul,lt_div_iff₀ hx0] at hh
      exact hh
    have hup : x 1 < (u+δ)*x 2 := by
      have hh := ht.2
      rw [← div_eq_inv_mul,div_lt_iff₀ hx0] at hh
      exact hh
    have hx1 : |x 1| ≤ M*ε := by
      apply abs_le.mpr
      constructor
      · have hs : -M ≤ l-δ := by dsimp [M]; linarith [neg_abs_le l,abs_nonneg u]
        have hs' := mul_le_mul_of_nonneg_right hs hx0.le
        have hm := mul_le_mul_of_nonneg_left hx.2 hM.le
        nlinarith
      · have hs : u+δ ≤ M := by dsimp [M]; linarith [le_abs_self u,abs_nonneg l]
        have hs' := mul_le_mul_of_nonneg_right hs hx0.le
        have hm := mul_le_mul_of_nonneg_left hx.2 hM.le
        nlinarith
    have hx2 : |x 2| ≤ M*ε := by
      rw [abs_of_pos hx0]
      have hM1 : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg l,abs_nonneg u]
      exact hx.2.trans (by nlinarith)
    have hpn : ‖((x 2,x 1) : ℝ × ℝ)‖ ≤ M*ε := by
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
      exact max_le hx2 hx1
    have hp := planeProductCoordinates.symm.toContinuousLinearMap.le_opNorm (x 2,x 1)
    have hmult := mul_le_mul_of_nonneg_left hpn hN
    change ‖planeProductCoordinates.symm (x 2,x 1)‖ ≤ N*‖((x 2,x 1) : ℝ × ℝ)‖ at hp
    have hex := mul_pos hM he
    nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma prismRotatedColumn_measurePreserving (R : Plane ≃ₗᵢ[ℝ] Plane) :
    MeasurePreserving (fun x : Cover ↦ (x 0,R (planeProductCoordinates.symm (x 2,x 1)))) volume volume := by
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod R.measurePreserving
  convert! hp.comp prismColumnCoordinates_measurePreserving using 1

lemma prismPlanarProjection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun x : Cover ↦ planeProductCoordinates.symm (x 2,x 1)) volume volume := by
  have hh := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))).comp
    prismColumnCoordinates_measurePreserving.quasiMeasurePreserving
  convert! hh using 1

theorem prismFrame_product_model {B : Set Cover} {C : Set Plane} {n : Cover} {η : ℝ}
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∀ᵐ x : Cover ∂volume, |x 0| < η → ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      (x ∈ (prismFrame n R) ⁻¹' B ↔ planeProductCoordinates.symm (x 2,x 1) ∈ R ⁻¹' C) := by
  filter_upwards [(prismRotatedColumn_measurePreserving R).quasiMeasurePreserving.ae hprod]
    with x hx ha hp
  change prismFrame n R x ∈ B ↔ R (planeProductCoordinates.symm (x 2,x 1)) ∈ C
  rw [prismFrame_apply]
  exact hx ha (by simpa only [R.norm_map] using hp)

theorem prismFrame_angular_sector_model
    {B : Set Cover} {C : Set Plane} {n : Cover} {η b l u δ : ℝ}
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hangular : ∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      (planarWedgeCoordinates y).2 ∈ Ioo (l-δ) (u+δ) →
      (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ Ioo l u)) :
    ∀ᵐ x : Cover ∂volume, |x 0| < η → ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ (prismFrame n R) ⁻¹' B ↔ (x 2)⁻¹*x 1 ∈ Ioo l u) := by
  filter_upwards [prismFrame_product_model hprod R,
    prismPlanarProjection_quasiMeasurePreserving.ae hangular] with x hp ha hax hpn hr hs
  have he : planarWedgeCoordinates (planeProductCoordinates.symm (x 2,x 1)) =
      (x 2,(x 2)⁻¹*x 1) := by simp [planarWedgeCoordinates]
  simp only [he] at ha
  exact (hp hax hpn).trans (ha hr hs)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_eq_trace (F : Cover → Cover) (x : Cover) :
    divergence F x = LinearMap.trace ℝ Cover (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp [divergence,Matrix.trace,LinearMap.toMatrix_apply]

lemma divergence_isometry_pullback (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : Differentiable ℝ F) (x : Cover) :
    divergence (fun y ↦ R.symm (F (R y))) x = divergence F (R x) := by
  rw [divergence_eq_trace,divergence_eq_trace]
  have hd := R.symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    ((hF (R x)).hasFDerivAt.comp x R.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ R.symm (F (R y))) _ x at hd
  rw [hd.fderiv]
  have he : (R.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((fderiv ℝ F (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap)).toLinearMap =
      R.symm.toLinearEquiv.conj (fderiv ℝ F (R x)).toLinearMap := rfl
  rw [he,LinearMap.trace_conj']

lemma isometry_pullback_contDiff (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ R.symm (F (R x))) :=
  R.symm.toContinuousLinearEquiv.contDiff.comp (hF.comp R.toContinuousLinearEquiv.contDiff)

lemma isometry_pullback_compactSupport (R : Cover ≃ₗᵢ[ℝ] Cover) {F : Cover → Cover}
    (hs : HasCompactSupport F) : HasCompactSupport (fun x ↦ R.symm (F (R x))) :=
  (hs.comp_isClosedEmbedding R.toHomeomorph.isClosedEmbedding).comp_left (map_zero R.symm)

lemma isometry_pullback_tsupport (R : Cover ≃ₗᵢ[ℝ] Cover) (F : Cover → Cover) :
    tsupport (fun x ↦ R.symm (F (R x))) = R ⁻¹' tsupport F := by
  have h0 : Function.support (fun x ↦ R.symm (F (R x))) = R ⁻¹' Function.support F := by
    ext x
    change (R.symm (F (R x)) ≠ 0) ↔ (F (R x) ≠ 0)
    have he : (R.symm (F (R x)) = 0) ↔ (F (R x) = 0) := by
      constructor
      · intro hh
        simpa only [R.apply_symm_apply,map_zero] using congrArg R hh
      · intro hh
        rw [hh,map_zero]
    exact not_congr he
  change closure (Function.support (fun x ↦ R.symm (F (R x)))) = R ⁻¹' closure (Function.support F)
  rw [h0]
  exact (R.toHomeomorph.preimage_closure _).symm

lemma setIntegral_divergence_isometry_preimage (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A : Set Cover} (hA : MeasurableSet A) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    (∫ x in R ⁻¹' A, divergence (fun y ↦ R.symm (F (R y))) x) =
      ∫ x in A, divergence F x := by
  simp_rw [divergence_isometry_pullback R (hF.differentiable (by simp))]
  exact (R.measurePreserving.restrict_preimage hA).integral_comp R.toHomeomorph.measurableEmbedding _

theorem coverLocalPerimeter_isometry_preimage (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A : Set Cover} (hA : MeasurableSet A) (O : Set Cover) :
    coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) = coverLocalPerimeter A O := by
  have hle (R : Cover ≃ₗᵢ[ℝ] Cover) {A : Set Cover} (hA : MeasurableSet A) (O : Set Cover) :
      coverLocalPerimeter A O ≤ coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    apply iSup_le; intro hs
    apply iSup_le; intro hO
    apply iSup_le; intro hn
    let G : Cover → Cover := fun x ↦ R.symm (F (R x))
    have hG := isometry_pullback_contDiff R hF
    have hsG := isometry_pullback_compactSupport R hs
    have hOG : tsupport G ⊆ R ⁻¹' O := by
      rw [isometry_pullback_tsupport R F]
      exact preimage_mono hO
    have hnG (x) : ‖G x‖ ≤ 1 := by
      rw [R.symm.norm_map]; exact hn _
    have he := setIntegral_divergence_isometry_preimage R hA hF
    rw [← he]
    exact le_iSup_of_le G (le_iSup_of_le hG (le_iSup_of_le hsG
      (le_iSup_of_le hOG (le_iSup_of_le hnG le_rfl))))
  refine le_antisymm ?_ (hle R hA O)
  have hh := hle R.symm (hA.preimage R.continuous.measurable) (R ⁻¹' O)
  simpa only [preimage_preimage,R.apply_symm_apply,preimage_id'] using hh

end CubicTorus

end
end

end

end OAI
