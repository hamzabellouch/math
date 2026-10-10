import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVBlowupComplement

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def pullbackBlowupNormal (R : Cover ≃ₗᵢ[ℝ] Cover) (z : BlowupNormalBundle) : BlowupNormalBundle :=
  (R.symm z.1,⟨R.symm (z.2 : Cover),by simpa only [R.symm.norm_map] using z.2.property⟩)

lemma continuous_pullbackBlowupNormal (R : Cover ≃ₗᵢ[ℝ] Cover) :
    Continuous (pullbackBlowupNormal R) :=
  (R.symm.continuous.comp continuous_fst).prodMk
    ((R.symm.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)

lemma pullbackBlowupNormal_spatial_mass (R : Cover ≃ₗᵢ[ℝ] Cover)
    (ν : FiniteMeasure BlowupNormalBundle) {O : Set Cover} (hO : MeasurableSet O) :
    (ν.map (pullbackBlowupNormal R) : Measure BlowupNormalBundle) {z | z.1 ∈ R ⁻¹' O} =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O} := by
  rw [FiniteMeasure.toMeasure_map,Measure.map_apply (continuous_pullbackBlowupNormal R).measurable
    (show MeasurableSet {z : BlowupNormalBundle | z.1 ∈ R ⁻¹' O} from
      (hO.preimage R.continuous.measurable).preimage measurable_fst)]
  congr 1
  ext z
  change R (R.symm z.1) ∈ O ↔ z.1 ∈ O
  rw [R.apply_symm_apply]

lemma pullbackBlowupNormal_flux (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A O : Set Cover} (hA : MeasurableSet A) {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    (hFO : tsupport F ⊆ R ⁻¹' O) (hFn : ∀ x, ‖F x‖ ≤ 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν.map (pullbackBlowupNormal R) : Measure BlowupNormalBundle)) =
      ∫ x in R ⁻¹' A, divergence F x := by
  let G : Cover → Cover := fun x ↦ R (F (R.symm x))
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := isometry_pullback_contDiff R.symm hF
  have hsG : HasCompactSupport G := isometry_pullback_compactSupport R.symm hs
  have hGO : tsupport G ⊆ O := by
    change tsupport (fun x ↦ R.symm.symm (F (R.symm x))) ⊆ O
    rw [isometry_pullback_tsupport R.symm F]
    intro x hx
    simpa only [Set.mem_preimage,R.apply_symm_apply] using hFO hx
  have hGn (x) : ‖G x‖ ≤ 1 := by simpa only [G,R.norm_map] using hFn (R.symm x)
  rw [FiniteMeasure.toMeasure_map,integral_map (continuous_pullbackBlowupNormal R).measurable.aemeasurable
    (continuous_blowupFluxTest hF.continuous).aestronglyMeasurable]
  have hh (z : BlowupNormalBundle) :
      ⟪((pullbackBlowupNormal R z).2 : Cover),F (pullbackBlowupNormal R z).1⟫ =
        ⟪(z.2 : Cover),G z.1⟫ := by
    change ⟪R.symm (z.2 : Cover),F (R.symm z.1)⟫ = ⟪(z.2 : Cover),R (F (R.symm z.1))⟫
    simpa only [R.apply_symm_apply] using
      (R.inner_map_map (R.symm (z.2 : Cover)) (F (R.symm z.1))).symm
  simp_rw [hh]
  rw [hflux G hG hsG hGO hGn]
  have he := setIntegral_divergence_isometry_preimage R hA hG
  have hGF : (fun y ↦ R.symm (G (R y))) = F := by
    ext y
    simp only [G,R.symm_apply_apply]
  rw [hGF] at he
  exact he.symm

lemma coverLocalPerimeter_isometry_normal (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A O : Set Cover} (hA : MeasurableSet A) (hO : MeasurableSet O)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O}) :
    coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) =
      (ν.map (pullbackBlowupNormal R) : Measure BlowupNormalBundle) {z | z.1 ∈ R ⁻¹' O} := by
  rw [coverLocalPerimeter_isometry_preimage R hA,pullbackBlowupNormal_spatial_mass R ν hO,heq]

lemma coverLocalPerimeter_isometry_minimizing (R : Cover ≃ₗᵢ[ℝ] Cover)
    {A O K : Set Cover} (hA : MeasurableSet A)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O) :
    ∀ D : Set Cover, MeasurableSet D → (R ⁻¹' A) ∆ D ⊆ R ⁻¹' K →
      coverLocalPerimeter (R ⁻¹' A) (R ⁻¹' O) ≤ coverLocalPerimeter D (R ⁻¹' O) := by
  intro D hD hAD
  have hD' : MeasurableSet (R.symm ⁻¹' D) := hD.preimage R.symm.continuous.measurable
  have hsub : A ∆ (R.symm ⁻¹' D) ⊆ K := by
    intro x hx
    have hh := hAD (show R.symm x ∈ (R ⁻¹' A) ∆ D from by
      simpa only [mem_symmDiff,Set.mem_preimage,R.apply_symm_apply] using hx)
    simpa only [Set.mem_preimage,R.apply_symm_apply] using hh
  have he : R ⁻¹' (R.symm ⁻¹' D) = D := by ext x; simp only [Set.mem_preimage,R.symm_apply_apply]
  rw [coverLocalPerimeter_isometry_preimage R hA]
  have hc := coverLocalPerimeter_isometry_preimage R hD' O
  rw [he] at hc
  exact (hmin _ hD' hsub).trans_eq hc.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem no_minimizing_angular_sector {A O K : Set Cover} (hA : MeasurableSet A)
    {ρ η b l u δ : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hb : 0 < b)
    (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hKO : Metric.ball (0 : Cover) ρ ⊆ K) (hOO : Metric.ball (0 : Cover) ρ ⊆ O)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hmodel : ∀ᵐ x : Cover ∂volume, |x 0| < η →
      ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  obtain ⟨h,ε,hh,hhη,hε,hεb,hsmall,hplane⟩ := exists_small_sector_geometry hρ hη hb hδ (l := l) (u := u)
  have hmod : ∀ᵐ x : Cover ∂volume, x 0 ∈ Ioc (-h) h → x 2 ∈ Ioc 0 ε →
      (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u) := by
    filter_upwards [hmodel] with x hx hax hr hs
    apply hx (abs_lt.mpr ⟨by linarith [hax.1],hax.2.trans_lt hhη⟩)
      (hplane x hr hs) ⟨hr.1,hr.2.trans_lt hεb⟩ hs
  obtain ⟨hPA,hflatL,hflatU⟩ := slope_interval_radial_models hδ hgap hmod
  have habs {v : ℝ} : |v-δ|+|v+δ| ≤ 2*(|v|+δ) := by
    have h1 := abs_sub v δ
    have h2 := abs_add_le v δ
    rw [abs_of_pos hδ] at h1 h2
    linarith
  apply no_minimizing_small_radial_sector (a := -h) (c := h) (ε := ε)
    (l := l) (u := u) (l₀ := l-δ) (l₁ := l+δ) (u₀ := u-δ) (u₁ := u+δ)
    (by linarith) hε (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) hA hmin ?_ hPA hflatL hflatU ?_ ?_ heq hflux
  · exact (euclideanPrism_subset_radialPatchClosed (-h) h ε l u).trans
      ((hsmall l u (by linarith [abs_nonneg l,abs_nonneg u])).trans hKO)
  · exact (radialPatchOpen_subset_closed (-h) h ε (l-δ) (l+δ)).trans
      ((hsmall _ _ (by linarith [habs (v := l),abs_nonneg u])).trans hOO)
  · exact (radialPatchOpen_subset_closed (-h) h ε (u-δ) (u+δ)).trans
      ((hsmall _ _ (by linarith [habs (v := u),abs_nonneg l])).trans hOO)

theorem no_minimizing_angular_phase_sector {A O K : Set Cover} (hA : MeasurableSet A)
    (hO : MeasurableSet O)
    {ρ η b l u δ : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hb : 0 < b)
    (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hKO : Metric.ball (0 : Cover) ρ ⊆ K) (hOO : Metric.ball (0 : Cover) ρ ⊆ O)
    (hmin : ∀ D : Set Cover, MeasurableSet D → A ∆ D ⊆ K →
      coverLocalPerimeter A O ≤ coverLocalPerimeter D O)
    (hmodel : (∀ᵐ x : Cover ∂volume, |x 0| < η →
      ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ A ↔ (x 2)⁻¹*x 1 ∈ Ioo l u)) ∨
      (∀ᵐ x : Cover ∂volume, |x 0| < η →
      ‖planeProductCoordinates.symm (x 2,x 1)‖ < η →
      x 2 ∈ Ioo 0 b → (x 2)⁻¹*x 1 ∈ Ioo (l-δ) (u+δ) →
      (x ∈ Aᶜ ↔ (x 2)⁻¹*x 1 ∈ Ioo l u)))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : coverLocalPerimeter A O = (ν : Measure BlowupNormalBundle) {z | z.1 ∈ O})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ O → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in A, divergence F x) : False := by
  rcases hmodel with hm|hm
  · exact no_minimizing_angular_sector hA hρ hη hb hδ hgap hKO hOO hmin hm heq hflux
  · exact no_minimizing_angular_sector hA.compl hρ hη hb hδ hgap hKO hOO
      (coverLocalPerimeter_compl_minimizing hA hmin) hm
      (coverLocalPerimeter_normal_compl hA hO heq)
      (fun F hF hs hFO hFn ↦ reverseBlowupNormal_flux hA hflux hF hs hFO hFn)

theorem no_moving_product_angular_sector
    {B : Set Cover} {C : Set Plane} {n : Cover} {η b l u δ : ℝ}
    (hB : MeasurableSet B) (hη : 0 < η) (hb : 0 < b) (hδ : 0 < δ) (hgap : 3*δ < u-l)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < η → ‖z.2‖ < η →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C)) (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hangular : (∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      (planarWedgeCoordinates y).2 ∈ Ioo (l-δ) (u+δ) →
      (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ Ioo l u)) ∨
      (∀ᵐ y : Plane ∂volume, (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      (planarWedgeCoordinates y).2 ∈ Ioo (l-δ) (u+δ) →
      (y ∈ R ⁻¹' Cᶜ ↔ (planarWedgeCoordinates y).2 ∈ Ioo l u)))
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x) : False := by
  obtain ⟨r,hρr,hr1,hr⟩ := exists_normal_sphere_null_radius ν (show (1/2 : ℝ) < 1 by norm_num)
  have hr0 : 0 < r := by linarith
  have hpr := heq r hr0 hr1.le
  have hclosed := coverLocalPerimeter_closedBall_eq_ball_of_normal hr1.le hr hpr hflux
  have hmass : coverLocalPerimeter B (Metric.closedBall (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.closedBall (0 : Cover) r} := by
    rw [hclosed,hpr,measure_congr (normal_closedBall_ae_eq_ball hr)]
  let Q := prismFrame n R
  have hQO : Q ⁻¹' Metric.closedBall (0 : Cover) r = Metric.closedBall (0 : Cover) r := by
    rw [Q.preimage_closedBall,map_zero]
  have hQK : Q ⁻¹' Metric.ball (0 : Cover) (1/2) = Metric.ball (0 : Cover) (1/2) := by
    rw [Q.preimage_ball,map_zero]
  have hmin' := coverLocalPerimeter_isometry_minimizing Q hB
    (normal_radius_local_minimizing (by norm_num : (0 : ℝ) < 1/2) hρr hr1.le hr hpr hflux hmin)
  have hmass' := coverLocalPerimeter_isometry_normal Q hB Metric.isClosed_closedBall.measurableSet hmass
  have hflux' : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      tsupport F ⊆ Q ⁻¹' Metric.closedBall (0 : Cover) r → (∀ x, ‖F x‖ ≤ 1) →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν.map (pullbackBlowupNormal Q) : Measure BlowupNormalBundle)) =
        ∫ x in Q ⁻¹' B, divergence F x := by
    intro F hF hs hFO hFn
    exact pullbackBlowupNormal_flux Q hB
      (fun G hG _ hGO _ ↦ hflux G hG (hGO.trans (Metric.closedBall_subset_closedBall hr1.le)))
      hF hs hFO hFn
  apply no_minimizing_angular_phase_sector (hB.preimage Q.continuous.measurable)
    (Metric.isClosed_closedBall.measurableSet.preimage Q.continuous.measurable)
    (by norm_num : (0 : ℝ) < 1/2) hη hb hδ hgap
    (by rw [hQK]) (by rw [hQO]; exact (Metric.ball_subset_ball hρr.le).trans Metric.ball_subset_closedBall)
    hmin' ?_ hmass' hflux'
  rcases hangular with hm|hm
  · exact Or.inl (prismFrame_angular_sector_model hprod R hm)
  · apply Or.inr
    apply prismFrame_angular_sector_model (B := Bᶜ) (C := Cᶜ) (n := n) (η := η) ?_ R hm
    filter_upwards [hprod] with z hz hza hzp
    exact not_congr (hz hza hzp)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
lemma slopeScalarTest_tsupport_rectangle_wide {χ ψ : ℝ → ℝ} {a b w : ℝ}
    (ha : 0 < a) (hw : 0 ≤ w) (hχ : tsupport χ ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-w) w) :
    tsupport (slopeScalarTest χ ψ) ⊆
      planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-(w*b)) (w*b)) := by
  apply closure_minimal _ ((isClosed_Icc.prod isClosed_Icc).preimage
    planeProductCoordinates.continuous)
  intro x hx
  have hn : χ (planeProductCoordinates x).1 ≠ 0 ∧
      ψ ((planeProductCoordinates x).2/(planeProductCoordinates x).1) ≠ 0 :=
    mul_ne_zero_iff.mp hx
  have hs := hχ (subset_tsupport _ hn.1)
  have ht := hψ (subset_tsupport _ hn.2)
  have hs0 : 0 < (planeProductCoordinates x).1 := ha.trans_le hs.1
  have ht' : |(planeProductCoordinates x).2/(planeProductCoordinates x).1| ≤ w := abs_le.mpr ht
  rw [abs_div,abs_of_pos hs0,div_le_iff₀ hs0] at ht'
  exact ⟨hs,abs_le.mp (ht'.trans (mul_le_mul_of_nonneg_left hs.2 hw))⟩

lemma slopeScalarTest_hasCompactSupport_wide {χ ψ : ℝ → ℝ} {a b w : ℝ}
    (ha : 0 < a) (hw : 0 ≤ w) (hχ : tsupport χ ⊆ Icc a b)
    (hψ : tsupport ψ ⊆ Icc (-w) w) : HasCompactSupport (slopeScalarTest χ ψ) :=
  (planeProductCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset isClosed_closure
      (slopeScalarTest_tsupport_rectangle_wide ha hw hχ hψ)

theorem planar_slope_flux_wide {C : Set Plane} {D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) {a b w : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (hprod : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D))
    {χ ψ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsχ : tsupport χ ⊆ Ioo a b) (hsψ : tsupport ψ ⊆ Ioo (-w) w) :
    (∫ x in C, fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector) =
      (∫ s : ℝ, χ s)*(∫ t in D, deriv ψ t) := by
  have hχ0 : 0 ∉ tsupport χ := fun hh ↦ (ha.trans (hsχ hh).1).false
  have hf := slopeScalarTest_contDiff hχ hψ hχ0
  have hfs := slopeScalarTest_hasCompactSupport_wide ha hw
    (hsχ.trans Ioo_subset_Icc_self) (hsψ.trans Ioo_subset_Icc_self)
  let G : Plane → ℝ := C.indicator
    (fun x ↦ fderiv ℝ (slopeScalarTest χ ψ) x slopeVerticalVector)
  have hi : Integrable G volume :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfs.fderiv_apply ℝ slopeVerticalVector)).indicator hC
  have hL : MeasurePreserving planeProductCoordinates.symm :=
    planeProductCoordinates_measurePreserving.symm
      planeProductCoordinates.toHomeomorph.toMeasurableEquiv
  have hLi := (hL.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hsplit := Measure.ae_ae_of_ae_prod hprod
  have he : (fun s : ℝ ↦ ∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =ᵐ[volume]
      (fun s : ℝ ↦ χ s*(∫ t in D, deriv ψ t)) := by
    filter_upwards [hsplit] with s hs
    by_cases hsI : s ∈ Ioo a b
    · have hs0 : 0 < s := ha.trans hsI.1
      have hscale : (∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =
          s*(∫ t : ℝ, G (planarWedgeChart (s,t))) := by
        change (∫ y : ℝ, G (planeProductCoordinates.symm (s,y))) =
          s*(∫ t : ℝ, G (planeProductCoordinates.symm (s,s*t)))
        rw [Measure.integral_comp_mul_left (fun y : ℝ ↦ G (planeProductCoordinates.symm (s,y))) s,
          abs_of_pos (inv_pos.mpr hs0),smul_eq_mul]
        rw [mul_inv_cancel_left₀ hs0.ne']
      rw [hscale]
      have hinner : (fun t : ℝ ↦ G (planarWedgeChart (s,t))) =ᵐ[volume]
          (fun t : ℝ ↦ (χ s/s)*D.indicator (deriv ψ) t) := by
        filter_upwards [hs] with t ht
        have hd : fderiv ℝ (slopeScalarTest χ ψ) (planarWedgeChart (s,t))
            slopeVerticalVector = (χ s/s)*deriv ψ t := by
          rw [slopeScalarTest_vertical_derivative hχ hψ hχ0]
          simp [planarWedgeChart,mul_div_cancel_left₀ _ hs0.ne']
        by_cases htI : t ∈ Ioo (-w) w
        · by_cases htD : t ∈ D
          · simp only [G,indicator_of_mem ((ht hsI htI).mpr htD),indicator_of_mem htD,hd]
          · simp only [G,indicator_of_notMem htD,mul_zero,
              indicator_of_notMem (mt (ht hsI htI).mp htD)]
        · have hz : deriv ψ t = 0 := deriv_of_notMem_tsupport (fun hh ↦ htI (hsψ hh))
          simp only [hz,mul_zero] at hd
          by_cases htD : t ∈ D <;> by_cases htC : planarWedgeChart (s,t) ∈ C <;>
            simp [G,htD,htC,hd,hz]
      rw [integral_congr_ae hinner,integral_const_mul,integral_indicator hD]
      field_simp
    · have hz : χ s = 0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hsI (hsχ hh))
      rw [hz,zero_mul]
      apply integral_eq_zero_of_ae
      apply ae_of_all
      intro y
      have hd : fderiv ℝ (slopeScalarTest χ ψ) (planeProductCoordinates.symm (s,y))
          slopeVerticalVector = 0 := by
        rw [slopeScalarTest_vertical_derivative hχ hψ hχ0]
        simp [hz]
      by_cases hy : planeProductCoordinates.symm (s,y) ∈ C <;> simp [G,hy,hd]
  rw [← integral_indicator hC]
  change (∫ x : Plane, G x) = _
  rw [← hL.integral_comp planeProductCoordinates.symm.toHomeomorph.measurableEmbedding G]
  rw [Measure.volume_eq_prod] at hLi ⊢
  change Integrable (fun z : ℝ × ℝ ↦ G (planeProductCoordinates.symm z)) (volume.prod volume) at hLi
  rw [integral_prod _ hLi,integral_congr_ae he,integral_mul_const]

theorem planar_cone_slope_section_wide {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {a b w : ℝ} (ha : 0 < a) (hab : a < b)
    (hchart : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo (-w) w,
      planarWedgeChart (s,t) ∈ Metric.ball (0 : Plane) (1/16)) :
    ∃ D : Set ℝ, MeasurableSet D ∧ ∀ᵐ z : ℝ × ℝ ∂volume,
      z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D) := by
  have hwm : Measurable planarWedgeChart := planarWedgeChart_quasiMeasurePreserving.measurable
  have hm : MeasurableSet {z : Plane × ℝ | 0 < z.2 →
      z.1 ∈ Metric.ball (0 : Plane) (1/16) →
      z.2 • z.1 ∈ Metric.ball (0 : Plane) (1/16) →
      (z.2 • z.1 ∈ C ↔ z.1 ∈ C)} :=
    (measurableSet_lt measurable_const measurable_snd).imp
      ((Metric.isOpen_ball.measurableSet.preimage measurable_fst).imp
        ((Metric.isOpen_ball.measurableSet.preimage (measurable_snd.smul measurable_fst)).imp
          ((hC.preimage (measurable_snd.smul measurable_fst)).iff
            (hC.preimage measurable_fst))))
  have hx : ∀ᵐ y : Plane ∂volume, ∀ᵐ c : ℝ ∂volume,
      0 < c → y ∈ Metric.ball (0 : Plane) (1/16) →
      c • y ∈ Metric.ball (0 : Plane) (1/16) → (c • y ∈ C ↔ y ∈ C) := by
    apply (Measure.ae_ae_comm hm).mpr
    apply ae_of_all
    intro c
    by_cases hc0 : 0 < c
    · exact (planar_cone_all_positive_scales hc hc0).mono (fun _ h _ ↦ h)
    · exact ae_of_all _ (fun _ h ↦ (hc0 h).elim)
  have hsplit := Measure.ae_ae_of_ae_prod (planarWedgeChart_quasiMeasurePreserving.ae hx)
  have hrel : ∀ᵐ s : ℝ ∂volume, ∀ᵐ t : ℝ ∂volume, ∀ᵐ r : ℝ ∂volume,
      s ∈ Ioo a b → r ∈ Ioo a b → t ∈ Ioo (-w) w →
      (planarWedgeChart (r,t) ∈ C ↔ planarWedgeChart (s,t) ∈ C) := by
    filter_upwards [hsplit] with s hs
    filter_upwards [hs] with t ht
    by_cases hsI : s ∈ Ioo a b
    · have hs0 : 0 < s := ha.trans hsI.1
      have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
        (inv_ne_zero hs0.ne')
      filter_upwards [hq.ae ht] with r hr _ hrI htI
      simp only [smul_eq_mul] at hr
      have hcp : 0 < s⁻¹*r := mul_pos (inv_pos.mpr hs0) (ha.trans hrI.1)
      have he : (s⁻¹*r) • planarWedgeChart (s,t) = planarWedgeChart (r,t) := by
        rw [planarWedgeChart_smul]
        congr 1
        field_simp
      have hh := hr hcp (hchart s hsI t htI)
      rw [he] at hh
      exact hh (hchart r hrI t htI)
    · exact ae_of_all _ (fun _ hs' ↦ (hsI hs').elim)
  have hpos : (volume : Measure ℝ) (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  obtain ⟨s,hsI,hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae hrel)
  let D : Set ℝ := {t | planarWedgeChart (s,t) ∈ C}
  have hD : MeasurableSet D := hC.preimage (hwm.comp (measurable_const.prodMk measurable_id))
  refine ⟨D,hD,?_⟩
  have hm' : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Ioo a b → z.1 ∈ Ioo (-w) w →
      (planarWedgeChart (z.2,z.1) ∈ C ↔ z.1 ∈ D)} :=
    (measurableSet_Ioo.preimage measurable_snd).imp
      ((measurableSet_Ioo.preimage measurable_fst).imp
        ((hC.preimage (hwm.comp measurable_swap)).iff (hD.preimage measurable_fst)))
  apply (Measure.ae_prod_iff_ae_ae (hm'.preimage measurable_swap)).mpr
  apply (Measure.ae_ae_comm hm').mp
  filter_upwards [hs] with t ht
  filter_upwards [ht] with r hr hrI htI
  exact hr hsI hrI htI

theorem planar_slope_directional_bound_wide {C : Set Plane} {D : Set ℝ}
    (hC : MeasurableSet C) (hD : MeasurableSet D) {a b w : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (hprod : ∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
      (planarWedgeChart z ∈ C ↔ z.2 ∈ D))
    (hrect : planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-(w*b)) (w*b)) ⊆
      Metric.closedBall (0 : Plane) (1/32))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hsχ : tsupport χ ⊆ Ioo a b) (hbχ : ∀ t, |χ t| ≤ 1)
    (hJ : 0 < ∫ t : ℝ, χ t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) →
      |∫ t in D, deriv ψ t| ≤ L := by
  refine ⟨K/(∫ t : ℝ, χ t),div_nonneg hK hJ.le,?_⟩
  intro ψ hψ hsψ hbψ
  have hχ0 : 0 ∉ tsupport χ := fun hh ↦ (ha.trans (hsχ hh).1).false
  have hh := hbv (slopeScalarTest χ ψ) (slopeScalarTest_contDiff hχ hψ hχ0)
    ((slopeScalarTest_tsupport_rectangle_wide ha hw (hsχ.trans Ioo_subset_Icc_self)
      (hsψ.trans Ioo_subset_Icc_self)).trans hrect)
    (slopeScalarTest_bound hbχ hbψ) slopeVerticalVector slopeVerticalVector_norm
  rw [planar_slope_flux_wide hC hD ha hw hprod hχ hψ hsχ hsψ,abs_mul,abs_of_pos hJ] at hh
  exact (le_div_iff₀ hJ).mpr (by simpa only [mul_comm] using hh)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma slope_rectangle_ball_wide {a b w : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (hb : ‖planeProductCoordinates.symm.toContinuousLinearMap‖*((w+1)*b) ≤ (1/32 : ℝ)) :
    planeProductCoordinates ⁻¹' (Icc a b ×ˢ Icc (-(w*b)) (w*b)) ⊆
      Metric.closedBall (0 : Plane) (1/32) := by
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  have hb0 : 0 ≤ b := (ha.trans_le hx.1.1).le.trans hx.1.2
  have hnorm : ‖planeProductCoordinates x‖ ≤ (w+1)*b := by
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs,abs_of_pos (ha.trans_le hx.1.1)]
      exact hx.1.2.trans (by nlinarith)
    · rw [Real.norm_eq_abs]
      exact (abs_le.mpr hx.2).trans (by nlinarith)
  calc
    ‖x‖ = ‖planeProductCoordinates.symm (planeProductCoordinates x)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
    _ ≤ ‖planeProductCoordinates.symm.toContinuousLinearMap‖*‖planeProductCoordinates x‖ :=
      planeProductCoordinates.symm.toContinuousLinearMap.le_opNorm (planeProductCoordinates x)
    _ ≤ ‖planeProductCoordinates.symm.toContinuousLinearMap‖*((w+1)*b) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ _ := hb

theorem planar_cone_angular_dual_bv_wide {C : Set Plane} (hC : MeasurableSet C)
    {w : ℝ} (hw : 0 ≤ w)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K) :
    ∃ (a b L : ℝ) (D : Set ℝ), 0 < a ∧ a < b ∧
      ‖planeProductCoordinates.symm.toContinuousLinearMap‖*((w+1)*b) ≤ (1/32 : ℝ) ∧ 0 ≤ L ∧ MeasurableSet D ∧
      (∀ᵐ z : ℝ × ℝ ∂volume, z.1 ∈ Ioo a b → z.2 ∈ Ioo (-w) w →
        (planarWedgeChart z ∈ C ↔ z.2 ∈ D)) ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) →
        |∫ t in D, deriv ψ t| ≤ L := by
  let N : ℝ := ‖planeProductCoordinates.symm.toContinuousLinearMap‖
  let b : ℝ := 1/(128*(N+1)*(w+1))
  have hN : 0 ≤ N := norm_nonneg _
  have hb : 0 < b := by dsimp [b]; positivity
  have hNb : N*((w+1)*b) ≤ 1/32 := by
    dsimp [b]
    rw [mul_one_div,← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hN hw]
  have ha : 0 < b/4 := div_pos hb (by norm_num)
  have hab : b/4 < b := by linarith
  have hrect := slope_rectangle_ball_wide ha hw hNb
  have hchart (s : ℝ) (hs : s ∈ Ioo (b/4) b) (t : ℝ) (ht : t ∈ Ioo (-w) w) :
      planarWedgeChart (s,t) ∈ Metric.ball (0 : Plane) (1/16) := by
    apply (Metric.closedBall_subset_ball (by norm_num : (1/32 : ℝ)<1/16))
    apply hrect
    change (planeProductCoordinates (planeProductCoordinates.symm (s,s*t))).1 ∈ Icc (b/4) b ∧
      (planeProductCoordinates (planeProductCoordinates.symm (s,s*t))).2 ∈ Icc (-(w*b)) (w*b)
    rw [ContinuousLinearEquiv.apply_symm_apply]
    constructor
    · exact ⟨hs.1.le,hs.2.le⟩
    · have hs0 : 0 < s := ha.trans hs.1
      have hst : |s*t| ≤ w*b := by
        rw [abs_mul,abs_of_pos hs0]
        calc
          s*|t| ≤ s*w := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1.le,ht.2.le⟩) hs0.le
          _ ≤ w*b := by nlinarith [mul_le_mul_of_nonneg_left hs.2.le hw]
      exact abs_le.mp hst
  obtain ⟨D,hD,hprod⟩ := planar_cone_slope_section_wide hC hc ha hab hchart
  let χ : ContDiffBump (b/2) := {
    rIn := b/16
    rOut := b/8
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hsχ : tsupport (χ : ℝ → ℝ) ⊆ Ioo (b/4) b := by
    rw [χ.tsupport_eq,Real.closedBall_eq_Icc]
    intro t ht
    change b/2-b/8 ≤ t ∧ t ≤ b/2+b/8 at ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨L,hL,hdual⟩ := planar_slope_directional_bound_wide hC hD ha hw hprod hrect hK hbv
    χ.contDiff hsχ (fun t ↦ by rw [abs_of_nonneg χ.nonneg]; exact χ.le_one) χ.integral_pos
  exact ⟨b/4,b,L,D,ha,hab,hNb,hL,hD,hprod,hdual⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma scaled_test_deriv {w : ℝ} (hw : 0 < w) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (t : ℝ) :
    deriv (fun s ↦ ψ (w⁻¹*s)) (w*t) = w⁻¹*deriv ψ t := by
  have hd := ((hψ.differentiable (by simp)) (w⁻¹*(w*t))).hasDerivAt.comp (w*t)
    ((hasDerivAt_id (w*t)).const_mul w⁻¹)
  simpa only [Function.comp_def,id_eq,mul_one,inv_mul_cancel_left₀ hw.ne',mul_comm] using hd.deriv

lemma scaled_setIntegral_deriv {D : Set ℝ} (hD : MeasurableSet D)
    {w : ℝ} (hw : 0 < w) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∫ t in (fun s : ℝ ↦ w*s) ⁻¹' D, deriv ψ t) =
      ∫ t in D, deriv (fun s ↦ ψ (w⁻¹*s)) t := by
  let φ : ℝ → ℝ := fun s ↦ ψ (w⁻¹*s)
  let g := D.indicator (deriv φ)
  have he (t : ℝ) : g (w*t) = w⁻¹*((fun s : ℝ ↦ w*s) ⁻¹' D).indicator (deriv ψ) t := by
    by_cases ht : w*t ∈ D
    · simp only [g,indicator_of_mem ht,scaled_test_deriv hw hψ,φ,
        indicator_of_mem (show t ∈ (fun s : ℝ ↦ w*s) ⁻¹' D from ht)]
    · simp only [g,indicator_of_notMem ht,
        indicator_of_notMem (show t ∉ (fun s : ℝ ↦ w*s) ⁻¹' D from ht),mul_zero]
  have hm : Measurable (fun t : ℝ ↦ w*t) := measurable_const.mul measurable_id
  have hi := Measure.integral_comp_mul_left g w
  simp_rw [he] at hi
  rw [integral_const_mul,integral_indicator (hD.preimage hm),
    abs_of_pos (inv_pos.mpr hw),smul_eq_mul] at hi
  have hc := mul_left_cancel₀ (inv_ne_zero hw.ne') hi
  simpa only [g,integral_indicator hD] using hc

lemma angular_dual_bv_rescale {D : Set ℝ} (hD : MeasurableSet D)
    {w L : ℝ} (hw : 0 < w)
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) → |∫ t in D, deriv ψ t| ≤ L) :
    ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-1 : ℝ) 1 → (∀ t, |ψ t| ≤ 1) →
      |∫ t in (fun s : ℝ ↦ w*s) ⁻¹' D, deriv ψ t| ≤ L := by
  intro ψ hψ hsψ hbψ
  rw [scaled_setIntegral_deriv hD hw hψ]
  apply hdual
  · exact hψ.comp (contDiff_const.mul contDiff_id)
  · change tsupport (ψ ∘ (Homeomorph.mulLeft₀ w⁻¹ (inv_ne_zero hw.ne'))) ⊆ Ioo (-w) w
    rw [tsupport_comp_eq_preimage]
    intro t ht
    have hh := hsψ ht
    change -1 < w⁻¹*t ∧ w⁻¹*t < 1 at hh
    rw [← div_eq_inv_mul] at hh
    constructor
    · have h := (lt_div_iff₀ hw).mp hh.1
      nlinarith
    · have h := (div_lt_iff₀ hw).mp hh.2
      nlinarith
  · exact fun t ↦ hbψ _

lemma volume_positive_mul_preimage {w : ℝ} (hw : 0 < w) (D : Set ℝ) :
    0 < volume ((fun t : ℝ ↦ w*t) ⁻¹' D) ↔ 0 < volume D := by
  rw [Real.volume_preimage_mul_left hw.ne']
  have hc : 0 < ENNReal.ofReal |w⁻¹| := ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hw.ne'))
  constructor
  · intro hh
    by_contra h
    rw [le_antisymm (not_lt.mp h) (zero_le),mul_zero] at hh
    exact hh.false
  · intro hh
    exact ENNReal.mul_pos hc.ne' hh.ne'

lemma mul_preimage_phase_ball {w : ℝ} (hw : 0 < w) (D : Set ℝ) (x δ : ℝ) :
    (fun t : ℝ ↦ w*t) ⁻¹' (D ∩ Metric.ball (w*x) (w*δ)) =
      ((fun t : ℝ ↦ w*t) ⁻¹' D) ∩ Metric.ball x δ := by
  ext t
  simp only [Set.mem_preimage,Set.mem_inter_iff,Metric.mem_ball,Real.dist_eq,
    ← mul_sub,abs_mul,abs_of_pos hw,mul_lt_mul_iff_right₀ hw]

lemma angularEssentialBoundary_mul_preimage {w : ℝ} (hw : 0 < w) (D : Set ℝ) :
    angularEssentialBoundary ((fun t : ℝ ↦ w*t) ⁻¹' D) =
      (fun t : ℝ ↦ w*t) ⁻¹' angularEssentialBoundary D := by
  ext x
  constructor
  · intro hx δ hδ
    have h := hx (δ/w) (div_pos hδ hw)
    have he : w*(δ/w) = δ := by field_simp
    have hscale (S : Set ℝ) :
        0 < volume (((fun t : ℝ ↦ w*t) ⁻¹' S) ∩ Metric.ball x (δ/w)) ↔
          0 < volume (S ∩ Metric.ball (w*x) δ) := by
      rw [← mul_preimage_phase_ball hw,he,volume_positive_mul_preimage hw]
    exact ⟨(hscale D).mp h.1,(hscale Dᶜ).mp h.2⟩
  · intro hx δ hδ
    have h := hx (w*δ) (mul_pos hw hδ)
    have hscale (S : Set ℝ) :
        0 < volume (((fun t : ℝ ↦ w*t) ⁻¹' S) ∩ Metric.ball x δ) ↔
          0 < volume (S ∩ Metric.ball (w*x) (w*δ)) := by
      rw [← mul_preimage_phase_ball hw,volume_positive_mul_preimage hw]
    exact ⟨(hscale D).mpr h.1,(hscale Dᶜ).mpr h.2⟩

theorem angular_dual_bv_finite_transitions_wide {D : Set ℝ} (hD : MeasurableSet D)
    {w L : ℝ} (hw : 0 < w)
    (hdual : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      tsupport ψ ⊆ Ioo (-w) w → (∀ t, |ψ t| ≤ 1) → |∫ t in D, deriv ψ t| ≤ L) :
    (Icc (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Finite := by
  have hm : Measurable (fun t : ℝ ↦ w*t) := measurable_const.mul measurable_id
  have hfin := angular_dual_bv_finite_transitions
    (hD.preimage hm) (angular_dual_bv_rescale hD hw hdual)
  have him := hfin.image (fun t : ℝ ↦ w*t)
  apply him.subset
  intro x hx
  refine ⟨x/w,⟨?_,?_⟩,?_⟩
  · constructor
    · apply (le_div_iff₀ hw).mpr
      nlinarith [hx.1.1]
    · apply (div_le_iff₀ hw).mpr
      nlinarith [hx.1.2]
  · rw [angularEssentialBoundary_mul_preimage hw]
    simpa only [Set.mem_preimage,mul_div_cancel₀ _ hw.ne'] using hx.2
  · field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma planarWedgeCoordinates_smul {r : ℝ} (hr : r ≠ 0) (y : Plane) :
    planarWedgeCoordinates (r • y) =
      (r * (planarWedgeCoordinates y).1, (planarWedgeCoordinates y).2) := by
  simp only [planarWedgeCoordinates, map_smul, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_inv_rev]
  congr 1
  field_simp

theorem planar_cone_annulus_to_vertex {C : Set Plane} {D : Set ℝ}
    {a b δ ρ : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) ρ → (t⁻¹ • y ∈ C ↔ y ∈ C))
    (hchart : ∀ y : Plane, (planarWedgeCoordinates y).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ → y ∈ Metric.ball (0 : Plane) ρ)
    (hmodel : ∀ᵐ y : Plane ∂volume,
      (planarWedgeCoordinates y).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D)) :
    ∀ᵐ y : Plane ∂volume,
      (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
  have hq (q : ℚ) : ∀ᵐ y : Plane ∂volume,
      1 ≤ (q : ℝ) → (planarWedgeCoordinates ((q : ℝ) • y)).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
    by_cases hq : 1 ≤ (q : ℝ)
    · have hq0 : (q : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
      have hqm := Measure.quasiMeasurePreserving_smul (volume : Measure Plane) hq0
      filter_upwards [hqm.ae (hc q hq),hqm.ae hmodel] with y hcy hmy _ hy hd
      have hcoord := planarWedgeCoordinates_smul hq0 y
      have hd' : |(planarWedgeCoordinates ((q : ℝ) • y)).2| < δ := by
        simpa only [hcoord] using hd
      have he := hcy (hchart _ hy hd')
      rw [inv_smul_smul₀ hq0] at he
      exact he.trans (by simpa only [hcoord] using hmy hy hd')
    · exact ae_of_all _ (fun _ h ↦ (hq h).elim)
  have hall : ∀ᵐ y : Plane ∂volume, ∀ q : ℚ,
      1 ≤ (q : ℝ) → (planarWedgeCoordinates ((q : ℝ) • y)).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < δ →
      (y ∈ C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
    exact ae_all_iff.mpr hq
  filter_upwards [hall] with y hy hs hd
  let s : ℝ := (planarWedgeCoordinates y).1
  have hs0 : 0 < s := hs.1
  have hmax : max 1 (a/s) < b/s := by
    apply max_lt
    · exact (lt_div_iff₀ hs0).mpr (by simpa [s] using hs.2)
    · exact (div_lt_div_iff_of_pos_right hs0).mpr hab
  obtain ⟨q,hql,hqu⟩ := exists_rat_btwn hmax
  have hq1 : 1 ≤ (q : ℝ) := (le_max_left _ _).trans hql.le
  have hq0 : (q : ℝ) ≠ 0 :=
    ne_of_gt ((div_pos ha hs0).trans ((le_max_right _ _).trans_lt hql))
  apply hy q hq1 ?_ hd
  rw [planarWedgeCoordinates_smul hq0]
  constructor
  · exact (div_lt_iff₀ hs0).mp ((le_max_right _ _).trans_lt hql)
  · exact (lt_div_iff₀ hs0).mp hqu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem planar_cone_wide_vertex_section {C : Set Plane} (hC : MeasurableSet C)
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    (R : Plane ≃ₗᵢ[ℝ] Plane) {w : ℝ} (hw : 0 < w) :
    ∃ (b : ℝ) (D : Set ℝ), 0 < b ∧ MeasurableSet D ∧
      (Icc (-(w/4)) (w/4) ∩ angularEssentialBoundary D).Finite ∧
      ∀ᵐ y : Plane ∂volume,
        (planarWedgeCoordinates y).1 ∈ Ioo 0 b →
        |(planarWedgeCoordinates y).2| < w →
        (y ∈ R ⁻¹' C ↔ (planarWedgeCoordinates y).2 ∈ D) := by
  let C' := R ⁻¹' C
  have hC' : MeasurableSet C' := hC.preimage R.continuous.measurable
  have hc' := planar_cone_rotation hc R
  obtain ⟨a,b,L,D,ha,hab,hNb,hL,hD,hprod,hdual⟩ :=
    planar_cone_angular_dual_bv_wide hC' hw.le hc' hK (planar_directional_bv_rotation hbv R)
  have hmodel : ∀ᵐ y : Plane ∂volume,
      (planarWedgeCoordinates y).1 ∈ Ioo a b →
      |(planarWedgeCoordinates y).2| < w →
      (y ∈ C' ↔ (planarWedgeCoordinates y).2 ∈ D) := by
    filter_upwards [planarWedgeCoordinates_quasiMeasurePreserving.ae hprod] with y hy hy1 hy2
    have hnot : (planeProductCoordinates y).1 ≠ 0 := ne_of_gt (ha.trans hy1.1)
    have hh := hy hy1 (abs_lt.mp hy2)
    rwa [planarWedgeChart_coordinates hnot] at hh
  have hchart (y : Plane) (hy1 : (planarWedgeCoordinates y).1 ∈ Ioo a b)
      (hy2 : |(planarWedgeCoordinates y).2| < w) :
      y ∈ Metric.ball (0 : Plane) (1/16) := by
    apply Metric.closedBall_subset_ball (by norm_num : (1/32 : ℝ) < 1/16)
    apply slope_rectangle_ball_wide ha hw.le hNb
    change (planeProductCoordinates y).1 ∈ Icc a b ∧
      (planeProductCoordinates y).2 ∈ Icc (-(w*b)) (w*b)
    have hs0 : 0 < (planeProductCoordinates y).1 := ha.trans hy1.1
    refine ⟨⟨hy1.1.le,hy1.2.le⟩,abs_le.mp ?_⟩
    have he : (planeProductCoordinates y).2 =
        (planeProductCoordinates y).1 * (planarWedgeCoordinates y).2 := by
      simp [planarWedgeCoordinates,hs0.ne']
    rw [he,abs_mul,abs_of_pos hs0]
    calc
      _ ≤ (planeProductCoordinates y).1*w := mul_le_mul_of_nonneg_left hy2.le hs0.le
      _ ≤ w*b := by
        have hyb : (planeProductCoordinates y).1 ≤ b := hy1.2.le
        nlinarith [mul_le_mul_of_nonneg_left hyb hw.le]
  exact ⟨b,D,ha.trans hab,hD,angular_dual_bv_finite_transitions_wide hD hw hdual,
    planar_cone_annulus_to_vertex ha hab hc' hchart hmodel⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma angularEssentialBoundary_compl (D : Set ℝ) :
    angularEssentialBoundary Dᶜ = angularEssentialBoundary D := by
  ext x
  simp only [angularEssentialBoundary,Set.mem_ofPred_eq,compl_compl]
  exact forall_congr' (fun _ ↦ forall_congr' (fun _ ↦ and_comm))

lemma nonempty_interval_two_phases_not_null (D : Set ℝ) {a b : ℝ} (hab : a < b)
    (hD : volume (Ioo a b ∩ D) = 0) (hC : volume (Ioo a b ∩ Dᶜ) = 0) : False := by
  have he : (Ioo a b ∩ D) ∪ (Ioo a b ∩ Dᶜ) = Ioo a b := by
    ext x
    change ((x ∈ Ioo a b ∧ x ∈ D) ∨ (x ∈ Ioo a b ∧ x ∉ D)) ↔ x ∈ Ioo a b
    tauto
  have hh := measure_union_null hD hC
  rw [he,Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hh
  linarith

lemma finite_angular_next_transition {D : Set ℝ} {a b l v : ℝ}
    (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hl : l ∈ Ioo a b) (hv : v ∈ Ioo a b) (hlv : l < v)
    (hvb : v ∈ angularEssentialBoundary D) :
    ∃ u : ℝ, l < u ∧ u ≤ v ∧ u ∈ angularEssentialBoundary D ∧
      Disjoint (Ioo l u) (angularEssentialBoundary D) := by
  classical
  let S : Set ℝ := Ioc l v ∩ angularEssentialBoundary D
  have hS : S.Finite := hfin.subset (by
    intro x hx
    exact ⟨⟨hl.1.le.trans hx.1.1.le,hx.1.2.trans hv.2.le⟩,hx.2⟩)
  have hn : hS.toFinset.Nonempty := ⟨v,by simp only [Finite.mem_toFinset]; exact ⟨⟨hlv,le_rfl⟩,hvb⟩⟩
  let u := hS.toFinset.min' hn
  have hu : u ∈ S := by
    exact (Finite.mem_toFinset hS).mp (Finset.min'_mem hS.toFinset hn)
  refine ⟨u,hu.1.1,hu.1.2,hu.2,?_⟩
  rw [Set.disjoint_left]
  intro x hx hxb
  have hxS : x ∈ hS.toFinset := by
    rw [Finite.mem_toFinset]
    exact ⟨⟨hx.1,hx.2.le.trans hu.1.2⟩,hxb⟩
  exact (not_le_of_gt hx.2) (Finset.min'_le hS.toFinset x hxS)

theorem occupied_adjacent_angular_model {D : Set ℝ} (hD : MeasurableSet D)
    {a b l u : ℝ} (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hl : l ∈ Ioo a b) (hu : u ∈ Ioo a b) (hlu : l < u)
    (hlb : l ∈ angularEssentialBoundary D) (hub : u ∈ angularEssentialBoundary D)
    (hinside : volume (Ioo l u ∩ Dᶜ) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ 3*δ < u-l ∧
      ∀ᵐ t : ℝ ∂volume, t ∈ Ioo (l-δ) (u+δ) →
        (t ∈ D ↔ t ∈ Ioo l u) := by
  obtain ⟨δL,hδL,hjumpL⟩ := finite_angular_transition_is_jump hD hfin hl hlb
  obtain ⟨δU,hδU,hjumpU⟩ := finite_angular_transition_is_jump hD hfin hu hub
  let δ : ℝ := min (min δL δU) ((u-l)/4)
  have hδ : 0 < δ := lt_min (lt_min hδL hδU) (by linarith)
  have hδl : δ ≤ δL := (min_le_left _ _).trans (min_le_left _ _)
  have hδu : δ ≤ δU := (min_le_left _ _).trans (min_le_right _ _)
  have hδg : δ ≤ (u-l)/4 := min_le_right _ _
  have hgap : 3*δ < u-l := by linarith
  have hleft : volume (Ioo (l-δ) l ∩ D) = 0 := by
    rcases hjumpL with hgood|hbad
    · exact measure_mono_null (by intro t ht; exact ⟨⟨by linarith [ht.1.1],ht.1.2⟩,ht.2⟩) hgood.1
    · exfalso
      apply nonempty_interval_two_phases_not_null D (show l < l+δ by linarith)
      · exact measure_mono_null (by intro t ht; exact ⟨⟨ht.1.1,by linarith [ht.1.2]⟩,ht.2⟩) hbad.2
      · exact measure_mono_null (by intro t ht; exact ⟨⟨ht.1.1,by linarith [ht.1.2]⟩,ht.2⟩) hinside
  have hright : volume (Ioo u (u+δ) ∩ D) = 0 := by
    rcases hjumpU with hbad|hgood
    · exfalso
      apply nonempty_interval_two_phases_not_null D (show u-δ < u by linarith)
      · exact measure_mono_null (by intro t ht; exact ⟨⟨by linarith [ht.1.1],ht.1.2⟩,ht.2⟩) hbad.1
      · exact measure_mono_null (by intro t ht; exact ⟨⟨by linarith [ht.1.1],ht.1.2⟩,ht.2⟩) hinside
    · exact measure_mono_null (by intro t ht; exact ⟨⟨ht.1.1,by linarith [ht.1.2]⟩,ht.2⟩) hgood.2
  have hlne : ∀ᵐ t : ℝ ∂volume, t ≠ l := by rw [ae_iff]; simp
  have hune : ∀ᵐ t : ℝ ∂volume, t ≠ u := by rw [ae_iff]; simp
  refine ⟨δ,hδ,hgap,?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hleft,
    measure_eq_zero_iff_ae_notMem.mp hright,measure_eq_zero_iff_ae_notMem.mp hinside,
    hlne,hune] with t htL htU htI htl htu ht
  constructor
  · intro htD
    constructor
    · by_contra h
      exact htL ⟨⟨ht.1,lt_of_le_of_ne (not_lt.mp h) htl⟩,htD⟩
    · by_contra h
      exact htU ⟨⟨lt_of_le_of_ne (not_lt.mp h) htu.symm,ht.2⟩,htD⟩
  · intro hti
    by_contra h
    exact htI ⟨hti,h⟩

theorem adjacent_angular_sector_model {D : Set ℝ} (hD : MeasurableSet D)
    {a b l u : ℝ} (hfin : (Icc a b ∩ angularEssentialBoundary D).Finite)
    (hl : l ∈ Ioo a b) (hu : u ∈ Ioo a b) (hlu : l < u)
    (hlb : l ∈ angularEssentialBoundary D) (hub : u ∈ angularEssentialBoundary D)
    (hadj : Disjoint (Ioo l u) (angularEssentialBoundary D)) :
    ∃ δ : ℝ, 0 < δ ∧ 3*δ < u-l ∧
      ((∀ᵐ t : ℝ ∂volume, t ∈ Ioo (l-δ) (u+δ) → (t ∈ D ↔ t ∈ Ioo l u)) ∨
       (∀ᵐ t : ℝ ∂volume, t ∈ Ioo (l-δ) (u+δ) → (t ∈ Dᶜ ↔ t ∈ Ioo l u))) := by
  rcases connected_angular_phase hD measurableSet_Ioo isPreconnected_Ioo hadj with hempty|hfull
  · have hfin' : (Icc a b ∩ angularEssentialBoundary Dᶜ).Finite := by
      rwa [angularEssentialBoundary_compl]
    have hlb' : l ∈ angularEssentialBoundary Dᶜ := by rwa [angularEssentialBoundary_compl]
    have hub' : u ∈ angularEssentialBoundary Dᶜ := by rwa [angularEssentialBoundary_compl]
    obtain ⟨δ,hδ,hgap,hmod⟩ := occupied_adjacent_angular_model hD.compl hfin' hl hu hlu hlb' hub'
      (by simpa only [compl_compl] using hempty)
    exact ⟨δ,hδ,hgap,Or.inr hmod⟩
  · obtain ⟨δ,hδ,hgap,hmod⟩ := occupied_adjacent_angular_model hD hfin hl hu hlu hlb hub hfull
    exact ⟨δ,hδ,hgap,Or.inl hmod⟩

end CubicTorus

end
end

end

end OAI
