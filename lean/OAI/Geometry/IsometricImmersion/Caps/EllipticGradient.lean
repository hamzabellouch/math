import OAI.Geometry.IsometricImmersion.Caps.EllipticApplication

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def weightedGradient (b : ℝ) (u : Coord → ℝ) (p : Coord) : ℝ :=
  edgeDistance b p ^ 7 * ((coordPartial 0 u p) ^ 2 + (coordPartial 1 u p) ^ 2)

def coordinateSubsetIntegral (S : Set Coord) (f : Coord → ℝ) : ℝ :=
  ∫ q in (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S, f (boxPoint q.1 q.2)

theorem elliptic_gradient_scalar {d D a A x y : ℝ}
    (hd : 0 < d) (hdD : d ≤ D) (ha : 0 < a) (hA : a * d ≤ A) :
    d ^ 7 * (x ^ 2 + y ^ 2) ≤ (D + 1 / a) * (d ^ 6 * (x ^ 2 + A * y ^ 2)) := by
  have hD : 0 ≤ D := hd.le.trans hdD
  have hApos : 0 < A := (mul_pos ha hd).trans_le hA
  have hda : d ≤ A / a := (le_div_iff₀ ha).2 (by nlinarith)
  have hx := mul_le_mul_of_nonneg_right hdD (sq_nonneg x)
  have hy := mul_le_mul_of_nonneg_right hda (sq_nonneg y)
  have hfirst : d * (x ^ 2 + y ^ 2) ≤ D * x ^ 2 + (A / a) * y ^ 2 := by nlinarith
  have hsecond : D * x ^ 2 + (A / a) * y ^ 2 ≤
      (D + 1 / a) * (x ^ 2 + A * y ^ 2) := by
    have hgap : 0 ≤ D * A * y ^ 2 + x ^ 2 / a := by positivity
    have he : (D + 1 / a) * (x ^ 2 + A * y ^ 2) -
        (D * x ^ 2 + (A / a) * y ^ 2) = D * A * y ^ 2 + x ^ 2 / a := by ring
    linarith
  have hm := mul_le_mul_of_nonneg_left (hfirst.trans hsecond) (pow_pos hd 6).le
  nlinarith only [hm]

theorem ellipticWeight_eq_distance_six {b c c1 : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hcc : c ≤ c1) (hd : 0 < edgeDistance b p)
    (hchi : chi p = 1) (hK : c1 * edgeDistance b p ≤ K p) :
    ellipticWeight b c chi K p = edgeDistance b p ^ 6 := by
  have hratio : c ≤ K p / edgeDistance b p := by
    apply (le_div_iff₀ hd).2
    exact (mul_le_mul_of_nonneg_right hcc hd.le).trans hK
  simp [ellipticWeight, hchi, ellipticPhi_one hc hratio]

theorem ellipticCutoff_gradient_pointwise
    {b c c1 g0 D : ℝ} {chi K G1 u : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hcc : c ≤ c1) (hg0 : 0 < g0)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hchi : chi p = 1) (hK : c1 * edgeDistance b p ≤ K p) (hG1 : g0 ≤ G1 p) :
    weightedGradient b u p ≤ (D + 1 / (g0 * c1)) *
      ellipticEnergy (fun q => G1 q * K q) (ellipticWeight b c chi K) u p := by
  have hc1 : 0 < c1 := hc.trans_le hcc
  have hKpos : 0 < K p := (mul_pos hc1 hd).trans_le hK
  have hA : (g0 * c1) * edgeDistance b p ≤ G1 p * K p := by
    have h1 := mul_le_mul_of_nonneg_left hK hg0.le
    have h2 := mul_le_mul_of_nonneg_right hG1 hKpos.le
    nlinarith [h1, h2]
  unfold weightedGradient ellipticEnergy
  rw [ellipticWeight_eq_distance_six hc hcc hd hchi hK]
  exact elliptic_gradient_scalar hd hdD (mul_pos hg0 hc1) hA

variable {tl tr sb st : ℝ} {S : Set Coord} {F G : Coord → ℝ}

theorem coordinateRectangle_closed_area_integrable
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) (Icc tl tr ×ˢ Icc sb st) := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hF.comp (by unfold boxPoint; fun_prop) (fun q hq => boxPoint_mem hq.1 hq.2)
  exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem rectangleIntegral_eq_closed_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F =
      ∫ q in Icc tl tr ×ˢ Icc sb st, F (boxPoint q.1 q.2) := by
  rw [rectangleIntegral_swap ht hs hF]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs,
    ← integral_Icc_eq_integral_Ioc]
  have hi : IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      (Icc tl tr ×ˢ Icc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using coordinateRectangle_closed_area_integrable hF
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun q : ℝ × ℝ => F (boxPoint q.1 q.2)) hi).symm

theorem coordinateSubset_preimage_mem (hSbox : S ⊆ closedRectangle tl tr sb st)
    {q : ℝ × ℝ} (hq : q ∈ (fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :
    q ∈ Icc tl tr ×ˢ Icc sb st := by
  have hp := hSbox hq
  change q.1 ∈ Icc tl tr ∧ q.2 ∈ Icc sb st
  change (boxPoint q.1 q.2) 0 ∈ Icc tl tr ∧ (boxPoint q.1 q.2) 1 ∈ Icc sb st at hp
  have h0 : (boxPoint q.1 q.2) 0 = q.1 := by simp [boxPoint]
  have h1 : (boxPoint q.1 q.2) 1 = q.2 := by simp [boxPoint]
  rwa [h0, h1] at hp

theorem coordinateSubset_integrable
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hSbox : S ⊆ closedRectangle tl tr sb st) :
    IntegrableOn (fun q : ℝ × ℝ => F (boxPoint q.1 q.2))
      ((fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :=
  (coordinateRectangle_closed_area_integrable hF).mono_set
    (fun _ hq => coordinateSubset_preimage_mem hSbox hq)

theorem coordinateSubsetIntegral_mono (hS : MeasurableSet S)
    (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hle : ∀ p ∈ S, F p ≤ G p) :
    coordinateSubsetIntegral S F ≤ coordinateSubsetIntegral S G := by
  have hm : MeasurableSet ((fun q : ℝ × ℝ => boxPoint q.1 q.2) ⁻¹' S) :=
    hS.preimage (by unfold boxPoint; fun_prop)
  apply setIntegral_mono_on (coordinateSubset_integrable hF hSbox)
    (coordinateSubset_integrable hG hSbox) hm
  intro q hq
  exact hle (boxPoint q.1 q.2) hq

theorem coordinateSubsetIntegral_le_rectangle
    (ht : tl ≤ tr) (hs : sb ≤ st) (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hn : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ F p) :
    coordinateSubsetIntegral S F ≤ rectangleIntegral tl tr sb st F := by
  rw [rectangleIntegral_eq_closed_area ht hs hF]
  have hnonneg : (0 : ℝ × ℝ → ℝ) ≤ᵐ[volume.restrict (Icc tl tr ×ˢ Icc sb st)]
      (fun q => F (boxPoint q.1 q.2)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with q hq
    exact hn (boxPoint q.1 q.2) (boxPoint_mem hq.1 hq.2)
  exact setIntegral_mono_set (coordinateRectangle_closed_area_integrable hF) hnonneg
    (Filter.Eventually.of_forall (fun _ hq => coordinateSubset_preimage_mem hSbox hq))

theorem coordinateSubsetIntegral_const_mul (S : Set Coord) (r : ℝ) (F : Coord → ℝ) :
    coordinateSubsetIntegral S (fun p => r * F p) = r * coordinateSubsetIntegral S F := by
  unfold coordinateSubsetIntegral
  exact integral_const_mul r _

theorem restricted_gradient_from_energy
    (ht : tl ≤ tr) (hs : sb ≤ st) (hS : MeasurableSet S)
    (hSbox : S ⊆ closedRectangle tl tr sb st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hn : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ G p)
    {Q : ℝ} (hQ : 0 ≤ Q) (hFG : ∀ p ∈ S, F p ≤ Q * G p) :
    coordinateSubsetIntegral S F ≤ Q * rectangleIntegral tl tr sb st G := by
  calc
    _ ≤ coordinateSubsetIntegral S (fun p => Q * G p) :=
      coordinateSubsetIntegral_mono hS hSbox hF (continuousOn_const.mul hG) hFG
    _ = Q * coordinateSubsetIntegral S G := coordinateSubsetIntegral_const_mul _ _ _
    _ ≤ Q * rectangleIntegral tl tr sb st G :=
      mul_le_mul_of_nonneg_left (coordinateSubsetIntegral_le_rectangle ht hs hSbox hG hn) hQ

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c c1 MK g0 M : ℝ}

theorem threeEdge_elliptic_gradient_bound
    (hL : l0 < l1) (hR : r1 < r0) (hSwidth : a0 < a1)
    (ht : l0 ≤ r0) (hs : a0 ≤ b) (hc : 0 < c) (hcc : c ≤ c1)
    (hMK : 0 ≤ MK) (hg0 : 0 < g0) (hM : 0 ≤ M)
    (hU : IsOpen U) (hK : ContDiffOn ℝ ∞ K U) (hG1 : ContDiffOn ℝ ∞ G1 U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle l0 r0 a0 b ⊆ U)
    (hEq : ∀ p ∈ U, multiplierOperator (fun q => G1 q * K q) B C u p = f p)
    (hKi : ∀ p ∈ closedRectangle l0 r0 a0 b, ∀ i : Fin 2, |coordPartial i K p| ≤ MK)
    (hGlow : ∀ p ∈ closedRectangle l0 r0 a0 b, g0 ≤ G1 p)
    (hAhi : ∀ p ∈ closedRectangle l0 r0 a0 b, |G1 p * K p| ≤ M)
    (hAs : ∀ p ∈ closedRectangle l0 r0 a0 b,
      |coordPartial 1 (fun q => G1 q * K q) p| ≤ M)
    (hBb : ∀ p ∈ closedRectangle l0 r0 a0 b, |B p| ≤ M)
    (hCb : ∀ p ∈ closedRectangle l0 r0 a0 b, |C p| ≤ M)
    (hS : MeasurableSet S) (hSbox : S ⊆ closedRectangle l0 r0 a0 b)
    (hchiOne : ∀ p ∈ S, threeEdgeCutoff l0 l1 r1 r0 a0 a1 p = 1)
    (hdpos : ∀ p ∈ S, 0 < edgeDistance b p)
    (hKell : ∀ p ∈ S, c1 * edgeDistance b p ≤ K p) :
    coordinateSubsetIntegral S (weightedGradient b u) ≤
      (b - a0 + 1 / (g0 * c1)) *
        ((b - a0) ^ 6 * rectangleIntegral l0 r0 a0 b (fun p => (f p) ^ 2) +
          ((b - a0) ^ 6 + ellipticRatioConstant (b - a0) (g0 * c / 2)
            (ellipticCutoffDerivativeConstant c MK
              (threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1)) M) *
            rectangleIntegral l0 r0 a0 b (fun p => (u p) ^ 2)) := by
  let chi := threeEdgeCutoff l0 l1 r1 r0 a0 a1
  let v := ellipticWeight b c chi K
  let vc := ellipticWeightC1 b c chi K
  let A := fun p => G1 p * K p
  have hA : ContDiffOn ℝ ∞ A U := hG1.mul hK
  have hchi : ContDiffOn ℝ ∞ chi U := (threeEdgeCutoff_contDiff _ _ _ _ _ _).contDiffOn
  have hvc : ContDiffOn ℝ 1 vc U :=
    ellipticWeightC1_contDiffOn hc (hchi.of_le (by simp)) (hK.of_le (by simp))
  have hE : ContinuousOn (ellipticEnergy A v u) (closedRectangle l0 r0 a0 b) := by
    obtain ⟨_, _, henergy, _⟩ := elliptic_fields_C1 hU hA hB hC hvc hu
    apply (henergy.mono hbox).congr
    intro p hp
    unfold ellipticEnergy
    rw [show vc p = v p from ellipticWeightC1_eq hp.2.2]
  have hF : ContinuousOn (weightedGradient b u) (closedRectangle l0 r0 a0 b) := by
    have hdist : ContDiffOn ℝ ∞ (edgeDistance b) U :=
      contDiffOn_const.sub (contDiffOn_apply ℝ ℝ 1 U)
    exact ((hdist.pow 7).mul (((partial_contDiffOn hu hU 0).pow 2).add
      ((partial_contDiffOn hu hU 1).pow 2))).continuousOn.mono hbox
  have hEnonneg (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) :
      0 ≤ ellipticEnergy A v u p := by
    apply ellipticEnergy_nonneg A v u p (ellipticWeight_nonneg _ _ _ _ p)
    intro hv
    have hd : p 1 < b := by
      have hpB := hp.2.2
      by_contra hn
      have he : p 1 = b := le_antisymm hpB (le_of_not_gt hn)
      have hz : v p = 0 := ellipticWeight_edge_zero _ _ _ _ p he
      linarith
    have hcurv := ellipticWeight_pos_implies_curvature hc hd hv
    have hKpos : 0 < K p :=
      (mul_pos (by positivity : 0 < c / 2) (sub_pos.mpr hd)).trans hcurv
    exact mul_pos (hg0.trans_le (hGlow p hp)) hKpos
  have hQ : 0 ≤ b - a0 + 1 / (g0 * c1) := by
    have hc1 := hc.trans_le hcc
    have hD := sub_nonneg.mpr hs
    positivity
  have hcomp : coordinateSubsetIntegral S (weightedGradient b u) ≤
      (b - a0 + 1 / (g0 * c1)) * rectangleIntegral l0 r0 a0 b (ellipticEnergy A v u) := by
    apply restricted_gradient_from_energy ht hs hS hSbox hF hE hEnonneg hQ
    intro p hp
    exact ellipticCutoff_gradient_pointwise hc hcc hg0 (hdpos p hp)
      (by unfold edgeDistance; linarith [(hSbox hp).2.1])
      (hchiOne p hp) (hKell p hp) (hGlow p (hSbox hp))
  have henergy := threeEdge_elliptic_energy_bound hL hR hSwidth ht hs hc hMK hg0 hM
    hU hK hG1 hB hC hu hbox hEq hKi hGlow hAhi hAs hBb hCb
  exact hcomp.trans (mul_le_mul_of_nonneg_left henergy hQ)

end SmoothLocal.Weighted

end

end OAI
