import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev MetricTensor (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

theorem metric_invertible {G : MetricTensor E}
    (hG : ∀ v : E, v ≠ 0 → 0 < G v v) : G.IsInvertible := by
  have hinj : Function.Injective G := by
    apply (G : E →ₗ[ℝ] E →L[ℝ] ℝ).ker_eq_bot.mp
    apply LinearMap.ker_eq_bot.mpr
    apply (injective_iff_map_eq_zero G).mpr
    intro v hv
    by_contra hn
    have hp := hG v hn
    exact (lt_irrefl (0 : ℝ)) (by simpa only [hv, zero_apply] using hp)
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (toDual ℝ E).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective G
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj), rfl⟩

def lowerChristoffel (D : E →L[ℝ] MetricTensor E) (v w : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (D v w + D w v - (D.flip v).flip w)

omit [FiniteDimensional ℝ E] in
@[simp] theorem lowerChristoffel_apply (D : E →L[ℝ] MetricTensor E) (v w z : E) :
    lowerChristoffel D v w z = (D v w z + D w v z - D z v w) / 2 := by
  simp [lowerChristoffel, div_eq_mul_inv, mul_comm]

def christoffel (G : E → MetricTensor E) (x v w : E) : E :=
  (G x).inverse (lowerChristoffel (fderiv ℝ G x) v w)

def geodesicSpray (G : E → MetricTensor E) (q : E × E) : E × E :=
  (q.2, -christoffel G q.1 q.2 q.2)

variable {G : E → MetricTensor E} {S : Set E}

theorem metric_christoffel {x : E} (hpos : ∀ v : E, v ≠ 0 → 0 < G x v v)
    (v w z : E) :
    G x (christoffel G x v w) z =
      (fderiv ℝ G x v w z + fderiv ℝ G x w v z - fderiv ℝ G x z v w) / 2 := by
  unfold christoffel
  rw [(metric_invertible hpos).self_apply_inverse, lowerChristoffel_apply]

omit [FiniteDimensional ℝ E] in
theorem derivative_metric_symmetric (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v) {x : E} (hx : x ∈ S)
    (a v w : E) : fderiv ℝ G x a v w = fderiv ℝ G x a w v := by
  have hd := (hG x hx).differentiableAt (hS.mem_nhds hx)
  have h₁ := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  have h₂ := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).clm_apply (hasFDerivAt_const v x)
  have heq : (fun y => G y v w) =ᶠ[𝓝 x] (fun y => G y w v) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact hsym y hy v w
  simpa using congrArg (fun L : E →L[ℝ] ℝ => L a)
    (h₁.unique (h₂.congr_of_eventuallyEq heq))

omit [FiniteDimensional ℝ E] in
theorem christoffel_symmetric (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v) {x : E} (hx : x ∈ S)
    (v w : E) : christoffel G x v w = christoffel G x w v := by
  unfold christoffel
  congr 1
  ext z
  simp only [lowerChristoffel_apply, derivative_metric_symmetric hS hG hsym hx z v w]
  ring

theorem metric_compatible (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {x : E} (hx : x ∈ S) (v w z : E) :
    fderiv ℝ G x v w z = G x (christoffel G x v w) z + G x w (christoffel G x v z) := by
  rw [hsym x hx w, metric_christoffel (hpos x hx), metric_christoffel (hpos x hx)]
  rw [derivative_metric_symmetric hS hG hsym hx v z w,
    derivative_metric_symmetric hS hG hsym hx z v w,
    derivative_metric_symmetric hS hG hsym hx w v z]
  ring

theorem contDiffOn_metric_inverse (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ContDiffOn ℝ ∞ (fun x => (G x).inverse) S := by
  intro x hx
  obtain ⟨e, he⟩ := metric_invertible (hpos x hx)
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G x) := by
    rw [← he]
    exact contDiffAt_map_inverse e
  exact (hi.comp x ((hG x hx).contDiffAt (hS.mem_nhds hx))).contDiffWithinAt

theorem contDiffOn_geodesicSpray (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ContDiffOn ℝ ∞ (geodesicSpray G) (S ×ˢ univ) := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (MetricTensor E) := inferInstance
  let : NormedSpace ℝ (MetricTensor E) := inferInstance
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ G) S :=
    hG.fderiv_of_isOpen hS (by rw [ENat.coe_top_add_one])
  have hD' : ContDiffOn ℝ ∞ (fun q : E × E => fderiv ℝ G q.1) (S ×ˢ univ) :=
    hD.comp contDiffOn_fst (fun q hq => hq.1)
  have hG' : ContDiffOn ℝ ∞ (fun q : E × E => (G q.1).inverse) (S ×ˢ univ) :=
    (contDiffOn_metric_inverse hS hG hpos).comp contDiffOn_fst (fun q hq => hq.1)
  have hA : ContDiffOn ℝ ∞ (fun q : E × E =>
      (fderiv ℝ G q.1).flip q.2) (S ×ˢ univ) :=
    ((ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp_contDiffOn hD').clm_apply
      contDiffOn_snd
  have hB : ContDiffOn ℝ ∞ (fun q : E × E =>
      ((fderiv ℝ G q.1).flip q.2).flip q.2) (S ×ˢ univ) :=
    ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.contDiff.comp_contDiffOn hA).clm_apply
      contDiffOn_snd
  have hC := (hD'.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd
  exact contDiffOn_snd.prodMk (hG'.clm_apply ((hC.add hC |>.sub hB).const_smul (1 / 2 : ℝ))).neg

omit [FiniteDimensional ℝ E] in
theorem hasDerivAt_metric_pairing {c V W : ℝ → E} {t : ℝ} {c' V' W' : E}
    (hG : DifferentiableAt ℝ G (c t)) (hc : HasDerivAt c c' t)
    (hV : HasDerivAt V V' t) (hW : HasDerivAt W W' t) :
    HasDerivAt (fun r => G (c r) (V r) (W r))
      (fderiv ℝ G (c t) c' (V t) (W t) + G (c t) V' (W t) + G (c t) (V t) W') t := by
  have hgc : HasFDerivAt (fun r => G (c r))
      ((fderiv ℝ G (c t)).comp (ContinuousLinearMap.toSpanSingleton ℝ c')) t :=
    HasFDerivAt.comp (f := c) (g := G) t hG.hasFDerivAt hc.hasFDerivAt
  have hgv := hgc.clm_apply hV.hasFDerivAt
  have hd := (hgv.clm_apply hW.hasFDerivAt).hasDerivAt
  convert! hd using 1
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul]
  ring

theorem geodesic_energy_hasDerivAt_zero (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {c V : ℝ → E} {t : ℝ} (ht : c t ∈ S)
    (hc : HasDerivAt c (V t) t)
    (hV : HasDerivAt V (-christoffel G (c t) (V t) (V t)) t) :
    HasDerivAt (fun r => G (c r) (V r) (V r)) 0 t := by
  have hd := hasDerivAt_metric_pairing ((hG (c t) ht).differentiableAt (hS.mem_nhds ht)) hc hV hV
  have hm := metric_compatible hS hG hsym hpos ht (V t) (V t) (V t)
  convert! hd using 1
  simp only [map_neg, neg_apply]
  linarith

theorem geodesic_energy_constant (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {c V : ℝ → E} {a b : ℝ}
    (hmem : ∀ t ∈ Icc a b, c t ∈ S)
    (hc : ∀ t ∈ Icc a b, HasDerivAt c (V t) t)
    (hV : ∀ t ∈ Icc a b, HasDerivAt V (-christoffel G (c t) (V t) (V t)) t) :
    ∀ t ∈ Icc a b, G (c t) (V t) (V t) = G (c a) (V a) (V a) := by
  have hd := fun t ht => geodesic_energy_hasDerivAt_zero hS hG hsym hpos (hmem t ht) (hc t ht) (hV t ht)
  exact constant_of_has_deriv_right_zero (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

omit [FiniteDimensional ℝ E] in
@[simp] theorem christoffel_zero_left (G : E → MetricTensor E) (x v : E) :
    christoffel G x 0 v = 0 := by
  simp [christoffel, lowerChristoffel]

omit [FiniteDimensional ℝ E] in
@[simp] theorem christoffel_zero_right (G : E → MetricTensor E) (x v : E) :
    christoffel G x v 0 = 0 := by
  simp [christoffel, lowerChristoffel]

omit [FiniteDimensional ℝ E] in
@[simp] theorem geodesicSpray_zero (G : E → MetricTensor E) (x : E) :
    geodesicSpray G (x, 0) = 0 := by
  simp [geodesicSpray]

theorem hasFDerivAt_geodesicSpray_zero (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v) {x : E} (hx : x ∈ S) :
    HasFDerivAt (geodesicSpray G)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (x, 0) := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (MetricTensor E) := inferInstance
  let : NormedSpace ℝ (MetricTensor E) := inferInstance
  have hc := (hG x hx).contDiffAt (hS.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fun q : E × E => fderiv ℝ G q.1) (x, 0) :=
    (hc.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).comp (x, 0) contDiffAt_fst
  have hA : HasFDerivAt (fun q : E × E => fderiv ℝ G q.1 q.2 q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    have hd := (((hD.differentiableAt (by simp)).hasFDerivAt.clm_apply hasFDerivAt_snd).clm_apply hasFDerivAt_snd)
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hDflip : ContDiffAt ℝ ∞ (fun q : E × E => (fderiv ℝ G q.1).flip) (x, 0) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.contDiffAt.comp (x, 0) hD
  have hAflip := hDflip.clm_apply contDiffAt_snd
  have hDflip2 : ContDiffAt ℝ ∞ (fun q : E × E => ((fderiv ℝ G q.1).flip q.2).flip) (x, 0) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.contDiff.contDiffAt.comp (x, 0) hAflip
  have hB : HasFDerivAt (fun q : E × E => ((fderiv ℝ G q.1).flip q.2).flip q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    have hd₁ := (hDflip.differentiableAt (by simp)).hasFDerivAt.clm_apply hasFDerivAt_snd
    have hd₂ := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.hasFDerivAt.comp (x, 0) hd₁
    have hd := hd₂.clm_apply hasFDerivAt_snd
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hL : HasFDerivAt (fun q : E × E => lowerChristoffel (fderiv ℝ G q.1) q.2 q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    convert! ((hA.add hA).sub hB).const_smul (1 / 2 : ℝ) using 1
    simp
  have hI : ContDiffAt ℝ ∞ (fun q : E × E => (G q.1).inverse) (x, 0) :=
    ((contDiffOn_metric_inverse hS hG hpos x hx).contDiffAt (hS.mem_nhds hx)).comp (x, 0) contDiffAt_fst
  have hC : HasFDerivAt (fun q : E × E => christoffel G q.1 q.2 q.2) (0 : E × E →L[ℝ] E) (x, 0) := by
    have hd := (hI.differentiableAt (by simp)).hasFDerivAt.clm_apply hL
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    simp [lowerChristoffel]
  convert! hasFDerivAt_snd.prodMk hC.neg using 1
  simp

end
end CoordinateGeometry

open Set Filter
open scoped Topology ContDiff

end

end WeakMTWGlobalSupport

end OAI
