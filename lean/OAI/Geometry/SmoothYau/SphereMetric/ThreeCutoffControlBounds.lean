import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.InverseFrequencyWeightedZero
import OAI.Geometry.SmoothYau.SphereMetric.ExistsThreeScalarProducer

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
lemma threeNormalInv_isOpenMap : IsOpenMap threeNormalInv := by
  intro U hU
  change IsOpen (((chartAt ThreeModel threeProfileCenter).symm ∘ threeNormalEquiv) '' U)
  rw [image_comp]
  exact (chartAt ThreeModel threeProfileCenter).isOpen_image_symm_of_subset_target
    (threeNormalEquiv.toHomeomorph.isOpenMap U hU) (by rw [three_chart_target]; exact subset_univ _)
lemma threeNormalInv_closedBall_closed (r : ℝ) : IsClosed (threeNormalInv '' closedBall 0 r) :=
  ((isCompact_closedBall (0:NormalWaveSpace) r).image threeNormalInv_continuous).isClosed
lemma threeNormalInv_mem_closedBall_iff (y : NormalWaveSpace) (r : ℝ) :
    threeNormalInv y ∈ threeNormalInv '' closedBall 0 r ↔ ‖y‖≤r := by
  rw [threeNormalInv_injective.mem_set_image,mem_closedBall,dist_zero_right]
lemma threeNormalInv_mem_ball_iff (y : NormalWaveSpace) (r : ℝ) :
    threeNormalInv y ∈ threeNormalInv '' ball 0 r ↔ ‖y‖<r := by
  rw [threeNormalInv_injective.mem_set_image,mem_ball,dist_zero_right]
lemma exists_three_radial_cutoff {a b : ℝ} (hab : a<b) :
    ∃ χ : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ χ ∧
      (∀ q, χ q∈Icc (0:ℝ) 1) ∧
      (∀ q∈threeNormalInv '' closedBall 0 a, χ q=1) ∧
      (∀ q∉threeNormalInv '' ball 0 b, χ q=0) := by
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,ThreeModel)) (n:=(⊤:ℕ∞)) (s:=threeNormalInv '' closedBall 0 a)
    (t:=threeNormalInv '' ball 0 b) (threeNormalInv_closedBall_closed a) (by
      rw [(threeNormalInv_isOpenMap _ isOpen_ball).interior_eq]
      exact image_mono (closedBall_subset_ball hab))
  exact ⟨χ,χ.contMDiff,hχrange,fun q hq => hχ1.self_of_nhdsSet q hq,hχ0⟩
lemma three_wave_exterior_germ {u : NormalWaveSpace → ℝ} (hc : HasCompactSupport u)
    {r : ℝ} (hs : tsupport u⊆closedBall 0 r) (k : ℕ) {q : ThreeManifold}
    (hq : q∉threeNormalInv '' closedBall 0 r) :
    threeCoupled threeCouplingRadius k+threeWaveLift u =ᶠ[𝓝 q] threeCoupled threeCouplingRadius k := by
  have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hq (threeWaveLift_tsupport hc hs h))
  filter_upwards [hz] with y hy
  simp only [Pi.add_apply,hy,Pi.zero_apply,add_zero]
lemma three_wave_residual_support (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set ThreeManifold} (hF : IsClosed F) {r : ℝ}
    (hFr : F⊆threeNormalInv '' closedBall 0 r)
    (hext : ∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    {u : NormalWaveSpace → ℝ} (_hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (hs : tsupport u⊆closedBall 0 r) {k : ℕ} (hk : 2 ≤ k) :
    tsupport (fun q => laplaceBeltrami g (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
      productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q)⊆
      threeNormalInv '' closedBall 0 r := by
  apply (threeNormalInv_closedBall_closed r).closure_subset_iff.mpr
  intro q hq
  by_contra hn
  have hg : ∀ᶠ z in 𝓝 q, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) z,
      g.inner z v w=threeBackgroundMetric.inner z v w := by
    filter_upwards [hF.isOpen_compl.mem_nhds (fun hf => hn (hFr hf))] with z hz
    exact hext z hz
  have he := three_wave_exterior_germ hc hs k hn
  have hl := laplaceBeltrami_metric_congr_nhds g threeBackgroundMetric (threeCoupled threeCouplingRadius k) hg
  have hU := threeCoupled_eigen threeCouplingRadius k hk q
  apply hq
  change laplaceBeltrami g (threeCoupled threeCouplingRadius k+threeWaveLift u) q+
    productFrequency k*(threeCoupled threeCouplingRadius k+threeWaveLift u) q=0
  rw [laplaceBeltrami_congr_nhds g he,he.eq_of_nhds,hl]
  linarith
lemma three_clean_conjugating_margin (g : SmoothMetric ThreeModel ThreeManifold)
    (p : ThreeManifold) (hg : ∀ v z : TangentSpace 𝓘(ℝ,ThreeModel) p,
      g.inner p v z=threeBackgroundMetric.inner p v z)
    (k : ℕ) (hk : 1 ≤ k) (hρ : 1/2 ≤ ‖productA p.1‖) (hρu : ‖productA p.1‖ ≤ 3/4)
    (w : ThreeManifold → ℝ) (hwl : 1/2 ≤ w p)
    (hGw : coordinateGradientPair g w w p ≤ 1/4096) :
    (threeCoupled threeCouplingRadius k p)^2*coordinateGradientPair g w w p <
      (w p)^2*coordinateGradientPair g (threeCoupled threeCouplingRadius k) (threeCoupled threeCouplingRadius k) p := by
  let W := ‖productA p.1‖^k
  have hW : 0<W := pow_pos ((by norm_num : (0:ℝ)<1/2).trans_le hρ) k
  have hlower := threeCoupled_clean_gradient_lower k hk p hρ hρu
  rw [←coordinateGradientPair_metric_point_eq g threeBackgroundMetric p hg] at hlower
  have hU := threeCoupled_clean_abs k p hρ
  have hUp : (threeCoupled threeCouplingRadius k p)^2≤4*W^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*W)).mpr hU
    rw [sq_abs] at hh; nlinarith
  have hwl2 : 1/4≤(w p)^2 := by nlinarith
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hK : W^2≤((k:ℝ)*W)^2 := by nlinarith [mul_le_mul_of_nonneg_right hkR hW.le]
  have hsm := mul_le_mul hUp hGw (coordinateGradientPair_nonneg g w p) (by positivity : 0≤4*W^2)
  have hl := mul_le_mul hwl2 hlower (by positivity : 0≤(1/32:ℝ)*((k:ℝ)*W)^2) (sq_nonneg (w p))
  nlinarith [sq_pos_of_pos hW]
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma three_coordinateGradientPair_pos_derivative_ne (g : SmoothMetric E M) (u : M → ℝ)
    (x : M) (hp : 0 < coordinateGradientPair g u u x) :
    fderiv ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0 := by
  intro hz
  simp [coordinateGradientPair,hz] at hp

lemma three_regular_quotient_at_zero (g : SmoothMetric E M) {u w : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u) (hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w)
    (hw0 : ∀ x, w x ≠ 0) (x : M) (hxu : u x=0)
    (hp : 0 < coordinateGradientPair g u u x) :
    fderiv ℝ ((fun q => u q/w q) ∘ (chartAt E x).symm) (chartAt E x x) ≠ 0 := by
  let c := chartAt E x
  have hxt : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hc : c.symm (c x)=x := c.left_inv (mem_chart_source E x)
  have hdu := (contDiffAt_inChart hu x hxt).differentiableAt (by simp)
  have hdw := (contDiffAt_inChart hw x hxt).differentiableAt (by simp)
  have hne : (w ∘ c.symm) (c x) ≠ 0 := by
    simpa only [Function.comp_apply,hc] using hw0 x
  have he := fderiv_fun_mul hdu (hdw.inv hne)
  change fderiv ℝ (fun y => (u ∘ c.symm) y/(w ∘ c.symm) y) (c x) ≠ 0
  simp only [div_eq_mul_inv]
  have he' : fderiv ℝ (fun y => (u ∘ c.symm) y*((w ∘ c.symm) y)⁻¹) (c x) =
      (u ∘ c.symm) (c x) • fderiv ℝ (w ∘ c.symm)⁻¹ (c x)+
      ((w ∘ c.symm) (c x))⁻¹ • fderiv ℝ (u ∘ c.symm) (c x) := he
  rw [he']
  simp only [Function.comp_apply,hc,hxu,zero_smul,zero_add]
  exact smul_ne_zero (inv_ne_zero (hw0 x)) (three_coordinateGradientPair_pos_derivative_ne g u x hp)
end


section
open Set Filter Function Manifold Metric
open scoped Topology ContDiff InnerProductSpace
def ThreeAnnulus (d e : ℝ) : Set ThreeManifold :=
  (threeNormalInv '' closedBall 0 e) \ (threeNormalInv '' ball 0 d)
lemma threeAnnulus_closed (d e : ℝ) : IsClosed (ThreeAnnulus d e) :=
  (threeNormalInv_closedBall_closed e).sdiff (threeNormalInv_isOpenMap _ isOpen_ball)
lemma threeAnnulus_not_inner {c d e : ℝ} (hcd : c<d) {q : ThreeManifold}
    (hq : q∈ThreeAnnulus d e) : q∉threeNormalInv '' closedBall 0 c := by
  intro h
  apply hq.2
  exact image_mono (closedBall_subset_ball hcd) h
lemma threeAnnulus_clean {d e R : ℝ} (heR : e≤R) (hc : ThreeCleanBall R)
    {q : ThreeManifold} (hq : q∈ThreeAnnulus d e) :
    1/2≤‖productA q.1‖ ∧ ‖productA q.1‖≤3/4 := by
  obtain ⟨y,hy,rfl⟩ := hq.1
  exact hc y (closedBall_subset_closedBall heR hy)
theorem three_annular_projection_uniform
    (g : SmoothMetric ThreeModel ThreeManifold)
    {F : Set ThreeManifold} {c d e R : ℝ} (hcd : c<d) (heR : e≤R)
    (hclean : ThreeCleanBall R) (hFc : F⊆threeNormalInv '' closedBall 0 c)
    (hext : ∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
      g.inner q v w=threeBackgroundMetric.inner q v w)
    (tests : List (CoordinateTest ThreeModel ThreeManifold)) (h : ℕ) {D : ℝ} (hD : 0≤D) :
    ∃ C>0, ∀ w : ThreeManifold → ℝ, ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w →
      (∀ q, 1/2≤w q) → (∀ q, w q≤2) →
      (∀ t∈tests, ∀ y∈t.compactSet, ∀ j≤h+1,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel t.center).symm) y‖≤D) →
      (∀ q, coordinateGradientPair g w w q≤1/4096) →
      ∀ {u : NormalWaveSpace → ℝ}, HasCompactSupport u → tsupport u⊆closedBall 0 c →
      ∀ n : ℕ, 1≤n → ∀ t∈tests, ∀ y∈t.compactSet,
      (chartAt ThreeModel t.center).symm y∈ThreeAnnulus d e →
      ∀ i j : CoordIndex ThreeModel, ∀ k≤h,
        ‖iteratedFDeriv ℝ k (chartGradientProjection g
          (fun q => (threeCoupled threeCouplingRadius n+threeWaveLift u) q/w q)
          t.center i j) y‖≤C*(n:ℝ)^k := by
  classical
  let K (t : CoordinateTest ThreeModel ThreeManifold) := t.compactSet ∩
    (chartAt ThreeModel t.center).symm ⁻¹' ThreeAnnulus d e
  have hKt (t : CoordinateTest ThreeModel ThreeManifold) : IsCompact (K t) :=
    t.isCompact.inter_right ((threeAnnulus_closed d e).preimage (three_chart_symm_continuous t.center))
  have hKO (t : CoordinateTest ThreeModel ThreeManifold) : K t⊆(chartAt ThreeModel t.center).target :=
    fun y hy => t.inTarget hy.1
  have hg (t : CoordinateTest ThreeModel ThreeManifold) (y : ThreeModel) (hy : y∈K t)
      (v z : TangentSpace 𝓘(ℝ,ThreeModel) ((chartAt ThreeModel t.center).symm y)) :
      g.inner _ v z=threeBackgroundMetric.inner _ v z :=
    hext _ (fun hf => threeAnnulus_not_inner hcd hy.2 (hFc hf)) v z
  choose C hC hCJ using fun (t : CoordinateTest ThreeModel ThreeManifold) (k : Fin (h+1)) =>
    threeCoupled_conjugate_projection_uniform g t.center (hKt t) (hKO t) (hg t) k.val hD
      (fun y hy => (threeAnnulus_clean heR hclean hy.2).1)
      (fun y hy => (threeAnnulus_clean heR hclean hy.2).2)
  let B := 1+∑ t∈tests.toFinset, ∑ k : Fin (h+1), C t k
  have hB : 0<B := by
    apply add_pos_of_pos_of_nonneg zero_lt_one
    exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun k _ => (hC t k).le))
  have hCB (t : CoordinateTest ThreeModel ThreeManifold) (ht : t∈tests) (k : Fin (h+1)) : C t k≤B := by
    have hk := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin (h+1)))) => (hC t k).le)
      (Finset.mem_univ k)
    have ht' := Finset.single_le_sum (fun t (_ : t∈tests.toFinset) =>
      Finset.sum_nonneg (fun k (_ : k∈(Finset.univ : Finset (Fin (h+1)))) => (hC t k).le))
      (List.mem_toFinset.mpr ht)
    change C t k≤1+_
    linarith
  refine ⟨B,hB,?_⟩
  intro w hw hwl hwu hwJ hwG u hc hs n hn t ht y hy hann i j k hk
  let k' : Fin (h+1) := ⟨k,by omega⟩
  have hK : y∈K t := ⟨hy,hann⟩
  have hw0 : ∀ q, w q≠0 := fun q => ne_of_gt (by linarith [hwl q])
  have hp := hCJ t k' w hw hw0 (fun y _ => hwl _) (fun y _ => hwu _)
    (fun j _ hj y hy => hwJ t ht y hy.1 j (by have := k'.isLt; omega))
    (fun y _ => hwG _) n hn y hK i j
  have he := three_wave_exterior_germ hc hs n (threeAnnulus_not_inner hcd hann)
  have hew : (fun q => (threeCoupled threeCouplingRadius n+threeWaveLift u) q/w q) =ᶠ[𝓝 ((chartAt ThreeModel t.center).symm y)]
      (fun q => threeCoupled threeCouplingRadius n q/w q) := by
    filter_upwards [he] with q hq
    rw [hq]
  have heP := (chartGradientProjection_congr_nhds g t.center (t.inTarget hy) hew i j).iteratedFDeriv ℝ k
  rw [heP.eq_of_nhds]
  exact hp.trans (mul_le_mul_of_nonneg_right (hCB t ht k') (pow_nonneg (Nat.cast_nonneg n) k))
end


open Set Filter Function Manifold Metric BoxIntegral
open scoped Topology ContDiff ENNReal InnerProductSpace

lemma three_cutoff_control_bounds
    (g : SmoothMetric ThreeModel ThreeManifold) (β χ v : ThreeManifold → ℝ)
    (hχrange : ∀ q, χ q ∈ Icc (0:ℝ) 1) {η G Λ : ℝ}
    (hηhalf : η < 1/2) (hvsmall : ∀ q, |v q-1| ≤ η)
    (hGl : G*η < 1/32) (hGgrad : G*η < 1/4096)
    (hΛ : 1 ≤ Λ)
    (hctrl : ∀ q, |weightedLaplacian g β (cutoffFactor χ v) q| ≤ G*η ∧
      Real.sqrt (coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q) ≤ G*η) :
    (∀ q, 1/2 ≤ cutoffFactor χ v q ∧ cutoffFactor χ v q ≤ 2) ∧
    (∀ q, coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) q ≤ 1/4096) ∧
    (∀ q, |Λ⁻¹*cutoffFactor χ v q*weightedLaplacian g β (cutoffFactor χ v) q| ≤ 1/16) := by
  let w := cutoffFactor χ v
  have hwsmall (q : ThreeManifold) : |w q-1| ≤ 1/2 := by
    change |1+χ q*(v q-1)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (hχrange q).1]
    exact (mul_le_mul_of_nonneg_right (hχrange q).2 (abs_nonneg _)).trans
      (by simpa using (hvsmall q).trans hηhalf.le)
  have hwl (q : ThreeManifold) : 1/2 ≤ w q := by have := (abs_le.mp (hwsmall q)).1; linarith
  have hwu (q : ThreeManifold) : w q ≤ 2 := by have := (abs_le.mp (hwsmall q)).2; linarith
  have hwp (q : ThreeManifold) : 0 < w q := by linarith [hwl q]
  refine ⟨fun q => ⟨hwl q,hwu q⟩,?_,?_⟩
  · intro q
    have hp0 := coordinateGradientPair_nonneg g w q
    have hs0 := Real.sqrt_nonneg (coordinateGradientPair g w w q)
    have hs2 := Real.sq_sqrt hp0
    have hsle : Real.sqrt (coordinateGradientPair g w w q) ≤ G*η := (hctrl q).2
    have hs1 : Real.sqrt (coordinateGradientPair g w w q) ≤ 1 := by linarith
    nlinarith
  · intro q
    have hΛ0 : 0 ≤ Λ⁻¹ := inv_nonneg.mpr (zero_le_one.trans hΛ)
    have hΛi : Λ⁻¹ ≤ 1 := by
      simpa using (inv_le_inv₀ (zero_lt_one.trans_le hΛ) (show (0:ℝ)<1 by norm_num)).mpr hΛ
    change |Λ⁻¹*w q*weightedLaplacian g β w q| ≤ _
    rw [abs_mul,abs_mul,abs_of_nonneg hΛ0,abs_of_pos (hwp q)]
    calc
      _ ≤ (1*2)*(G*η) := mul_le_mul (mul_le_mul hΛi (hwu q) (hwp q).le (by norm_num))
        (hctrl q).1 (abs_nonneg _) (by norm_num)
      _ ≤ 1/16 := by linarith

lemma three_cutoff_raw_bounded_by_near_one
    (χ v : ThreeManifold → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ χ)
    (hv : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ v)
    (t : CoordinateTest ThreeModel ThreeManifold) (h : ℕ) {B D η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hB : 0 ≤ B) (hDB : D ≤ B)
    (hctrl : ∀ y ∈ t.compactSet, ∀ k ≤ h,
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘
        (chartAt ThreeModel t.center).symm) y‖ ≤ D*η) :
    ∀ y ∈ t.compactSet, ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (cutoffFactor χ v ∘ (chartAt ThreeModel t.center).symm) y‖ ≤ 1+B := by
  intro y hy j hj
  have hw : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ (cutoffFactor χ v) :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hnear (k : ℕ) (hk : k ≤ h) :
      ‖iteratedFDeriv ℝ k ((fun q => cutoffFactor χ v q-1) ∘ (chartAt ThreeModel t.center).symm) y‖ ≤ B :=
    (hctrl y hy k hk).trans ((mul_le_mul_of_nonneg_right hDB hη0).trans
      (by simpa using mul_le_mul_of_nonneg_left hη1 hB))
  exact raw_jets_of_near_one (chartAt ThreeModel t.center).open_target (t.inTarget hy)
    (fun y hy => (contDiffAt_inChart hw t.center hy).contDiffWithinAt) h hB hnear j hj

theorem exists_three_exact_stage :
    ∃ R : ℝ, 0<R ∧ ThreeCleanBall R ∧ ∃ N : Set (SmoothMetric ThreeModel ThreeManifold),
      IsSmoothNeighborhood threeBackgroundMetric N ∧ threeBackgroundMetric∈N ∧
      ∀ g∈N, ∀ a b : ℝ, 0<a → a<b → b<R/2 →
      ∀ F : Set ThreeManifold, IsClosed F → F⊆threeNormalInv '' closedBall 0 a →
      (∀ q∉F, ∀ v w : TangentSpace 𝓘(ℝ,ThreeModel) q,
        g.inner q v w=threeBackgroundMetric.inner q v w) → ∀ A : ℝ,
      ∀ V : Set (SmoothMetric ThreeModel ThreeManifold), IsSmoothNeighborhood g V →
    ∃ e : ℝ, b<e ∧ e<R/2 ∧ ∃ I : Box (Fin 3), normalWaveEquiv '' Box.Icc I⊆closedBall 0 a ∧
    ∃ partition : TaggedPrepartition I, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J∈partition, 0<ℓ J) ∧ ∃ ε>0,
    ∀ᶠ n : ℕ in atTop, ∃ ĝ∈V, ∃ u : ThreeManifold → ℝ,
      ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ u ∧
      (∀ q, -laplaceBeltrami ĝ u q=productFrequency n*u q) ∧
      (∀ q, u q=0 → fderiv ℝ (u ∘ (chartAt ThreeModel q).symm) (chartAt ThreeModel q q)≠0) ∧
      (∀ q∉threeNormalInv '' closedBall 0 e,
        (∀ v w, ĝ.inner q v w=g.inner q v w) ∧ u q=threeCoupled threeCouplingRadius n q) ∧
      ENNReal.ofReal (A*productWaveFrequency n)<SignTests.signCertificate
        (fun j : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo j.val)
        (fun j => ε/(productWaveFrequency n*ℓ j.val))
        ((u ∘ threeNormalInv) ∘ normalWaveEquiv) := by
  classical
  obtain ⟨R,hR,hclean,N,hN,h0N,hproduce⟩ := exists_three_scalar_producer
  refine ⟨R,hR,hclean,N,hN,h0N,?_⟩
  intro g hg a b ha hab hbR F hF hFa hext A V hV
  let c := (b+R/2)/2
  let d := (c+R/2)/2
  let e := (d+R/2)/2
  have hac : a<c := by dsimp [c]; linarith
  have hcd : c<d := by dsimp [d,c]; linarith
  have hde : d<e := by dsimp [e,d,c]; linarith
  have heR : e<R/2 := by dsimp [e,d,c]; linarith
  have hbe : b<e := by dsimp [e,d,c]; linarith
  have hFc : F⊆threeNormalInv '' closedBall 0 c :=
    hFa.trans (image_mono (closedBall_subset_closedBall hac.le))
  obtain ⟨χ,hχ,hχrange,hχd,hχe⟩ := exists_three_radial_cutoff hde
  obtain ⟨tests,h,δ,hδ,hreal⟩ := cutoff_exactification_in_smooth_neighborhood
    threeModel_finrank g V hV χ hχ
  have hs0 : Module.finrank ℝ ThreeModel<2*(2*(2:ℝ)) := by norm_num [threeModel_finrank]
  let atlas := Classical.choice (nonempty_compactMetricAtlas g 2 hs0)
  let i₀ : CoordIndex ThreeModel := ⟨0,by simp [threeModel_finrank]⟩
  obtain ⟨G,hG,hglobal⟩ := atlas.global_cutoff_raw_controls i₀ χ hχ
  choose D hD hDJ using fun z : CoordinateTest ThreeModel ThreeManifold =>
    cutoffFactor_compact_raw χ hχ z.center z.isCompact z.inTarget (h+1)
  let B := 1+∑ z∈tests.toFinset, D z
  have hB : 0<B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun z _ => (hD z).le))
  have hDB (z : CoordinateTest ThreeModel ThreeManifold) (hz : z∈tests) : D z≤B := by
    have hh := Finset.single_le_sum (fun z (_ : z∈tests.toFinset) => (hD z).le)
      (List.mem_toFinset.mpr hz)
    change D z≤1+_
    linarith
  obtain ⟨C,hC,hproj⟩ := three_annular_projection_uniform g hcd
    (heR.le.trans (by linarith : R/2≤R)) hclean hFc hext tests h (show 0≤1+B by linarith)
  obtain ⟨I,hIa,partition,hpart,ℓ,hℓ,ε,hε,hscalar⟩ := hproduce g hg a b ha hab hbR F hF hFa hext A
  obtain ⟨L,hL,hpacket⟩ := hscalar (tests++atlas.coveringRawTests i₀) (h+2) (h+3)
  let η (n : ℕ) := L*inverseFrequency n^(h+3)
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa [η] using (inverseFrequency_pow_zero (h+3) (by omega)).const_mul L
  have hGη : Tendsto (fun n => G*η n) atTop (𝓝 0) := by simpa using hη.const_mul G
  have hrate := inverseFrequency_weighted_zero L C h
  refine ⟨e,hbe,heR,I,hIa,partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  filter_upwards [hpacket,eventually_ge_atTop (2:ℕ),hη.eventually (gt_mem_nhds hδ),
    hη.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<1/32 by norm_num)),
    hGη.eventually (gt_mem_nhds (show (0:ℝ)<1/4096 by norm_num)),
    hrate.eventually (gt_mem_nhds hδ)] with n hp hn hηδ hηhalf hGl hGgrad hηrate
  obtain ⟨u,hu,huc,hus,hreg,hβ,hz,hpos,hweighted,hβs,hzs,v,hv,hvp,hve,hsmall,hraw,hscore⟩ := hp
  have husc : tsupport u⊆closedBall 0 c := hus.trans ball_subset_closedBall
  let U := threeCoupled threeCouplingRadius n+threeWaveLift u
  let β := intrinsicCorrectionB g (productWaveFrequency n) (productFrequency n) U
  let z := intrinsicCorrectionS g (productWaveFrequency n) (productFrequency n) U
  let w := cutoffFactor χ v
  have hU : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ U :=
    (threeCoupled_smooth _ _).add (threeWaveLift_smooth hu huc)
  have hw : ContMDiff 𝓘(ℝ,ThreeModel) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hη0 : 0≤η n := mul_nonneg hL.le (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) _)
  have hη1 : η n≤1 := by linarith
  have hvhalf (q : ThreeManifold) : |v q-1|≤1/2 := (hsmall q).2.2.trans hηhalf.le
  have hΛ : 1≤productFrequency n := by
    have hnR : (2:ℝ)≤n := by exact_mod_cast hn
    unfold productFrequency; nlinarith
  have hctrl := hglobal β v hβ hv (η n) hη0 hη1
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inr ht)) y hy j (by omega)).2.2)
  obtain ⟨hwb,hwG,hsmallw⟩ := three_cutoff_control_bounds g β χ v hχrange
    hηhalf (fun q => (hsmall q).2.2) hGl hGgrad hΛ hctrl
  have hwl (q) : 1/2≤w q := (hwb q).1
  have hwu (q) : w q≤2 := (hwb q).2
  have hwp (q) : 0<w q := by linarith [hwl q]
  let O := threeNormalInv '' ball 0 d
  let Fout := (threeNormalInv '' closedBall 0 e)ᶜ
  have hO : IsOpen O := threeNormalInv_isOpenMap _ isOpen_ball
  have hFo : IsOpen Fout := (threeNormalInv_closedBall_closed e).isOpen_compl
  have hann {q : ThreeManifold} (hq : q∉O∪Fout) : q∈ThreeAnnulus d e := by
    exact ⟨by simpa only [Fout,mem_compl_iff,not_not] using (not_or.mp hq).2,(not_or.mp hq).1⟩
  have hres := three_wave_residual_support g hF hFc hext hu huc husc hn
  have hcoeffout (q : ThreeManifold) (hq : q∈Fout) : β q=1 ∧ z q=1 := by
    have hnres : q∉tsupport (fun q => laplaceBeltrami g U q+productFrequency n*U q) :=
      fun hh => hq (image_mono (closedBall_subset_closedBall (hcd.trans hde).le) (hres hh))
    exact ⟨sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => β q-1) (fun hh => hnres (hβs hh))),
      sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun q => z q-1) (fun hh => hnres (hzs hh)))⟩
  have hmargin (q : ThreeManifold) (hq : q∉O∪Fout) :
      U q^2*coordinateGradientPair g w w q<w q^2*coordinateGradientPair g U U q := by
    have hannq := hann hq
    have hnot := threeAnnulus_not_inner hcd hannq
    have he := three_wave_exterior_germ huc husc n hnot
    change (threeCoupled threeCouplingRadius n+threeWaveLift u) q^2*_<_
    rw [he.eq_of_nhds,coordinateGradientPair_congr_nhds_cutoff g he]
    exact three_clean_conjugating_margin g q (hext q (fun hf => hnot (hFc hf))) n (by omega)
      (threeAnnulus_clean (heR.le.trans (by linarith : R/2≤R)) hclean hannq).1
      (threeAnnulus_clean (heR.le.trans (by linarith : R/2≤R)) hclean hannq).2 w (hwl q) (hwG q)
  have hwJ (t : CoordinateTest ThreeModel ThreeManifold) (ht : t∈tests)
      (y : ThreeModel) (hy : y∈t.compactSet) (j : ℕ) (hj : j≤h+1) :
      ‖iteratedFDeriv ℝ j (w ∘ (chartAt ThreeModel t.center).symm) y‖≤1+B := by
    apply three_cutoff_raw_bounded_by_near_one χ v hχ hv t (h+1) hη0 hη1 hB.le (hDB t ht)
      (fun y hy => hDJ t v hv y hy (η n) hη0
        (fun k hk => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy k (by omega)).2.2)) y hy j hj
  obtain ⟨ĝ,hĝ,f,hf,hfe,hfU,hfZ,hfsgn,hfout⟩ := hreal β z U v (productFrequency n) O Fout
    hβ hz hU hv hΛ (fun q => (hpos q).1) hχrange hvhalf
    (fun q => (hsmall q).2.1.trans hηhalf.le) hweighted hve hO hFo
    (fun q hq => hχd q (image_mono ball_subset_closedBall hq))
    (fun q hq => hχe q (fun hh => hq (image_mono ball_subset_closedBall hh)))
    hcoeffout hsmallw hmargin
    (η n) C (n:ℝ) hη0 hηδ.le hC.le (by exact_mod_cast (show 1≤n by omega)) hηrate
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j (by omega)).2.1)
    (fun t ht y hy j hj => (hraw t (List.mem_append.mpr (Or.inl ht)) y hy j hj).2.2)
    (fun t ht y hy hout i j k hk => hproj w hw hwl hwu hwJ hwG huc husc n (by omega)
      t ht y hy (hann hout) i j k hk)
  refine ⟨ĝ,hĝ,f,hf,hfe,?_,?_,?_⟩
  · intro q hq
    have hUq := (hfZ q).mp hq
    have he : f=fun q => U q/w q := funext hfU
    rw [he]
    exact three_regular_quotient_at_zero g hU hw (fun q => (hwp q).ne') q hUq (hreg q hUq)
  · intro q hq
    refine ⟨(hfout q hq).1,(hfout q hq).2.trans ?_⟩
    exact (three_wave_exterior_germ huc husc n (fun hh =>
      hq (image_mono (closedBall_subset_closedBall (hcd.trans hde).le) hh))).eq_of_nhds
  · have he : ((f ∘ threeNormalInv) ∘ normalWaveEquiv)=fun y =>
        (w (threeNormalInv (normalWaveEquiv y)))⁻¹*(((U ∘ threeNormalInv) ∘ normalWaveEquiv) y) := by
      funext y
      simp only [Function.comp_apply,hfU,div_eq_mul_inv]
      exact mul_comm _ _
    rw [he,SignTests.signCertificate_pos_mul _ _ _ _ (fun y => inv_pos.mpr (hwp _))]
    exact hscore

end YauCounterexamples
end

end OAI
