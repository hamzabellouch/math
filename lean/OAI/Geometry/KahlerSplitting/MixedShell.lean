import OAI.Geometry.KahlerSplitting.DiskArea

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open scoped Manifold
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open Set
open scoped Manifold ContDiff
open Set MeasureTheory
open Set Metric
open scoped ContDiff
open Set Metric Filter Topology

namespace UniversalCoverSplitting

def complexAnnulus (a b : ℝ) : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}

lemma isOpen_complexAnnulus (a b : ℝ) : IsOpen (complexAnnulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma complexAnnulus_subset_ball (a b : ℝ) : complexAnnulus a b ⊆ ball 0 b :=
  fun _ hz ↦ by simpa using hz.2

lemma complexAnnulus_nonempty {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (complexAnnulus a b).Nonempty := by
  obtain ⟨r,har,hrb⟩ := exists_between hab
  refine ⟨(r:ℂ),?_⟩
  simpa [complexAnnulus,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (ha.trans_lt har)] using And.intro har hrb

lemma isPreconnected_complexAnnulus {a b : ℝ} (ha : 0 ≤ a) :
    IsPreconnected (complexAnnulus a b) := by
  let F : ℝ × ℝ → ℂ := fun p ↦ (p.1:ℂ) * Complex.exp ((p.2:ℂ)*Complex.I)
  have hF : Continuous F := by fun_prop
  have he : F '' (Ioo a b ×ˢ (univ : Set ℝ)) = complexAnnulus a b := by
    ext z
    constructor
    · rintro ⟨⟨r,t⟩,⟨hr,_⟩,rfl⟩
      have hp : 0 < r := ha.trans_lt hr.1
      simpa [complexAnnulus,F,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hp,Complex.norm_exp_ofReal_mul_I] using hr
    · intro hz
      refine ⟨(‖z‖,z.arg),⟨hz,mem_univ _⟩,?_⟩
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← he]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ hF.continuousOn

lemma complexAnnulus_inter_ball {a b R : ℝ} (hR : R ≤ b) :
    complexAnnulus a b ∩ ball (0:ℂ) R = complexAnnulus a R := by
  ext z
  simp only [complexAnnulus,mem_inter_iff,mem_ofPred_eq,mem_ball,dist_zero_right]
  exact ⟨fun h ↦ ⟨h.1.1,h.2⟩,fun h ↦ ⟨⟨h.1,h.2.trans_le hR⟩,h.2⟩⟩

lemma complexAnnulus_union_ball {a b R : ℝ} (haR : a < R) (hRb : R ≤ b) :
    ball (0:ℂ) R ∪ complexAnnulus a b = ball 0 b := by
  ext z
  simp only [complexAnnulus,mem_union,mem_ofPred_eq,mem_ball,dist_zero_right]
  constructor
  · rintro (h|h)
    · exact h.trans_le hRb
    · exact h.2
  · intro hz
    by_cases h : ‖z‖ < R
    · exact Or.inl h
    · exact Or.inr ⟨haR.trans_le (le_of_not_gt h),hz⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma box_shifted_diagonal_germ_unique (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {D : Set ℂ} (hD : IsOpen D) {f g : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) (hg : IsBox S U g) (p : ℂ × ℂ) {v : ℂ} (hv : v ∈ D)
    (hmap : ∀ z ∈ D, separatedAffine p (1,1) (z,z) ∈ U)
    (he : ∀ z ∈ D, f (separatedAffine p (1,1) (z,z)) = g (separatedAffine p (1,1) (z,z))) :
    f =ᶠ[𝓝 (separatedAffine p (1,1) (v,v))] g := by
  let T := separatedAffine p (1,1)
  have hT : Continuous T := continuous_iff_continuousAt.mpr fun z ↦ (separatedAffine_hasFDerivAt p (1,1) z).continuousAt
  let V := (D ×ˢ D) ∩ T ⁻¹' U
  have hVo : IsOpen V := (hD.prod hD).inter (hU.preimage hT)
  have hvV : (v,v) ∈ V := ⟨⟨hv,hv⟩,hmap v hv⟩
  obtain ⟨e,hepos,hesub⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hvV)
  have hprod : ball v e ×ˢ ball v e = ball (v,v) e := ball_prod_same _ _ _
  have hTU : MapsTo T (ball v e ×ˢ ball v e) U := fun z hz ↦ (hesub (hprod ▸ hz)).2
  have hf' := hf.comp_separatedAffine hU p (1,1) hTU
  have hg' := hg.comp_separatedAffine hU p (1,1) hTU
  have hdiag : ∀ z ∈ ball v e, (f ∘ T) (z,z) = (g ∘ T) (z,z) := by
    intro z hz
    exact he z (hesub (hprod ▸ (show (z,z) ∈ ball v e ×ˢ ball v e from ⟨hz,hz⟩))).1.1
  have hfg := box_diagonal_germ_unique h₁ h₂ isOpen_ball hf' hg' hdiag (mem_ball_self hepos)
  let B : ℂ × ℂ → ℂ × ℂ := separatedAffine (-p.1,-p.2) (1,1)
  have hB : Continuous B := continuous_iff_continuousAt.mpr fun z ↦ (separatedAffine_hasFDerivAt (-p.1,-p.2) (1,1) z).continuousAt
  have hBT (z : ℂ × ℂ) : B (T z) = z := by ext <;> simp [B,T,separatedAffine]
  have hTB (z : ℂ × ℂ) : T (B z) = z := by ext <;> simp [B,T,separatedAffine]
  have hlim : Tendsto B (𝓝 (T (v,v))) (𝓝 (v,v)) := by
    have h := hB.continuousAt (x := T (v,v))
    change Tendsto B _ (𝓝 (B (T (v,v)))) at h
    rw [hBT] at h
    exact h
  have hh := hfg.comp_tendsto hlim
  change (fun x ↦ f (T (B x))) =ᶠ[𝓝 (T (v,v))] (fun x ↦ g (T (B x))) at hh
  simpa only [hTB] using hh

lemma IsMixedBox.eqOn_of_slice (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W D : Set ℂ} (hW : IsOpen W) (hD : IsOpen D)
    (hWc : IsPreconnected W) (hDc : IsPreconnected D) {w : ℂ} (hw : w ∈ W)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc (W ×ˢ D) f)
    (hg : IsMixedBox (S := S) c hc (W ×ˢ D) g)
    (he : ∀ z ∈ D, f (w,z) = g (w,z)) : EqOn f g (W ×ˢ D) := by
  intro z hz
  let M := mixedEquiv c hc
  let p : ℂ × ℂ := (c.1*w,c.2*w)
  have hcalc (v : ℂ) : separatedAffine p (1,1) (v,v) = M (w,v) := by
    ext <;> simp [p,M,separatedAffine,mixedEquiv_apply,add_comm]
  have hmo : IsOpen (M '' (W ×ˢ D)) := M.toHomeomorph.isOpenMap _ (hW.prod hD)
  have hh : (f ∘ M.symm) =ᶠ[𝓝 (M (w,z.2))] (g ∘ M.symm) := by
    rw [← hcalc]
    apply box_shifted_diagonal_germ_unique h₁ h₂ hmo hD hf hg p hz.2
    · intro v hv
      rw [hcalc]
      exact mem_image_of_mem M ⟨hw,hv⟩
    · intro v hv
      change f (M.symm (separatedAffine p (1,1) (v,v))) = g (M.symm (separatedAffine p (1,1) (v,v)))
      rw [hcalc,M.symm_apply_apply]
      exact he v hv
  have hevent : f =ᶠ[𝓝 (w,z.2)] g := by
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh.comp_tendsto M.continuous.continuousAt
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hW.prod hD) (hWc.prod hDc)
    hf.holomorphic hg.holomorphic (show (w,z.2) ∈ W ×ˢ D from ⟨hw,hz.2⟩) hevent hz

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem holomorphic_curve_mixed_thickening (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (c : ℂ × ℂ) (hc : c.1 ≠ c.2)
    {D V K : Set ℂ} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) (hVK : V ⊆ K)
    {f : ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f D) (w : ℂ) :
    ∃ e : ℝ, 0 < e ∧ ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball w e ×ˢ V) F ∧ ∀ v ∈ V, F (w,v) = f v := by
  obtain ⟨U,hU,hDU,G,hG,hGdiag⟩ := holomorphic_curve_box_thickening h₁ h₂ hD hf
  obtain ⟨e,he,heU⟩ := diagonal_compact_tube hU hK (fun z hz ↦ hDU z (hKD hz)) c
  let p : ℂ × ℂ := (-c.1*w,-c.2*w)
  let T := separatedAffine p (1,1)
  let M := mixedEquiv c hc
  have hcalc (q : ℂ × ℂ) : T (M q) = (q.2+c.1*(q.1-w),q.2+c.2*(q.1-w)) := by
    ext <;> dsimp [T,p,M,separatedAffine,mixedEquiv_apply] <;> ring
  have hmap : MapsTo T (M '' (ball w e ×ˢ V)) U := by
    rintro z ⟨q,hq,rfl⟩
    rw [hcalc]
    apply heU (q.1-w) _ q.2 (hVK hq.2)
    simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hq.1
  have hGT : IsBox S (M '' (ball w e ×ˢ V)) (G ∘ T) := hG.comp_separatedAffine hU p (1,1) hmap
  refine ⟨e,he,(G ∘ T) ∘ M,isMixedBox_iff.mpr hGT,?_⟩
  intro v hv
  simpa only [Function.comp_apply,hcalc,sub_self,mul_zero,add_zero] using hGdiag v (hKD (hVK hv))

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma glue_mixed_boxes {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {ι : Type*}
    (U : ι → Set (ℂ × ℂ)) (hU : ∀ i, IsOpen (U i))
    (f : ι → ℂ × ℂ → X.Carrier) (hf : ∀ i, IsMixedBox (S := S) c hc (U i) (f i))
    (he : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) (d : X.Carrier) :
    ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (⋃ i, U i) F ∧
      ∀ i, EqOn F (f i) (U i) := by
  let M := mixedEquiv c hc
  have hV (i : ι) : IsOpen (M '' U i) := M.toHomeomorph.isOpenMap _ (hU i)
  have hcompat (i j : ι) : EqOn (f i ∘ M.symm) (f j ∘ M.symm) ((M '' U i) ∩ (M '' U j)) := by
    intro z hz
    apply he i j
    constructor
    · rcases hz.1 with ⟨x,hx,rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
    · rcases hz.2 with ⟨x,hx,rfl⟩
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  obtain ⟨G,hG,hGF⟩ := glue_boxes (fun i ↦ M '' U i) hV (fun i ↦ f i ∘ M.symm) hf hcompat d
  have hd : IsBox S (M '' (⋃ i, U i)) G := by
    rw [image_iUnion]
    exact hG
  refine ⟨G ∘ M,isMixedBox_iff.mpr hd,?_⟩
  intro i z hz
  have h := hGF i (mem_image_of_mem M hz)
  simpa only [Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using h

lemma glue_mixed_boxes_pair {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U V : Set (ℂ × ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f)
    (hg : IsMixedBox (S := S) c hc V g) (he : EqOn f g (U ∩ V)) :
    ∃ F : ℂ × ℂ → X.Carrier, IsMixedBox (S := S) c hc (U ∪ V) F ∧
      EqOn F f U ∧ EqOn F g V := by
  let W : Bool → Set (ℂ × ℂ) := fun i ↦ if i then U else V
  let G : Bool → ℂ × ℂ → X.Carrier := fun i ↦ if i then f else g
  have hWo (i : Bool) : IsOpen (W i) := by cases i <;> assumption
  have hG (i : Bool) : IsMixedBox (S := S) c hc (W i) (G i) := by cases i <;> assumption
  have hGG (i j : Bool) : EqOn (G i) (G j) (W i ∩ W j) := by
    cases i <;> cases j
    · exact fun _ _ ↦ rfl
    · exact fun z hz ↦ (he ⟨hz.2,hz.1⟩).symm
    · exact he
    · exact fun _ _ ↦ rfl
  obtain ⟨F,hF,hFG⟩ := glue_mixed_boxes W hWo G hG hGG (f 0)
  have hWW : (⋃ i, W i) = U ∪ V := by ext z; simp [W,or_comm]
  exact ⟨F,hWW ▸ hF,hFG true,hFG false⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem mixed_shell_fill_of_slice (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) {w : ℂ} (hw : w ∈ W)
    {a R b : ℝ} (ha : 0 ≤ a) (haR : a < R) (hRb : R ≤ b)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    {H : ℂ → X.Carrier} (hH : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) H (ball 0 R))
    (hHs : ∀ v ∈ complexAnnulus a R, H v = Fs (w,v)) :
    ∃ e : ℝ, 0 < e ∧ ball w e ⊆ W ∧ ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F ∧
      EqOn F Fs (ball w e ×ˢ complexAnnulus a b) := by
  obtain ⟨q,haq,hqR⟩ := exists_between haR
  have hq : 0 < q := ha.trans_lt haq
  obtain ⟨e₁,he₁,G,hG,hGH⟩ := holomorphic_curve_mixed_thickening h₁ h₂ c hc
    isOpen_ball (isCompact_closedBall (0:ℂ) q) (closedBall_subset_ball hqR)
    (ball_subset_closedBall (x := (0:ℂ)) (ε := q)) hH w
  obtain ⟨e₂,he₂,h₂W⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hw)
  let e := min e₁ e₂
  have he : 0 < e := lt_min he₁ he₂
  have heG : ball w e ⊆ ball w e₁ := ball_subset_ball (min_le_left _ _)
  have heW : ball w e ⊆ W := (ball_subset_ball (min_le_right _ _)).trans h₂W
  have hG' : IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 q) G := hG.mono (prod_mono heG subset_rfl)
  have hs' : IsMixedBox (S := S) c hc (ball w e ×ˢ complexAnnulus a b) Fs := hs.mono (prod_mono heW subset_rfl)
  have hqa : complexAnnulus a q ⊆ ball 0 q := complexAnnulus_subset_ball _ _
  have hqab : complexAnnulus a q ⊆ complexAnnulus a b := fun _ hz ↦ ⟨hz.1,hz.2.trans_le (hqR.le.trans hRb)⟩
  have hcompat : EqOn G Fs (ball w e ×ˢ complexAnnulus a q) := by
    apply IsMixedBox.eqOn_of_slice h₁ h₂ isOpen_ball (isOpen_complexAnnulus _ _)
      (convex_ball w e).isPreconnected (isPreconnected_complexAnnulus ha) (mem_ball_self he)
      (hG'.mono (prod_mono subset_rfl hqa)) (hs'.mono (prod_mono subset_rfl hqab))
    intro v hv
    exact (hGH v (hqa hv)).trans (hHs v ⟨hv.1,hv.2.trans hqR⟩)
  have hcompat' : EqOn G Fs ((ball w e ×ˢ ball 0 q) ∩ (ball w e ×ˢ complexAnnulus a b)) := by
    intro z hz
    exact hcompat ⟨hz.1.1,hz.2.2.1,by simpa using hz.1.2⟩
  obtain ⟨F,hF,hFG,hFs⟩ := glue_mixed_boxes_pair (isOpen_ball.prod isOpen_ball)
    (isOpen_ball.prod (isOpen_complexAnnulus _ _)) hG' hs' hcompat'
  have hV : (ball w e ×ˢ ball 0 q) ∪ (ball w e ×ˢ complexAnnulus a b) = ball w e ×ˢ ball 0 b := by
    rw [← prod_union,complexAnnulus_union_ball haq (hqR.le.trans hRb)]
  exact ⟨e,he,heW,F,hV ▸ hF,hFs⟩

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem mixed_shell_fill_of_bounded_slices [CompactSpace X.Carrier]
    (g : KahlerMetric X) (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {W : Set ℂ} (hW : IsOpen W) {w : ℂ} (hw : w ∈ W)
    {a R b : ℝ} (ha : 0 ≤ a) (haR : a < R) (hRb : R < b)
    {Fs : ℂ × ℂ → X.Carrier} (hs : IsMixedBox (S := S) c hc (W ×ˢ complexAnnulus a b) Fs)
    (wj : ℕ → ℂ) (_hwj : ∀ j, wj j ∈ W) (hlim : Tendsto wj atTop (𝓝 w))
    (fj : ℕ → ℂ → X.Carrier)
    (hfj : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (fj j) (ball 0 b))
    (heq : ∀ j v, v ∈ complexAnnulus a b → fj j v = Fs (wj j,v))
    (C : ℝ≥0) (hC : ∀ j, curveArea g (fj j) (closedBall 0 R) ≤ (C : ℝ≥0∞)) :
    ∃ e : ℝ, 0 < e ∧ ball w e ⊆ W ∧ ∃ F : ℂ × ℂ → X.Carrier,
      IsMixedBox (S := S) c hc (ball w e ×ˢ ball 0 b) F ∧
      EqOn F Fs (ball w e ×ˢ complexAnnulus a b) := by
  have hR : 0 < R := ha.trans_lt haR
  obtain ⟨σ,hσ,A,hA,hAK,H,hH,hconv⟩ := bounded_curveArea_subsequence_with_removed_limit
    g fj isOpen_ball (isCompact_closedBall (0:ℂ) R)
    (nonempty_closedBall.mpr hR.le) (closedBall_subset_ball hRb) hfj C hC
  rw [interior_closedBall _ hR.ne'] at hH hconv
  have hsmall : complexAnnulus a R ⊆ complexAnnulus a b := fun _ hv ↦ ⟨hv.1,hv.2.trans hRb⟩
  have hcont : ContinuousOn (fun v ↦ Fs (w,v)) (complexAnnulus a R) :=
    hs.holomorphic.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv ↦ ⟨hw,hsmall hv⟩)
  have heoff : EqOn H (fun v ↦ Fs (w,v)) (complexAnnulus a R \ A) := by
    intro v hv
    have hl := hconv.tendsto_at ⟨complexAnnulus_subset_ball _ _ hv.1,hv.2⟩
    have hscont : ContinuousAt Fs (w,v) := hs.holomorphic.continuousOn.continuousAt
      ((hW.prod (isOpen_complexAnnulus _ _)).mem_nhds ⟨hw,hsmall hv.1⟩)
    have hl' : Tendsto (fun j ↦ Fs (wj (σ j),v)) atTop (𝓝 (Fs (w,v))) :=
      hscont.tendsto.comp ((hlim.comp hσ.tendsto_atTop).prodMk_nhds tendsto_const_nhds)
    have hfun : (fun j ↦ fj (σ j) v) = (fun j ↦ Fs (wj (σ j),v)) :=
      funext fun j ↦ heq (σ j) v (hsmall hv.1)
    change Tendsto (fun j ↦ fj (σ j) v) atTop (𝓝 (H v)) at hl
    rw [hfun] at hl
    exact tendsto_nhds_unique hl hl'
  have heall : EqOn H (fun v ↦ Fs (w,v)) (complexAnnulus a R) :=
    heoff.of_subset_closure (hH.continuousOn.mono (complexAnnulus_subset_ball _ _)) hcont
      sdiff_subset ((hA.countable.dense_compl ℂ).open_subset_closure_inter (isOpen_complexAnnulus _ _))
  exact mixed_shell_fill_of_slice h₁ h₂ hW hw ha haR hRb.le hs hH (fun v hv ↦ heall hv)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.mixed_slope_bound (g : KahlerMetric X) {U : Set (ℂ × ℂ)}
    (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (c : ℂ × ℂ) (hc : c.1 ≠ c.2) (C₁ C₂ : ℝ)
    (hC₁ : ∀ x (u : Tangent X x), metricNorm g x (S.projection x u) ≤ C₁ * metricNorm g x u)
    (hC₂ : ∀ x (u : Tangent X x), metricNorm g x (complementaryProjection S x u) ≤ C₂ * metricNorm g x u)
    {z : ℂ × ℂ} (hz : mixedEquiv c hc z ∈ U) :
    metricNorm g ((f ∘ mixedEquiv c hc) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ mixedEquiv c hc) z (1,0)) ≤
    (‖c.1‖ * C₁ + ‖c.2‖ * C₂) * metricNorm g ((f ∘ mixedEquiv c hc) z)
      (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) (f ∘ mixedEquiv c hc) z (0,1)) := by
  let M := mixedEquiv c hc
  have hm := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds hz)) M.differentiableAt.mdifferentiableAt
  rw [hm,mfderiv_eq_fderiv,M.hasFDerivAt.fderiv]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (M z)) := mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (M z)
  change metricNorm g (f (M z)) (D (M (1,0))) ≤
    (‖c.1‖ * C₁ + ‖c.2‖ * C₂) * metricNorm g (f (M z)) (D (M (0,1)))
  have ht : S.projection (f (M z)) (D (1,0)) = D (1,0) ∧
      S.projection (f (M z)) (D (0,1)) = 0 := hf.2 _ hz
  simpa only [M,mixedEquiv_apply,mul_one,zero_add,mul_zero,add_zero,div_one] using
    mixed_direction_metric_norm_le g (f (M z)) (S.projection (f (M z))) D ht.1 ht.2 C₁ C₂
      (hC₁ _) (hC₂ _) c.1 c.2 1 1 one_ne_zero one_ne_zero

theorem exists_uniform_mixed_slope [CompactSpace X.Carrier]
    (g : KahlerMetric X) (S : HolomorphicSplitting X r s) (c : ℂ × ℂ) (hc : c.1 ≠ c.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (ℂ × ℂ)) (f : ℂ × ℂ → X.Carrier),
      IsOpen U → IsMixedBox (S := S) c hc U f → ∀ z ∈ U,
      metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (1,0)) ≤
        C * metricNorm g (f z) (mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z (0,1)) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,h₁,h₂⟩ := g.exists_uniform_splitting_bound S
  refine ⟨‖c.1‖ * C₁ + ‖c.2‖ * C₂,by positivity,?_⟩
  intro U f hU hf z hz
  have hh := IsBox.mixed_slope_bound g ((mixedEquiv c hc).toHomeomorph.isOpenMap _ hU)
    hf c hc C₁ C₂ h₁ h₂ (mem_image_of_mem (mixedEquiv c hc) hz)
  have he : (f ∘ (mixedEquiv c hc).symm) ∘ mixedEquiv c hc = f := by
    funext x
    exact congrArg f ((mixedEquiv c hc).symm_apply_apply x)
  rw [he] at hh
  exact hh

end UniversalCoverSplitting

end

end OAI
