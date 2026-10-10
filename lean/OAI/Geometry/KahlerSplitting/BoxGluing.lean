import OAI.Geometry.KahlerSplitting.HolomorphicIdentity

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
open Set MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open scoped ContDiff
open Set
open scoped Manifold ContDiff
open Set Metric
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold

namespace UniversalCoverSplitting

section Separation
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem separated_eq_diagonal {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {f : ℂ × ℂ → E × F} (hf : DifferentiableOn ℂ f (U ×ˢ U))
    (ht : ∀ z ∈ U ×ˢ U, (fderiv ℂ f z (1,0)).2 = 0 ∧
      (fderiv ℂ f z (0,1)).1 = 0) {u v : ℂ} (hu : u ∈ U) (hv : v ∈ U) :
    f (u,v) = ((f (u,u)).1,(f (v,v)).2) := by
  have h₁ (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hU).mem_nhds (show (u,z) ∈ U ×ˢ U from ⟨hu,hz⟩))).hasFDerivAt
    have hh := hd.fst.comp_hasDerivAt z ((hasDerivAt_const z u).prodMk (hasDerivAt_id z))
    change HasDerivAt (fun w : ℂ ↦ (f (u,w)).1) ((fderiv ℂ f (u,z) (0,1)).1) z at hh
    rwa [(ht (u,z) ⟨hu,hz⟩).2] at hh
  have h₂ (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) 0 z := by
    have hd := (hf.differentiableAt ((hU.prod hU).mem_nhds (show (z,v) ∈ U ×ˢ U from ⟨hz,hv⟩))).hasFDerivAt
    have hh := hd.snd.comp_hasDerivAt z ((hasDerivAt_id z).prodMk (hasDerivAt_const z v))
    change HasDerivAt (fun w : ℂ ↦ (f (w,v)).2) ((fderiv ℂ f (z,v) (1,0)).2) z at hh
    rwa [(ht (z,v) ⟨hz,hv⟩).1] at hh
  apply Prod.ext
  · exact hU.is_const_of_deriv_eq_zero hUc
      (fun z hz ↦ (h₁ z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (h₁ z hz).deriv) hv hu
  · exact hU.is_const_of_deriv_eq_zero hUc
      (fun z hz ↦ (h₂ z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (h₂ z hz).deriv) hu hv
end Separation

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

theorem box_diagonal_germ_unique (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsBox S (U ×ˢ U) f) (hg : IsBox S (U ×ˢ U) g)
    (heq : ∀ z ∈ U, f (z,z) = g (z,z)) {p : ℂ} (hp : p ∈ U) :
    f =ᶠ[𝓝 (p,p)] g := by
  obtain ⟨e,het,_⟩ := exists_splittingChart S h₁ h₂ (f (p,p))
  have hpp : (p,p) ∈ U ×ˢ U := ⟨hp,hp⟩
  have hfn := (hf.1.continuousOn.continuousAt ((hU.prod hU).mem_nhds hpp))
    (e.chart.open_source.mem_nhds het)
  have hgn := (hg.1.continuousOn.continuousAt ((hU.prod hU).mem_nhds hpp))
    (e.chart.open_source.mem_nhds ((heq p hp) ▸ het))
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp (inter_mem ((hU.prod hU).mem_nhds hpp) (inter_mem hfn hgn))
  have hprod : ball p a ×ˢ ball p a = ball (p,p) a := ball_prod_same _ _ _
  have hsub : ball p a ⊆ U := by
    intro z hz
    exact (hasub (hprod ▸ (show (z,p) ∈ ball p a ×ˢ ball p a from ⟨hz,mem_ball_self ha⟩))).1.1
  have hm (z : ℂ × ℂ) (hz : z ∈ ball p a ×ˢ ball p a) :
      f z ∈ e.chart.source ∧ g z ∈ e.chart.source := (hasub (hprod ▸ hz)).2
  have hbsub : ball p a ×ˢ ball p a ⊆ U ×ˢ U := prod_mono hsub hsub
  have hfb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball p a) f from ⟨hf.1.mono hbsub,fun z hz ↦ hf.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).1)
  have hgb := e.box_coordinates (isOpen_ball.prod isOpen_ball)
    (show IsBox S (ball p a ×ˢ ball p a) g from ⟨hg.1.mono hbsub,fun z hz ↦ hg.2 z (hbsub hz)⟩)
    (fun z hz ↦ (hm z hz).2)
  filter_upwards [ball_mem_nhds (p,p) ha] with z hz
  have hzz : z ∈ ball p a ×ˢ ball p a := hprod.symm ▸ hz
  apply e.chart.injOn (hm z hzz).1 (hm z hzz).2
  have hfe := separated_eq_diagonal isOpen_ball (convex_ball p a).isPreconnected hfb.1 hfb.2 hzz.1 hzz.2
  have hge := separated_eq_diagonal isOpen_ball (convex_ball p a).isPreconnected hgb.1 hgb.2 hzz.1 hzz.2
  change (e.chart ∘ f) z = (e.chart ∘ g) z
  rw [hfe,hge]
  simp only [Function.comp_apply,heq z.1 (hsub hzz.1),heq z.2 (hsub hzz.2)]

theorem box_eqOn_of_diagonal (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f g : ℂ × ℂ → X.Carrier}
    (hf : IsBox S (U ×ˢ U) f) (hg : IsBox S (U ×ˢ U) g)
    (heq : ∀ z ∈ U, f (z,z) = g (z,z)) : EqOn f g (U ×ˢ U) := by
  intro z hz
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq (hU.prod hU) (hUc.prod hUc)
    (x := (z.1,z.1)) hf.1 hg.1 ⟨hz.1,hz.1⟩ (box_diagonal_germ_unique h₁ h₂ hU hf hg heq hz.1) hz

theorem SplittingChart.diagonal_box (e : SplittingChart S) {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f U)
    (hmap : MapsTo f U e.chart.source) :
    IsBox S (U ×ˢ U) (fun z : ℂ × ℂ ↦ e.chart.symm ((e.chart (f z.1)).1,(e.chart (f z.2)).2)) ∧
      ∀ z ∈ U, e.chart.symm ((e.chart (f z)).1,(e.chart (f z)).2) = f z := by
  let q := e.chart ∘ f
  have hq : DifferentiableOn ℂ q U :=
    mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hf hmap)
  let G : ℂ × ℂ → Model r × Model s := fun z ↦ ((q z.1).1,(q z.2).2)
  have hd (z : ℂ × ℂ) (hz : z ∈ U ×ˢ U) :
      HasFDerivAt G ((((ContinuousLinearMap.fst ℂ (Model r) (Model s)).comp (fderiv ℂ q z.1)).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)).prod
        (((ContinuousLinearMap.snd ℂ (Model r) (Model s)).comp (fderiv ℂ q z.2)).comp (ContinuousLinearMap.snd ℂ ℂ ℂ))) z := by
    exact ((hq.differentiableAt (hU.mem_nhds hz.1)).hasFDerivAt.fst.comp z hasFDerivAt_fst).prodMk
      ((hq.differentiableAt (hU.mem_nhds hz.2)).hasFDerivAt.snd.comp z hasFDerivAt_snd)
  have hG : DifferentiableOn ℂ G (U ×ˢ U) := fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt
  have hGmap : MapsTo G (U ×ˢ U) e.chart.target := by
    intro z hz
    have h₁' := e.chart.map_source (hmap hz.1)
    have h₂' := e.chart.map_source (hmap hz.2)
    rw [e.product_range] at h₁' h₂' ⊢
    exact ⟨h₁'.1,h₂'.2⟩
  have ht : ∀ z ∈ U ×ˢ U, (fderiv ℂ G z (1,0)).2 = 0 ∧ (fderiv ℂ G z (0,1)).1 = 0 := by
    intro z hz
    rw [(hd z hz).fderiv]
    simp
  refine ⟨e.box_of_coordinate_tangencies (hU.prod hU) hG hGmap ht,?_⟩
  intro z hz
  exact e.chart.left_inv (hmap hz)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.mono {U V : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) (hV : V ⊆ U) : IsBox S V f :=
  ⟨hf.1.mono hV,fun z hz ↦ hf.2 z (hV hz)⟩

theorem glue_boxes {ι : Type*} (U : ι → Set (ℂ × ℂ)) (hU : ∀ i, IsOpen (U i))
    (f : ι → ℂ × ℂ → X.Carrier) (hf : ∀ i, IsBox S (U i) (f i))
    (heq : ∀ i j, EqOn (f i) (f j) (U i ∩ U j)) (d : X.Carrier) :
    ∃ F : ℂ × ℂ → X.Carrier, IsBox S (⋃ i, U i) F ∧ ∀ i, EqOn F (f i) (U i) := by
  classical
  let F : ℂ × ℂ → X.Carrier := fun z ↦ if hz : z ∈ ⋃ i, U i then
    f (mem_iUnion.mp hz).choose z else d
  have hF (i : ι) : EqOn F (f i) (U i) := by
    intro z hz
    have hzU : z ∈ ⋃ i, U i := mem_iUnion.mpr ⟨i,hz⟩
    dsimp only [F]
    rw [dite_eq_left hzU]
    exact heq _ i ⟨(mem_iUnion.mp hzU).choose_spec,hz⟩
  have hlocal (z : ℂ × ℂ) (hz : z ∈ ⋃ i, U i) :
      ∃ i, z ∈ U i ∧ F =ᶠ[𝓝 z] f i := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨i,hi,Filter.mem_of_superset ((hU i).mem_nhds hi) (hF i)⟩
  refine ⟨F,⟨?_,?_⟩,hF⟩
  · intro z hz
    obtain ⟨i,hi,he⟩ := hlocal z hz
    exact (((hf i).1.mdifferentiableAt ((hU i).mem_nhds hi)).congr_of_eventuallyEq he).mdifferentiableWithinAt
  · intro z hz
    obtain ⟨i,hi,he⟩ := hlocal z hz
    have hd := he.mfderiv_eq (I := 𝓘(ℂ,ℂ × ℂ)) (I' := model n)
    rw [he.eq_of_nhds,hd]
    exact (hf i).2 z hi

theorem holomorphic_curve_box_thickening (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → X.Carrier} (hf : MDifferentiableOn 𝓘(ℂ,ℂ) (model n) f D) :
    ∃ U : Set (ℂ × ℂ), IsOpen U ∧ (∀ z ∈ D, (z,z) ∈ U) ∧
      ∃ F : ℂ × ℂ → X.Carrier, IsBox S U F ∧ ∀ z ∈ D, F (z,z) = f z := by
  classical
  have hloc (p : D) : ∃ e : SplittingChart S, ∃ R : ℝ, 0 < R ∧
      ball (p:ℂ) R ⊆ D ∧ MapsTo f (ball (p:ℂ) R) e.chart.source := by
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (f p)
    have hn := (hf.continuousOn.continuousAt (hD.mem_nhds p.property)) (e.chart.open_source.mem_nhds he)
    obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hD.mem_nhds p.property) hn)
    exact ⟨e,R,hR,fun z hz ↦ (hsub hz).1,fun z hz ↦ (hsub hz).2⟩
  choose e R hR hRD hRe using hloc
  let V (p : D) : Set ℂ := ball (p:ℂ) (R p)
  let W (p : D) : Set (ℂ × ℂ) := V p ×ˢ V p
  let F (p : D) : ℂ × ℂ → X.Carrier := fun z ↦
    (e p).chart.symm (((e p).chart (f z.1)).1,((e p).chart (f z.2)).2)
  have hbox (p : D) : IsBox S (W p) (F p) :=
    ((e p).diagonal_box isOpen_ball (hf.mono (hRD p)) (hRe p)).1
  have hdiag (p : D) (z : ℂ) (hz : z ∈ V p) : F p (z,z) = f z :=
    ((e p).diagonal_box isOpen_ball (hf.mono (hRD p)) (hRe p)).2 z hz
  have hcompat (p q : D) : EqOn (F p) (F q) (W p ∩ W q) := by
    let B : Set ℂ := V p ∩ V q
    have hB : IsOpen B := isOpen_ball.inter isOpen_ball
    have hBc : IsPreconnected B := ((convex_ball (p:ℂ) (R p)).inter (convex_ball (q:ℂ) (R q))).isPreconnected
    have hp : B ×ˢ B ⊆ W p := prod_mono inter_subset_left inter_subset_left
    have hq : B ×ˢ B ⊆ W q := prod_mono inter_subset_right inter_subset_right
    have he := box_eqOn_of_diagonal h₁ h₂ hB hBc ((hbox p).mono hp) ((hbox q).mono hq)
      (fun z hz ↦ (hdiag p z hz.1).trans (hdiag q z hz.2).symm)
    intro z hz
    exact he ⟨⟨hz.1.1,hz.2.1⟩,⟨hz.1.2,hz.2.2⟩⟩
  obtain ⟨G,hG,hGF⟩ := glue_boxes W (fun _ ↦ isOpen_ball.prod isOpen_ball) F hbox hcompat (f 0)
  refine ⟨⋃ p, W p,isOpen_iUnion (fun _ ↦ isOpen_ball.prod isOpen_ball),?_,G,hG,?_⟩
  · intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,mem_ball_self (hR ⟨z,hz⟩),mem_ball_self (hR ⟨z,hz⟩)⟩
  · intro z hz
    have hh : (z,z) ∈ W ⟨z,hz⟩ := ⟨mem_ball_self (hR ⟨z,hz⟩),mem_ball_self (hR ⟨z,hz⟩)⟩
    exact (hGF ⟨z,hz⟩ hh).trans (hdiag ⟨z,hz⟩ z hh.1)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def separatedAffine (p b : ℂ × ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 + b.1 * z.1,p.2 + b.2 * z.2)

def separatedLinear (b : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (b.1 • ContinuousLinearMap.fst ℂ ℂ ℂ).prod (b.2 • ContinuousLinearMap.snd ℂ ℂ ℂ)

lemma separatedAffine_hasFDerivAt (p b z : ℂ × ℂ) :
    HasFDerivAt (separatedAffine p b) (separatedLinear b) z := by
  exact ((hasFDerivAt_fst.const_mul b.1).const_add p.1).prodMk
    ((hasFDerivAt_snd.const_mul b.2).const_add p.2)

lemma IsBox.comp_separatedAffine {U V : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hU : IsOpen U) (hf : IsBox S U f) (p b : ℂ × ℂ)
    (hmap : MapsTo (separatedAffine p b) V U) :
    IsBox S V (f ∘ separatedAffine p b) := by
  have hd : ∀ z, MDifferentiableAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,ℂ × ℂ)
      (separatedAffine p b) z := fun z ↦ (separatedAffine_hasFDerivAt p b z).differentiableAt.mdifferentiableAt
  refine ⟨hf.1.comp (fun z _ ↦ (hd z).mdifferentiableWithinAt) hmap,?_⟩
  intro z hz
  have hmf := mfderiv_comp z (hf.1.mdifferentiableAt (hU.mem_nhds (hmap hz))) (hd z)
  rw [hmf,mfderiv_eq_fderiv,(separatedAffine_hasFDerivAt p b z).fderiv]
  have h₁ : separatedLinear b (1,0) = b.1 • (1,0) := by ext <;> simp [separatedLinear]
  have h₂ : separatedLinear b (0,1) = b.2 • (0,1) := by ext <;> simp [separatedLinear]
  let D : (ℂ × ℂ) →L[ℂ] Tangent X (f (separatedAffine p b z)) :=
    mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f (separatedAffine p b z)
  change S.projection (f (separatedAffine p b z)) (D (separatedLinear b (1,0))) =
      D (separatedLinear b (1,0)) ∧
    S.projection (f (separatedAffine p b z)) (D (separatedLinear b (0,1))) = 0
  have ht : S.projection (f (separatedAffine p b z)) (D (1,0)) = D (1,0) ∧
      S.projection (f (separatedAffine p b z)) (D (0,1)) = 0 := hf.2 _ (hmap hz)
  simp only [h₁,h₂,map_smul,ht.1,ht.2,smul_zero,and_self]

theorem diagonal_compact_tube {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : ∀ z ∈ K, (z,z) ∈ U) (c : ℂ × ℂ) :
    ∃ e : ℝ, 0 < e ∧ ∀ w ∈ ball (0:ℂ) e, ∀ z ∈ K,
      (z+c.1*w,z+c.2*w) ∈ U := by
  let T : ℂ × ℂ → ℂ × ℂ := fun q ↦ (q.2+c.1*q.1,q.2+c.2*q.1)
  have hT : Continuous T := by fun_prop
  have hsub : ({0} : Set ℂ) ×ˢ K ⊆ T ⁻¹' U := by
    rintro ⟨w,z⟩ ⟨hw,hz⟩
    have hw0 : w = 0 := mem_singleton_iff.mp hw
    subst w
    simpa [T] using hKU z hz
  obtain ⟨V,W,hVo,hWo,h0,hK',hVW⟩ := generalized_tube_lemma isCompact_singleton hK
    (hU.preimage hT) hsub
  obtain ⟨e,he,heV⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds (h0 (mem_singleton 0)))
  refine ⟨e,he,?_⟩
  intro w hw z hz
  exact hVW (show (w,z) ∈ V ×ˢ W from ⟨heV hw,hK' hz⟩)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

def mixedLinear (c : ℂ × ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun q := (q.2+c.1*q.1,q.2+c.2*q.1)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' a x := by ext <;> dsimp <;> ring

@[simp] lemma mixedLinear_apply (c q : ℂ × ℂ) :
    mixedLinear c q = (q.2+c.1*q.1,q.2+c.2*q.1) := rfl

def mixedLinearEquiv (c : ℂ × ℂ) (hc : c.1 ≠ c.2) : (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) :=
  { mixedLinear c with
    invFun := fun z ↦ ((z.1-z.2)/(c.1-c.2),(c.1*z.2-c.2*z.1)/(c.1-c.2))
    left_inv := by
      intro z
      have h : c.1-c.2 ≠ 0 := sub_ne_zero.mpr hc
      ext <;> dsimp <;> field_simp <;> ring
    right_inv := by
      intro z
      have h : c.1-c.2 ≠ 0 := sub_ne_zero.mpr hc
      ext <;> dsimp <;> field_simp <;> ring }

def mixedEquiv (c : ℂ × ℂ) (hc : c.1 ≠ c.2) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (mixedLinearEquiv c hc).toContinuousLinearEquiv

@[simp] lemma mixedEquiv_apply (c : ℂ × ℂ) (hc : c.1 ≠ c.2) (q : ℂ × ℂ) :
    mixedEquiv c hc q = (q.2+c.1*q.1,q.2+c.2*q.1) := rfl

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def IsMixedBox (c : ℂ × ℂ) (hc : c.1 ≠ c.2) (U : Set (ℂ × ℂ))
    (f : ℂ × ℂ → X.Carrier) : Prop :=
  IsBox S (mixedEquiv c hc '' U) (f ∘ (mixedEquiv c hc).symm)

lemma IsMixedBox.mono {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {U V : Set (ℂ × ℂ)}
    {f : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f) (hV : V ⊆ U) :
    IsMixedBox (S := S) c hc V f := IsBox.mono hf (image_mono hV)

lemma IsMixedBox.holomorphic {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {U : Set (ℂ × ℂ)}
    {f : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f) :
    MDifferentiableOn 𝓘(ℂ,ℂ × ℂ) (model n) f U := by
  have hh := hf.1.comp ((mixedEquiv c hc).differentiable.mdifferentiable.mdifferentiableOn)
    (mapsTo_image (mixedEquiv c hc) U)
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh

lemma isMixedBox_iff {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {U : Set (ℂ × ℂ)}
    {f : ℂ × ℂ → X.Carrier} :
    IsMixedBox (S := S) c hc U (f ∘ mixedEquiv c hc) ↔ IsBox S (mixedEquiv c hc '' U) f := by
  simp only [IsMixedBox,Function.comp_def,ContinuousLinearEquiv.apply_symm_apply]

lemma IsMixedBox.eqOn {c : ℂ × ℂ} {hc : c.1 ≠ c.2} {U : Set (ℂ × ℂ)}
    {f g : ℂ × ℂ → X.Carrier} (hU : IsOpen U) (hf : IsMixedBox (S := S) c hc U f)
    (he : EqOn f g U) : IsMixedBox (S := S) c hc U g := by
  have hU' : IsOpen (mixedEquiv c hc '' U) := (mixedEquiv c hc).toHomeomorph.isOpenMap _ hU
  have he' : EqOn (f ∘ (mixedEquiv c hc).symm) (g ∘ (mixedEquiv c hc).symm)
      (mixedEquiv c hc '' U) := by
    rintro z ⟨q,hq,rfl⟩
    simpa only [Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using he hq
  refine ⟨hf.1.congr he'.symm,?_⟩
  intro z hz
  have hev : (g ∘ (mixedEquiv c hc).symm) =ᶠ[𝓝 z] (f ∘ (mixedEquiv c hc).symm) :=
    Filter.mem_of_superset (hU'.mem_nhds hz) he'.symm
  rw [hev.eq_of_nhds,hev.mfderiv_eq]
  exact hf.2 z hz

end UniversalCoverSplitting

end

end OAI
