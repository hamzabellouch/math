import OAI.Geometry.KahlerSplitting.EtaleGerms

namespace OAI

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

def SplittingChart.firstProjection (e : SplittingChart S) (b : Model s) (x : X.Carrier) : X.Carrier :=
  e.chart.symm ((e.chart x).1,b)

lemma SplittingChart.firstProjection_target (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) {x : X.Carrier} (hx : x ∈ e.chart.source) :
    ((e.chart x).1,b) ∈ e.chart.target := by
  have h := e.chart.map_source hx
  rw [e.product_range] at h ⊢
  exact ⟨h.1,hb⟩

lemma SplittingChart.firstProjection_source (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) {x : X.Carrier} (hx : x ∈ e.chart.source) :
    e.firstProjection b x ∈ e.chart.source := e.chart.map_target (e.firstProjection_target hb hx)

lemma SplittingChart.firstProjection_coordinates (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) {x : X.Carrier} (hx : x ∈ e.chart.source) :
    e.chart (e.firstProjection b x)=((e.chart x).1,b) :=
  e.chart.right_inv (e.firstProjection_target hb hx)

lemma SplittingChart.firstProjection_holomorphic (e : SplittingChart S) {b : Model s}
    (hb : b ∈ ball 0 e.radius) :
    MDifferentiableOn (model n) (model n) (e.firstProjection b) e.chart.source := by
  have hfst : MDifferentiableOn (model n) (model r) (fun x ↦ (e.chart x).1) e.chart.source := by
    intro x hx
    exact (mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst).comp_mdifferentiableWithinAt x
      (e.holomorphic x hx)
  exact e.inverse_holomorphic.comp (hfst.prodMk_space mdifferentiableOn_const)
    (fun _ hx ↦ e.firstProjection_target hb hx)

lemma SplittingChart.firstProjection_self (e : SplittingChart S) {x : X.Carrier}
    (hx : x ∈ e.chart.source) : e.firstProjection (e.chart x).2 x=x := by
  exact e.chart.left_inv hx

namespace FirstGerm

lemma extends_plaque (g : HolomorphicEtale.Germs X X) (hg : IsFirst (S := S) g.val)
    (e : SplittingChart S) (he : HolomorphicEtale.base X X g ∈ e.chart.source) :
    ∃ V : Set X.Carrier, IsOpen V ∧
      ∃ F : X.Carrier → X.Carrier, MDifferentiableOn (model n) (model n) F V ∧
        g.val=FunctionEtale.sectionOf F (HolomorphicEtale.base X X g) ∧
        (∀ y ∈ e.chart.source,
          (e.chart y).1=(e.chart (HolomorphicEtale.base X X g)).1 → y ∈ V) ∧
        ∀ y ∈ V, IsFirst (S := S) (FunctionEtale.sectionOf F y) := by
  obtain ⟨U,hU,hxU,f,hf,hgF⟩ := g.property
  let x := HolomorphicEtale.base X X g
  obtain ⟨h,hh⟩ := hg e he
  have hfh : f =ᶠ[𝓝 x] (fun y ↦ h (e.chart y).1) :=
    FunctionEtale.section_eq.mp (hgF.symm.trans hh)
  have hb : (e.chart x).2 ∈ ball 0 e.radius := by
    have H := e.chart.map_source he
    rw [e.product_range] at H
    exact H.2
  let P := e.firstProjection (e.chart x).2
  have hP : MDifferentiableOn (model n) (model n) P e.chart.source := e.firstProjection_holomorphic hb
  have hPx : P x=x := e.firstProjection_self he
  have hPc : ContinuousAt P x := hP.continuousOn.continuousAt (e.chart.open_source.mem_nhds he)
  let F := f ∘ P
  let V := e.chart.source ∩ P ⁻¹' U
  have hV : IsOpen V := hP.continuousOn.isOpen_inter_preimage e.chart.open_source hU
  have hPV : MapsTo P V U := fun _ hy ↦ hy.2
  refine ⟨V,hV,F,hf.comp (hP.mono inter_subset_left) hPV,?_,?_,?_⟩
  · apply hgF.trans
    apply FunctionEtale.section_eq.mpr
    have hhh : (fun y ↦ f (P y)) =ᶠ[𝓝 x] (fun y ↦ h (e.chart (P y)).1) :=
      hfh.comp_tendsto (by simpa only [ContinuousAt,hPx] using hPc)
    filter_upwards [hfh,hhh,e.chart.open_source.mem_nhds he] with y hy hy' hye
    dsimp only [F,Function.comp_apply]
    rw [hy,hy',e.firstProjection_coordinates hb hye]
  · intro y hy hxy
    refine ⟨hy,?_⟩
    have hPy : P y=x := by
      change e.chart.symm ((e.chart y).1,(e.chart x).2)=x
      rw [hxy]
      exact e.chart.left_inv he
    change P y ∈ U
    rw [hPy]
    exact hxU
  · intro y hy
    exact of_factor e hy.1 (fun a ↦ f (e.chart.symm (a,(e.chart x).2)))

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace IntervalChain
variable {E X : Type*} [TopologicalSpace E]

theorem lift_cells (p : E → X) (Q : E → Prop) (γ : I → X)
    (t : ℕ → I) (ht0 : t 0=0) (ht : Monotone t) (N : ℕ) (hN : t N=1)
    (e₀ : E) (he₀ : p e₀=γ 0) (hQ₀ : Q e₀)
    (local_lift : ∀ i e, p e=γ (t i) → Q e →
      ∃ f : cell t i → E, Continuous f ∧
        f ⟨t i,le_rfl,ht (Nat.le_succ i)⟩=e ∧
        ∀ u, p (f u)=γ u ∧ Q (f u)) :
    ∃ F : I → E, Continuous F ∧ F 0=e₀ ∧ ∀ u, p (F u)=γ u ∧ Q (F u) := by
  classical
  let State (i : ℕ) := {e : E // p e=γ (t i) ∧ Q e}
  have ex (i : ℕ) (e : State i) : ∃ f : cell t i → E, Continuous f ∧
      f ⟨t i,le_rfl,ht (Nat.le_succ i)⟩=e.val ∧ ∀ u, p (f u)=γ u ∧ Q (f u) :=
    local_lift i e.val e.property.1 e.property.2
  choose L hLc hL0 hL using ex
  let initial : State 0 := ⟨e₀,by simpa only [ht0] using he₀,hQ₀⟩
  let next (i : ℕ) (e : State i) : State (i+1) :=
    ⟨L i e ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩,hL i e _⟩
  let state : ∀ i, State i := fun i ↦ Nat.rec initial next i
  let f (i : ℕ) : cell t i → E := L i (state i)
  have seam (i : ℕ) : f i ⟨t (i+1),ht (Nat.le_succ i),le_rfl⟩=
      f (i+1) ⟨t (i+1),le_rfl,ht (Nat.le_succ (i+1))⟩ := by
    exact (hL0 (i+1) (state (i+1))).symm
  have cover (u : I) : ∃ i : Fin (N+1), u ∈ cell t i := by
    obtain ⟨i,hi,hu⟩ := covers t ht0 ht N hN u
    exact ⟨⟨i,by omega⟩,hu⟩
  obtain ⟨F,hF,hFr⟩ := ClosedCoverGlue.exists_glue (fun i : Fin (N+1) ↦ cell t i)
    (fun _ ↦ isClosed_Icc) cover (fun i ↦ f i) (fun i ↦ hLc i (state i))
    (fun i j u hi hj ↦ overlap t ht f seam i j u hi hj)
  have heq (i : ℕ) (u : cell t i) : F u=f i u := by
    obtain ⟨j,hj⟩ := cover u
    exact (hFr j ⟨u,hj⟩).trans (overlap t ht f seam j i u hj u.property)
  refine ⟨F,hF,?_,?_⟩
  · have H := (heq 0 ⟨t 0,le_rfl,ht (Nat.le_succ 0)⟩).trans (hL0 0 (state 0))
    change F (t 0)=e₀ at H
    simpa only [ht0] using H
  · intro u
    obtain ⟨i,hi⟩ := cover u
    rw [heq i ⟨u,hi⟩]
    exact hL i (state i) _

end IntervalChain
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
namespace FirstGerm
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]

lemma lift_chart (e : SplittingChart S) {β : A → X.Carrier}
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β)
    (hmap : ∀ a, β a ∈ e.chart.source) (a₀ : A)
    (g : HolomorphicEtale.Germs X X) (hbase : HolomorphicEtale.base X X g=β a₀)
    (hg : IsFirst (S := S) g.val) :
    ∃ G : A → HolomorphicEtale.Germs X X, Continuous G ∧ G a₀=g ∧
      ∀ a, HolomorphicEtale.base X X (G a)=β a ∧ IsFirst (S := S) (G a).val := by
  have he : HolomorphicEtale.base X X g ∈ e.chart.source := hbase ▸ hmap a₀
  obtain ⟨V,hV,F,hF,hgF,hplaque,hfirst⟩ := extends_plaque g hg e he
  have hl : IsLocallyConstant (fun a ↦ (e.chart (β a)).1) :=
    (hβ.2 e.chart ⟨e,rfl⟩).comp_continuous (continuous_id.subtype_mk hmap)
  have hbV (a : A) : β a ∈ V := by
    apply hplaque _ (hmap a)
    rw [hbase]
    exact hl.apply_eq_of_preconnectedSpace a a₀
  let G : A → HolomorphicEtale.Germs X X :=
    fun a ↦ HolomorphicEtale.sectionOf X X F hV hF ⟨β a,hbV a⟩
  refine ⟨G,(HolomorphicEtale.continuous_section X X F hV hF).comp
    (hβ.1.subtype_mk hbV),?_,fun a ↦ ⟨rfl,hfirst _ (hbV a)⟩⟩
  apply Subtype.ext
  change FunctionEtale.sectionOf F (β a₀)=g.val
  rw [←hbase]
  exact hgF.symm

lemma lift_vertical (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {β : I → X.Carrier}
    (hβ : ProductBoxTopology.IsVertical (splittingAtlas S) β)
    (g : HolomorphicEtale.Germs X X) (hbase : HolomorphicEtale.base X X g=β 0)
    (hg : IsFirst (S := S) g.val) :
    ∃ G : I → HolomorphicEtale.Germs X X, Continuous G ∧ G 0=g ∧
      ∀ a, HolomorphicEtale.base X X (G a)=β a ∧ IsFirst (S := S) (G a).val := by
  classical
  have ex (a : I) : ∃ e : SplittingChart S, β a ∈ e.chart.source := by
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (β a)
    exact ⟨e,he⟩
  choose e he using ex
  let U : I → Set I := fun a ↦ β ⁻¹' (e a).chart.source
  have hU (a : I) : IsOpen (U a) := (e a).chart.open_source.preimage hβ.1
  have cover : univ ⊆ ⋃ a, U a := fun a _ ↦ mem_iUnion.mpr ⟨a,he a⟩
  obtain ⟨t,ht0,ht,⟨N,hN⟩,hsub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval hU cover
  choose k hk using hsub
  apply IntervalChain.lift_cells (HolomorphicEtale.base X X) (fun g ↦ IsFirst (S := S) g.val)
    β t ht0 ht N (hN N le_rfl) g hbase hg
  intro i a ha hfirst
  let : PreconnectedSpace (Icc (t i) (t (i+1))) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  exact lift_chart (e (k i)) (hβ.precomp continuous_subtype_val)
    (fun u ↦ hk i u.property) ⟨t i,le_rfl,ht (Nat.le_succ i)⟩ a ha hfirst

end FirstGerm
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma independent_first_of_fderiv_zero
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsPreconnected U) {f : E × F → H}
    (hf : DifferentiableOn ℂ f (U ×ˢ V))
    (hzero : ∀ p ∈ U ×ˢ V, ∀ v : E, fderiv ℂ f p (v,0)=0)
    {a c : E} (ha : a ∈ U) (hc : c ∈ U) {b : F} (hb : b ∈ V) : f (a,b)=f (c,b) := by
  have hd (x : E) (hx : x ∈ U) :
      HasFDerivAt (fun t : E ↦ f (t,b)) (0 : E →L[ℂ] H) x := by
    have hp : HasFDerivAt (fun t : E ↦ (t,b)) (ContinuousLinearMap.inl ℂ E F) x := by
      convert (hasFDerivAt_id (𝕜 := ℂ) x).prodMk (hasFDerivAt_const (𝕜 := ℂ) b x) using 1 <;> rfl
    have hh := ((hf (x,b) ⟨hx,hb⟩).differentiableAt
      ((hU.prod hV).mem_nhds ⟨hx,hb⟩)).hasFDerivAt.comp x hp
    have he : fderiv ℂ f (x,b) ∘L ContinuousLinearMap.inl ℂ E F=0 := by
      ext v
      exact hzero (x,b) ⟨hx,hb⟩ v
    rw [he] at hh
    exact hh
  exact hU.is_const_of_fderiv_eq_zero hUc
    (fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hd x hx).fderiv) ha hc

lemma SplittingChart.transition_second (e d : SplittingChart S) {x : X.Carrier}
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    (fun y ↦ (e.chart y).2) =ᶠ[𝓝 x]
      (fun y ↦ (e.chart (d.chart.symm ((d.chart x).1,(d.chart y).2))).2) := by
  let z := d.chart x
  have hzt : z ∈ d.chart.target := d.chart.map_source hd
  have hN : d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source ∈ 𝓝 z := by
    refine inter_mem (d.chart.open_target.mem_nhds hzt) ((d.chart.symm.continuousAt hzt) ?_)
    simpa only [z,d.chart.left_inv hd] using e.chart.open_source.mem_nhds he
  obtain ⟨ε,hε,hεN⟩ := Metric.mem_nhds_iff.mp hN
  let U := ball z.1 ε
  let V := ball z.2 ε
  have hUV : U ×ˢ V ⊆ d.chart.target ∩ d.chart.symm ⁻¹' e.chart.source := by
    simpa only [U,V,ball_prod_same,Prod.eta] using hεN
  have hc := e.block_coordinates (isOpen_ball.prod isOpen_ball)
    (d.inverse_isBlockBox.mono (fun _ h ↦ (hUV h).1)) (fun _ h ↦ (hUV h).2)
  let F : Model r × Model s → Model s := fun p ↦ (e.chart (d.chart.symm p)).2
  have hF : DifferentiableOn ℂ F (U ×ˢ V) := hc.1.snd
  have hzero : ∀ p ∈ U ×ˢ V, ∀ v : Model r, fderiv ℂ F p (v,0)=0 := by
    intro p hp v
    have H := ((hc.1.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hp)).hasFDerivAt.snd).fderiv
    change fderiv ℂ F p = _ at H
    rw [H]
    exact (hc.2 p hp).1 v
  have hloc : ∀ p ∈ U ×ˢ V, F p=F (z.1,p.2) := by
    intro p hp
    exact independent_first_of_fderiv_zero isOpen_ball isOpen_ball (convex_ball z.1 ε).isPreconnected
      hF hzero hp.1 (mem_ball_self hε) hp.2
  have hdx := d.chart.continuousAt hd
  filter_upwards [d.chart.open_source.mem_nhds hd,
    hdx ((isOpen_ball.prod isOpen_ball).mem_nhds (show z ∈ U ×ˢ V from
      ⟨mem_ball_self hε,mem_ball_self hε⟩))] with y hy hdy
  simpa only [F,d.chart.left_inv hy] using hloc (d.chart y) hdy

lemma SplittingChart.firstProjection_germ_eq (e d : SplittingChart S) {x : X.Carrier}
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    e.firstProjection (e.chart x).2 =ᶠ[𝓝 x] d.firstProjection (d.chart x).2 := by
  have hb : (d.chart x).2 ∈ ball 0 d.radius := by
    have H := d.chart.map_source hd
    rw [d.product_range] at H
    exact H.2
  have hb' : (e.chart x).2 ∈ ball 0 e.radius := by
    have H := e.chart.map_source he
    rw [e.product_range] at H
    exact H.2
  let P := d.firstProjection (d.chart x).2
  have hPx : P x=x := d.firstProjection_self hd
  have hpc : Tendsto P (𝓝 x) (𝓝 x) := by
    have H := (d.firstProjection_holomorphic hb).continuousOn.continuousAt
      (d.chart.open_source.mem_nhds hd)
    change Tendsto P (𝓝 x) (𝓝 (P x)) at H
    simpa only [hPx] using H
  have hsecond := (e.transition_second d he hd).comp_tendsto hpc
  filter_upwards [e.chart.open_source.mem_nhds he,d.chart.open_source.mem_nhds hd,
    hpc (e.chart.open_source.mem_nhds he),e.transition_first d he hd,hsecond] with y hye hyd hpe hfirst hsec
  apply e.chart.injOn (e.firstProjection_source hb' hye) hpe
  rw [e.firstProjection_coordinates hb' hye]
  apply Prod.ext
  · exact hfirst
  · have H := congrArg (fun z : Model r × Model s ↦ z.2) (d.firstProjection_coordinates hb hyd)
    change (d.chart (P y)).2=(d.chart x).2 at H
    dsimp only [Function.comp_def] at hsec
    rw [H,d.chart.left_inv hd] at hsec
    exact hsec.symm

namespace FirstGerm

def projection (e : SplittingChart S) (x : X.Carrier) (hx : x ∈ e.chart.source) :
    HolomorphicEtale.Germs X X :=
  ⟨FunctionEtale.sectionOf (e.firstProjection (e.chart x).2) x,
    e.chart.source,e.chart.open_source,hx,e.firstProjection (e.chart x).2,
    e.firstProjection_holomorphic (by
      have H := e.chart.map_source hx
      rw [e.product_range] at H
      exact H.2),rfl⟩

lemma projection_first (e : SplittingChart S) (x : X.Carrier) (hx : x ∈ e.chart.source) :
    IsFirst (S := S) (projection e x hx).val :=
  of_factor e hx (fun a ↦ e.chart.symm (a,(e.chart x).2))

lemma projection_eq (e d : SplittingChart S) (x : X.Carrier)
    (he : x ∈ e.chart.source) (hd : x ∈ d.chart.source) :
    projection e x he=projection d x hd := by
  apply Subtype.ext
  exact FunctionEtale.section_eq.mpr (e.firstProjection_germ_eq d he hd)

end FirstGerm
end UniversalCoverSplitting
end
end

end OAI
