import OAI.Geometry.KahlerSplitting.ContinuousBoxes

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {P A B X C D : Type*} [TopologicalSpace P] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

structure ProductChart (atlas : Set (OpenPartialHomeomorph X (C × D))) where
  chart : OpenPartialHomeomorph X (C × D)
  mem_atlas : chart ∈ atlas
  first : Set C
  second : Set D
  product_range : chart.target = first ×ˢ second
  inverse_box : IsBox atlas (fun p : first × second ↦ chart.symm (p.1,p.2))

lemma ProductChart.parameter_tile [T2Space X] [CompactSpace A] [CompactSpace B]
    [PathConnectedSpace A] [PathConnectedSpace B]
    {atlas : Set (OpenPartialHomeomorph X (C × D))}
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source) (e : ProductChart atlas)
    {R : P → A × B → X} (hR : ∀ p, IsBox atlas (R p)) (p₀ : P) (a₀ : A) (b₀ : B)
    (hbottom : Continuous (fun z : P × A ↦ R z.1 (z.2,b₀)))
    (hleft : Continuous (fun z : P × B ↦ R z.1 (a₀,z.2)))
    (he : ∀ w, R p₀ w ∈ e.chart.source) :
    ∃ U : Set P, IsOpen U ∧ p₀ ∈ U ∧
      Continuous (fun z : U × (A × B) ↦ R z.1 z.2) := by
  have hb : ∀ᶠ p in 𝓝 p₀, ∀ a, R p (a,b₀) ∈ e.chart.source := by
    simpa only [mem_univ,forall_true_left] using
      isCompact_univ.eventually_forall_of_forall_eventually
        (fun a _ ↦ hbottom.continuousAt.eventually (e.chart.open_source.mem_nhds (he (a,b₀))))
  have hl : ∀ᶠ p in 𝓝 p₀, ∀ b, R p (a₀,b) ∈ e.chart.source := by
    simpa only [mem_univ,forall_true_left] using
      isCompact_univ.eventually_forall_of_forall_eventually
        (fun b _ ↦ hleft.continuousAt.eventually (e.chart.open_source.mem_nhds (he (a₀,b))))
  obtain ⟨U,hUsub,hU,hpU⟩ := mem_nhds_iff.mp (hb.and hl)
  have hbU (p : U) (a : A) : R p (a,b₀) ∈ e.chart.source := (hUsub p.property).1 a
  have hlU (p : U) (b : B) : R p (a₀,b) ∈ e.chart.source := (hUsub p.property).2 b
  let f : U × A → C := fun z ↦ (e.chart (R z.1 (z.2,b₀))).1
  let g : U × B → D := fun z ↦ (e.chart (R z.1 (a₀,z.2))).2
  have hf : Continuous f := (e.chart.continuousOn.comp_continuous
    (hbottom.comp (continuous_subtype_val.prodMap continuous_id)) (fun z ↦ hbU z.1 z.2)).fst
  have hg : Continuous g := (e.chart.continuousOn.comp_continuous
    (hleft.comp (continuous_subtype_val.prodMap continuous_id)) (fun z ↦ hlU z.1 z.2)).snd
  have hfmem (z : U × A) : f z ∈ e.first := by
    have h := e.chart.map_source (hbU z.1 z.2)
    rw [e.product_range] at h
    exact h.1
  have hgmem (z : U × B) : g z ∈ e.second := by
    have h := e.chart.map_source (hlU z.1 z.2)
    rw [e.product_range] at h
    exact h.2
  let M : U → A × B → X := fun p w ↦ e.chart.symm (f (p,w.1),g (p,w.2))
  have hM : ∀ p, IsBox atlas (M p) := by
    intro p
    exact e.inverse_box.precomp
      ((hf.comp (continuous_const.prodMk continuous_id)).subtype_mk (fun a ↦ hfmem (p,a)))
      ((hg.comp (continuous_const.prodMk continuous_id)).subtype_mk (fun b ↦ hgmem (p,b)))
  have hEq (p : U) : R p = M p := by
    apply unique_connected atlas hcover (hR p) (hM p) a₀ b₀
    · intro a
      have hs := (hR p).separated e.mem_atlas isPreconnected_univ isPreconnected_singleton
        (U := univ) (V := {b₀})
        (fun w hw ↦ by rcases w with ⟨a,b⟩; have h : b=b₀ := hw.2; subst b; exact hbU p a)
        (a := a) (a₀ := a₀) (b := b₀) (b₀ := b₀) trivial trivial rfl rfl
      change R p (a,b₀)=e.chart.symm ((e.chart (R p (a,b₀))).1,(e.chart (R p (a₀,b₀))).2)
      rw [← hs,e.chart.left_inv (hbU p a)]
    · intro b
      have hs := (hR p).separated e.mem_atlas isPreconnected_singleton isPreconnected_univ
        (U := {a₀}) (V := univ)
        (fun w hw ↦ by rcases w with ⟨a,b⟩; have h : a=a₀ := hw.1; subst a; exact hlU p b)
        (a := a₀) (a₀ := a₀) (b := b) (b₀ := b₀) rfl rfl trivial trivial
      change R p (a₀,b)=e.chart.symm ((e.chart (R p (a₀,b₀))).1,(e.chart (R p (a₀,b))).2)
      rw [← hs,e.chart.left_inv (hlU p b)]
  refine ⟨U,hU,hpU,?_⟩
  have hMc : Continuous (fun z : U × (A × B) ↦ M z.1 z.2) :=
    e.chart.continuousOn_symm.comp_continuous
      ((hf.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
        (hg.comp (continuous_fst.prodMk continuous_snd.snd)))
      (fun z ↦ e.product_range ▸ ⟨hfmem (z.1,z.2.1),hgmem (z.1,z.2.2)⟩)
  exact hMc.congr (fun z ↦ congrFun (hEq z.1).symm z.2)

end ProductBoxTopology
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.isBlockBox {U : Set (ℂ × ℂ)} {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) : IsBlockBox S U f := by
  refine ⟨hf.1,fun z hz ↦ ⟨?_,?_⟩⟩
  · intro v
    let D : (ℂ × ℂ) →L[ℂ] Model n := mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z
    let P : Model n →L[ℂ] Model n := S.projection (f z)
    change P (D (v,0)) = D (v,0)
    have hd : D (v,0) = v • D (1,0) := by
      simpa only [Prod.smul_mk,smul_eq_mul,mul_one,mul_zero,smul_zero] using D.map_smul v (1,0)
    rw [hd,P.map_smul]
    exact congrArg (fun x ↦ v • x) (hf.2 z hz).1
  · intro w
    let D : (ℂ × ℂ) →L[ℂ] Model n := mfderiv 𝓘(ℂ,ℂ × ℂ) (model n) f z
    let P : Model n →L[ℂ] Model n := S.projection (f z)
    change P (D (0,w)) = 0
    have hd : D (0,w) = w • D (0,1) := by
      simpa only [Prod.smul_mk,smul_eq_mul,mul_one,mul_zero,smul_zero] using D.map_smul w (0,1)
    rw [hd,P.map_smul]
    have hzero : P (D (0,1)) = 0 := (hf.2 z hz).2
    rw [hzero,smul_zero]

def SplittingChart.productChart (e : SplittingChart S) :
    ProductBoxTopology.ProductChart (splittingAtlas S) where
  chart := e.chart
  mem_atlas := ⟨e,rfl⟩
  first := ball 0 e.radius
  second := ball 0 e.radius
  product_range := e.product_range
  inverse_box := by
    have h := e.inverse_isBlockBox
    rw [e.product_range] at h
    exact h.plaqueBox isOpen_ball isOpen_ball

lemma splittingProductCharts_cover (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) (x : X.Carrier) :
    ∃ e : ProductBoxTopology.ProductChart (splittingAtlas S), x ∈ e.chart.source := by
  obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ x
  exact ⟨e.productChart,he⟩

section BlockLocal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma IsBlockBox.of_local {U : Set (E × F)} {f : E × F → X.Carrier}
    (hl : ∀ z ∈ U, ∃ V : Set (E × F), IsOpen V ∧ z ∈ V ∧ IsBlockBox S V f) :
    IsBlockBox S U f := by
  constructor
  · intro z hz
    obtain ⟨V,hV,hzV,hf⟩ := hl z hz
    exact (hf.1.mdifferentiableAt (hV.mem_nhds hzV)).mdifferentiableWithinAt
  · intro z hz
    obtain ⟨V,_,hzV,hf⟩ := hl z hz
    exact hf.2 z hzV

lemma IsBlockBox.congr {U : Set (E × F)} (hU : IsOpen U)
    {f g : E × F → X.Carrier} (hf : IsBlockBox S U f) (hfg : EqOn g f U) :
    IsBlockBox S U g := by
  refine ⟨hf.1.congr hfg,?_⟩
  intro z hz
  have he : g =ᶠ[𝓝 z] f := Filter.eventually_of_mem (hU.mem_nhds hz) hfg
  have hd := he.mfderiv_eq (I := 𝓘(ℂ,E × F)) (I' := model n)
  rw [hfg hz,hd]
  exact hf.2 z hz

end BlockLocal
end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

abbrev unitComplex (t : I) : ℂ := ((t:ℝ):ℂ)

lemma norm_unitComplex (t : I) : ‖unitComplex t‖ = (t:ℝ) := by
  simp [unitComplex,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg t.property.1]

lemma continuous_unitComplex : Continuous unitComplex :=
  Complex.continuous_ofReal.comp continuous_subtype_val

lemma smul_unit_ball {a : ℂ} (ha : ‖a‖ ≤ 1) {p : E} (hp : p ∈ ball (0:E) 1) :
    a • p ∈ ball (0:E) 1 := by
  rw [mem_ball_zero_iff,norm_smul]
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg p)).trans_lt (by simpa using hp)

lemma radial_scaled_ball {a : ℝ} (ha : 0 < a) {p : E} (hp : ‖p‖ < a)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) : (z/(a:ℂ)) • p ∈ ball (0:E) 1 := by
  rw [mem_ball_zero_iff,norm_smul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
  calc
    ‖z‖ / a * ‖p‖ ≤ 1 / a * ‖p‖ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hz1 ha.le) (norm_nonneg p)
    _ = ‖p‖ / a := by ring
    _ < 1 := (div_lt_one ha).mpr hp

theorem exists_radial_plaque_box [CompactSpace X.Carrier] (g : KahlerMetric X)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    {α : E → X.Carrier} {β : F → X.Carrier}
    (hα : IsHorizontalMap S (ball (0:E) 1) α) (hβ : IsVerticalMap S (ball (0:F) 1) β)
    (hbase : α 0=β 0) {p : E} {q : F} (hp : p ∈ ball (0:E) 1) (hq : q ∈ ball (0:F) 1) :
    ∃ R : I × I → X.Carrier, ProductBoxTopology.IsBox (splittingAtlas S) R ∧
      (∀ t : I, R (t,0)=α (unitComplex t • p)) ∧
      (∀ t : I, R (0,t)=β (unitComplex t • q)) := by
  have hm : max ‖p‖ ‖q‖ < 1 := max_lt (mem_ball_zero_iff.mp hp) (mem_ball_zero_iff.mp hq)
  obtain ⟨a,hma,ha1⟩ := exists_between hm
  have ha : 0 < a := (norm_nonneg p).trans_lt ((le_max_left _ _).trans_lt hma)
  have hap : ‖p‖ < a := (le_max_left _ _).trans_lt hma
  have haq : ‖q‖ < a := (le_max_right _ _).trans_lt hma
  have haC : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hαs := hα.comp isOpen_ball isOpen_ball
    (show DifferentiableOn ℂ (fun z : ℂ ↦ (z/(a:ℂ)) • p) (ball 0 1) from by fun_prop)
    (fun z hz ↦ radial_scaled_ball ha hap hz)
  have hβs := hβ.comp isOpen_ball isOpen_ball
    (show DifferentiableOn ℂ (fun z : ℂ ↦ (z/(a:ℂ)) • q) (ball 0 1) from by fun_prop)
    (fun z hz ↦ radial_scaled_ball ha haq hz)
  obtain ⟨H,hH,hHα,hHβ⟩ := disk_axes g h₁ h₂ hαs.curve hβs.curve (by simpa using hbase)
  have ht (t : I) : (a:ℂ)*unitComplex t ∈ ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,norm_unitComplex]
    exact (mul_le_mul_of_nonneg_left t.property.2 ha.le).trans_lt (by simpa using ha1)
  let i : I → ball (0:ℂ) 1 := fun t ↦ ⟨(a:ℂ)*unitComplex t,ht t⟩
  have hi : Continuous i := (continuous_const.mul continuous_unitComplex).subtype_mk _
  let R : I × I → X.Carrier := fun w ↦ H (i w.1,i w.2)
  refine ⟨R,(hH.isBlockBox.plaqueBox isOpen_ball isOpen_ball).precomp hi hi,?_,?_⟩
  · intro t
    change H ((a:ℂ)*unitComplex t,(a:ℂ)*unitComplex 0)=α (unitComplex t • p)
    simpa [unitComplex,Function.comp_def,haC] using hHα ((a:ℂ)*unitComplex t) (ht t)
  · intro t
    change H ((a:ℂ)*unitComplex 0,(a:ℂ)*unitComplex t)=β (unitComplex t • q)
    simpa [unitComplex,Function.comp_def,haC] using hHβ ((a:ℂ)*unitComplex t) (ht t)

end UniversalCoverSplitting
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem block_endpoint_of_family (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S))
    {U : Set (E × F)} (hU : IsOpen U) {R : (E × F) → I × I → X.Carrier}
    (hR : ∀ p ∈ U, ProductBoxTopology.IsBox (splittingAtlas S) (R p))
    (hc : ContinuousOn (Function.uncurry R) (U ×ˢ univ))
    (hb : ∀ t : I, IsBlockBox S U (fun p ↦ R p (t,0)))
    (hl : ∀ t : I, IsBlockBox S U (fun p ↦ R p (0,t))) :
    IsBlockBox S U (fun p ↦ R p (1,1)) := by
  classical
  apply IsBlockBox.of_local
  intro p₀ hp₀
  let c : SplittingChart S → Set (I × I) := fun e ↦ R p₀ ⁻¹' e.chart.source
  have hco : ∀ e, IsOpen (c e) := fun e ↦ e.chart.open_source.preimage (hR p₀ hp₀).1
  have hcov : univ ⊆ ⋃ e, c e := by
    intro w _
    obtain ⟨e,he,_⟩ := exists_splittingChart S h₁ h₂ (R p₀ w)
    exact mem_iUnion.mpr ⟨e,he⟩
  obtain ⟨t,ht0,htmono,⟨N,hN⟩,ht⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hco hcov
  have hnode : ∀ i j, ∃ V : Set (E × F), IsOpen V ∧ p₀ ∈ V ∧
      IsBlockBox S V (fun p ↦ R p (t i,t j)) := by
    intro i
    induction i with
    | zero => intro j; simpa only [ht0] using ⟨U,hU,hp₀,hl (t j)⟩
    | succ i hi =>
      intro j
      induction j with
      | zero => simpa only [ht0] using ⟨U,hU,hp₀,hb (t (i+1))⟩
      | succ j hj =>
        have hti : t i ≤ t (i+1) := htmono (Nat.le_succ i)
        have htj : t j ≤ t (j+1) := htmono (Nat.le_succ j)
        obtain ⟨e,he⟩ := ht i j
        let K := Icc (t i) (t (i+1)) ×ˢ Icc (t j) (t (j+1))
        have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
        have hmap : ∀ᶠ p in 𝓝 p₀, ∀ w ∈ K, R p w ∈ e.chart.source :=
          hK.eventually_forall_of_forall_eventually fun w hw ↦
            (hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hp₀,trivial⟩)).eventually
              (e.chart.open_source.mem_nhds (he hw))
        obtain ⟨O,hOsub,hO,hpO⟩ := _root_.mem_nhds_iff.mp hmap
        obtain ⟨V,hV,hpV,hbV⟩ := hj
        obtain ⟨W,hW,hpW,hlW⟩ := hi (j+1)
        let L := ((U ∩ O) ∩ V) ∩ W
        have hL : IsOpen L := ((hU.inter hO).inter hV).inter hW
        have hpL : p₀ ∈ L := ⟨⟨⟨hp₀,hpO⟩,hpV⟩,hpW⟩
        have hbL : IsBlockBox S L (fun p ↦ R p (t (i+1),t j)) :=
          hbV.mono (fun _ h ↦ h.1.2)
        have hlL : IsBlockBox S L (fun p ↦ R p (t i,t (j+1))) :=
          hlW.mono (fun _ h ↦ h.2)
        have hmi (p : E × F) (hp : p ∈ L) : MapsTo (R p) K e.chart.source :=
          hOsub hp.1.1.2
        have himem : t (i+1) ∈ Icc (t i) (t (i+1)) := ⟨hti,le_rfl⟩
        have hjmem : t (j+1) ∈ Icc (t j) (t (j+1)) := ⟨htj,le_rfl⟩
        have hi0 : t i ∈ Icc (t i) (t (i+1)) := ⟨le_rfl,hti⟩
        have hj0 : t j ∈ Icc (t j) (t (j+1)) := ⟨le_rfl,htj⟩
        have hm := e.mix_block_maps hL hbL hlL
          (fun p hp ↦ hmi p hp ⟨himem,hj0⟩) (fun p hp ↦ hmi p hp ⟨hi0,hjmem⟩)
        refine ⟨L,hL,hpL,hm.congr hL ?_⟩
        intro p hp
        have hs := (hR p hp.1.1.1).separated (show e.chart ∈ splittingAtlas S from ⟨e,rfl⟩)
          isPreconnected_Icc isPreconnected_Icc (hmi p hp) himem hi0 hjmem hj0
        change R p (t (i+1),t (j+1)) =
          e.chart.symm ((e.chart (R p (t (i+1),t j))).1,(e.chart (R p (t i,t (j+1)))).2)
        rw [← hs,e.chart.left_inv (hmi p hp ⟨himem,hjmem⟩)]
  simpa only [hN N le_rfl] using hnode N N

end UniversalCoverSplitting
end
end

end OAI
