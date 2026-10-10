import Mathlib
import OAI.Geometry.BallPacking.Necessity.FiniteContinuation

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function
namespace TwoPointContinuation

 theorem finite_space_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (F : ℝ × E → E) (hF : Continuous F) (hzero : ∀ x, F (0,x)=x)
    (Ω : Set E) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h0 : 0∈Ω)
    (hside : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, x∉Ω → F (t,x)≠0) :
    ∃ x∈Ω, F (1,x)=0 := by
  let n := Module.finrank ℝ E
  let e : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let G : ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun y => e (F (y.1,e.symm y.2))
  have hG : Continuous G := e.continuous.comp (hF.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  have hG0 (x : Fin n → ℝ) : G (0,x)=x := by simp [G,hzero]
  let U := e.symm ⁻¹' Ω
  have hU : U=e '' Ω := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
    · rintro ⟨x,hx,rfl⟩
      simpa only [U,Set.mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hx
  have hu : IsOpen U := ho.preimage e.symm.continuous
  have hbu : Bornology.IsBounded U := by rw [hU]; exact e.lipschitzWith.isBounded_image hb
  have h0u : 0∈U := by simpa only [U,Set.mem_preimage,ContinuousLinearEquiv.map_zero] using h0
  have hsu (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : Fin n → ℝ) (hx : x∈closure U) (hn : x∉U) : G (t,x)≠0 := by
    have hcl : e.symm x∈closure Ω := e.symm.continuous.closure_preimage_subset Ω hx
    intro he
    have hh : F (t,e.symm x)=0 := e.injective (by simpa only [G,ContinuousLinearEquiv.map_zero] using he)
    exact hside t ht (e.symm x) hcl hn hh
  obtain ⟨x,hx,hx0⟩ := continuous_localized_continuation n G hG hG0 U hu hbu h0u hsu
  refine ⟨e.symm x,hx,e.injective ?_⟩
  simpa only [G,ContinuousLinearEquiv.map_zero] using hx0


 

 

open scoped ContDiff Topology
open Set Filter Function

 theorem compact_residual_gap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (hT : Continuous T) (D : Set (ℝ × E)) (hD : IsClosed D)
    (ht : ∀ y∈D, y.1∈Icc (0:ℝ) 1)
    (S : Set E) (hS : IsCompact S) (hTS : ∀ y∈D, T y∈S)
    (hno : ∀ y∈D, y.2-T y≠0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ y∈D, δ≤‖y.2-T y‖ := by
  classical
  by_contra hn
  push Not at hn
  have hh (n : ℕ) : ∃ y∈D, ‖y.2-T y‖<1/((n:ℝ)+1) := hn _ (by positivity)
  choose y hy hyr using hh
  have hr : Tendsto (fun n => (y n).2-T (y n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hyr n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨a,ha,φ,hφ,hm⟩ := (isCompact_Icc.prod hS).tendsto_subseq
    (x := fun n => ((y n).1,T (y n))) (fun n => ⟨ht (y n) (hy n),hTS (y n) (hy n)⟩)
  have hx : Tendsto (fun n => (y (φ n)).2) atTop (𝓝 a.2) := by
    have hh := hm.snd_nhds.add (hr.comp hφ.tendsto_atTop)
    simpa only [comp_apply,add_sub_cancel,add_zero] using hh
  have hyconv : Tendsto (y ∘ φ) atTop (𝓝 a) := hm.fst_nhds.prodMk_nhds hx
  have had : a∈D := hD.mem_of_tendsto hyconv (Eventually.of_forall (fun n => hy (φ n)))
  have he : T a=a.2 := tendsto_nhds_unique (hT.continuousAt.tendsto.comp hyconv) hm.snd_nhds
  exact hno a had (sub_eq_zero.mpr he.symm)


 

 

open scoped ContDiff Topology
open Set Filter Function

 

theorem compact_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (hT : Continuous T) (hzero : ∀ x, T (0,x)=0)
    (Ω : Set E) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (h0 : 0∈Ω)
    (S : Set E) (hS : IsCompact S)
    (hTS : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, T (t,x)∈S)
    (hside : ∀ t∈Icc (0:ℝ) 1, ∀ x∈closure Ω, x∉Ω → T (t,x)≠x) :
    ∃ x∈Ω, T (1,x)=x := by
  classical
  by_contra hn
  have hfinal (x : E) (hx : x∈closure Ω) : T (1,x)≠x := by
    by_cases hm : x∈Ω
    · exact fun he => hn ⟨x,hm,he⟩
    · exact hside 1 ⟨zero_le_one,le_rfl⟩ x hx hm
  let D := (Icc (0:ℝ) 1 ×ˢ (closure Ω\Ω)) ∪ ({1} ×ˢ closure Ω)
  have hD : IsClosed D := (isClosed_Icc.prod (isClosed_closure.inter ho.isClosed_compl)).union
    (isClosed_singleton.prod isClosed_closure)
  have htd (y : ℝ × E) (hy : y∈D) : y.1∈Icc (0:ℝ) 1 := by
    rcases hy with hy|hy
    · exact hy.1
    · rw [show y.1=1 from hy.1]; exact ⟨zero_le_one,le_rfl⟩
  have hxd (y : ℝ × E) (hy : y∈D) : y.2∈closure Ω := by
    rcases hy with hy|hy
    · exact hy.2.1
    · exact hy.2
  have hTSd (y : ℝ × E) (hy : y∈D) : T y∈S := hTS y.1 (htd y hy) y.2 (hxd y hy)
  have hno (y : ℝ × E) (hy : y∈D) : y.2-T y≠0 := by
    intro he
    have he' : T y=y.2 := (sub_eq_zero.mp he).symm
    rcases hy with hy|hy
    · exact hside y.1 hy.1 y.2 hy.2.1 hy.2.2 he'
    · have ht : y.1=1 := hy.1
      exact hfinal y.2 hy.2 (by simpa only [←ht] using he')
  obtain ⟨δ,hδ,hgap⟩ := compact_residual_gap T hT D hD htd S hS hTSd hno
  obtain ⟨V,hV,P,hP,happ⟩ := finite_rank_approx (S∪{0}) (hS.union isCompact_singleton)
    (δ/4) (by positivity)
  let : FiniteDimensional ℝ V := hV
  let F : ℝ × V → V := fun y => y.2-(P (T (y.1,(y.2:E)))-P 0)
  have hF : Continuous F := continuous_snd.sub
    ((hP.comp (hT.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).sub continuous_const)
  have hF0 (x : V) : F (0,x)=x := by simp [F,hzero]
  let U := ((↑) : V → E) ⁻¹' Ω
  have hu : IsOpen U := ho.preimage continuous_subtype_val
  have hbu : Bornology.IsBounded U := by
    obtain ⟨R,hR,hbR⟩ := hb.exists_pos_norm_le
    apply (Metric.isBounded_iff_subset_closedBall (0:V)).mpr
    refine ⟨R,fun x hx => ?_⟩
    change dist x 0≤R
    rw [dist_zero_right]
    change ‖(x:E)‖≤R
    exact hbR (x:E) hx
  have h0u : (0:V)∈U := h0
  have hclose (x : V) (hx : x∈closure U) : (x:E)∈closure Ω :=
    continuous_subtype_val.closure_preimage_subset Ω hx
  have hnear (t : ℝ) (x : V) (hmem : T (t,(x:E))∈S) (hf : F (t,x)=0) :
      ‖(x:E)-T (t,(x:E))‖<δ := by
    have he : (x:E)=(P (T (t,(x:E))) : E)-(P 0:E) :=
      congrArg (fun u : V => (u:E)) (sub_eq_zero.mp hf)
    have h1 := happ (T (t,(x:E))) (Or.inl hmem)
    have h2 := happ 0 (Or.inr rfl)
    simp only [sub_zero] at h2
    have he' : (x:E)-T (t,(x:E))=((P (T (t,(x:E))):E)-T (t,(x:E)))-(P 0:E) := by
      calc
        (x:E)-T (t,(x:E))=((P (T (t,(x:E))):E)-(P 0:E))-T (t,(x:E)) :=
          congrArg (fun v : E => v-T (t,(x:E))) he
        _ = _ := by abel
    rw [he']
    have hh := norm_sub_le ((P (T (t,(x:E))):E)-T (t,(x:E))) (P 0:E)
    linarith
  have hsideF (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : V) (hx : x∈closure U) (hn : x∉U) : F (t,x)≠0 := by
    intro hf
    exact (not_lt_of_ge (hgap (t,(x:E)) (Or.inl ⟨ht,hclose x hx,hn⟩)))
      (hnear t x (hTS t ht (x:E) (hclose x hx)) hf)
  obtain ⟨x,hx,hfx⟩ := finite_space_continuation F hF hF0 U hu hbu h0u hsideF
  have hxcl : (x:E)∈closure Ω := subset_closure hx
  exact (not_lt_of_ge (hgap (1,(x:E)) (Or.inr ⟨rfl,hxcl⟩)))
    (hnear 1 x (hTS 1 ⟨zero_le_one,le_rfl⟩ (x:E) hxcl) hfx)


 

 

open scoped ContDiff Topology
open Set Filter Function

 theorem local_compact_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (U : Set E) (hU : IsOpen U)
    (hT : ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, ContinuousAt T (t,x))
    (hzero : ∀ x∈U, T (0,x)=0)
    (S : Set E) (hS : IsCompact S) (hTS : ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, T (t,x)∈S)
    (K : Set E) (hK : IsCompact K) (hKU : K⊆U) (h0 : 0∈K)
    (hfix : ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, T (t,x)=x → x∈K) :
    ∃ x∈U, T (1,x)=x := by
  classical
  obtain ⟨χ,hχ0,hχ1,hχb⟩ := exists_continuous_zero_one_of_isClosed
    hU.isClosed_compl hK.isClosed (Set.disjoint_left.mpr (fun x hx hk => hx (hKU hk)))
  let ρ : E → ℝ := fun x => min 1 (max 0 (4*(χ x-1/4)))
  have hρ : Continuous ρ := continuous_const.min (continuous_const.max
    (continuous_const.mul (χ.continuous.sub continuous_const)))
  have hρb (x : E) : ρ x∈Icc (0:ℝ) 1 := by
    dsimp [ρ]
    exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
  have hρone (x : E) (hx : (1/2:ℝ)≤χ x) : ρ x=1 := by
    dsimp [ρ]
    rw [min_eq_left]
    exact (by linarith : (1:ℝ)≤4*(χ x-1/4)).trans (le_max_right _ _)
  have hρzero (x : E) (hx : χ x≤(1/4:ℝ)) : ρ x=0 := by
    dsimp [ρ]
    rw [max_eq_left (by linarith),min_eq_right (by norm_num)]
  let τ : ℝ → ℝ := fun t => min 1 (max 0 t)
  have hτ : Continuous τ := continuous_const.min (continuous_const.max continuous_id)
  have hτb (t : ℝ) : τ t∈Icc (0:ℝ) 1 :=
    ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
  have hτe (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : τ t=t := by
    dsimp [τ]; rw [max_eq_right ht.1,min_eq_right ht.2]
  let G : ℝ × E → E := fun y => ρ y.2 • T (τ y.1,y.2)
  have hG : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hx : y.2∈U
    · exact (hρ.comp continuous_snd).continuousAt.smul
        ((hT (τ y.1) (hτb y.1) y.2 hx).comp (f := fun z : ℝ × E => (τ z.1,z.2)) ((hτ.comp continuous_fst).prodMk continuous_snd).continuousAt)
    · have hc : χ y.2=0 := hχ0 hx
      have hn : ∀ᶠ z : ℝ × E in 𝓝 y, χ z.2<(1/4:ℝ) :=
        (χ.continuous.comp continuous_snd).continuousAt.eventually (eventually_lt_nhds (by change χ y.2<(1/4:ℝ); rw [hc]; norm_num))
      apply (continuousAt_const (y := (0:E))).congr_of_eventuallyEq
      filter_upwards [hn] with z hz
      change ρ z.2 • T (τ z.1,z.2)=(0:E)
      rw [hρzero z.2 hz.le,zero_smul]
  have hG0 (x : E) : G (0,x)=0 := by
    by_cases hx : x∈U
    · simp only [G,hτe 0 ⟨le_rfl,zero_le_one⟩,hzero x hx,smul_zero]
    · simp only [G,hρzero x (by rw [hχ0 hx]; norm_num),zero_smul]
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0:E)
  let Ω := {x : E | (3/4:ℝ)<χ x} ∩ Metric.ball 0 R
  have ho : IsOpen Ω := (isOpen_lt continuous_const χ.continuous).inter Metric.isOpen_ball
  have hb : Bornology.IsBounded Ω := Metric.isBounded_ball.subset inter_subset_right
  have hKΩ : K⊆Ω := by
    intro x hx
    exact ⟨by change (3/4:ℝ)<χ x; rw [hχ1 hx]; norm_num,hKR hx⟩
  have hcl (x : E) (hx : x∈closure Ω) : (3/4:ℝ)≤χ x := by
    exact closure_minimal (t := {x : E | (3/4:ℝ)≤χ x}) (by intro x (hx : x∈Ω); change (3/4:ℝ)≤χ x; exact hx.1.le) (isClosed_le continuous_const χ.continuous) hx
  have hclU (x : E) (hx : x∈closure Ω) : x∈U := by
    by_contra hn
    have hh := hcl x hx
    rw [hχ0 hn] at hh
    norm_num at hh
  have hGe (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (x : E) (hx : x∈closure Ω) : G (t,x)=T (t,x) := by
    simp only [G,hτe t ht,hρone x (by have hh := hcl x hx; linarith),one_smul]
  obtain ⟨x,hx,he⟩ := compact_continuation G hG hG0 Ω ho hb (hKΩ h0) S hS
    (fun t ht x hx => by rw [hGe t ht x hx]; exact hTS t ht x (hclU x hx))
    (by
      intro t ht x hx hn he
      rw [hGe t ht x hx] at he
      exact hn (hKΩ (hfix t ht x (hclU x hx) he)))
  exact ⟨x,hclU x (subset_closure hx),by rwa [hGe 1 ⟨zero_le_one,le_rfl⟩ x (subset_closure hx)] at he⟩


 

 

open scoped Topology
open Set Filter Function

 def LocallyPrecompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) : Prop := ∃ V∈𝓝 x, ∃ K : Set Y, IsCompact K ∧ f '' V⊆K

 theorem locallyPrecompact_finite {X Y : Type*} [TopologicalSpace X]
    [MetricSpace Y] [ProperSpace Y] (f : X → Y) (x : X) (hf : ContinuousAt f x) :
    LocallyPrecompact f x := by
  refine ⟨f ⁻¹' Metric.closedBall (f x) 1,hf.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (by norm_num)),
    Metric.closedBall (f x) 1,isCompact_closedBall _ _,image_preimage_subset _ _⟩

 theorem locallyPrecompact_compactLinear {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (hL : IsCompactOperator L) (x : X) : LocallyPrecompact L x := by
  obtain ⟨K,hK,hLK⟩ := hL.image_closedBall_subset_compact (‖x‖+1)
  refine ⟨Metric.closedBall 0 (‖x‖+1),?_,K,hK,hLK⟩
  apply mem_of_superset (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1))
  intro y hy
  rw [Metric.mem_closedBall,dist_zero_right]
  have hh := norm_le_norm_sub_add y x
  have hy' : ‖y-x‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  linarith

 theorem LocallyPrecompact.prod {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : X → Z} {x : X}
    (hf : LocallyPrecompact f x) (hg : LocallyPrecompact g x) :
    LocallyPrecompact (fun x => (f x,g x)) x := by
  obtain ⟨V,hV,K,hK,hfK⟩ := hf
  obtain ⟨W,hW,L,hL,hgL⟩ := hg
  exact ⟨V∩W,inter_mem hV hW,K×ˢL,hK.prod hL,by rintro _ ⟨y,hy,rfl⟩; exact ⟨hfK ⟨y,hy.1,rfl⟩,hgL ⟨y,hy.2,rfl⟩⟩⟩

 theorem LocallyPrecompact.comp {X Y Z : Type*} [TopologicalSpace X] [MetricSpace Y]
    [TopologicalSpace Z] {f : X → Y} {x : X} (hf : LocallyPrecompact f x)
    (hfc : ContinuousAt f x) (g : Y → Z) (U : Set Y) (ho : IsOpen U)
    (hgu : ContinuousOn g U) (hx : f x∈U) : LocallyPrecompact (g∘f) x := by
  obtain ⟨V,hV,K,hK,hfK⟩ := hf
  obtain ⟨r,hr,hru⟩ := Metric.isOpen_iff.mp ho (f x) hx
  let C := K∩Metric.closedBall (f x) (r/2)
  have hC : IsCompact C := hK.inter_right Metric.isClosed_closedBall
  have hCU : C⊆U := by
    intro y hy
    apply hru
    exact lt_of_le_of_lt hy.2 (half_lt_self hr)
  refine ⟨V∩f ⁻¹' Metric.closedBall (f x) (r/2),inter_mem hV
    (hfc.preimage_mem_nhds (Metric.closedBall_mem_nhds _ (half_pos hr))),g '' C,hC.image_of_continuousOn (hgu.mono hCU),?_⟩
  rintro _ ⟨y,hy,rfl⟩
  exact ⟨f y,⟨hfK ⟨y,hy.1,rfl⟩,hy.2⟩,rfl⟩

 theorem compact_tube_precompact {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace F] (T : ℝ × E → F) (K : Set E) (hK : IsCompact K)
    (hlocal : ∀ y∈Icc (0:ℝ) 1 ×ˢ K, LocallyPrecompact T y) :
    ∃ U : Set E, IsOpen U ∧ K⊆U ∧ ∃ S : Set F, IsCompact S ∧
      ∀ t∈Icc (0:ℝ) 1, ∀ x∈U, T (t,x)∈S := by
  classical
  let Y := Icc (0:ℝ) 1 ×ˢ K
  have hY : IsCompact Y := isCompact_Icc.prod hK
  have hchoice : ∀ y : Y, ∃ W : Set (ℝ×E), IsOpen W ∧ (y : ℝ×E)∈W ∧
      ∃ C : Set F, IsCompact C ∧ T '' W⊆C := by
    intro y
    obtain ⟨V,hV,C,hC,hTC⟩ := hlocal y y.2
    obtain ⟨W,hWV,ho,hyW⟩ := mem_nhds_iff.mp hV
    exact ⟨W,ho,hyW,C,hC,(image_mono hWV).trans hTC⟩
  choose W hWo hyW C hC hTC using hchoice
  obtain ⟨s,hs⟩ := hY.elim_finite_subcover W hWo (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hyW ⟨y,hy⟩⟩)
  let O := ⋃ y∈s, W y
  have ho : IsOpen O := isOpen_biUnion (fun y hy => hWo y)
  obtain ⟨δ,hδ,hδO⟩ := hY.exists_thickening_subset_open ho hs
  refine ⟨Metric.thickening δ K,Metric.isOpen_thickening,Metric.self_subset_thickening hδ _,
    ⋃ y∈s, C y,?_ ,?_⟩
  · exact s.finite_toSet.isCompact_biUnion (fun y hy => hC y)
  · intro t ht x hx
    obtain ⟨k,hk,hxk⟩ := Metric.mem_thickening_iff.mp hx
    have hyO : (t,x)∈O := hδO (Metric.mem_thickening_iff.mpr ⟨(t,k),⟨ht,hk⟩,by
      simpa only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : (0:ℝ)≤dist x k)] using hxk⟩)
    obtain ⟨y,hy,hyW⟩ := mem_iUnion₂.mp hyO
    exact mem_iUnion₂.mpr ⟨y,hy,hTC y ⟨(t,x),hyW,rfl⟩⟩

 theorem local_degree_continuation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ × E → E) (V : Set E) (hV : IsOpen V)
    (hT : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, ContinuousAt T (t,x))
    (hzero : ∀ x∈V, T (0,x)=0)
    (K : Set E) (hK : IsCompact K) (hKV : K⊆V) (h0 : 0∈K)
    (hfix : ∀ t∈Icc (0:ℝ) 1, ∀ x∈V, T (t,x)=x → x∈K)
    (hloc : ∀ t∈Icc (0:ℝ) 1, ∀ x∈K, LocallyPrecompact T (t,x)) :
    ∃ x∈V, T (1,x)=x := by
  obtain ⟨U,hU,hKU,S,hS,hTS⟩ := compact_tube_precompact T K hK (fun y hy => hloc y.1 hy.1 y.2 hy.2)
  obtain ⟨x,hx,he⟩ := local_compact_continuation T (U∩V) (hU.inter hV)
    (fun t ht x hx => hT t ht x hx.2) (fun x hx => hzero x hx.2) S hS
    (fun t ht x hx => hTS t ht x hx.1) K hK (fun x hx => ⟨hKU hx,hKV hx⟩) h0
    (fun t ht x hx he => hfix t ht x hx.2 he)
  exact ⟨x,hx.2,he⟩

end TwoPointContinuation

end

end OAI
