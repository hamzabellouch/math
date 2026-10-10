import Mathlib
import OAI.Geometry.BallPacking.SurfaceArea.QuadricEndResidueMass

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
section
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j,a j≠0)]

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem projectionDomain_frontier_norm {R : ℝ} {x : locus a}
    (hx : x∈frontier (projectionDomain a R)) : ‖x.val.1‖=R := by
  have hle : ‖x.val.1‖≤R := (projectionDomain_closed a R).frontier_subset hx
  apply le_antisymm hle
  by_contra! hlt
  apply hx.2
  have ho : IsOpen {y : locus a | ‖y.val.1‖<R} :=
    isOpen_lt ((continuous_fst.comp continuous_subtype_val).norm) continuous_const
  exact interior_maximal (fun {y : locus a} (hy : ‖y.val.1‖<R) => hy.le) ho hlt

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem projectionDomain_frontier_regular {R : ℝ} (hR : ∀ j,‖a j‖<R^2)
    {x : locus a} (hx : x∈frontier (projectionDomain a R)) : ∀ j,x.val.2 j≠0 := by
  intro j hj
  have he := mem_locus.mp x.property j
  rw [hj,zero_pow (by decide)] at he
  have ht : x.val.1^2=a j := sub_eq_zero.mp he.symm
  have hn := congrArg norm ht
  rw [norm_pow,projectionDomain_frontier_norm hx] at hn
  exact (ne_of_lt (hR j)) hn.symm

theorem projectionDomain_smoothBoundary {R : ℝ} (hRp : 0<R) (hR : ∀ j,‖a j‖<R^2) :
    Hamiltonian.HasSmoothSurfaceBoundary (projectionDomain a R) := by
  intro x hx
  obtain ⟨e,he,heq⟩ := exists_projection_chart x (projectionDomain_frontier_regular hR hx)
  have h0 : 0<(e x).1^2+(e x).2^2 := by
    rw [heq x]
    change 0<x.val.1.re^2+x.val.1.im^2
    have hh := projectionDomain_frontier_norm hx
    have hs : x.val.1.re^2+x.val.1.im^2=R^2 := by
      rw [← Complex.sq_norm_sub_sq_im]
      rw [hh]
      ring
    rw [hs]
    exact sq_pos_of_pos hRp
  obtain ⟨f,hf,hfq⟩ := exists_diskBoundaryDiffeomorph R h0
  refine ⟨e.trans f,⟨he,hf⟩,?_⟩
  intro y _hy
  change ‖y.val.1‖≤R ↔ 0≤(f (e y)).2
  rw [hfq,heq y]
  change ‖y.val.1‖≤R ↔ 0≤R^2-(y.val.1.re^2+y.val.1.im^2)
  have hsq : y.val.1.re^2+y.val.1.im^2=‖y.val.1‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [hsq,sub_nonneg]
  exact sq_le_sq₀ (norm_nonneg _) hRp.le |>.symm

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
def exhaustionRadius (a : Fin m → ℂ) (ℓ : ℕ) : ℝ := 2+∑ j,‖a j‖+ℓ

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem exhaustionRadius_pos (a : Fin m → ℂ) (ℓ : ℕ) : 0<exhaustionRadius a ℓ := by
  unfold exhaustionRadius
  positivity

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem exhaustionRadius_branch (a : Fin m → ℂ) (ℓ : ℕ) (j : Fin m) :
    ‖a j‖<(exhaustionRadius a ℓ)^2 := by
  have hs : ‖a j‖≤∑ k,‖a k‖ := Finset.single_le_sum (fun k _ => norm_nonneg (a k)) (Finset.mem_univ j)
  have he : 2+‖a j‖≤exhaustionRadius a ℓ := by
    unfold exhaustionRadius
    linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  nlinarith [sq_nonneg (exhaustionRadius a ℓ-1),norm_nonneg (a j)]

theorem exists_actual_smooth_projection_exhaustion (a : Fin m → ℂ)
    [Fact (Injective a)] [Fact (∀ j,a j≠0)] :
    ∃ K : ℕ→Set (locus a),(∀ ℓ,IsCompact (K ℓ)) ∧
      (∀ ℓ,K ℓ⊆interior (K (ℓ+1))) ∧ (⋃ ℓ,K ℓ)=univ ∧
      ∀ ℓ,Hamiltonian.HasSmoothSurfaceBoundary (K ℓ) := by
  refine ⟨fun ℓ => projectionDomain a (exhaustionRadius a ℓ),fun ℓ => projectionDomain_compact a _,?_,?_,?_⟩
  · intro ℓ
    apply projectionDomain_nested
    simp only [exhaustionRadius,Nat.cast_add,Nat.cast_one]
    linarith
  · exact projectionDomain_cover a (2+∑ j,‖a j‖)
  · intro ℓ
    exact projectionDomain_smoothBoundary (exhaustionRadius_pos a ℓ) (exhaustionRadius_branch a ℓ)

end

variable {m : ℕ} {a : Fin m → ℂ}

 def signFlip (j : Fin m) (x : locus a) : locus a :=
  ⟨(x.val.1,fun i => if i=j then -x.val.2 i else x.val.2 i), by
    apply mem_locus.mpr
    intro i
    dsimp only
    split_ifs <;> simpa only [neg_sq] using mem_locus.mp x.property i⟩

@[simp] theorem signFlip_projection (j : Fin m) (x : locus a) : (signFlip j x).val.1=x.val.1 := rfl

theorem signFlip_continuous (j : Fin m) : Continuous (signFlip (a := a) j) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
  apply continuous_pi
  intro i
  by_cases hi : i=j
  · simp only [ite_eq_left hi]
    fun_prop
  · simp only [ite_eq_right hi]
    fun_prop

theorem signFlip_fixed_branch (j : Fin m) (b : ℂ) (hb : b^2=a j)
    {x : locus a} (hx : x.val.1=b) : signFlip j x=x := by
  have hj := mem_locus.mp x.property j
  rw [hx,hb,sub_self] at hj
  have hz : x.val.2 j=0 := sq_eq_zero_iff.mp hj
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext i
  by_cases hi : i=j
  · subst i
    simp [signFlip,hz]
  · simp [signFlip,hi]

 def fiberMix (x y : locus a) (hxy : x.val.1=y.val.1) (F : Finset (Fin m)) : locus a :=
  ⟨(x.val.1,fun j => if j∈F then y.val.2 j else x.val.2 j),by
    apply mem_locus.mpr
    intro j
    dsimp only
    split_ifs
    · rw [hxy]; exact mem_locus.mp y.property j
    · exact mem_locus.mp x.property j⟩

@[simp] theorem fiberMix_empty (x y : locus a) (hxy : x.val.1=y.val.1) :
    fiberMix x y hxy ∅=x := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext j
  simp [fiberMix]

@[simp] theorem fiberMix_univ (x y : locus a) (hxy : x.val.1=y.val.1) :
    fiberMix x y hxy Finset.univ=y := by
  apply Subtype.ext
  refine Prod.ext hxy ?_
  funext j
  simp [fiberMix]

theorem fiberMix_insert (x y : locus a) (hxy : x.val.1=y.val.1)
    (F : Finset (Fin m)) (j : Fin m) (hj : j∉F) :
    fiberMix x y hxy (insert j F)=fiberMix x y hxy F ∨
    fiberMix x y hxy (insert j F)=signFlip j (fiberMix x y hxy F) := by
  have hs : y.val.2 j^2=x.val.2 j^2 := by
    rw [mem_locus.mp y.property j,mem_locus.mp x.property j,hxy]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with he | he
  · left
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext i
    by_cases hi : i=j
    · subst i; simp [fiberMix,hj,he]
    · simp [fiberMix,hi]
  · right
    apply Subtype.ext
    refine Prod.ext rfl ?_
    funext i
    by_cases hi : i=j
    · subst i; simp [fiberMix,signFlip,hj,he]
    · simp [fiberMix,signFlip,hi]

theorem signStable_contains_fiber {S : Set (locus a)}
    (hS : ∀ j,MapsTo (signFlip j) S S) {x y : locus a}
    (hx : x∈S) (hxy : x.val.1=y.val.1) : y∈S := by
  have h : ∀ F : Finset (Fin m),fiberMix x y hxy F∈S := by
    intro F
    induction F using Finset.induction_on with
    | empty => simpa using hx
    | @insert j F hj ih =>
      rcases fiberMix_insert x y hxy F j hj with he | he
      · rwa [he]
      · rw [he]; exact hS j ih
  simpa using h Finset.univ

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport
open scoped Topology
open Set Function

theorem component_image_eq_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] [PreconnectedSpace Y]
    (f : X→Y) (hf : IsProperMap f) (ho : IsOpenMap f) (x : X) :
    f '' connectedComponent x=univ := by
  apply IsClopen.eq_univ
  · exact ⟨hf.isClosedMap _ isClosed_connectedComponent,ho _ isOpen_connectedComponent⟩
  · exact ⟨f x,⟨x,mem_connectedComponent,rfl⟩⟩

theorem component_preserved_of_fixed_fiber {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [LocallyConnectedSpace X] [PreconnectedSpace Y]
    (f : X→Y) (hf : IsProperMap f) (ho : IsOpenMap f)
    (τ : X→X) (hτ : Continuous τ) (b : Y) (hfix : ∀ p,f p=b→τ p=p) (x : X) :
    MapsTo τ (connectedComponent x) (connectedComponent x) := by
  have hb : b∈f '' connectedComponent x := by rw [component_image_eq_univ f hf ho x]; trivial
  obtain ⟨p,hp,hpb⟩ := hb
  have hc : connectedComponent p=connectedComponent x := (connectedComponent_eq hp).symm
  have hi := hτ.image_connectedComponent_subset p
  rw [hfix p hpb,hc] at hi
  exact fun y hy => hi ⟨y,hy,rfl⟩

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter MeasureTheory
open Hamiltonian
section

variable {m : ℕ} {a : Fin m → ℂ}

theorem curveProjection_surjective (a : Fin m → ℂ) : Surjective (curveProjection a) := by
  intro t
  refine ⟨⟨(t,fun j => Complex.sqrt (t^2-a j)),?_⟩,rfl⟩
  exact mem_locus.mpr (fun j => sqrt_sq_complex _)

 def signFlipOver (V : Set ℂ) (j : Fin m) (x : curveProjection a ⁻¹' V) :
    curveProjection a ⁻¹' V :=
  ⟨signFlip j x.val,x.property⟩

theorem signFlipOver_continuous (V : Set ℂ) (j : Fin m) :
    Continuous (signFlipOver (a := a) V j) :=
  ((signFlip_continuous j).comp continuous_subtype_val).subtype_mk _

variable [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem projection_preimage_preconnected {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hbranch : ∀ j,Complex.sqrt (a j)∈V) :
    IsPreconnected (curveProjection a ⁻¹' V) := by
  let : LocallyConnectedSpace (locus a) := ChartedSpace.locallyConnectedSpace ℂ (locus a)
  let : LocallyConnectedSpace (curveProjection a ⁻¹' V) :=
    (hVo.preimage (curveProjection_continuous a)).locallyConnectedSpace
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hVc
  rw [isPreconnected_iff_preconnectedSpace]
  apply preconnectedSpace_iff_connectedComponent.mpr
  intro x
  apply eq_univ_of_forall
  intro y
  let f := V.restrictPreimage (curveProjection a)
  have hf : IsProperMap f := (curveProjection_proper a).restrictPreimage V
  have ho : IsOpenMap f := curveProjection_open.restrictPreimage V
  have hflip : ∀ j,MapsTo (signFlipOver V j) (connectedComponent x) (connectedComponent x) := by
    intro j
    apply PackingSufficiencySupport.component_preserved_of_fixed_fiber f hf ho
      (signFlipOver V j) (signFlipOver_continuous V j) ⟨Complex.sqrt (a j),hbranch j⟩ _ x
    intro p hp
    apply Subtype.ext
    exact signFlip_fixed_branch j _ (sqrt_sq_complex _) (congrArg Subtype.val hp)
  have him : f y∈f '' connectedComponent x := by
    rw [PackingSufficiencySupport.component_image_eq_univ f hf ho x]
    trivial
  obtain ⟨z,hz,hzy⟩ := him
  let S : Set (locus a) := Subtype.val '' connectedComponent x
  have hS : ∀ j,MapsTo (signFlip j) S S := by
    rintro j p ⟨q,hq,rfl⟩
    exact ⟨signFlipOver V j q,hflip j hq,rfl⟩
  have hy : y.val∈S := signStable_contains_fiber hS ⟨z,hz,rfl⟩ (congrArg Subtype.val hzy)
  obtain ⟨q,hq,hqy⟩ := hy
  exact (Subtype.ext hqy) ▸ hq

theorem projection_preimage_connected {V : Set ℂ} (hVo : IsOpen V)
    (hVc : IsConnected V) (hbranch : ∀ j,Complex.sqrt (a j)∈V) :
    IsConnected (curveProjection a ⁻¹' V) := by
  refine ⟨?_,projection_preimage_preconnected hVo hVc.isPreconnected hbranch⟩
  obtain ⟨t,ht⟩ := hVc.nonempty
  obtain ⟨x,rfl⟩ := curveProjection_surjective a t
  exact ⟨x,ht⟩

theorem actual_curve_connected : ConnectedSpace (locus a) := by
  have h := projection_preimage_connected (a := a) isOpen_univ isConnected_univ (fun _ => mem_univ _)
  have hp : IsPreconnected (univ : Set (locus a)) := by
    simpa only [preimage_univ] using h.isPreconnected
  let : PreconnectedSpace (locus a) := ⟨hp⟩
  exact ⟨⟨(curveProjection_surjective a 0).choose⟩⟩

theorem projectionDomain_interior {R : ℝ} (hR : 0<R) :
    interior (projectionDomain a R)=curveProjection a ⁻¹' Metric.ball 0 R := by
  have he : projectionDomain a R=curveProjection a ⁻¹' Metric.closedBall 0 R := by
    ext x
    simp only [projectionDomain,mem_ofPred_eq,mem_preimage,Metric.mem_closedBall,
      dist_zero_right,curveProjection]
  rw [he,← curveProjection_open.preimage_interior_eq_interior_preimage
    (curveProjection_continuous a),interior_closedBall _ hR.ne']

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
 theorem sqrt_mem_disk {R : ℝ} (hR : 0<R) {z : ℂ} (hz : ‖z‖<R^2) :
    Complex.sqrt z∈Metric.ball 0 R := by
  rw [Metric.mem_ball,dist_zero_right]
  have he := congrArg norm (sqrt_sq_complex z)
  rw [norm_pow] at he
  exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mp (by rwa [he])

theorem projectionDomain_interior_connected {R : ℝ} (hR : 0<R)
    (hbranch : ∀ j,‖a j‖<R^2) : IsConnected (interior (projectionDomain a R)) := by
  rw [projectionDomain_interior hR]
  exact projection_preimage_connected Metric.isOpen_ball ⟨Metric.nonempty_ball.mpr hR,(convex_ball (0 : ℂ) R).isPreconnected⟩
    (fun j => sqrt_mem_disk hR (hbranch j))

theorem exists_actual_connected_smooth_exhaustion (a : Fin m → ℂ)
    [Fact (Injective a)] [Fact (∀ j,a j≠0)] :
    ∃ K : ℕ→Set (locus a),(∀ ℓ,IsCompact (K ℓ)) ∧
      (∀ ℓ,K ℓ⊆interior (K (ℓ+1))) ∧ (⋃ ℓ,K ℓ)=univ ∧
      (∀ ℓ,IsConnected (interior (K ℓ))) ∧
      ∀ ℓ,Hamiltonian.HasSmoothSurfaceBoundary (K ℓ) := by
  refine ⟨fun ℓ => projectionDomain a (exhaustionRadius a ℓ),fun ℓ => projectionDomain_compact a _,?_,?_,?_,?_⟩
  · intro ℓ
    apply projectionDomain_nested
    simp only [exhaustionRadius,Nat.cast_add,Nat.cast_one]
    linarith
  · exact projectionDomain_cover a (2+∑ j,‖a j‖)
  · intro ℓ
    exact projectionDomain_interior_connected (exhaustionRadius_pos a ℓ) (exhaustionRadius_branch a ℓ)
  · intro ℓ
    exact projectionDomain_smoothBoundary (exhaustionRadius_pos a ℓ) (exhaustionRadius_branch a ℓ)

end
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance : SigmaCompactSpace (locus a) := curveSigmaCompact a

omit [Fact (Injective a)] [Fact (∀ j,a j≠0)] in
theorem compact_eventually_subset_projectionDomain {K : Set (locus a)} (hK : IsCompact K) :
    ∀ᶠ ℓ in atTop,K⊆projectionDomain a (exhaustionRadius a ℓ) := by
  obtain ⟨B,_hB,hbound⟩ := (hK.image (curveProjection_continuous a)).isBounded.exists_pos_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt B
  filter_upwards [eventually_ge_atTop N] with ℓ hℓ
  intro x hx
  have hnx : ‖x.val.1‖≤B := hbound _ ⟨x,hx,rfl⟩
  have hn : (N:ℝ)≤ℓ := by exact_mod_cast hℓ
  change ‖x.val.1‖≤2+∑ j,‖a j‖+ℓ
  have hp : 0≤∑ j,‖a j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg (a j))
  linarith

theorem compact_area_le_degree {c : ℝ} (hc : 0<c) {D : Set (locus a)} (hD : IsCompact D) :
    compactSurfaceFormIntegral hD (curveFSForm a c)≤(2:ℝ)^m*c*Real.pi := by
  obtain ⟨g,r,R,hr,hR,hg,hgc,hb,h1,h0,hreg⟩ := exists_end_cutoff a
  apply ge_of_tendsto (tendsto_curveEndCutoff_mass a hg hgc hr hR.le hreg h1 h0 hb c)
  filter_upwards [curveEndCutoff_eventually_one_on_compact a hR.le h0 hD] with n hn
  exact compactIntegral_le_surfaceCutoffMass (positivePlaneTransitions a) hD
    (shrinking_curveEndCutoff_compact a hr h1 n)
    (curveEndCutoff_smooth a (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
    (fun x => (curveEndCutoff_range a (fun t => hb _) x).1) hn
    (curveFSForm_smooth a c) (curveFSForm_skew a c)
    (fun b y hy => (curveFSForm_positive a hc b hy).le)

theorem tendsto_exhaustion_area {c : ℝ} (hc : 0<c) :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ)) (curveFSForm a c))
      atTop (𝓝 ((2:ℝ)^m*c*Real.pi)) := by
  obtain ⟨g,r,R,hr,hR,hg,hgc,hb,h1,h0,hreg⟩ := exists_end_cutoff a
  have ht := tendsto_curveEndCutoff_mass a hg hgc hr hR.le hreg h1 h0 hb c
  apply tendsto_order.mpr
  constructor
  · intro b hbdeg
    obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).1 b hbdeg).exists
    filter_upwards [compact_eventually_subset_projectionDomain a
      (shrinking_curveEndCutoff_compact a hr h1 n)] with ℓ hℓ
    apply hn.trans_le
    exact surfaceCutoffMass_le_compactIntegral (positivePlaneTransitions a)
      (projectionDomain_compact a _) (shrinking_curveEndCutoff_compact a hr h1 n) hℓ
      (curveEndCutoff_smooth a (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hgc n))
      (fun x => (curveEndCutoff_range a (fun t => hb _) x).2)
      (curveFSForm_smooth a c) (curveFSForm_skew a c)
      (fun b y hy => (curveFSForm_positive a hc b hy).le)
  · intro b hb
    exact Eventually.of_forall (fun ℓ => (compact_area_le_degree a hc
      (projectionDomain_compact a (exhaustionRadius a ℓ))).trans_lt hb)

theorem tendsto_normalized_exhaustion_area :
    Tendsto (fun ℓ => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ)) (curveFSForm a (1/Real.pi)))
      atTop (𝓝 ((2:ℝ)^m)) := by
  have ht := tendsto_exhaustion_area a (one_div_pos.mpr Real.pi_pos)
  convert ht using 1
  field_simp

end

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance : SigmaCompactSpace (locus a) := curveSigmaCompact a

 theorem general_curveCutoffDefect_end_coefficient
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (ε : Fin m → Bool) (c : ℝ)
    {β : Plane → Plane →L[ℝ] ℝ} {y : Plane}
    (hy : y∈(infinityDiffeomorph a ε).source) (hβ : DifferentiableAt ℝ β y)
    (he : (fun z => euclideanPullbackOneForm (fun _ => α)
      (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y] fun z => β z-(c/2) • angularOneForm z) :
    partialChartCoefficient (infinityDiffeomorph a ε)
      (spatialCutoffDefect (curveEndCutoff a g) α) y=
      -cutoffWedge (fun z => g (radiusSq z)) β y+c*deriv g (radiusSq y) := by
  have hD : Complex.equivRealProdCLM.symm y∈infinityDomain a := by
    simpa only [infinityDiffeomorph_source,mem_preimage] using hy
  have hz : radiusSq y≠0 := by
    rw [← radiusSq_complex]
    exact ne_of_gt (Complex.normSq_pos.mpr hD.1)
  have hκα : (fun z => curveEndCutoff a g (infinityDiffeomorph a ε z) •
      euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y]
        fun z => (1-g (radiusSq z)) • (β z-(c/2) • angularOneForm z) := by
    filter_upwards [(infinityDiffeomorph a ε).open_source.mem_nhds hy,he] with z hz haz
    rw [curveEndCutoff_infinity a g ε hz,haz]
  rw [spatialCutoffDefect_coefficient _ (curveEndCutoff_smooth a hg hc)
    hα hy,planarCurl_congr_of_eventuallyEq hκα,
    planarCurl_congr_of_eventuallyEq he,curveEndCutoff_infinity a g ε hy]
  exact planar_residue_defect (hg.differentiable (by simp) _) hβ hz c

 theorem curveEndCutoff_variable_residue_partition_mass
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    {I : Type*} [Fintype I] {K : Set (locus a)} (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox (locus a))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus a) K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκK : tsupport (curveEndCutoff a g)⊆K)
    (hSK : ∀ ε : Fin m → Bool,curveEndAnnulus a ε r R⊆K)
    (c : (Fin m → Bool) → ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
    (he : ∀ ε, ∀ y : Plane,y∈radialAnnulus 0 R → y∈(infinityDiffeomorph a ε).source →
      (fun z => euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y]
        fun z => β ε z-(c ε/2) • angularOneForm z) :
    partitionFormMass B ρ (fun x => curveEndCutoff a g x • manifoldExteriorOneForm α x)=
      (∑ ε : Fin m → Bool,c ε)*Real.pi-
        ∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z := by
  have hκ := curveEndCutoff_smooth a hg hc
  have hzκ (x : locus a) (hx : x∉K) : curveEndCutoff a g x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (hκK hh))
  rw [partitionFormMass_cutoff_defect (positivePlaneTransitions a) hK B ρ hρ hκ hα hzκ]
  have hd := partitionFormMass_finite_disjoint_charts hK (infinityDiffeomorph a)
    (infinityDiffeomorph_positive a)
    (fun i j hij => by simpa only [infinityDiffeomorph_target] using infinityBranch_disjoint a hij)
    (fun ε => curveEndAnnulus a ε r R) (curveEndAnnulus_compact a hr hR) hSK
    (curveEndAnnulus_subset_target a hr hR) B ρ hρ
    (spatialCutoffDefect_smooth hκ hα) (spatialCutoffDefect_skew _ _)
    (fun x hx => by
      obtain ⟨b,hb⟩ := curveEndCutoff_locally_constant_off_annuli a hc hr hR h1 h0 hx
      exact spatialCutoffDefect_zero_of_locally_constant hα hb)
  rw [hd]
  have hi (ε : Fin m → Bool) :
      (∫ y in (infinityDiffeomorph a ε).symm '' curveEndAnnulus a ε r R,
        partialChartCoefficient (infinityDiffeomorph a ε)
          (spatialCutoffDefect (curveEndCutoff a g) α) y)=
        (∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z)-c ε*Real.pi := by
    rw [curveEndAnnulus_coordinates a hr hR ε]
    calc
      _ = ∫ y in radialAnnulus r R,-cutoffWedge (fun z => g (radiusSq z)) (β ε) y+c ε*deriv g (radiusSq y) := by
        apply setIntegral_congr_fun (radialAnnulus_compact r R).measurableSet
        intro y hy
        have hys := radialAnnulus_in_end a hr hR ε hy
        exact general_curveCutoffDefect_end_coefficient a α hα hg hc ε (c ε) hys
          ((hβ ε).differentiable (by simp) _)
          (he ε y ⟨hr.le.trans hy.1,hy.2⟩ hys)
      _ = _ := integral_planar_residue_annulus hg hc hr h1 h0 (hβ ε) (c ε)
  simp_rw [hi]
  rw [Finset.sum_sub_distrib,Finset.sum_mul]
  ring

 theorem curveEndCutoff_variable_residue_mass
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (Ω : ManifoldTwoForm RealModel (locus a)) (hΩ : SmoothTwoForm Ω)
    (hsk : ∀ x v w,Ω x v w= -Ω x w v) (hd : manifoldExteriorOneForm α=Ω)
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκc : HasCompactSupport (curveEndCutoff a g)) (c : (Fin m → Bool) → ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
    (he : ∀ ε, ∀ y : Plane,y∈radialAnnulus 0 R → y∈(infinityDiffeomorph a ε).source →
      (fun z => euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y]
        fun z => β ε z-(c ε/2) • angularOneForm z) :
    surfaceCutoffMass hκc Ω=(∑ ε : Fin m → Bool,c ε)*Real.pi-
      ∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z := by
  let K := tsupport (curveEndCutoff a g)∪⋃ ε : Fin m → Bool,curveEndAnnulus a ε r R
  have hK : IsCompact K := hκc.union (isCompact_iUnion (curveEndAnnulus_compact a hr hR))
  let B := fun b : compactSurfaceBoxes hK => b.1
  let ρ := compactSurfacePartition hK
  have hρ := compactSurfacePartition_subordinate hK
  rw [surfaceCutoffMass_eq (positivePlaneTransitions a) B ρ hρ hκc subset_union_left
    (curveEndCutoff_smooth a hg hc) hΩ hsk,← hd]
  exact curveEndCutoff_variable_residue_partition_mass a α hα hK B ρ hρ hg hc hr hR h1 h0
    subset_union_left (fun ε => (subset_iUnion (curveEndAnnulus a · r R) ε).trans subset_union_right)
    c β hβ he

 theorem tendsto_curveEndCutoff_variable_residue
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (Ω : ManifoldTwoForm RealModel (locus a)) (hΩ : SmoothTwoForm Ω)
    (hsk : ∀ x v w,Ω x v w= -Ω x w v) (hd : manifoldExteriorOneForm α=Ω)
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0<r) (hRp : 0≤R) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hb : ∀ t,g t∈Icc (0:ℝ) 1) (c : (Fin m → Bool) → ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε)) (hβc : ∀ ε,HasCompactSupport (β ε))
    (he : ∀ ε, ∀ y : Plane,y∈radialAnnulus 0 R → y∈(infinityDiffeomorph a ε).source →
      (fun z => euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z))=ᶠ[𝓝 y]
        fun z => β ε z-(c ε/2) • angularOneForm z) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) Ω)
      atTop (𝓝 ((∑ ε : Fin m → Bool,c ε)*Real.pi)) := by
  have hmass (n : ℕ) : surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) Ω=
      (∑ ε : Fin m → Bool,c ε)*Real.pi-
        ∑ ε : Fin m → Bool,∫ z : Plane,shrinkingCutoff g n (radiusSq z)*planarCurl (β ε) z :=
    curveEndCutoff_variable_residue_mass a α hα Ω hΩ hsk hd
      (shrinkingCutoff_smooth hg n) (shrinkingCutoff_compact hc n)
      (div_pos hr (by positivity : 0<(n:ℝ)+1)) hR (shrinkingCutoff_one h1 n)
      (shrinkingCutoff_tsupport hRp h0 n) _ c β hβ he
  simp_rw [hmass]
  have hs := tendsto_finsetSum Finset.univ (fun ε _ => tendsto_shrinking_regular_residue hg hc hb (hβ ε) (hβc ε))
  have hh := (tendsto_const_nhds (x := (∑ ε : Fin m → Bool,c ε)*Real.pi)).sub hs
  simpa only [Finset.sum_const_zero,sub_zero] using hh

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
