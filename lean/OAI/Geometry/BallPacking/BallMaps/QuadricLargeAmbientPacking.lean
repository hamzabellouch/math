import Mathlib
import OAI.Geometry.BallPacking.Normal.QuadricMovingCone

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open Hamiltonian MomentPolytope

 theorem actual_large_polynomial_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ b d t : ℝ,b<1-a₀ ∧ 0<d ∧ d<1/2 ∧ 0<t ∧
      ∃ f : Fin N → Ambient (m+4) → Affine (m+2) × Plane,
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+4) (r' i))
          (fun _ => successorStandardForm (m+3))
          (euclideanExteriorOneForm (firstLinePrimitive
            (normalAmbientPrimitive (parameters m) (1/Real.pi) d t))) (f i)) ∧
        (∀ i,∀ x∈closedBall (m+4) (r' i),radialArea (f i x).2<b) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall (m+4) (r' i))
          (f j '' closedBall (m+4) (r' j))) := by
  classical
  obtain ⟨h₁,h₂,d₁,d₂,_hr₁,hhd₁,hd₁,hr₂,hhd₂,hd₂,ℓ,φ,hφ,hφK,hdisj⟩ :=
    actual_large_normal_packing m r r' hr hr' hrr ha₀ ha₁ hrs hhalf hvol
  let K : Set (LargeNormalSpace (parameters m)) := ⋃ i,φ i '' closedBall (m+4) (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact (m+4) (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hh₁d₁ : (h₁:ℝ)<d₁ := by exact_mod_cast hhd₁
  have hh₂d₂ : (h₂:ℝ)<d₂ := by exact_mod_cast hhd₂
  have hd : 0<(d₂:ℝ) := by
    obtain ⟨i⟩ := ‹Nonempty (Fin N)›
    exact ((hr i).trans (hr₂ i)).trans hh₂d₂
  have hKb (x : LargeNormalSpace (parameters m)) (hx : x∈K) :
      radialArea (normalHead (m+2) x.2)<(d₁:ℝ) := by
    obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
    have hm := (interior_subset (hφK i hy)).2.2 0
    simp only [largeModelBounds,Fin.sum_univ_succ,Matrix.cons_val_zero,
      Fin.cons_zero,Fin.cons_succ,zero_mul,Finset.sum_const_zero,
      add_zero,one_mul] at hm
    exact hm.trans_lt hh₁d₁
  have hKd (x : LargeNormalSpace (parameters m)) (hx : x∈K) :
      Real.pi*phaseSq (normalTail (m+2) x.2)<(d₂:ℝ)*(1-radialArea (normalHead (m+2) x.2)) := by
    have hu := hKb x hx
    have hu1 : radialArea (normalHead (m+2) x.2)<1 := hu.trans (by linarith)
    obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
    have hm := (interior_subset (hφK i hy)).2.2 1
    rw [Fin.sum_univ_succ] at hm
    simp only [largeModelBounds,Matrix.cons_val_one,
      Matrix.cons_val_zero,Fin.cons_zero,Fin.cons_succ,one_mul] at hm
    have he : (∑ j : Fin (m+2),planeMoments (φ i y).2 j.succ)=
        Real.pi*phaseSq (normalTail (m+2) (φ i y).2) := by
      simp only [planeMoments,radialArea,radiusSq,phaseSq,phaseDot_apply,
        normalTail,ContinuousLinearMap.pi_apply,ContinuousLinearMap.proj_apply,
        pow_two,← Finset.mul_sum]
    rw [he] at hm
    have hmul := mul_lt_mul_of_pos_right hh₂d₂ (sub_pos.mpr hu1)
    change (h₂:ℝ)*radialArea (normalHead (m+2) (φ i y).2)+_≤(h₂:ℝ) at hm
    linarith
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hginto,hgform⟩ :=
    exists_actual_large_normal_transfer (parameters m) (by linarith : (d₁:ℝ)<1)
      hd hd₂ hK hKb hKd
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall (m+4) (r' i))
    (fun _ => successorStandardForm (m+3))
    (globalHorizontalCoupling phaseArea (largeHorizontalPrimitive (q := m+2) (parameters m) ∘ planeMoments))
    (euclideanExteriorOneForm (firstLinePrimitive
      (normalAmbientPrimitive (parameters m) (1/Real.pi) d₂ t)))
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hdisj
  exact ⟨d₁,d₂,t,hd₁,hd,hd₂,ht,fun i => g ∘ φ i,hf,
    fun i x hx => hginto _ (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Function Filter
open Set
open Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem primitivePullback_exterior_at {α : F → F →L[ℝ] ℝ} {g : E → F} {x : E}
    (hα : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (primitivePullback α g) x=
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  have hs : ContDiffAt ℝ ∞ (chartOneForm α (g x)) (extChartAt 𝓘(ℝ,F) (g x) (g x)) := by
    rw [show chartOneForm α (g x)=α from funext (vector_chartOneForm α (g x))]
    simpa only [extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using hα
  have hh := manifold_pullback_exterior_at (α := α) (g := g) hs hg.contMDiffAt
  have he : manifoldPullbackOneForm (fun _ => α) g 0=primitivePullback α g := by
    funext z
    simp [manifoldPullbackOneForm,manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback]
  rw [he] at hh
  simpa only [vector_exteriorOneForm,manifoldPullbackOneForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,mfderiv_eq_fderiv,primitivePullback] using hh

 theorem euclideanExteriorOneForm_congr_nhds {α β : E → E →L[ℝ] ℝ} {x : E}
    (he : α =ᶠ[𝓝 x] β) : euclideanExteriorOneForm α x=euclideanExteriorOneForm β x := by
  simp only [euclideanExteriorOneForm,he.fderiv_eq]

end
section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

 def firstDiskDomain : Set (V × Plane) := {x | radialArea x.2<1}
omit [NormedSpace ℝ V] in
 theorem firstDiskDomain_open : IsOpen (firstDiskDomain (V := V)) :=
  isOpen_lt (radialArea_smooth.continuous.comp continuous_snd) continuous_const

 def firstDiskScale (x : V × Plane) : V × Plane :=
  (Real.sqrt (1-radialArea x.2) • x.1,x.2)
 def firstDiskUnscale (x : V × Plane) : V × Plane :=
  ((Real.sqrt (1-radialArea x.2))⁻¹ • x.1,x.2)

 theorem firstDiskScale_smoothOn :
    ContDiffOn ℝ ∞ (firstDiskScale (V := V)) firstDiskDomain :=
  (((contDiffOn_const.sub (radialArea_smooth.comp contDiff_snd).contDiffOn).sqrt
    (fun _ hx => (sub_pos.mpr hx).ne')).smul contDiffOn_fst).prodMk contDiffOn_snd

 theorem firstDiskUnscale_smoothOn :
    ContDiffOn ℝ ∞ (firstDiskUnscale (V := V)) firstDiskDomain :=
  ((((contDiffOn_const.sub (radialArea_smooth.comp contDiff_snd).contDiffOn).sqrt
    (fun _ hx => (sub_pos.mpr hx).ne')).inv
      (fun _ hx => (Real.sqrt_pos.mpr (sub_pos.mpr hx)).ne')).smul contDiffOn_fst).prodMk contDiffOn_snd

 def firstDiskScaleHomeomorph : firstDiskDomain (V := V) ≃ₜ firstDiskDomain (V := V) where
  toEquiv :=
    { toFun := fun x => ⟨firstDiskScale x.val,x.property⟩
      invFun := fun x => ⟨firstDiskUnscale x.val,x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · change (Real.sqrt (1-radialArea x.val.2))⁻¹ •
            (Real.sqrt (1-radialArea x.val.2) • x.val.1)=x.val.1
          rw [smul_smul,inv_mul_cancel₀ (Real.sqrt_pos.mpr (sub_pos.mpr x.property)).ne',one_smul]
        · rfl
      right_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · change Real.sqrt (1-radialArea x.val.2) •
            ((Real.sqrt (1-radialArea x.val.2))⁻¹ • x.val.1)=x.val.1
          rw [smul_smul,mul_inv_cancel₀ (Real.sqrt_pos.mpr (sub_pos.mpr x.property)).ne',one_smul]
        · rfl }
  continuous_toFun := (firstDiskScale_smoothOn.continuousOn.comp_continuous
    continuous_subtype_val (fun x => x.property)).subtype_mk _
  continuous_invFun := (firstDiskUnscale_smoothOn.continuousOn.comp_continuous
    continuous_subtype_val (fun x => x.property)).subtype_mk _

 theorem firstDiskScale_isEmbedding :
    Topology.IsEmbedding (fun x : firstDiskDomain (V := V) => firstDiskScale x.val) :=
  Topology.IsEmbedding.subtypeVal.comp firstDiskScaleHomeomorph.isEmbedding

variable {ι : Type} [Fintype ι]
 def phasePlusPlanePrimitive (x : PlanePhase ι × Plane) : (PlanePhase ι × Plane) →L[ℝ] ℝ :=
  (standardLiouville x.1).comp (ContinuousLinearMap.fst ℝ _ _)+
    (linearLiouville planarArea x.2).comp (ContinuousLinearMap.snd ℝ _ _)

 theorem phasePlusPlanePrimitive_smooth : ContDiff ℝ ∞ (phasePlusPlanePrimitive (ι := ι)) :=
  (((standardLiouville_smooth (ι := ι)).comp contDiff_fst).clm_comp contDiff_const).add
    (((linearLiouville_smooth planarArea).comp contDiff_snd).clm_comp contDiff_const)

 def firstDiskRadial (c : ℝ) (x : PlanePhase ι × Plane) : PlanePhase ι × Plane :=
  firstDiskScale (fsBallMap c x.1,x.2)

 theorem firstDiskRadial_smoothOn (c : ℝ) :
    ContDiffOn ℝ ∞ (firstDiskRadial (ι := ι) c) firstDiskDomain :=
  firstDiskScale_smoothOn.comp
    (((fsBallMap_smooth c).comp contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hx => hx)

 theorem firstDiskRadial_isEmbedding {c : ℝ} (hc : 0<c) :
    Topology.IsEmbedding (fun x : firstDiskDomain (V := PlanePhase ι) => firstDiskRadial c x.val) := by
  have he : Topology.IsEmbedding (fun x : PlanePhase ι × Plane => (fsBallMap c x.1,x.2)) :=
    (fsBallMap_isEmbedding hc).prodMap Topology.IsEmbedding.id
  exact firstDiskScale_isEmbedding.comp
    ((he.comp Topology.IsEmbedding.subtypeVal).codRestrict firstDiskDomain (fun x => x.property))

 theorem firstDiskRadial_primitive {c : ℝ} (hc : 0≤c) {x : PlanePhase ι × Plane}
    (hx : x∈firstDiskDomain) :
    primitivePullback phasePlusPlanePrimitive (firstDiskRadial c) x=
      firstLinePrimitive (affineFSPrimitive c) x := by
  apply ContinuousLinearMap.ext
  intro u
  let s : PlanePhase ι × Plane → ℝ := fun y => Real.sqrt (1-radialArea y.2)
  let w : PlanePhase ι × Plane → PlanePhase ι := fun y => fsBallMap c y.1
  have hs : ContDiffAt ℝ ∞ s x :=
    ((contDiff_const.sub (radialArea_smooth.comp contDiff_snd)).contDiffAt).sqrt (sub_pos.mpr hx).ne'
  have hw : ContDiff ℝ ∞ w := (fsBallMap_smooth c).comp contDiff_fst
  have hD := (((hs.differentiableAt (by simp)).smul (hw.differentiable (by simp) x)).hasFDerivAt.prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x))).fderiv
  change fderiv ℝ (firstDiskRadial c) x=_ at hD
  change phasePlusPlanePrimitive (firstDiskRadial c x) (fderiv ℝ (firstDiskRadial c) x u)=_
  rw [hD]
  change linearLiouville phaseArea (s x • w x) (fderiv ℝ (fun y => s y • w y) x u)+
    linearLiouville planarArea x.2 u.2=_
  rw [linearLiouville_variable_smul phaseArea phaseArea_self (hs.differentiableAt (by simp))
    (hw.differentiable (by simp) x)]
  have hwD := ((fsBallMap_hasFDerivAt c x.1).comp x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).fderiv
  change fderiv ℝ w x=_ at hwD
  rw [hwD]
  rw [← (fsBallMap_hasFDerivAt c x.1).fderiv]
  change (Real.sqrt (1-radialArea x.2))^2*
    standardLiouville (fsBallMap c x.1) (fderiv ℝ (fsBallMap c) x.1 u.1)+
      linearLiouville planarArea x.2 u.2=_
  rw [Real.sq_sqrt (sub_pos.mpr hx).le,fsBallMap_primitive hc,firstLinePrimitive_apply]
  ring

 theorem firstDiskRadial_exterior {c : ℝ} (hc : 0≤c) {x : PlanePhase ι × Plane}
    (hx : x∈firstDiskDomain) :
    (euclideanExteriorOneForm phasePlusPlanePrimitive (firstDiskRadial c x)).bilinearComp
      (fderiv ℝ (firstDiskRadial c) x) (fderiv ℝ (firstDiskRadial c) x)=
        euclideanExteriorOneForm (firstLinePrimitive (affineFSPrimitive c)) x := by
  rw [← primitivePullback_exterior_at (phasePlusPlanePrimitive_smooth (ι := ι)).contDiffAt
    ((firstDiskRadial_smoothOn c).contDiffAt (firstDiskDomain_open.mem_nhds hx))]
  exact euclideanExteriorOneForm_congr_nhds
    (Filter.eventually_of_mem (firstDiskDomain_open.mem_nhds hx) (fun _ hy => firstDiskRadial_primitive hc hy))

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem euclideanTimeField_smooth {V : ℝ × E → E} (hV : ContDiff ℝ ∞ V) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) E)) := by
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have h := (contDiff_snd.prodMk hV).contMDiff
  have hh := contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ,E)) (n := ∞)
  rw [ModelWithCorners.tangent, ← modelWithCornersSelf_prod] at hh
  exact hh.comp h

theorem euclidean_nonautonomous_curve_eqOn_Icc
    {V : ℝ × E → E} (hV : ContDiff ℝ ∞ V) {γ δ : ℝ → E}
    (hγ : ∀ s∈Icc (0:ℝ) 1,HasDerivAt γ (V (s,γ s)) s)
    (hδ : ∀ s∈Icc (0:ℝ) 1,HasDerivAt δ (V (s,δ s)) s)
    (h0 : γ 0=δ 0) : EqOn γ δ (Icc (0:ℝ) 1) := by
  exact nonautonomous_curve_eqOn_Icc (euclideanTimeField_smooth hV)
    (fun s hs => hasMFDerivAt_iff_hasFDerivAt.mpr (hγ s hs).hasFDerivAt)
    (fun s hs => hasMFDerivAt_iff_hasFDerivAt.mpr (hδ s hs).hasFDerivAt) h0

theorem closed_flow_linear_equivariant_on
    {V Φ : ℝ × E → E} (hV : ContDiff ℝ ∞ V)
    (hODE : ∀ x s,s∈Icc (0:ℝ) 1 → HasDerivAt (fun r => Φ (r,x)) (V (s,Φ (s,x))) s)
    (hΦ0 : ∀ x,Φ (0,x)=x) {K : Set E}
    (hstay : ∀ s∈Icc (0:ℝ) 1,∀ x∈K,Φ (s,x)∈K)
    (U : E →L[ℝ] E)
    (hrel : ∀ s∈Icc (0:ℝ) 1,∀ x∈K,V (s,U x)=U (V (s,x))) :
    ∀ s∈Icc (0:ℝ) 1,∀ x∈K,Φ (s,U x)=U (Φ (s,x)) := by
  intro s hs x hx
  apply euclidean_nonautonomous_curve_eqOn_Icc hV
    (fun r hr => hODE (U x) r hr) ?_ ?_ hs
  · intro r hr
    have hd := U.hasFDerivAt.comp_hasDerivAt r (hODE x r hr)
    simpa only [Function.comp_def, hrel r hr _ (hstay r hr x hx)] using hd
  · simp only [hΦ0]

theorem closed_flow_linear_fixed_on
    {V Φ : ℝ × E → E} (hV : ContDiff ℝ ∞ V)
    (hODE : ∀ x s,s∈Icc (0:ℝ) 1 → HasDerivAt (fun r => Φ (r,x)) (V (s,Φ (s,x))) s)
    (hΦ0 : ∀ x,Φ (0,x)=x) {K : Set E}
    (hstay : ∀ s∈Icc (0:ℝ) 1,∀ x∈K,Φ (s,x)∈K)
    (U : E →L[ℝ] E)
    (hrel : ∀ s∈Icc (0:ℝ) 1,∀ x∈K,V (s,U x)=U (V (s,x)))
    {x : E} (hx : x∈K) (hUx : U x=x) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    U (Φ (s,x))=Φ (s,x) := by
  simpa only [hUx] using (closed_flow_linear_equivariant_on hV hODE hΦ0 hstay U hrel s hs x hx).symm

end

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem homogeneousCone_shell_flow_linear_equivariant
    {F : PlanePhase ι → PlanePhase κ} (hF : ContDiff ℝ ∞ F)
    (hF0 : ∀ z,z≠0 → F z≠0)
    (hD : ∀ z,fderiv ℝ F z z=(2:ℝ)•F z)
    (hJ : ∀ z v,fderiv ℝ F z (phaseJ v)=phaseJ (fderiv ℝ F z v))
    {c d a b : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2) (ha : 0<a)
    {Φ V : ℝ × PlanePhase ι → PlanePhase ι}
    (hΦ0 : ∀ x,Φ (0,x)=x)
    (hΦr : ∀ s∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (s,x))=phaseSq x)
    (hV : ContDiff ℝ ∞ V)
    (hODE : ∀ x s,s∈Ioo (-2:ℝ) 2 → HasDerivAt (fun r => Φ (r,x)) (V (s,Φ (s,x))) s)
    (hVe : ∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,V (s,x)=homogeneousConeField F c d s x)
    (U : PlanePhase ι ≃L[ℝ] PlanePhase ι) (T : PlanePhase κ →L[ℝ] PlanePhase κ)
    (hFT : ∀ z,F (U z)=T (F z))
    (hUD : ∀ z v,phaseDot (U z) (U v)=phaseDot z v)
    (hUA : ∀ z v,phaseArea (U z) (U v)=phaseArea z v)
    (hTD : ∀ z v,phaseDot (T z) (T v)=phaseDot z v)
    (hTA : ∀ z v,phaseArea (T z) (T v)=phaseArea z v) :
    ∀ s∈Icc (0:ℝ) 1,∀ x∈phaseShell a b,Φ (s,U x)=U (Φ (s,x)) := by
  apply closed_flow_linear_equivariant_on hV
    (fun x s hs => hODE x s ⟨by linarith [hs.1],by linarith [hs.2]⟩) hΦ0
    (fun s hs x hx => phaseShell_radial a b hx (hΦr s hs x)) U.toContinuousLinearMap
  intro s hs x hx
  have hUx : U x∈phaseShell a b :=
    phaseShell_radial a b hx (hUD x x)
  change V (s,U x)=U (V (s,x))
  rw [hVe s hs _ hUx,hVe s hs x hx]
  exact homogeneousConeField_linear_invariant hF hF0 hD hJ U T hFT hUD hUA hTD hTA
    hc (mul_nonneg hs.1 hd) (lt_of_le_of_lt (by nlinarith [hs.2]) hdhalf)
    (phaseShell_nonzero ha hx)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
open Hamiltonian

variable {m : ℕ}

abbrev HomogeneousInput (m : ℕ) := Option (Option (Fin m)) → ℂ
abbrev HomogeneousOutput (m : ℕ) := Option (NormalPolynomialIndex m) → ℂ

def homogeneousPolynomial (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    HomogeneousOutput m
  | none => z none^2
  | some (.inl (.inl i)) => z none*z (some i.2)
  | some (.inl (.inr i)) => z (some i.1)*z (some i.2)
  | some (.inr j) => (t:ℂ)⁻¹*(z (some (some j))^2-z (some none)^2+a j*z none^2)

theorem homogeneousPolynomial_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℂ ∞ (homogeneousPolynomial a t) := by
  apply contDiff_pi.mpr
  rintro (_|((⟨b,i⟩|⟨i,j⟩)|j))
  · exact (contDiff_apply ℂ ℂ none).pow 2
  · exact (contDiff_apply ℂ ℂ none).mul (contDiff_apply ℂ ℂ (some i))
  · exact (contDiff_apply ℂ ℂ (some i)).mul (contDiff_apply ℂ ℂ (some j))
  · exact contDiff_const.mul (((contDiff_apply ℂ ℂ (some (some j))).pow 2).sub
      ((contDiff_apply ℂ ℂ (some none)).pow 2) |>.add
      (contDiff_const.mul ((contDiff_apply ℂ ℂ none).pow 2)))

theorem homogeneousPolynomial_homogeneous (a : Fin m → ℂ) (t : ℝ)
    (b : ℂ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t (b•z)=b^2•homogeneousPolynomial a t z := by
  funext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  all_goals simp only [homogeneousPolynomial,Pi.smul_apply,smul_eq_mul]; ring

theorem homogeneousPolynomial_zero_iff (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t z=0 ↔ z=0 := by
  constructor
  · intro h
    funext i
    cases i with
    | none =>
      have hh := congrFun h none
      change z none^2=0 at hh
      exact eq_zero_of_pow_eq_zero hh
    | some i =>
      have hh := congrFun h (some (.inl (.inr (i,i))))
      change z (some i)*z (some i)=0 at hh
      exact (mul_self_eq_zero.mp hh)
  · rintro rfl
    funext i
    rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
    all_goals simp [homogeneousPolynomial]

theorem homogeneousPolynomial_nonzero (a : Fin m → ℂ) (t : ℝ)
    {z : HomogeneousInput m} (hz : z≠0) : homogeneousPolynomial a t z≠0 :=
  fun h => hz ((homogeneousPolynomial_zero_iff a t z).mp h)

theorem homogeneousPolynomial_affine (a : Fin m → ℂ) (t : ℝ) (z : Affine m) :
    homogeneousPolynomial a t (fun i => match i with
      | none => 1 | some j => affineComplex m z j)=
    (fun i => match i with | none => 1 | some j => normalPolynomial a t z j) := by
  funext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  · simp [homogeneousPolynomial]
  · simp [homogeneousPolynomial,normalPolynomial,veronese]
  · rfl
  · simp [homogeneousPolynomial,normalPolynomial,equations,affineComplex]

theorem homogeneousPolynomial_euler (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    fderiv ℂ (homogeneousPolynomial a t) z z= (2:ℂ)•homogeneousPolynomial a t z := by
  have hf := (homogeneousPolynomial_smooth a t).differentiable (by simp) z
  have hf' : HasFDerivAt (homogeneousPolynomial a t)
      (fderiv ℂ (homogeneousPolynomial a t) z) ((1:ℂ)•z) := by
    simpa only [one_smul] using hf.hasFDerivAt
  have hd := hf'.comp_hasDerivAt (1:ℂ) ((hasDerivAt_id (1:ℂ)).smul_const z)
  have he : (fun b : ℂ => homogeneousPolynomial a t (b•z))=
      (fun b : ℂ => b^2•homogeneousPolynomial a t z) :=
    funext (fun b => homogeneousPolynomial_homogeneous a t b z)
  have hd' : HasDerivAt (fun b : ℂ => b^2•homogeneousPolynomial a t z)
      ((2:ℂ)•homogeneousPolynomial a t z) 1 := by
    convert! (((hasDerivAt_id (1:ℂ)).pow 2).smul_const (homogeneousPolynomial a t z)) using 1; simp
  simp only [Function.comp_def,id_eq] at hd
  rw [he] at hd
  simpa only [one_smul] using hd.unique hd'

def homogeneousCartesian (a : Fin m → ℂ) (t : ℝ) :
    PlanePhase (Option (Option (Fin m))) → PlanePhase (Option (NormalPolynomialIndex m)) :=
  fun z => complexCartesian (homogeneousPolynomial a t (complexCartesian.symm z))

theorem homogeneousCartesian_smooth (a : Fin m → ℂ) (t : ℝ) :
    ContDiff ℝ ∞ (homogeneousCartesian a t) :=
  (complexCartesian (ι := Option (NormalPolynomialIndex m))).contDiff.comp
    (((homogeneousPolynomial_smooth a t).restrict_scalars ℝ).comp
      (complexCartesian (ι := Option (Option (Fin m)))).symm.contDiff)

theorem homogeneousCartesian_nonzero (a : Fin m → ℂ) (t : ℝ)
    {z : PlanePhase (Option (Option (Fin m)))} (hz : z≠0) : homogeneousCartesian a t z≠0 := by
  intro h
  have hP : homogeneousPolynomial a t (complexCartesian.symm z)=0 :=
    complexCartesian.injective (h.trans (map_zero _).symm)
  have hh := (homogeneousPolynomial_zero_iff a t _).mp hP
  exact hz (by simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using congrArg complexCartesian hh)

theorem homogeneousCartesian_fderiv (a : Fin m → ℂ) (t : ℝ)
    (z v : PlanePhase (Option (Option (Fin m)))) :
    fderiv ℝ (homogeneousCartesian a t) z v=complexCartesian
      (fderiv ℂ (homogeneousPolynomial a t) (complexCartesian.symm z) (complexCartesian.symm v)) := by
  have hh := ((homogeneousPolynomial_smooth a t).differentiable (by simp)
    (complexCartesian.symm z)).hasFDerivAt.restrictScalars ℝ
  have hd := complexCartesian.toContinuousLinearMap.hasFDerivAt.comp z
    (hh.comp z (complexCartesian (ι := Option (Option (Fin m)))).symm.hasFDerivAt)
  exact congrArg (fun L => L v) hd.fderiv

theorem homogeneousCartesian_euler (a : Fin m → ℂ) (t : ℝ)
    (z : PlanePhase (Option (Option (Fin m)))) :
    fderiv ℝ (homogeneousCartesian a t) z z=(2:ℝ)•homogeneousCartesian a t z := by
  rw [homogeneousCartesian_fderiv,homogeneousPolynomial_euler]
  rw [show (2:ℂ)•homogeneousPolynomial a t (complexCartesian.symm z)=
    (2:ℝ)•homogeneousPolynomial a t (complexCartesian.symm z) by
      ext i; simp [Pi.smul_apply,Complex.real_smul]]
  exact map_smul _ _ _

theorem homogeneousCartesian_J (a : Fin m → ℂ) (t : ℝ)
    (z v : PlanePhase (Option (Option (Fin m)))) :
    fderiv ℝ (homogeneousCartesian a t) z (phaseJ v)=
      phaseJ (fderiv ℝ (homogeneousCartesian a t) z v) := by
  have hJ : complexCartesian.symm (phaseJ v)=Complex.I•complexCartesian.symm v := by
    apply complexCartesian.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply,complexCartesian_I]
  rw [homogeneousCartesian_fderiv,homogeneousCartesian_fderiv,hJ,map_smul,complexCartesian_I]

theorem homogeneousQuadricCone_isInvertible (a : Fin m → ℂ) (t : ℝ)
    {c d : ℝ} (hc : 0<c) (hd : 0≤d) (hdhalf : d<1/2)
    {z : PlanePhase (Option (Option (Fin m)))} (hz : z≠0) :
    (euclideanExteriorOneForm (homogeneousConePrimitive (homogeneousCartesian a t) c d) z).IsInvertible :=
  homogeneousConePrimitive_nondegenerate (homogeneousCartesian_smooth a t).contDiffAt hz
    (homogeneousCartesian_nonzero a t hz) (homogeneousCartesian_euler a t z)
    (homogeneousCartesian_J a t z) hc hd hdhalf

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators

variable {ι : Type*} [Fintype ι]

def infinitySign : Option ι → ℂ
  | none => -1
  | some _ => 1

omit [Fintype ι] in
theorem infinitySign_unit (i : Option ι) : Complex.normSq (infinitySign i)=1 := by
  cases i <;> norm_num [infinitySign]

omit [Fintype ι] in
theorem complexDiagonal_infinity_fixed (z : Option ι → ℂ) :
    complexDiagonal infinitySign z=z ↔ z none=0 := by
  constructor
  · intro h
    have h₀ := congrFun h none
    change (-1:ℂ)*z none=z none at h₀
    have hh : (2:ℂ)*z none=0 := by linear_combination -h₀
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  · intro h
    ext i
    cases i <;> simp [complexDiagonal_apply,infinitySign,h]

theorem phaseUnitDiagonal_infinity_fixed (z : PlanePhase (Option ι)) :
    phaseUnitDiagonal infinitySign infinitySign_unit z=z ↔
      complexCartesian.symm z none=0 := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  simp only [phaseUnitDiagonal_apply,phaseDiagonal_cartesian,
    ContinuousLinearEquiv.symm_apply_apply,complexCartesian.injective.eq_iff,
    complexDiagonal_infinity_fixed]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff BigOperators
open Hamiltonian

variable {m : ℕ}

def homogeneousInfinityOutputSign : Option (NormalPolynomialIndex m) → ℂ
  | some (.inl (.inl _)) => -1
  | _ => 1

theorem homogeneousInfinityOutputSign_unit (i : Option (NormalPolynomialIndex m)) :
    Complex.normSq (homogeneousInfinityOutputSign i)=1 := by
  rcases i with _|((_ |_)|_)
  all_goals norm_num [homogeneousInfinityOutputSign]

theorem homogeneousPolynomial_infinity (a : Fin m → ℂ) (t : ℝ) (z : HomogeneousInput m) :
    homogeneousPolynomial a t (complexDiagonal infinitySign z)=
      complexDiagonal homogeneousInfinityOutputSign (homogeneousPolynomial a t z) := by
  ext i
  rcases i with _|((⟨e,i⟩|⟨i,j⟩)|j)
  all_goals simp [homogeneousPolynomial,complexDiagonal_apply,infinitySign,
    homogeneousInfinityOutputSign]

theorem homogeneousCartesian_diagonal (a : Fin m → ℂ) (t : ℝ)
    (u : Option (Option (Fin m)) → ℂ) (hu : ∀ i,Complex.normSq (u i)=1)
    (v : Option (NormalPolynomialIndex m) → ℂ)
    (he : ∀ z,homogeneousPolynomial a t (complexDiagonal u z)=
      complexDiagonal v (homogeneousPolynomial a t z))
    (z : PlanePhase (Option (Option (Fin m)))) :
    homogeneousCartesian a t (phaseUnitDiagonal u hu z)=
      phaseDiagonal v (homogeneousCartesian a t z) := by
  obtain ⟨z,rfl⟩ := complexCartesian.surjective z
  simp only [homogeneousCartesian,phaseUnitDiagonal_apply,phaseDiagonal_cartesian,
    ContinuousLinearEquiv.symm_apply_apply,he]

theorem homogeneousCartesian_circle (a : Fin m → ℂ) (t : ℝ) (ζ : ℂ)
    (hζ : Complex.normSq ζ=1) (z : PlanePhase (Option (Option (Fin m)))) :
    homogeneousCartesian a t (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z)=
      phaseDiagonal (fun _ => ζ^2) (homogeneousCartesian a t z) := by
  apply homogeneousCartesian_diagonal
  intro z
  change homogeneousPolynomial a t (ζ•z)=ζ^2•homogeneousPolynomial a t z
  exact homogeneousPolynomial_homogeneous a t ζ z

theorem homogeneousCartesian_infinity (a : Fin m → ℂ) (t : ℝ)
    (z : PlanePhase (Option (Option (Fin m)))) :
    homogeneousCartesian a t (phaseUnitDiagonal infinitySign infinitySign_unit z)=
      phaseDiagonal homogeneousInfinityOutputSign (homogeneousCartesian a t z) :=
  homogeneousCartesian_diagonal a t infinitySign infinitySign_unit homogeneousInfinityOutputSign
    (homogeneousPolynomial_infinity a t) z

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
