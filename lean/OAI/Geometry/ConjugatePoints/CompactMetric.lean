import OAI.Geometry.ConjugatePoints.Metric
import OAI.Geometry.ConjugatePoints.Cometric

namespace OAI

noncomputable section

/-!
# The smooth Riemannian metric on the compact glued manifold.
-/

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction

def radialLinear (a : ℝ) (ha : a ≠ 0) : P ≃L[ℝ] P :=
  { toFun := fun v => (a*v.1,v.2)
    invFun := fun v => (v.1/a,v.2)
    left_inv := by intro v; apply Prod.ext <;> simp [ha]
    right_inv := by
      intro v
      apply Prod.ext
      · change a*(v.1/a) = v.1
        field_simp
      · rfl
    map_add' := by
      intro v w
      apply Prod.ext
      · change a*(v.1+w.1) = a*v.1+a*w.1
        ring
      · rfl
    map_smul' := by
      intro c v
      apply Prod.ext
      · change a*(c*v.1) = c*(a*v.1)
        ring
      · rfl }

def radial (L : ℝ) (x : Cylinder) : Cylinder := (RadialProfile.coordinate L x.1,x.2)
def radialLift (L : ℝ) (x : P) : P := (RadialProfile.coordinate L x.1,x.2)
lemma radial_smooth (L : ℝ) : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (radial L) := by
  have h := ((RadialProfile.coordinate_smooth L).contMDiff.comp
    (projection_fst_smooth (E := ℝ) (F := ℝ × ℝ) (M := ℝ) (N := AddCircle (6:ℝ) × AddCircle (6:ℝ)))).prodMk
      (projection_snd_smooth (E := ℝ) (F := ℝ × ℝ) (M := ℝ) (N := AddCircle (6:ℝ) × AddCircle (6:ℝ)))
  convert! h using 1
  simp only [← modelWithCornersSelf_prod]
lemma radialLift_smooth (L : ℝ) : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (radialLift L) :=
  ((RadialProfile.coordinate_smooth L).comp contDiff_fst |>.prodMk contDiff_snd).contMDiff
lemma radialLift_deriv {L : ℝ} (hL : 4 ≤ L) (x : P) :
    (radialLinear (RadialProfile.slope L x.1) (RadialProfile.slope_pos hL x.1).ne').toContinuousLinearMap =
      mfderiv 𝓘(ℝ,P) 𝓘(ℝ,P) (radialLift L) x := by
  rw [mfderiv_eq_fderiv]
  have hd := ((RadialProfile.coordinate_deriv L x.1).comp_hasFDerivAt x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  calc
    _ = _ := ?_
    _ = fderiv ℝ (radialLift L) x := hd.fderiv.symm
  apply ContinuousLinearMap.ext
  intro v
  rfl
lemma radial_commutes (L : ℝ) : radial L ∘ projection = projection ∘ radialLift L := rfl

def radialPull (g : Metric (E := P) Cylinder) {L : ℝ} (hL : 4 ≤ L) :
    Metric (E := P) Cylinder :=
  pullbackFromLift projection_cover projection_smooth local_inverse_smooth
    (radial_smooth L) (radialLift_smooth L) (radial_commutes L)
    (fun x => radialLinear (RadialProfile.slope L x.1) (RadialProfile.slope_pos hL x.1).ne')
    (radialLift_deriv hL) section_spec g

def radius₁ (δ B : ℝ) (t : ℝ) : ℝ := δ^2*B/6 * Collar.ell δ t
def radius₂ (δ B : ℝ) (t : ℝ) : ℝ := B/6 * Collar.ell δ (1-t)
lemma radius₁_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1/2)) (B : ℝ) : ContDiff ℝ ∞ (radius₁ δ B) :=
  contDiff_const.mul (Collar.ell_smooth hδ)
lemma radius₂_smooth {δ : ℝ} (hδ : δ ∈ Icc 0 (1/2)) (B : ℝ) : ContDiff ℝ ∞ (radius₂ δ B) :=
  contDiff_const.mul ((Collar.ell_smooth hδ).comp (contDiff_const.sub contDiff_id))
lemma radius₁_pos {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) (t : ℝ) : 0 < radius₁ δ B t :=
  mul_pos (div_pos (mul_pos (sq_pos_of_pos hδ) hB) (by norm_num)) (Collar.ell_pos δ t)
lemma radius₂_pos {δ B : ℝ} (hB : 0 < B) (t : ℝ) : 0 < radius₂ δ B t :=
  mul_pos (div_pos hB (by norm_num)) (Collar.ell_pos δ (1-t))

def neck {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) : Metric (E := P) Cylinder :=
  CylinderConstruction.metric (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B)
    (radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B) Cometric.χ_smooth
    (fun t => (radius₁_pos hδ.1 hB t).ne') (fun t => (radius₂_pos hB t).ne')
end ThreeManifold.CompactMetric

namespace ThreeManifold.MetricConstruction
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma openSubtype_inverse_smooth (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    {x : M} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (U.openPartialHomeomorphSubtypeCoe hU).symm x := by
  apply (ContMDiffAt.subtypeVal_comp_iff U _ x).mp
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv (by simpa using hy)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma openSubtype_mdifferentiable (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    (U.openPartialHomeomorphSubtypeCoe hU).MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,E) := by
  constructor
  · exact (contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiable (by simp) |>.mdifferentiableOn
  · intro x hx
    exact (openSubtype_inverse_smooth U hU (by simpa using hx)).mdifferentiableAt
      (by simp) |>.mdifferentiableWithinAt

def restrict (g : Metric (E := E) M) (U : TopologicalSpace.Opens M) : Metric (E := E) U :=
  pullback g (contMDiff_subtype_val (U := U))
    (fun x => (openSubtype_mdifferentiable U ⟨x⟩).mfderiv (by simp)) (fun _ => rfl)

lemma restrict_inner (g : Metric (E := E) M) (U : TopologicalSpace.Opens M) (x : U) :
    (restrict g U).inner x = pullInner g (Subtype.val : U → M) x := rfl
end ThreeManifold.MetricConstruction

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction
open HyperbolicCore (rayOpens)

def timeReverse : ℝ ≃ₜ ℝ where
  toFun t := 1-t
  invFun t := 1-t
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

def switch : Cylinder ≃ₜ Cylinder := timeReverse.prodCongr GluedConstruction.torusShear
lemma switch_smooth : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ switch := by
  have h0 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun q : Cylinder => 1-q.1) :=
    contMDiff_const.sub projection_fst_smooth
  have h1 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ × ℝ) ∞
      (fun q : Cylinder => GluedConstruction.torusShear q.2) := by
    convert! GluedConstruction.torusShear_smooth.comp
      (projection_snd_smooth (E := ℝ) (F := ℝ × ℝ) (M := ℝ) (N := AddCircle (6:ℝ) × AddCircle (6:ℝ))) using 1
    simp only [← modelWithCornersSelf_prod]
  convert! h0.prodMk h1 using 1
  simp only [← modelWithCornersSelf_prod]
lemma switch_symm_smooth : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ switch.symm := by
  have h0 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun q : Cylinder => 1-q.1) :=
    contMDiff_const.sub projection_fst_smooth
  have h1 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ × ℝ) ∞
      (fun q : Cylinder => GluedConstruction.torusShear.symm q.2) := by
    convert! GluedConstruction.torusShear_symm_smooth.comp
      (projection_snd_smooth (E := ℝ) (F := ℝ × ℝ) (M := ℝ) (N := AddCircle (6:ℝ) × AddCircle (6:ℝ))) using 1
    simp only [← modelWithCornersSelf_prod]
  convert! h0.prodMk h1 using 1
  simp only [← modelWithCornersSelf_prod]

def switched (g : Metric (E := P) Cylinder) : Metric (E := P) Cylinder :=
  pullbackHomeomorph g switch switch_smooth switch_symm_smooth

abbrev HeightCylinder (a : ℝ) := Ioi a × (AddCircle (6:ℝ) × AddCircle (6:ℝ))
def logDomain (a : ℝ) : TopologicalSpace.Opens Cylinder :=
  ⟨{q | Real.log a < q.1},isOpen_lt continuous_const continuous_fst⟩

def logCylinderHomeomorph (a : ℝ) (ha : 0 < a) : HeightCylinder a ≃ₜ logDomain a where
  toFun q := ⟨(Real.log q.1.1,q.2), (Real.strictMonoOn_log ha (lt_trans ha q.1.2) q.1.2)⟩
  invFun q := (⟨Real.exp q.1.1,by
    have h := Real.exp_lt_exp.mpr q.2
    rwa [Real.exp_log ha] at h⟩,q.1.2)
  left_inv q := by ext <;> simp [Real.exp_log (lt_trans ha q.1.2)]
  right_inv q := by ext <;> simp
  continuous_toFun := (((continuous_subtype_val.comp continuous_fst).log
      (fun q => ne_of_gt (lt_trans ha q.1.2))).prodMk continuous_snd).subtype_mk _
  continuous_invFun := (((Real.continuous_exp.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val))

lemma logCylinder_smooth (a : ℝ) (ha : 0 < a) :
    ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (logCylinderHomeomorph a ha) := by
  apply (ContMDiff.subtypeVal_comp_iff (logDomain a) _).mp
  have hh : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun q : HeightCylinder a => q.1.1) :=
    (contMDiff_subtype_val (U := rayOpens a)).comp projection_fst_smooth
  have hl : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun q : HeightCylinder a => Real.log q.1.1) :=
    fun q => (Real.contDiffAt_log.mpr (ne_of_gt (lt_trans ha q.1.2))).contMDiffAt.comp q (hh q)
  have hs : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ × ℝ) ∞ (Prod.snd : HeightCylinder a → _) :=
    projection_snd_smooth
  convert! hl.prodMk hs using 1
  simp only [← modelWithCornersSelf_prod]

lemma logCylinder_symm_smooth (a : ℝ) (ha : 0 < a) :
    ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (logCylinderHomeomorph a ha).symm := by
  have hv : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (Subtype.val : logDomain a → Cylinder) :=
    contMDiff_subtype_val
  have h0 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun q : logDomain a =>
      (logCylinderHomeomorph a ha).symm q |>.1) := by
    apply (ContMDiff.subtypeVal_comp_iff (rayOpens a) _).mp
    exact Real.contDiff_exp.contMDiff.comp (projection_fst_smooth.comp hv)
  have h1 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ × ℝ) ∞ (fun q : logDomain a => q.1.2) :=
    projection_snd_smooth.comp hv
  convert! h0.prodMk h1 using 1
  simp only [← modelWithCornersSelf_prod]

def heightMetric (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 0 < a) :
    Metric (E := P) (HeightCylinder a) :=
  pullbackHomeomorph (MetricConstruction.restrict g (logDomain a)) (logCylinderHomeomorph a ha)
    (logCylinder_smooth a ha) (logCylinder_symm_smooth a ha)
end ThreeManifold.CompactMetric

namespace ThreeManifold.MetricConstruction

section
variable {E M A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

structure LocalMetric (M : Type*) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] where
  domain : Set M
  open_domain : IsOpen domain
  inner : ∀ x : M, TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ
  symm : ∀ x ∈ domain, ∀ u v, inner x u v = inner x v u
  pos : ∀ x ∈ domain, ∀ u, u ≠ 0 → 0 < inner x u u
  bounded : ∀ x ∈ domain, IsVonNBounded ℝ {u | inner x u u < 1}
  smooth : ∀ x ∈ domain, ContMDiffAt 𝓘(ℝ,E)
    (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun z => TangentSpace 𝓘(ℝ,E) z →L[ℝ] TangentSpace 𝓘(ℝ,E) z →L[ℝ] ℝ)
      y (inner y)) x

variable (g : A → LocalMetric (E := E) M)
    (cover : ∀ x, ∃ i, x ∈ (g i).domain)
    (compat : ∀ i j x, x ∈ (g i).domain → x ∈ (g j).domain → (g i).inner x = (g j).inner x)

def localGluedInner (x : M) := (g (cover x).choose).inner x

include compat in
lemma localGluedInner_eq (i : A) (x : M) (hx : x ∈ (g i).domain) :
    localGluedInner g cover x = (g i).inner x :=
  compat _ i x (cover x).choose_spec hx

include compat in
lemma localGluedInner_smooth :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z => TangentSpace 𝓘(ℝ,E) z →L[ℝ] TangentSpace 𝓘(ℝ,E) z →L[ℝ] ℝ)
        y (localGluedInner g cover y)) := by
  intro x
  obtain ⟨i,hi⟩ := cover x
  apply ((g i).smooth x hi).congr_of_eventuallyEq
  filter_upwards [(g i).open_domain.mem_nhds hi] with y hy
  exact congrArg (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y)
    (localGluedInner_eq g cover compat i y hy)

def glueLocal : Metric (E := E) M where
  inner := localGluedInner g cover
  symm x := (g (cover x).choose).symm x (cover x).choose_spec
  pos x := (g (cover x).choose).pos x (cover x).choose_spec
  isVonNBounded x := (g (cover x).choose).bounded x (cover x).choose_spec
  contMDiff := localGluedInner_smooth g cover compat

lemma glueLocal_eq (i : A) (x : M) (hx : x ∈ (g i).domain) :
    (glueLocal g cover compat).inner x = (g i).inner x :=
  localGluedInner_eq g cover compat i x hx
end

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def localPull (g : Metric (E := F) N) (e : OpenPartialHomeomorph M N)
    (hs : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ e e.source)
    (he : e.MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F)) : LocalMetric (E := E) M where
  domain := e.source
  open_domain := e.open_source
  inner := pullInner g e
  symm x _ u v := g.symm (e x) _ _
  pos x hx u hu := by
    apply g.pos
    let d := he.mfderiv hx
    exact fun hh => hu (d.injective (hh.trans d.map_zero.symm))
  bounded x hx := by
    let d := he.mfderiv hx
    apply ((g.isVonNBounded (e x)).image d.symm.toContinuousLinearMap).subset
    intro u hu
    exact ⟨d u,hu,d.symm_apply_apply u⟩
  smooth x hx := pullback_inner_smoothAt g ((hs x hx).contMDiffAt (e.open_source.mem_nhds hx))

def localOn (g : Metric (E := E) M) (U : TopologicalSpace.Opens M) : LocalMetric (E := E) M where
  domain := U
  open_domain := U.isOpen
  inner := g.inner
  symm x _ := g.symm x
  pos x _ := g.pos x
  bounded x _ := g.isVonNBounded x
  smooth x _ := g.contMDiff x
end ThreeManifold.MetricConstruction

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction
open HyperbolicCore (Surface cusp cuspOpens cuspCoordinates cuspCoordinates_smooth cuspCoordinates_symm_smooth rayOpens)
abbrev WholePiece := Surface × AddCircle (6:ℝ)
abbrev EP := ℂ × ℝ

def wholeCusp (a : ℝ) : TopologicalSpace.Opens WholePiece :=
  ⟨{q | q.1 ∈ cusp a}, (cuspOpens a).isOpen.preimage continuous_fst⟩

def wholeCoordinates (a : ℝ) (ha : 1 < a) : wholeCusp a ≃ₜ HeightCylinder a where
  toFun q := ((cuspCoordinates a ha ⟨q.1.1,q.2⟩).1,
    ( (cuspCoordinates a ha ⟨q.1.1,q.2⟩).2, q.1.2))
  invFun q := ⟨(((cuspCoordinates a ha).symm (q.1,q.2.1)).1,q.2.2),
    ((cuspCoordinates a ha).symm (q.1,q.2.1)).2⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((cuspCoordinates a ha).symm_apply_apply ⟨q.1.1,q.2⟩)
    · rfl
  right_inv q := by
    have h := (cuspCoordinates a ha).apply_symm_apply (q.1,q.2.1)
    change ((cuspCoordinates a ha ((cuspCoordinates a ha).symm (q.1,q.2.1))).1,
      (cuspCoordinates a ha ((cuspCoordinates a ha).symm (q.1,q.2.1))).2,q.2.2) = q
    rw [h]
  continuous_toFun := by
    have h := (cuspCoordinates a ha).continuous.comp
      ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun q : wholeCusp a => q.2))
    exact h.fst.prodMk (h.snd.prodMk (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    have h := (cuspCoordinates a ha).symm.continuous.comp
      ((continuous_fst : Continuous (Prod.fst : HeightCylinder a → Ioi a)).prodMk (continuous_fst.comp continuous_snd))
    exact ((continuous_subtype_val.comp h).prodMk (continuous_snd.comp continuous_snd)).subtype_mk (fun q => ((cuspCoordinates a ha).symm (q.1,q.2.1)).2)

lemma wholeCoordinates_smooth (a : ℝ) (ha : 1 < a) :
    ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (wholeCoordinates a ha) := by
  have hv : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ (Subtype.val : wholeCusp a → WholePiece) :=
    contMDiff_subtype_val
  have hsub : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,ℂ) ∞
      (fun q : wholeCusp a => (⟨q.1.1,q.2⟩ : cusp a)) :=
    (ContMDiff.subtypeVal_comp_iff (cuspOpens a) _).mp (projection_fst_smooth.comp hv)
  have hc := (cuspCoordinates_smooth a ha).comp hsub
  have h0 := hc.fst
  have h1 := hc.snd.prodMk (projection_snd_smooth.comp hv)
  convert! h0.prodMk h1 using 1
  simp only [← modelWithCornersSelf_prod]

lemma wholeCoordinates_symm_smooth (a : ℝ) (ha : 1 < a) :
    ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,EP) ∞ (wholeCoordinates a ha).symm := by
  have h0 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℂ) ∞
      (fun q : HeightCylinder a => ((cuspCoordinates a ha).symm (q.1,q.2.1)).1) := by
    apply (contMDiff_subtype_val (U := cuspOpens a)).comp
    apply (cuspCoordinates_symm_smooth a ha).comp
    convert! (projection_fst_smooth (E := ℝ) (F := ℝ × ℝ) (M := Ioi a)
      (N := AddCircle (6:ℝ) × AddCircle (6:ℝ))).prodMk
      (projection_fst_smooth.comp projection_snd_smooth) using 1
  have h1 : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,ℝ) ∞ (fun q : HeightCylinder a => q.2.2) :=
    projection_snd_smooth.comp projection_snd_smooth
  apply (ContMDiff.subtypeVal_comp_iff (wholeCusp a) _).mp
  convert! h0.prodMk h1 using 1
  simp only [← modelWithCornersSelf_prod]

lemma wholeCusp_nonempty (a : ℝ) (ha : 1 < a) : Nonempty (wholeCusp a) := by
  let q : HeightCylinder a := (⟨a+1,show a < a+1 by linarith⟩,0,0)
  exact ⟨(wholeCoordinates a ha).symm q⟩

def cuspChart (a : ℝ) (ha : 1 < a) : OpenPartialHomeomorph WholePiece (HeightCylinder a) :=
  ((wholeCusp a).openPartialHomeomorphSubtypeCoe (wholeCusp_nonempty a ha)).symm.trans
    (wholeCoordinates a ha).toOpenPartialHomeomorph

lemma cuspChart_smooth (a : ℝ) (ha : 1 < a) :
    ContMDiffOn 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (cuspChart a ha) (cuspChart a ha).source := by
  intro x hx
  have hx' : x ∈ wholeCusp a := by simpa [cuspChart] using hx
  exact ((wholeCoordinates_smooth a ha) _).comp x
    (openSubtype_inverse_smooth (wholeCusp a) (wholeCusp_nonempty a ha) hx') |>.contMDiffWithinAt
lemma cuspChart_mdifferentiable (a : ℝ) (ha : 1 < a) :
    (cuspChart a ha).MDifferentiable 𝓘(ℝ,EP) 𝓘(ℝ,P) := by
  apply (openSubtype_mdifferentiable (wholeCusp a) (wholeCusp_nonempty a ha)).symm.trans
  exact ⟨((wholeCoordinates_smooth a ha).mdifferentiable (by simp)).mdifferentiableOn,
    ((wholeCoordinates_symm_smooth a ha).mdifferentiable (by simp)).mdifferentiableOn⟩

def cuspMetric (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 1 < a) :
    LocalMetric (E := EP) WholePiece :=
  localPull (heightMetric g a (by linarith)) (cuspChart a ha)
    (cuspChart_smooth a ha) (cuspChart_mdifferentiable a ha)

end ThreeManifold.CompactMetric
end

section
open Matrix
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff UpperHalfPlane MatrixGroups RealInnerProductSpace
namespace ThreeManifold.MetricConstruction
open HyperbolicCore QuotientConstruction

lemma halfPlane_coe_smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ ((↑) : ℍ → ℂ) := by
  intro z
  have h := UpperHalfPlane.contMDiff_coe (n := ∞) z
  rw [contMDiffAt_iff] at h ⊢
  exact ⟨h.1,h.2.restrict_scalars ℝ⟩

lemma halfPlane_coe_deriv (z : ℍ) :
    mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ((↑) : ℍ → ℂ) z = ContinuousLinearMap.id ℝ ℂ := by
  exact mfderiv_extChartAt_self (I := 𝓘(ℝ,ℂ)) (x := z)

lemma halfPlane_im_smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ) ∞ (fun z : ℍ => z.im) :=
  Complex.imCLM.contDiff.comp_contMDiff halfPlane_coe_smooth

def halfPlaneFlat : Metric (E := ℂ) ℍ :=
  pullback (euclidean (V := ℂ)) halfPlane_coe_smooth
    (fun _ => ContinuousLinearEquiv.refl ℝ ℂ) (fun z => (halfPlane_coe_deriv z).symm)

def hyperbolic : Metric (E := ℂ) ℍ :=
  scaleSq halfPlaneFlat (fun z : ℍ => z.im⁻¹)
    (halfPlane_im_smooth.inv₀ (fun z => ne_of_gt z.im_pos))
    (fun z => inv_ne_zero (ne_of_gt z.im_pos))

lemma hyperbolic_inner (z : ℍ) (u v : TangentSpace 𝓘(ℝ,ℂ) z) :
    hyperbolic.inner z u v = z.im⁻¹ ^ 2 * @inner ℝ ℂ _ u v := by
  change z.im⁻¹ ^ 2 * @inner ℝ ℂ _ (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ((↑) : ℍ → ℂ) z u)
    (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ((↑) : ℍ → ℂ) z v) = _
  rw [halfPlane_coe_deriv]
  rfl

lemma halfPlane_action_deriv (g : SL(2,ℤ)) (z : ℍ) :
    mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : ℍ => g • w) z =
    UpperHalfPlane.smulFDeriv (SpecialLinearGroup.mapGL ℝ g) z := by
  apply HasMFDerivAt.mfderiv
  constructor
  · exact (action_smooth g).continuous.continuousAt
  · have hd := (UpperHalfPlane.hasStrictFDerivAt_smul (SpecialLinearGroup.mapGL ℝ g) z).hasFDerivAt
    apply HasFDerivAt.hasFDerivWithinAt
    apply hd.congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ z).open_target.mem_nhds (mem_chart_target ℂ z)] with y hy
    have hy' : ((chartAt ℂ z).symm y : ℂ) = y := (chartAt ℂ z).right_inv hy
    have ho : UpperHalfPlane.ofComplex y = (chartAt ℂ z).symm y := by
      exact (congrArg UpperHalfPlane.ofComplex hy'.symm).trans (UpperHalfPlane.ofComplex_apply _)
    rw [ho]
    rfl

lemma halfPlane_action_deriv_apply (g : SL(2,ℤ)) (z : ℍ) (u : ℂ) :
    mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) (fun w : ℍ => g • w) z u =
      u / (UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) z) ^ 2 := by
  rw [halfPlane_action_deriv]
  have hd : (SpecialLinearGroup.mapGL ℝ g).det.val = 1 := mapGL_det g
  simp only [UpperHalfPlane.smulFDeriv,UpperHalfPlane.σ,hd,zero_lt_one,ite_eq_left]
  change u * ((1 : ℂ) / UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) z ^ 2) = _
  simp [div_eq_mul_inv]

lemma hyperbolic_action_quadratic (g : SL(2,ℤ)) (z : ℍ) (u : TangentSpace 𝓘(ℝ,ℂ) z) :
    pullInner hyperbolic (fun w : ℍ => g • w) z u u = hyperbolic.inner z u u := by
  let D : ℂ := UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) z
  let u' : ℂ := u
  have hi : (g • z).im = z.im / ‖D‖ ^ 2 := by
    change (SpecialLinearGroup.mapGL ℝ g • z).im = _
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp [Complex.normSq_eq_norm_sq,D]
  have hs : (g • z).im⁻¹ ^ 2 * inner ℝ (u' / D ^ 2) (u' / D ^ 2) =
      z.im⁻¹ ^ 2 * inner ℝ u' u' := by
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hi,norm_div,norm_pow]
    have hn : ‖D‖ ≠ 0 := norm_ne_zero_iff.mpr (UpperHalfPlane.denom_ne_zero _ z)
    field_simp
  rw [pullInner_apply]
  calc
    _ = (g • z).im⁻¹ ^ 2 * inner ℝ (u' / D ^ 2) (u' / D ^ 2) :=
      (hyperbolic_inner _ _ _).trans
        (congrArg (fun w : ℂ => (g • z).im⁻¹ ^ 2 * inner ℝ w w)
          (halfPlane_action_deriv_apply g z u'))
    _ = z.im⁻¹ ^ 2 * inner ℝ u' u' := hs
    _ = hyperbolic.inner z u u := (hyperbolic_inner z u u).symm

lemma hyperbolic_action_invariant (g : SL(2,ℤ)) (z : ℍ) :
    pullInner hyperbolic (fun w : ℍ => g • w) z = hyperbolic.inner z := by
  ext u v
  have h := hyperbolic_action_quadratic g z (u+v)
  have hu := hyperbolic_action_quadratic g z u
  have hv := hyperbolic_action_quadratic g z v
  have hs : ∀ u v : TangentSpace 𝓘(ℝ,ℂ) z, pullInner hyperbolic (fun w : ℍ => g • w) z u v =
      pullInner hyperbolic (fun w : ℍ => g • w) z v u := by
    intro u v
    exact hyperbolic.symm _ _ _
  simp only [map_add,_root_.add_apply] at h
  rw [hs v u,hyperbolic.symm z v u] at h
  linarith

lemma hyperbolic_effective_invariant (g : effective) (z : ℍ) :
    pullInner hyperbolic (fun w : ℍ => g • w) z = hyperbolic.inner z := by
  obtain ⟨a,rfl⟩ := effect_surjective g
  exact hyperbolic_action_invariant a.val z

def surfaceHyperbolic : Metric (E := ℂ) Surface :=
  descend projection_cover projection_smooth effective_smooth
    (local_lift_smoothAt projection_cover sectionMap_rightInverse effective_smooth)
    hyperbolic hyperbolic_effective_invariant sectionMap_rightInverse

lemma surface_projection_isometry (z : ℍ) :
    pullInner surfaceHyperbolic projection z = hyperbolic.inner z :=
  descend_projection projection_cover projection_smooth effective_smooth
    (local_lift_smoothAt projection_cover sectionMap_rightInverse effective_smooth)
    hyperbolic hyperbolic_effective_invariant sectionMap_rightInverse z

end ThreeManifold.MetricConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction
variable {E F V M N X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  [TopologicalSpace X] [ChartedSpace V X] [IsManifold 𝓘(ℝ,V) ∞ X]

lemma product_apply (g : Metric (E := E) M) (h : Metric (E := F) N) (x : M × N)
    (u v : TangentSpace 𝓘(ℝ,E × F) x) :
    (product g h).inner x u v = g.inner x.1 u.1 v.1 + h.inner x.2 u.2 v.2 :=
  productInner_apply g h x u v

omit [IsManifold 𝓘(ℝ,V) ∞ X] in
lemma pull_product {f : X → M} {k : X → N} {x : X}
    (hf : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,E) f x)
    (hk : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,F) k x)
    (g : Metric (E := E) M) (h : Metric (E := F) N) :
    pullInner (E := V) (product g h) (fun y => (f y,k y)) x = pullInner (E := V) g f x + pullInner (E := V) h k x := by
  ext u v
  rw [pullInner_apply,product_apply]
  have hd : mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E × F) (fun y => (f y,k y)) x =
      (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) f x).prod (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,F) k x) := by
    convert! mfderiv_prodMk hf hk using 1
  rw [hd]
  rfl

omit [IsManifold 𝓘(ℝ,V) ∞ X] in
lemma pull_scaleSq (g : Metric (E := E) M) (r : M → ℝ)
    (hr : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ r) (hp : ∀ x, r x ≠ 0)
    (f : X → M) (x : X) (u v : TangentSpace 𝓘(ℝ,V) x) :
    pullInner (scaleSq g r hr hp) f x u v = r (f x)^2 * pullInner (E := V) g f x u v := rfl
end ThreeManifold.MetricConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff UpperHalfPlane RealInnerProductSpace
namespace ThreeManifold.CompactMetric
open MetricConstruction
abbrev UniversalPiece := ℍ × ℝ

def sourceProjection : UniversalPiece → WholePiece :=
  Prod.map HyperbolicCore.projection ((↑) : ℝ → AddCircle (6:ℝ))
lemma sourceProjection_smooth : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ sourceProjection := by
  convert! HyperbolicCore.projection_smooth.prodMap (CircleConstruction.projection_smooth 6) using 1
  all_goals simp only [EP, ← modelWithCornersSelf_prod]
lemma sourceProjection_deriv (x : UniversalPiece) :
    mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) sourceProjection x =
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) HyperbolicCore.projection x.1).prodMap
        (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ((↑) : ℝ → AddCircle (6:ℝ)) x.2) := by
  convert! mfderiv_prodMap ((HyperbolicCore.projection_smooth x.1).mdifferentiableAt (by simp))
    ((CircleConstruction.projection_smooth 6 x.2).mdifferentiableAt (by simp)) using 1

lemma sourceProjection_deriv_surjective (x : UniversalPiece) :
    Function.Surjective (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) sourceProjection x) := by
  let ds := coveringDerivative HyperbolicCore.projection_cover HyperbolicCore.projection_smooth
    (QuotientConstruction.local_lift_smoothAt HyperbolicCore.projection_cover
      HyperbolicCore.sectionMap_rightInverse HyperbolicCore.effective_smooth) x.1
  let dc := coveringDerivative (CircleConstruction.projection_cover 6) (CircleConstruction.projection_smooth 6)
    (fun a _ h => QuotientConstruction.local_lift_smoothAt (CircleConstruction.projection_cover 6)
      (CircleConstruction.section_spec 6) (CircleConstruction.action_smooth 6) a h) x.2
  have hs : ds.toContinuousLinearMap = mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) HyperbolicCore.projection x.1 :=
    coveringDerivative_eq _ _ _ _
  have hc : dc.toContinuousLinearMap = mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ((↑) : ℝ → AddCircle (6:ℝ)) x.2 :=
    coveringDerivative_eq _ _ _ _
  rw [sourceProjection_deriv,← hs,← hc]
  exact ds.surjective.prodMap dc.surjective

def coreMetric (c : ℝ) (hc : c ≠ 0) : Metric (E := EP) WholePiece :=
  product surfaceHyperbolic (scaleSq (circle 6) (fun _ => c) contMDiff_const (fun _ => hc))
lemma coreMetric_apply (c : ℝ) (hc : c ≠ 0) (q : WholePiece)
    (u v : EP) :
    (coreMetric c hc).inner q u v = surfaceHyperbolic.inner q.1 u.1 v.1 +
      c^2*(circle 6).inner q.2 u.2 v.2 :=
  productInner_apply surfaceHyperbolic _ q u v
lemma coreMetric_projection (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece)
    (u v : EP) :
    pullInner (E := EP) (coreMetric c hc) sourceProjection x u v =
      x.1.im⁻¹^2 * inner ℝ u.1 v.1 + c^2*u.2*v.2 := by
  have hs := congrArg (fun B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ => B u.1 v.1)
    (surface_projection_isometry x.1)
  have ht := congrArg (fun B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ => B u.2 v.2)
    (circle_projection 6 x.2)
  let ds := mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) HyperbolicCore.projection x.1
  let dc := mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ((↑) : ℝ → AddCircle (6:ℝ)) x.2
  have hdu : mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) sourceProjection x u = (ds u.1,dc u.2) :=
    congrArg (fun D : EP →L[ℝ] EP => D u) (sourceProjection_deriv x)
  have hdv : mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) sourceProjection x v = (ds v.1,dc v.2) :=
    congrArg (fun D : EP →L[ℝ] EP => D v) (sourceProjection_deriv x)
  calc
    _ = (coreMetric c hc).inner (sourceProjection x) (ds u.1,dc u.2) (ds v.1,dc v.2) :=
      congrArg₂ (fun a b : EP => (coreMetric c hc).inner (sourceProjection x) a b) hdu hdv
    _ = surfaceHyperbolic.inner (HyperbolicCore.projection x.1) (ds u.1) (ds v.1) +
        c^2*(circle 6).inner (x.2 : AddCircle (6:ℝ)) (dc u.2) (dc v.2) :=
      coreMetric_apply c hc _ _ _
    _ = hyperbolic.inner x.1 u.1 v.1 + c^2*(u.2*v.2) :=
      congrArg₂ (fun a b : ℝ => a+c^2*b) hs (ht.trans (by
        change inner ℝ u.2 v.2 = u.2*v.2
        simp [mul_comm]))
    _ = x.1.im⁻¹^2 * inner ℝ u.1 v.1 + c^2*(u.2*v.2) :=
      congrArg (fun a : ℝ => a+c^2*(u.2*v.2)) (hyperbolic_inner x.1 u.1 v.1)
    _ = x.1.im⁻¹^2 * inner ℝ u.1 v.1 + c^2*u.2*v.2 := by ring
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.MetricConstruction
variable {E F H M N Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold 𝓘(ℝ,H) ∞ Q]
variable {G : Type*} [Group G] [MulAction G M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
  {p : M → X} (hp : IsQuotientCoveringMap p G)
  (hps : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ p)
  (hls : ∀ (b : M) {q : X}, q ∈ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b).source →
    ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (hp.isCoveringMap.isLocalHomeomorph.localInverseAt b) q)
  {f : X → X} {lift : M → M}
  (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f)
  (hl : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ lift)
  (comm : f ∘ p = p ∘ lift)
  (dl : M → E ≃L[ℝ] E)
  (hdl : ∀ x, (dl x).toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) lift x)
  {σ : X → M} (hσ : Function.RightInverse σ p)
lemma pullbackFromLift_projection (g : Metric (E := E) X) (x : M) :
    pullInner (E := E) (pullbackFromLift hp hps hls hf hl comm dl hdl hσ g) p x =
      pullBilin (E := E) (F := E) (pullInner g p (lift x))
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) lift x) := by
  let _ : IsManifold 𝓘(ℝ, E) ∞ M := inferInstance
  change pullBilin (E := E) (F := E) (pullInner g f (p x))
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) p x) = _
  rw [← pull_composition g ((hps x).mdifferentiableAt (by simp))
    ((hf _).mdifferentiableAt (by simp)), comm]
  exact pull_composition g ((hl x).mdifferentiableAt (by simp))
    ((hps _).mdifferentiableAt (by simp))
end ThreeManifold.MetricConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction

def heightToCylinder (a : ℝ) (ha : 0 < a) : HeightCylinder a → Cylinder :=
  Subtype.val ∘ logCylinderHomeomorph a ha
lemma heightToCylinder_smooth (a : ℝ) (ha : 0 < a) :
    ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (heightToCylinder a ha) :=
  (contMDiff_subtype_val (U := logDomain a)).comp (logCylinder_smooth a ha)
lemma heightMetric_inner (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 0 < a) (q : HeightCylinder a) :
    (heightMetric g a ha).inner q = pullInner (E := P) g (heightToCylinder a ha) q := by
  change pullBilin (E := P) (F := P)
    (pullInner g (Subtype.val : logDomain a → Cylinder) ((logCylinderHomeomorph a ha) q))
      (mfderiv 𝓘(ℝ,P) 𝓘(ℝ,P) (logCylinderHomeomorph a ha) q) = _
  exact (pull_composition g ((logCylinder_smooth a ha q).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (U := logDomain a) (n := ∞) _).mdifferentiableAt (by simp))).symm

def logCuspMap (a : ℝ) (ha : 1 < a) : WholePiece → Cylinder :=
  heightToCylinder a (by linarith) ∘ cuspChart a ha
lemma logCuspMap_smoothAt (a : ℝ) (ha : 1 < a) {x : WholePiece} (hx : x ∈ wholeCusp a) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (logCuspMap a ha) x := by
  have hs : x ∈ (cuspChart a ha).source := by simpa [cuspChart] using hx
  exact ((heightToCylinder_smooth a (by linarith)) _).comp x
    ((cuspChart_smooth a ha x hs).contMDiffAt ((cuspChart a ha).open_source.mem_nhds hs))
lemma cuspMetric_inner (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 1 < a)
    {x : WholePiece} (hx : x ∈ wholeCusp a) :
    (cuspMetric g a ha).inner x = pullInner (E := EP) g (logCuspMap a ha) x := by
  have hs : x ∈ (cuspChart a ha).source := by simpa [cuspChart] using hx
  change pullBilin (E := EP) (F := P) ((heightMetric g a (by linarith)).inner (cuspChart a ha x))
    (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) (cuspChart a ha) x) = _
  rw [heightMetric_inner]
  exact (pull_composition g
    (((cuspChart_smooth a ha x hs).contMDiffAt ((cuspChart a ha).open_source.mem_nhds hs)).mdifferentiableAt (by simp))
    (((heightToCylinder_smooth a (by linarith)) _).mdifferentiableAt (by simp))).symm

def logarithmicLift (x : UniversalPiece) : P := (Real.log x.1.im,x.1.re,x.2)
lemma logarithmicLift_smooth : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ logarithmicLift := by
  have hi : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,ℝ) ∞ (fun x : UniversalPiece => Real.log x.1.im) :=
    fun x => (Real.contDiffAt_log.mpr x.1.im_pos.ne').contMDiffAt.comp x
      ((halfPlane_im_smooth.comp projection_fst_smooth) x)
  have hr : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,ℝ) ∞ (fun x : UniversalPiece => x.1.re) :=
    HyperbolicCore.upperHalfPlane_re_smooth.comp projection_fst_smooth
  exact hi.prodMk_space (hr.prodMk_space projection_snd_smooth)

lemma logCusp_projection_apply (a : ℝ) (ha : 1 < a) (x : UniversalPiece) (hx : a < x.1.im) :
    logCuspMap a ha (sourceProjection x) = projection (logarithmicLift x) := by
  have hul : sourceProjection x ∈ wholeCusp a := ⟨x.1,hx,rfl⟩
  have hsub : ((wholeCusp a).openPartialHomeomorphSubtypeCoe (wholeCusp_nonempty a ha)).symm
      (sourceProjection x) = ⟨sourceProjection x,hul⟩ :=
    ((wholeCusp a).openPartialHomeomorphSubtypeCoe (wholeCusp_nonempty a ha)).left_inv (x := ⟨sourceProjection x,hul⟩) (by simp)
  have hc := HyperbolicCore.cuspCoordinates_apply a ha x.1 hx
  change ((heightToCylinder a (by linarith)) ((wholeCoordinates a ha)
    (((wholeCusp a).openPartialHomeomorphSubtypeCoe (wholeCusp_nonempty a ha)).symm (sourceProjection x)))) = _
  rw [hsub]
  change (Real.log ((HyperbolicCore.cuspCoordinates a ha ⟨HyperbolicCore.projection x.1,_⟩).1 : ℝ),
    (HyperbolicCore.cuspCoordinates a ha ⟨HyperbolicCore.projection x.1,_⟩).2,(x.2 : AddCircle (6:ℝ))) = _
  rw [hc]
  rfl
lemma logCusp_projection_germ (a : ℝ) (ha : 1 < a) {x : UniversalPiece} (hx : a < x.1.im) :
    (logCuspMap a ha ∘ sourceProjection) =ᶠ[nhds x] (projection ∘ logarithmicLift) := by
  have hh : ∀ᶠ y : UniversalPiece in nhds x, a < y.1.im :=
    (UpperHalfPlane.continuous_im.comp continuous_fst).continuousAt (isOpen_Ioi.mem_nhds hx)
  filter_upwards [hh] with y hy
  exact logCusp_projection_apply a ha y hy

lemma cuspMetric_projection (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 1 < a)
    {x : UniversalPiece} (hx : a < x.1.im) :
    pullBilin (E := EP) (F := EP) ((cuspMetric g a ha).inner (sourceProjection x))
      (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) sourceProjection x) =
    pullBilin (E := EP) (F := P) (pullInner g projection (logarithmicLift x))
      (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) logarithmicLift x) := by
  rw [cuspMetric_inner g a ha (show sourceProjection x ∈ wholeCusp a from ⟨x.1,hx,rfl⟩)]
  rw [← pull_composition g ((sourceProjection_smooth x).mdifferentiableAt (by simp))
    ((logCuspMap_smoothAt a ha ⟨x.1,hx,rfl⟩).mdifferentiableAt (by simp))]
  rw [pullInner_congr g (logCusp_projection_germ a ha hx)]
  exact pull_composition g ((logarithmicLift_smooth x).mdifferentiableAt (by simp))
    ((projection_smooth _).mdifferentiableAt (by simp))
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff UpperHalfPlane RealInnerProductSpace
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction

def universalCoordinates (x : UniversalPiece) : EP := (x.1,x.2)
lemma universalCoordinates_smooth : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ universalCoordinates := by
  exact (halfPlane_coe_smooth.comp projection_fst_smooth).prodMk_space projection_snd_smooth
lemma universalCoordinates_deriv (x : UniversalPiece) :
    mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) universalCoordinates x = ContinuousLinearMap.id ℝ EP := by
  change mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) (extChartAt 𝓘(ℝ,EP) x) x = _
  exact mfderiv_extChartAt_self

def logLinear (y : ℝ) : EP →L[ℝ] P :=
  ((y⁻¹ • Complex.imCLM).comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).prod
    ((Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℂ ℝ))
lemma logLinear_apply (y : ℝ) (u : EP) : logLinear y u = (y⁻¹*u.1.im,u.1.re,u.2) := rfl

def logNormed (x : EP) : P := (Real.log x.1.im, x.1.re, x.2)
lemma logNormed_deriv {x : EP} (hx : x.1.im ≠ 0) :
    HasFDerivAt logNormed (logLinear x.1.im) x := by
  have hi : HasFDerivAt (fun x : EP => x.1.im)
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) x :=
    Complex.imCLM.hasFDerivAt.comp x (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt
  have hl := (Real.hasDerivAt_log hx).comp_hasFDerivAt x hi
  have hr := Complex.reCLM.hasFDerivAt.comp x (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt
  convert! hl.prodMk (hr.prodMk (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt) using 1

lemma logarithmicLift_deriv (x : UniversalPiece) :
    mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) logarithmicLift x = logLinear x.1.im := by
  have he : logarithmicLift = logNormed ∘ universalCoordinates := rfl
  rw [he,mfderiv_comp x
    ((logNormed_deriv (x := universalCoordinates x) x.1.im_pos.ne').differentiableAt.mdifferentiableAt)
    ((universalCoordinates_smooth x).mdifferentiableAt (by simp)),universalCoordinates_deriv]
  rw [mfderiv_eq_fderiv]
  change (fderiv ℝ logNormed (universalCoordinates x)).comp (ContinuousLinearMap.id ℝ EP) = logLinear x.1.im
  rw [(logNormed_deriv (x := universalCoordinates x) x.1.im_pos.ne').fderiv]
  rfl
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.CompactMetric
open CylinderConstruction

def period (δ : ℝ) : ℝ := 6 / (Real.exp 4 * Collar.ell δ (-1))
def leftLength (δ : ℝ) : ℝ := 4-2*Real.log δ

def leftCircleScale (δ : ℝ) : ℝ := period δ/6 * Collar.ell δ 1
def rightCircleScale (δ : ℝ) : ℝ := δ^2*period δ/6 * Collar.ell δ 1
lemma period_pos (δ : ℝ) : 0 < period δ :=
  div_pos (by norm_num) (mul_pos (Real.exp_pos _) (Collar.ell_pos _ _))
lemma leftCircleScale_pos (δ : ℝ) : 0 < leftCircleScale δ :=
  mul_pos (div_pos (period_pos δ) (by norm_num)) (Collar.ell_pos _ _)
lemma rightCircleScale_pos {δ : ℝ} (hδ : 0 < δ) : 0 < rightCircleScale δ :=
  mul_pos (div_pos (mul_pos (sq_pos_of_pos hδ) (period_pos δ)) (by norm_num)) (Collar.ell_pos _ _)
lemma leftLength_ge {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : 4 ≤ leftLength δ := by
  have hl : Real.log δ ≤ 0 := Real.log_nonpos hδ.1.le (by linarith [hδ.2])
  unfold leftLength
  linarith
lemma exp_leftLength {δ : ℝ} (hδ : 0 < δ) : Real.exp (leftLength δ) = Real.exp 4 / δ^2 := by
  rw [leftLength,Real.exp_sub]
  congr 1
  rw [show 2*Real.log δ = Real.log (δ^2) by rw [Real.log_pow]; norm_num, Real.exp_log (sq_pos_of_pos hδ)]
lemma ell_plateau {δ t : ℝ} (hδ : δ ∈ Icc 0 (1/2)) (ht : 2/3 ≤ t) :
    Collar.ell δ t = Collar.ell δ 1 := by
  rw [Collar.ell_end_germ hδ (by linarith),Collar.ell_end_germ hδ (by norm_num)]
  rw [Cometric.A_plateau ht (by norm_num : (2/3:ℝ) ≤ 1)]
lemma radius₁_left_exact {δ r : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hr : r ≤ 1/4) :
    radius₁ δ (period δ) (RadialProfile.coordinate (leftLength δ) r) = Real.exp (-r) := by
  have hL := leftLength_ge hδ
  rw [RadialProfile.coordinate_left hr]
  unfold radius₁
  rw [Collar.ell_cusp_germ ⟨hδ.1.le,hδ.2⟩ (by linarith)]
  rw [show -(r-leftLength δ-1+1) = leftLength δ-r by ring,Real.exp_sub,exp_leftLength hδ.1]
  unfold period
  rw [Real.exp_neg]
  field_simp [hδ.1.ne',(Real.exp_pos 4).ne',(Collar.ell_pos δ (-1)).ne']
lemma radius₂_left_exact {δ r : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hr : r ≤ 1/4) :
    radius₂ δ (period δ) (RadialProfile.coordinate (leftLength δ) r) = leftCircleScale δ := by
  rw [RadialProfile.coordinate_left hr]
  unfold radius₂ leftCircleScale
  rw [ell_plateau ⟨hδ.1.le,hδ.2⟩ (by linarith [leftLength_ge hδ])]
lemma radius₂_right_exact {δ r : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hr : r ≤ 1/4) :
    radius₂ δ (period δ) (1-RadialProfile.coordinate 4 r) = Real.exp (-r) := by
  rw [RadialProfile.coordinate_left hr]
  unfold radius₂
  rw [show 1-(1-(r-4-1)) = r-4-1 by ring,
    Collar.ell_cusp_germ ⟨hδ.1.le,hδ.2⟩ (by linarith)]
  rw [show -(r-4-1+1) = (4:ℝ)-r by ring,Real.exp_sub]
  unfold period
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos 4).ne',(Collar.ell_pos δ (-1)).ne']
lemma radius₁_right_exact {δ r : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hr : r ≤ 1/4) :
    radius₁ δ (period δ) (1-RadialProfile.coordinate 4 r) = rightCircleScale δ := by
  rw [RadialProfile.coordinate_left hr]
  unfold radius₁ rightCircleScale
  rw [ell_plateau ⟨hδ.1.le,hδ.2⟩ (by linarith)]
lemma slope_left_exact {L r : ℝ} (hr : r < 1/4) : RadialProfile.slope L r = 1 := by
  have he : RadialProfile.coordinate L =ᶠ[nhds r] fun t => t-L-1 := by
    filter_upwards [Iio_mem_nhds hr] with t ht
    exact RadialProfile.coordinate_left ht.le
  exact (RadialProfile.coordinate_deriv L r).deriv.symm.trans
    (he.deriv_eq.trans (((hasDerivAt_id r).sub_const L).sub_const 1).deriv)
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction

lemma neck_projection_apply {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    (x : P) (u v : P) :
    pullInner (E := P) (neck hδ hB) projection x u v =
      u.1*v.1 + radius₁ δ B x.1 ^2 * (u.2.1-Cometric.χ x.1*u.2.2)*
        (v.2.1-Cometric.χ x.1*v.2.2) + radius₂ δ B x.1 ^2*u.2.2*v.2.2 := by
  rw [show pullInner (E := P) (neck hδ hB) projection x =
    (lifted (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B) (radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B) Cometric.χ_smooth
      (fun t => (radius₁_pos hδ.1 hB t).ne') (fun t => (radius₂_pos hB t).ne')).inner x from
      metric_projection _ _ _ _ _ x]
  exact lifted_apply _ _ _ _ _ x u v

lemma radialPull_projection (g : Metric (E := P) Cylinder) {L : ℝ} (hL : 4 ≤ L)
    (x : P) (u v : P) :
    pullInner (E := P) (radialPull g hL) projection x u v =
      pullInner (E := P) g projection (radialLift L x)
        (RadialProfile.slope L x.1*u.1,u.2) (RadialProfile.slope L x.1*v.1,v.2) := by
  have hh := pullbackFromLift_projection projection_cover projection_smooth local_inverse_smooth
    (radial_smooth L) (radialLift_smooth L) (radial_commutes L)
    (fun x => radialLinear (RadialProfile.slope L x.1) (RadialProfile.slope_pos hL x.1).ne')
    (radialLift_deriv hL) section_spec g x
  change pullInner (E := P) (radialPull g hL) projection x = _ at hh
  rw [hh,← radialLift_deriv hL x]
  rfl

def switchLift (x : P) : P := (1-x.1, x.2.1+x.2.2,x.2.1)
def switchLinear : P ≃L[ℝ] P :=
  { toFun := fun v => (-v.1, v.2.1+v.2.2,v.2.1)
    invFun := fun v => (-v.1, v.2.2,v.2.1-v.2.2)
    left_inv := by intro v; ext <;> simp
    right_inv := by intro v; ext <;> simp
    map_add' := by intro v w; ext <;> dsimp <;> ring
    map_smul' := by intro a v; ext <;> dsimp <;> ring }
lemma switchLift_eq (x : P) : switchLift x = switchLinear x + (1,0,0) := by
  ext <;> simp [switchLift,switchLinear,sub_eq_add_neg,add_comm]
lemma switchLift_smooth : ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ switchLift := by
  have he : switchLift = fun x => switchLinear x + (1,0,0) := funext switchLift_eq
  rw [he]
  exact switchLinear.contDiff.contMDiff.add contMDiff_const
lemma switchLift_deriv (x : P) :
    mfderiv 𝓘(ℝ,P) 𝓘(ℝ,P) switchLift x = switchLinear.toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ switchLift x = switchLinear.toContinuousLinearMap
  have he : switchLift = fun x => switchLinear x + (1,0,0) := funext switchLift_eq
  rw [he]
  exact (switchLinear.hasFDerivAt.add_const (1,0,0)).fderiv
lemma switch_commutes : switch ∘ projection = projection ∘ switchLift := by
  funext x
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact (AddCircle.coe_add (6:ℝ) x.2.1 x.2.2).symm
    · rfl

lemma switched_projection (g : Metric (E := P) Cylinder) (x : P) :
    pullInner (E := P) (switched g) projection x =
      pullBilin (E := P) (F := P) (pullInner g projection (switchLift x)) switchLinear.toContinuousLinearMap := by
  change pullBilin (E := P) (F := P) (pullInner g switch (projection x))
    (mfderiv 𝓘(ℝ,P) 𝓘(ℝ,P) projection x) = _
  rw [← pull_composition g ((projection_smooth x).mdifferentiableAt (by simp))
    ((switch_smooth _).mdifferentiableAt (by simp)),switch_commutes]
  rw [pull_composition g ((switchLift_smooth x).mdifferentiableAt (by simp))
    ((projection_smooth _).mdifferentiableAt (by simp)),switchLift_deriv]

def leftCylinder {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : Metric (E := P) Cylinder :=
  radialPull (neck hδ (period_pos δ)) (leftLength_ge hδ)
def rightCylinder {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : Metric (E := P) Cylinder :=
  radialPull (switched (neck hδ (period_pos δ))) (L := 4) le_rfl

lemma leftCylinder_low {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x : P) (hx : x.1 < 1/4)
    (u v : P) :
    pullInner (E := P) (leftCylinder hδ) projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + leftCircleScale δ^2*u.2.2*v.2.2 := by
  change pullInner (E := P) (radialPull _ (leftLength_ge hδ)) projection x u v = _
  have he := radialPull_projection (neck hδ (period_pos δ)) (leftLength_ge hδ) x u v
  have hn := neck_projection_apply hδ (period_pos δ) (radialLift (leftLength δ) x)
    (RadialProfile.slope (leftLength δ) x.1*u.1,u.2) (RadialProfile.slope (leftLength δ) x.1*v.1,v.2)
  apply Eq.trans (he.trans hn)
  change (RadialProfile.slope (leftLength δ) x.1*u.1)*(RadialProfile.slope (leftLength δ) x.1*v.1) +
    radius₁ δ (period δ) (RadialProfile.coordinate (leftLength δ) x.1)^2 *
      (u.2.1-Cometric.χ (RadialProfile.coordinate (leftLength δ) x.1)*u.2.2)*
      (v.2.1-Cometric.χ (RadialProfile.coordinate (leftLength δ) x.1)*v.2.2) +
    radius₂ δ (period δ) (RadialProfile.coordinate (leftLength δ) x.1)^2*u.2.2*v.2.2 = _
  rw [slope_left_exact hx,radius₁_left_exact hδ hx.le,radius₂_left_exact hδ hx.le]
  have hz : Cometric.χ (RadialProfile.coordinate (leftLength δ) x.1) = 0 := by
    rw [RadialProfile.coordinate_left hx.le]
    exact Cometric.χ_eq_zero (by linarith [leftLength_ge hδ])
  simp only [hz,zero_mul,sub_zero,one_mul]

lemma rightCylinder_low {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x : P) (hx : x.1 < 1/4)
    (u v : P) :
    pullInner (E := P) (rightCylinder hδ) projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + rightCircleScale δ^2*u.2.2*v.2.2 := by
  change pullInner (E := P) (radialPull _ (L := 4) le_rfl) projection x u v = _
  have he := radialPull_projection (switched (neck hδ (period_pos δ))) (L := 4) le_rfl x u v
  have hs := congrArg (fun D : P →L[ℝ] P →L[ℝ] ℝ =>
    D (RadialProfile.slope 4 x.1*u.1,u.2) (RadialProfile.slope 4 x.1*v.1,v.2))
    (switched_projection (neck hδ (period_pos δ)) (radialLift 4 x))
  have hn := neck_projection_apply hδ (period_pos δ) (switchLift (radialLift 4 x))
    (switchLinear (RadialProfile.slope 4 x.1*u.1,u.2))
    (switchLinear (RadialProfile.slope 4 x.1*v.1,v.2))
  apply Eq.trans (he.trans (hs.trans hn))
  change (-(RadialProfile.slope 4 x.1*u.1))*(-(RadialProfile.slope 4 x.1*v.1)) +
    radius₁ δ (period δ) (1-RadialProfile.coordinate 4 x.1)^2 *
      (u.2.1+u.2.2-Cometric.χ (1-RadialProfile.coordinate 4 x.1)*u.2.1)*
      (v.2.1+v.2.2-Cometric.χ (1-RadialProfile.coordinate 4 x.1)*v.2.1) +
    radius₂ δ (period δ) (1-RadialProfile.coordinate 4 x.1)^2*u.2.1*v.2.1 = _
  rw [slope_left_exact hx,radius₁_right_exact hδ hx.le,radius₂_right_exact hδ hx.le]
  have ho : Cometric.χ (1-RadialProfile.coordinate 4 x.1) = 1 := by
    rw [RadialProfile.coordinate_left hx.le]
    exact Cometric.χ_eq_one (by linarith)
  rw [ho]
  ring
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff UpperHalfPlane RealInnerProductSpace
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction

variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)

include low in
lemma cusp_linear_formula (x : UniversalPiece) (hx : Real.log x.1.im < 1/4) (u v : EP) :
    pullBilin (E := EP) (F := P) (pullInner g projection (logarithmicLift x))
      (logLinear x.1.im) u v =
        x.1.im⁻¹^2 * inner ℝ u.1 v.1 + c^2*u.2*v.2 := by
  have he := low (logarithmicLift x) hx (logLinear x.1.im u) (logLinear x.1.im v)
  apply he.trans
  change (x.1.im⁻¹*u.1.im)*(x.1.im⁻¹*v.1.im) + Real.exp (-Real.log x.1.im)^2*u.1.re*v.1.re +
    c^2*u.2*v.2 = _
  rw [Real.exp_neg,Real.exp_log x.1.im_pos,Complex.inner]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

include low in
lemma cusp_core_match_projection (a : ℝ) (ha : 1 < a) {x : UniversalPiece}
    (hx : a < x.1.im) (hl : Real.log x.1.im < 1/4) :
    (cuspMetric g a ha).inner (sourceProjection x) = (coreMetric c hc).inner (sourceProjection x) := by
  apply bilin_eq_of_pull_eq (E := EP) (F := EP) x (sourceProjection_deriv_surjective x)
  rw [cuspMetric_projection g a ha hx,logarithmicLift_deriv]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (cusp_linear_formula g c low x hl u v).trans (coreMetric_projection c hc x u v).symm

include low in
lemma cusp_core_match (a : ℝ) (ha : 1 < a) {q : WholePiece}
    (hq : q ∈ wholeCusp a) (hl : HyperbolicCore.height q.1 < 1/4) :
    (cuspMetric g a ha).inner q = (coreMetric c hc).inner q := by
  obtain ⟨z,hz,hzq⟩ := hq
  let r := CircleConstruction.sectionMap 6 q.2
  have he : sourceProjection (z,r) = q := by
    apply Prod.ext
    · exact hzq
    · exact CircleConstruction.section_spec 6 q.2
  have hlog : Real.log z.im < 1/4 := by
    rw [← HyperbolicCore.height_projection_high (ha.trans hz),hzq]
    exact hl
  exact he ▸ cusp_core_match_projection g c hc low a ha hz hlog

lemma left_cusp_core_match {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (a : ℝ) (ha : 1 < a)
    {q : WholePiece} (hq : q ∈ wholeCusp a) (hl : HyperbolicCore.height q.1 < 1/4) :
    (cuspMetric (leftCylinder hδ) a ha).inner q =
      (coreMetric (leftCircleScale δ) (leftCircleScale_pos δ).ne').inner q :=
  cusp_core_match _ _ _ (leftCylinder_low hδ) a ha hq hl
lemma right_cusp_core_match {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (a : ℝ) (ha : 1 < a)
    {q : WholePiece} (hq : q ∈ wholeCusp a) (hl : HyperbolicCore.height q.1 < 1/4) :
    (cuspMetric (rightCylinder hδ) a ha).inner q =
      (coreMetric (rightCircleScale δ) (rightCircleScale_pos hδ.1).ne').inner q :=
  cusp_core_match _ _ _ (rightCylinder_low hδ) a ha hq hl
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction

def coreRegion : TopologicalSpace.Opens WholePiece :=
  ⟨{q | HyperbolicCore.height q.1 < 1/4},
    isOpen_lt (HyperbolicCore.height_continuous.comp continuous_fst) continuous_const⟩
def cuspLevel : ℝ := Real.exp (1/8)
lemma cuspLevel_gt : 1 < cuspLevel := by
  unfold cuspLevel
  exact Real.one_lt_exp_iff.mpr (by norm_num)
lemma log_cuspLevel : Real.log cuspLevel = 1/8 := Real.log_exp _
lemma cuspMetric_domain (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 1 < a) :
    (cuspMetric g a ha).domain = wholeCusp a := by
  ext x
  simp [cuspMetric,localPull,cuspChart]

variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)

def wholeLocals (i : Bool) : LocalMetric (E := EP) WholePiece :=
  if i then cuspMetric g cuspLevel cuspLevel_gt else localOn (coreMetric c hc) coreRegion
lemma wholeLocals_cover (x : WholePiece) : ∃ i, x ∈ (wholeLocals g c hc i).domain := by
  by_cases hx : x ∈ coreRegion
  · exact ⟨false,hx⟩
  · refine ⟨true,?_⟩
    change x ∈ (cuspMetric g cuspLevel cuspLevel_gt).domain
    rw [cuspMetric_domain]
    apply (HyperbolicCore.mem_cusp_iff_height cuspLevel_gt x.1).mpr
    rw [log_cuspLevel]
    have hh : ¬HyperbolicCore.height x.1 < 1/4 := hx
    linarith
include low in
lemma wholeLocals_compatible (i j : Bool) (x : WholePiece)
    (hi : x ∈ (wholeLocals g c hc i).domain) (hj : x ∈ (wholeLocals g c hc j).domain) :
    (wholeLocals g c hc i).inner x = (wholeLocals g c hc j).inner x := by
  cases i <;> cases j
  · rfl
  · change (coreMetric c hc).inner x = (cuspMetric g cuspLevel cuspLevel_gt).inner x
    apply (cusp_core_match g c hc low cuspLevel cuspLevel_gt _ hi).symm
    change x ∈ (cuspMetric g cuspLevel cuspLevel_gt).domain at hj
    rw [cuspMetric_domain] at hj
    change x.1 ∈ HyperbolicCore.cusp cuspLevel
    exact hj
  · change (cuspMetric g cuspLevel cuspLevel_gt).inner x = (coreMetric c hc).inner x
    apply cusp_core_match g c hc low cuspLevel cuspLevel_gt _ hj
    change x ∈ (cuspMetric g cuspLevel cuspLevel_gt).domain at hi
    rw [cuspMetric_domain] at hi
    change x.1 ∈ HyperbolicCore.cusp cuspLevel
    exact hi
  · rfl

def wholeMetric : Metric (E := EP) WholePiece :=
  glueLocal (wholeLocals g c hc) (wholeLocals_cover g c hc) (wholeLocals_compatible g c hc low)
lemma wholeMetric_core {x : WholePiece} (hx : x ∈ coreRegion) :
    (wholeMetric g c hc low).inner x = (coreMetric c hc).inner x :=
  glueLocal_eq _ _ _ false x hx
lemma wholeMetric_cusp {x : WholePiece} (hx : x ∈ wholeCusp cuspLevel) :
    (wholeMetric g c hc low).inner x = (cuspMetric g cuspLevel cuspLevel_gt).inner x := by
  apply glueLocal_eq _ _ _ true x
  change x ∈ (cuspMetric g cuspLevel cuspLevel_gt).domain
  rwa [cuspMetric_domain]

def leftWhole {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : Metric (E := EP) WholePiece :=
  wholeMetric (leftCylinder hδ) (leftCircleScale δ) (leftCircleScale_pos δ).ne' (leftCylinder_low hδ)
def rightWhole {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : Metric (E := EP) WholePiece :=
  wholeMetric (rightCylinder hδ) (rightCircleScale δ) (rightCircleScale_pos hδ.1).ne' (rightCylinder_low hδ)
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction GluedConstruction HyperbolicCore

def pieceMap : Piece → WholePiece := fun x => (x.1.1,x.2)
lemma pieceMap_smooth : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ pieceMap := by
  have h := ((contMDiff_subtype_val (U := coreOpens 8) (n := ∞)).comp
    (projection_fst_smooth (E := ℂ) (F := ℝ) (M := OpenCore 8) (N := GluedConstruction.Circle))).prodMk
      (projection_snd_smooth (E := ℂ) (F := ℝ) (M := OpenCore 8) (N := GluedConstruction.Circle))
  convert! h using 1
  simp only [← modelWithCornersSelf_prod]

lemma core8_nonempty : Nonempty (coreOpens 8) := by
  exact HyperbolicCore.openCore_nonempty (by norm_num)

def pieceEmbedding : OpenPartialHomeomorph Piece WholePiece :=
  ((coreOpens 8).openPartialHomeomorphSubtypeCoe core8_nonempty).prod (OpenPartialHomeomorph.refl GluedConstruction.Circle)

lemma pieceEmbedding_smooth_inverse {x : WholePiece} (hx : x ∈ pieceEmbedding.target) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ pieceEmbedding.symm x := by
  have h1 := (openSubtype_inverse_smooth (coreOpens 8) core8_nonempty (by simpa using hx.1)).comp x
    ((projection_fst_smooth (E := ℂ) (F := ℝ) (M := Surface) (N := GluedConstruction.Circle)) x)
  have h2 := (projection_snd_smooth (E := ℂ) (F := ℝ) (M := Surface) (N := GluedConstruction.Circle)) x
  convert! h1.prodMk h2 using 1
  simp only [← modelWithCornersSelf_prod]
lemma pieceEmbedding_differentiable : pieceEmbedding.MDifferentiable 𝓘(ℝ,EP) 𝓘(ℝ,EP) := by
  constructor
  · exact (pieceMap_smooth.mdifferentiable (by simp)).mdifferentiableOn
  · intro x hx
    exact ((pieceEmbedding_smooth_inverse hx).mdifferentiableAt (by simp)).mdifferentiableWithinAt

def pieceMetric (g : Metric (E := EP) WholePiece) : Metric (E := EP) Piece :=
  pullback g pieceMap_smooth (fun x => pieceEmbedding_differentiable.mfderiv (by exact ⟨mem_univ _,mem_univ _⟩))
    (fun _ => rfl)
lemma pieceMetric_inner (g : Metric (E := EP) WholePiece) (x : Piece) :
    (pieceMetric g).inner x = pullInner g pieceMap x := rfl

def leftPiece {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : Metric (E := EP) Piece := pieceMetric (leftWhole hδ)
def rightPiece {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : Metric (E := EP) Piece := pieceMetric (rightWhole hδ)
end

open MetricConstruction CylinderConstruction

lemma cuspLevel_lt_two : cuspLevel < 2 := by
  rw [cuspLevel,← Real.exp_log (by norm_num : (0:ℝ)<2)]
  apply Real.exp_lt_exp.mpr
  linarith [RadialProfile.log_bounds.1]

lemma cuspMetric_change (g : Metric (E := P) Cylinder) (a b : ℝ) (ha : 1 < a) (hb : 1 < b)
    (hab : a ≤ b) {q : WholePiece} (hq : q ∈ wholeCusp b) :
    (cuspMetric g a ha).inner q = (cuspMetric g b hb).inner q := by
  obtain ⟨z,hz,hzq⟩ := hq
  let r := CircleConstruction.sectionMap 6 q.2
  have he : sourceProjection (z,r) = q := by
    exact Prod.ext hzq (CircleConstruction.section_spec 6 q.2)
  have ht : (cuspMetric g a ha).inner (sourceProjection (z,r)) =
      (cuspMetric g b hb).inner (sourceProjection (z,r)) := by
    apply bilin_eq_of_pull_eq (E := EP) (F := EP) (z,r) (sourceProjection_deriv_surjective (z,r))
    rw [cuspMetric_projection g a ha (x := (z,r)) (hab.trans_lt hz),cuspMetric_projection g b hb (x := (z,r)) hz]
  exact he ▸ ht

variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
lemma wholeMetric_cusp_two {q : WholePiece} (hq : q ∈ wholeCusp 2) :
    (wholeMetric g c hc low).inner q = pullInner (E := EP) g (logCuspMap 2 (by norm_num)) q := by
  have hqa : q ∈ wholeCusp cuspLevel := by
    obtain ⟨z,hz,hzq⟩ := hq
    exact ⟨z,cuspLevel_lt_two.trans hz,hzq⟩
  rw [wholeMetric_cusp g c hc low hqa,
    cuspMetric_change g cuspLevel 2 cuspLevel_gt (by norm_num) cuspLevel_lt_two.le hq,
    cuspMetric_inner g 2 (by norm_num) hq]
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction

def collarLog : collar → Cylinder := logCuspMap 2 (by norm_num) ∘ pieceMap ∘ Subtype.val
lemma collarLog_smooth : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ collarLog := by
  intro x
  exact (logCuspMap_smoothAt 2 (by norm_num) (show pieceMap x.1 ∈ wholeCusp 2 from x.2)).comp x
    ((pieceMap_smooth x.1).comp x ((contMDiff_subtype_val (U := collar) (n := ∞)) x))
lemma collarLog_eq (x : collar) :
    collarLog x = (Real.log (collarCoordinates x).1.1,(collarCoordinates x).2) := by
  obtain ⟨z,hz,r,rfl⟩ := neckLift_surjective x
  rw [neckLift_coordinates]
  exact logCusp_projection_apply 2 (by norm_num) (z,r) hz.1

variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
lemma pieceMetric_collar (x : collar) :
    pullInner (E := EP) (pieceMetric (wholeMetric g c hc low)) Subtype.val x =
      pullInner (E := EP) g collarLog x := by
  let f : collar → WholePiece := pieceMap ∘ Subtype.val
  have hfs : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ f :=
    pieceMap_smooth.comp (contMDiff_subtype_val (U := collar))
  change pullBilin (E := EP) (F := EP)
    (pullInner (wholeMetric g c hc low) pieceMap x.1)
      (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) (Subtype.val : collar → Piece) x) = _
  rw [← pull_composition _ ((contMDiff_subtype_val (U := collar) (n := ∞) x).mdifferentiableAt (by simp))
    ((pieceMap_smooth x.1).mdifferentiableAt (by simp))]
  change pullBilin (E := EP) (F := EP) ((wholeMetric g c hc low).inner (f x))
    (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) f x) = _
  rw [wholeMetric_cusp_two g c hc low (show f x ∈ wholeCusp 2 from x.2)]
  exact (pull_composition g ((hfs x).mdifferentiableAt (by simp))
    ((logCuspMap_smoothAt 2 (by norm_num) (show f x ∈ wholeCusp 2 from x.2)).mdifferentiableAt (by simp))).symm

def leftPosition (δ : ℝ) : collar → Cylinder := radial (leftLength δ) ∘ collarLog
def rightPosition : collar → Cylinder := switch ∘ radial 4 ∘ collarLog
lemma leftPosition_smooth (δ : ℝ) : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (leftPosition δ) :=
  (radial_smooth (leftLength δ)).comp collarLog_smooth
lemma rightPosition_smooth : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ rightPosition :=
  switch_smooth.comp ((radial_smooth 4).comp collarLog_smooth)
lemma position_match (δ : ℝ) : rightPosition ∘ gluingMap = leftPosition δ := by
  funext x
  change switch (radial 4 (collarLog (gluingMap x))) = radial (leftLength δ) (collarLog x)
  rw [collarLog_eq,collarLog_eq]
  have hc : collarCoordinates (gluingMap x) =
      (collarFlip (collarCoordinates x).1,torusShear.symm (collarCoordinates x).2) := by
    simp only [gluingMap,Homeomorph.trans_apply,Homeomorph.apply_symm_apply]
    rfl
  rw [hc]
  apply Prod.ext
  · change 1 - RadialProfile.coordinate 4 (Real.log (16/(collarCoordinates x).1.1)) =
      RadialProfile.coordinate (leftLength δ) (Real.log (collarCoordinates x).1.1)
    rw [RadialProfile.coordinate_flip (L := leftLength δ)
      (show (collarCoordinates x).1.1 ∈ Icc (2:ℝ) 8 from
        ⟨(collarCoordinates x).1.2.1.le,(collarCoordinates x).1.2.2.le⟩)]
    ring
  · exact torusShear.apply_symm_apply _

lemma leftPiece_collar {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x : collar) :
    pullInner (E := EP) (leftPiece hδ) Subtype.val x =
      pullInner (E := EP) (neck hδ (period_pos δ)) (leftPosition δ) x := by
  rw [show leftPiece hδ = pieceMetric (wholeMetric (leftCylinder hδ) (leftCircleScale δ)
    (leftCircleScale_pos δ).ne' (leftCylinder_low hδ)) from rfl,
    pieceMetric_collar]
  change pullBilin (E := EP) (F := P)
    (pullInner (neck hδ (period_pos δ)) (radial (leftLength δ)) (collarLog x))
    (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) collarLog x) = _
  exact (pull_composition _ ((collarLog_smooth x).mdifferentiableAt (by simp))
    ((radial_smooth (leftLength δ) _).mdifferentiableAt (by simp))).symm
lemma rightPiece_collar {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x : collar) :
    pullInner (E := EP) (rightPiece hδ) Subtype.val x =
      pullInner (E := EP) (neck hδ (period_pos δ)) rightPosition x := by
  rw [show rightPiece hδ = pieceMetric (wholeMetric (rightCylinder hδ) (rightCircleScale δ)
    (rightCircleScale_pos hδ.1).ne' (rightCylinder_low hδ)) from rfl,
    pieceMetric_collar]
  change pullBilin (E := EP) (F := P)
    (pullInner (switched (neck hδ (period_pos δ))) (radial 4) (collarLog x))
    (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) collarLog x) = _
  rw [← pull_composition _ ((collarLog_smooth x).mdifferentiableAt (by simp))
    ((radial_smooth 4 _).mdifferentiableAt (by simp))]
  change pullBilin (E := EP) (F := P)
    (pullInner (neck hδ (period_pos δ)) switch ((radial 4 ∘ collarLog) x))
    (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) (radial 4 ∘ collarLog) x) = _
  exact (pull_composition _ (((radial_smooth 4).comp collarLog_smooth x).mdifferentiableAt (by simp))
    ((switch_smooth _).mdifferentiableAt (by simp))).symm
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction

lemma gluing_smooth_self : ContMDiff 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ gluingMap := by
  simpa only [modelWithCornersSelf_prod] using gluingMap_smooth
lemma transition_smooth (x : collar) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ (TwoGluing.extendedTransition collar gluingMap) x.1 :=
  TwoGluing.extendedTransition_smooth collar gluingMap gluing_smooth_self x

lemma collar_pull_match {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x : collar) :
    pullInner (E := EP) (leftPiece hδ) Subtype.val x =
      pullInner (E := EP) (rightPiece hδ) (Subtype.val ∘ gluingMap) x := by
  rw [pull_composition _ ((gluing_smooth_self x).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (U := collar) (n := ∞) _).mdifferentiableAt (by simp)),
    rightPiece_collar,← pull_composition _ ((gluing_smooth_self x).mdifferentiableAt (by simp))
      ((rightPosition_smooth _).mdifferentiableAt (by simp)),position_match,leftPiece_collar]

lemma piece_overlap {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x : collar) :
    (leftPiece hδ).inner x.1 =
      pullInner (E := EP) (rightPiece hδ) (TwoGluing.extendedTransition collar gluingMap) x.1 := by
  apply bilin_eq_of_pull_eq (E := EP) (F := EP) x
    ((openSubtype_mdifferentiable collar ⟨x⟩).mfderiv (x := x) (mem_univ _) :
      TangentSpace 𝓘(ℝ,EP) x ≃L[ℝ] TangentSpace 𝓘(ℝ,EP) x.1).surjective
  have hc := pull_composition (E := EP) (F := EP) (rightPiece hδ)
    ((contMDiff_subtype_val (U := collar) (n := ∞) x).mdifferentiableAt (by simp))
    ((transition_smooth x).mdifferentiableAt (by simp))
  have he : TwoGluing.extendedTransition collar gluingMap ∘ (Subtype.val : collar → Piece) =
      Subtype.val ∘ gluingMap := funext (TwoGluing.extendedTransition_apply collar gluingMap)
  have hf := congrArg (fun f : collar → Piece => pullInner (E := EP) (rightPiece hδ) f x) he
  exact (collar_pull_match hδ x).trans (hf.symm.trans hc)
end ThreeManifold.CompactMetric

namespace ThreeManifold.MetricConstruction
variable {E F M N A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  (c : A → OpenPartialHomeomorph M N)
  (hc : ∀ x, ∃ i, x ∈ (c i).source)
  (hg : A → Metric (E := F) N)
  (heq : ∀ i j x, x ∈ (c i).source → x ∈ (c j).source →
    pullInner (E := E) (hg i) (c i) x = pullInner (E := E) (hg j) (c j) x)
  (hs : ∀ i, ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (c i) (c i).source)
  (hdi : ∀ i, (c i).MDifferentiable 𝓘(ℝ,E) 𝓘(ℝ,F))

def gluedInner (x : M) : TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ :=
  pullInner (E := E) (hg (hc x).choose) (c (hc x).choose) x

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
include heq in
lemma gluedInner_eq (i : A) (x : M) (hx : x ∈ (c i).source) :
    gluedInner c hc hg x = pullInner (E := E) (hg i) (c i) x :=
  heq _ i x (hc x).choose_spec hx

include heq hs in
lemma gluedInner_smooth :
    ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E).prod 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace 𝓘(ℝ,E) y →L[ℝ] TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ)
        x (gluedInner c hc hg x)) := by
  intro x
  obtain ⟨i,hi⟩ := hc x
  apply (pullback_inner_smoothAt (hg i) ((hs i x hi).contMDiffAt
    ((c i).open_source.mem_nhds hi))).congr_of_eventuallyEq
  filter_upwards [(c i).open_source.mem_nhds hi] with y hy
  exact congrArg (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y)
    (gluedInner_eq c hc hg heq i y hy)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma gluedInner_symm (x : M) (u v : TangentSpace 𝓘(ℝ,E) x) :
    gluedInner c hc hg x u v = gluedInner c hc hg x v u := by
  exact (hg (hc x).choose).symm _ _ _

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
include hdi in
lemma gluedInner_pos (x : M) (u : TangentSpace 𝓘(ℝ,E) x) (hu : u ≠ 0) :
    0 < gluedInner c hc hg x u u := by
  let e := (hdi (hc x).choose).mfderiv (hc x).choose_spec
  apply (hg (hc x).choose).pos
  exact fun hh => hu (e.injective (hh.trans e.map_zero.symm))

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
include hdi in
lemma gluedInner_bounded (x : M) :
    IsVonNBounded ℝ {u : TangentSpace 𝓘(ℝ,E) x | gluedInner c hc hg x u u < 1} := by
  let e := (hdi (hc x).choose).mfderiv (hc x).choose_spec
  have hb := ((hg (hc x).choose).isVonNBounded (c (hc x).choose x)).image
    e.symm.toContinuousLinearMap
  apply hb.subset
  intro u hu
  exact ⟨e u,hu,e.symm_apply_apply u⟩

def glue : Metric (E := E) M where
  inner := gluedInner c hc hg
  symm := gluedInner_symm c hc hg
  pos := gluedInner_pos c hc hg hdi
  isVonNBounded := gluedInner_bounded c hc hg hdi
  contMDiff := gluedInner_smooth c hc hg heq hs

lemma glue_local (i : A) (x : M) (hx : x ∈ (c i).source) :
    (glue c hc hg heq hs hdi).inner x = pullInner (E := E) (hg i) (c i) x :=
  gluedInner_eq c hc hg heq i x hx

lemma glue_inverse (i : A) (y : N) (hy : y ∈ (c i).target) :
    pullInner (E := F) (glue c hc hg heq hs hdi) (c i).symm y = (hg i).inner y := by
  have hx : (c i).symm y ∈ (c i).source := (c i).map_target hy
  have he : ((c i) ∘ (c i).symm) =ᶠ[nhds y] id := by
    filter_upwards [(c i).open_target.mem_nhds hy] with z hz
    exact (c i).right_inv hz
  have hd : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (c i) ((c i).symm y)).comp
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) (c i).symm y) = ContinuousLinearMap.id ℝ F := by
    rw [← mfderiv_comp y (((hdi i).1 _ hx).mdifferentiableAt
      ((c i).open_source.mem_nhds hx)) (((hdi i).2 _ hy).mdifferentiableAt
        ((c i).open_target.mem_nhds hy))]
    exact he.mfderiv_eq.trans mfderiv_id
  ext u v
  rw [pullInner_apply,glue_local c hc hg heq hs hdi i _ hx,pullInner_apply]
  have hdu := congrArg (fun L : F →L[ℝ] F => L u) hd
  have hdv := congrArg (fun L : F →L[ℝ] F => L v) hd
  calc
    _ = (hg i).inner (c i ((c i).symm y)) u v :=
      congrArg₂ (fun a b : F => (hg i).inner (c i ((c i).symm y)) a b) hdu hdv
    _ = (hg i).inner y u v :=
      congrArg (fun z : N => ((hg i).inner z : F →L[ℝ] F →L[ℝ] ℝ) u v) ((c i).right_inv hy)

end ThreeManifold.MetricConstruction

namespace ThreeManifold.GluedConstruction
open TwoGluing (pieceChart pieceChart_apply)
abbrev EPm := ℂ × ℝ

lemma inclusion_smooth (i : Bool) : ContMDiff 𝓘(ℝ,EPm) 𝓘(ℝ,EPm) ∞ (inclusion i) := by
  intro x
  let c := pieceChart (E := EPm) collar gluingMap i x
  have hc : c ∈ atlas EPm Manifold := ⟨i,x,rfl⟩
  have ht : chartAt EPm x x ∈ c.target := (chartAt EPm x).map_source (mem_chart_source _ _)
  have h1 := contMDiffAt_of_mem_maximalAtlas
    (I := 𝓘(ℝ,EPm)) (chart_mem_maximalAtlas (I := 𝓘(ℝ,EPm)) (n := ∞) x) (mem_chart_source _ _)
  have h2 := contMDiffAt_symm_of_mem_maximalAtlas
    (I := 𝓘(ℝ,EPm)) (subset_maximalAtlas (I := 𝓘(ℝ,EPm)) (n := ∞) hc) ht
  apply (h2.comp x h1).congr_of_eventuallyEq
  filter_upwards [(chartAt EPm x).open_source.mem_nhds (mem_chart_source _ _)] with y hy
  change inclusion i y = c.symm (chartAt EPm x y)
  change TwoGluing.inclusion collar gluingMap i y =
    TwoGluing.inclusion collar gluingMap i ((chartAt EPm x).symm (chartAt EPm x y))
  rw [(chartAt EPm x).left_inv hy]

def pieceOpenMap (i : Bool) : OpenPartialHomeomorph Piece Manifold :=
  (TwoGluing.inclusion_openEmbedding collar gluingMap i).toOpenPartialHomeomorph _
lemma pieceOpenMap_apply (i : Bool) : (pieceOpenMap i : Piece → Manifold) = inclusion i := rfl
lemma pieceOpenMap_inclusion (i : Bool) (x : Piece) : (pieceOpenMap i).symm (inclusion i x) = x :=
  (pieceOpenMap i).left_inv (by simp [pieceOpenMap])

lemma pieceOpenMap_inverse_smooth (i : Bool) {p : Manifold} (hp : p ∈ (pieceOpenMap i).target) :
    ContMDiffAt 𝓘(ℝ,EPm) 𝓘(ℝ,EPm) ∞ (pieceOpenMap i).symm p := by
  let x := (pieceOpenMap i).symm p
  have hxp : inclusion i x = p := (pieceOpenMap i).right_inv hp
  let c := pieceChart (E := EPm) collar gluingMap i x
  have hc : c ∈ atlas EPm Manifold := ⟨i,x,rfl⟩
  have hps : p ∈ c.source := ⟨x,mem_chart_source _ _,hxp⟩
  have hcp : c p ∈ (chartAt EPm x).target := c.map_source hps
  have h1 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,EPm))
    (subset_maximalAtlas (I := 𝓘(ℝ,EPm)) (n := ∞) hc) hps
  have h2 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,EPm))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,EPm)) (n := ∞) x) hcp
  apply (h2.comp p h1).congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hps] with q hq
  obtain ⟨y,hy,rfl⟩ := hq
  change (pieceOpenMap i).symm (inclusion i y) = (chartAt EPm x).symm (c (inclusion i y))
  rw [pieceOpenMap_inclusion]
  change y = (chartAt EPm x).symm (pieceChart (E := EPm) collar gluingMap i x (TwoGluing.inclusion collar gluingMap i y))
  rw [pieceChart_apply,(chartAt EPm x).left_inv hy]

lemma pieceOpenMap_mdifferentiable (i : Bool) : (pieceOpenMap i).MDifferentiable 𝓘(ℝ,EPm) 𝓘(ℝ,EPm) := by
  constructor
  · exact ((inclusion_smooth i).mdifferentiable (by simp)).mdifferentiableOn
  · intro p hp
    exact ((pieceOpenMap_inverse_smooth i hp).mdifferentiableAt (by simp)).mdifferentiableWithinAt

lemma pieceOpenMap_cover (p : Manifold) : ∃ i, p ∈ (pieceOpenMap i).symm.source := by
  obtain ⟨i,x,hx⟩ := TwoGluing.inclusion_surjective collar gluingMap p
  refine ⟨i,?_⟩
  have ht := (pieceOpenMap i).map_source (x := x) (by simp [pieceOpenMap])
  exact hx ▸ ht
end ThreeManifold.GluedConstruction

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction

lemma piece_inverse_transition {p : GluedConstruction.Manifold}
    (h0 : p ∈ (pieceOpenMap false).target) (h1 : p ∈ (pieceOpenMap true).target) :
    ∃ _hx : (pieceOpenMap false).symm p ∈ collar,
      TwoGluing.extendedTransition collar gluingMap ((pieceOpenMap false).symm p) =
        (pieceOpenMap true).symm p := by
  have he : TwoGluing.inclusion collar gluingMap false ((pieceOpenMap false).symm p) =
      TwoGluing.inclusion collar gluingMap true ((pieceOpenMap true).symm p) :=
    ((pieceOpenMap false).right_inv h0).trans ((pieceOpenMap true).right_inv h1).symm
  obtain ⟨hx,hxe⟩ := (TwoGluing.inclusion_mixed_eq collar gluingMap _ _).mp he
  exact ⟨hx,(TwoGluing.extendedTransition_apply collar gluingMap ⟨_,hx⟩).trans hxe⟩
lemma piece_inverse_transition_germ {p : GluedConstruction.Manifold}
    (h0 : p ∈ (pieceOpenMap false).target) (h1 : p ∈ (pieceOpenMap true).target) :
    (pieceOpenMap true).symm =ᶠ[nhds p]
      (TwoGluing.extendedTransition collar gluingMap ∘ (pieceOpenMap false).symm) := by
  filter_upwards [(pieceOpenMap false).open_target.mem_nhds h0,
    (pieceOpenMap true).open_target.mem_nhds h1] with q hq0 hq1
  exact (piece_inverse_transition hq0 hq1).choose_spec.symm

lemma glued_mixed_metric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {p : GluedConstruction.Manifold}
    (h0 : p ∈ (pieceOpenMap false).target) (h1 : p ∈ (pieceOpenMap true).target) :
    pullInner (E := EP) (leftPiece hδ) (pieceOpenMap false).symm p =
      pullInner (E := EP) (rightPiece hδ) (pieceOpenMap true).symm p := by
  obtain ⟨hx,hxe⟩ := piece_inverse_transition h0 h1
  rw [pullInner_congr _ (piece_inverse_transition_germ h0 h1)]
  rw [pull_composition _ ((pieceOpenMap_inverse_smooth false h0).mdifferentiableAt (by simp))
    ((transition_smooth ⟨_,hx⟩).mdifferentiableAt (by simp))]
  exact congrArg (fun b : EP →L[ℝ] EP →L[ℝ] ℝ =>
    pullBilin (E := EP) (F := EP) b (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) (pieceOpenMap false).symm p))
      (piece_overlap hδ ⟨_,hx⟩)

def pieceMetrics {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) : Metric (E := EP) Piece :=
  if i then rightPiece hδ else leftPiece hδ
lemma pieceMetrics_compatible {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i j : Bool)
    (p : GluedConstruction.Manifold) (hi : p ∈ (pieceOpenMap i).symm.source)
    (hj : p ∈ (pieceOpenMap j).symm.source) :
    pullInner (E := EP) (pieceMetrics hδ i) (pieceOpenMap i).symm p =
      pullInner (E := EP) (pieceMetrics hδ j) (pieceOpenMap j).symm p := by
  cases i <;> cases j
  · rfl
  · exact glued_mixed_metric hδ hi hj
  · exact (glued_mixed_metric hδ hj hi).symm
  · rfl
lemma inverse_piece_smooth (i : Bool) :
    ContMDiffOn 𝓘(ℝ,EP) 𝓘(ℝ,EP) ∞ (pieceOpenMap i).symm (pieceOpenMap i).symm.source :=
  fun _ hp => (pieceOpenMap_inverse_smooth i hp).contMDiffWithinAt

def compactMetric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : Metric (E := EP) GluedConstruction.Manifold :=
  glue (fun i => (pieceOpenMap i).symm) pieceOpenMap_cover (pieceMetrics hδ)
    (pieceMetrics_compatible hδ) inverse_piece_smooth (fun i => (pieceOpenMap_mdifferentiable i).symm)
lemma compactMetric_local {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) (x : Piece) :
    pullInner (E := EP) (compactMetric hδ) (inclusion i) x = (pieceMetrics hδ i).inner x := by
  exact glue_inverse (fun i => (pieceOpenMap i).symm) pieceOpenMap_cover (pieceMetrics hδ)
    (pieceMetrics_compatible hδ) inverse_piece_smooth (fun i => (pieceOpenMap_mdifferentiable i).symm) i x
    (by exact mem_univ _)
end ThreeManifold.CompactMetric

namespace ThreeManifold.Rechart
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (e : E ≃L[ℝ] F)

lemma identity_smooth_forward : let := charts (M := M) e
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (id : M → M) := by
  dsimp only
  let := charts (M := M) e
  let := isManifold (M := M) e
  intro x
  have h1 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) x) (mem_chart_source _ _)
  have h2 : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ e (chartAt E x x) :=
    e.contDiff.contMDiff.contMDiffAt
  have ht : e (chartAt E x x) ∈ (chartAt F x).target := by
    rw [show chartAt F x = chart e (chartAt E x) from rfl,chart_target]
    exact ⟨chartAt E x x,(chartAt E x).map_source (mem_chart_source _ _),rfl⟩
  have h3 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,F))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,F)) (n := ∞) x) ht
  apply (h3.comp x (h2.comp x h1)).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source _ _)] with y hy
  change y = (chartAt E x).symm (e.symm (e (chartAt E x y)))
  rw [e.symm_apply_apply,(chartAt E x).left_inv hy]

lemma identity_smooth_backward : let := charts (M := M) e
    ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (id : M → M) := by
  dsimp only
  let := charts (M := M) e
  let := isManifold (M := M) e
  intro x
  have h1 := contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℝ,F))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,F)) (n := ∞) x) (mem_chart_source _ _)
  have h2 : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e.symm (chartAt F x x) :=
    e.symm.contDiff.contMDiff.contMDiffAt
  have ht : e.symm (chartAt F x x) ∈ (chartAt E x).target := by
    change e.symm (e (chartAt E x x)) ∈ (chartAt E x).target
    rw [e.symm_apply_apply]
    exact (chartAt E x).map_source (mem_chart_source _ _)
  have h3 := contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,E))
    (chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) x) ht
  apply (h3.comp x (h2.comp x h1)).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source _ _)] with y hy
  change y = (chartAt E x).symm (e.symm (e (chartAt E x y)))
  rw [e.symm_apply_apply,(chartAt E x).left_inv hy]
end ThreeManifold.Rechart
end

open Set Filter Topology Bundle Manifold IsManifold Bornology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction

def realCompactMetric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : SmoothMetric GluedConstruction.Manifold :=
  pullbackHomeomorph (compactMetric hδ) (Homeomorph.refl _)
    (Rechart.identity_smooth_backward Coordinates3.coordinates)
    (Rechart.identity_smooth_forward Coordinates3.coordinates)

theorem closed_oriented_metric :
    ∃ (M : Type) (top : TopologicalSpace M),
      letI := top
      ∃ (_ : T2Space M) (_ : SecondCountableTopology M) (_ : CompactSpace M)
        (_ : ConnectedSpace M) (charts : ChartedSpace E3 M),
        letI := charts
        ∃ (smooth : IsManifold I3 ∞ M),
          letI := smooth
          OrientedAtlas (M := M) ∧ Nonempty (SmoothMetric M) := by
  exact ⟨GluedConstruction.Manifold,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,realCharts,realSmooth,manifold_oriented,
    ⟨realCompactMetric (δ := 1/4) (by norm_num)⟩⟩
end ThreeManifold.CompactMetric

end

end OAI
