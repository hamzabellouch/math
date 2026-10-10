import Mathlib
import OAI.Geometry.BallPacking.Forms.FixedSpatialIntegral

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem chartSupportedTwoForm_own_chart {c : M} {α : Plane → Plane →L[ℝ] Plane →L[ℝ] ℝ}
    {y : Plane} (hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target) :
    chartTwoForm (chartSupportedTwoForm c α) c y = α y := by
  have he : (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) c).symm) =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) c).mem_nhds hy] with z hz
    exact (extChartAt 𝓘(ℝ,Plane) c).right_inv hz
  rw [chartSupportedTwoForm_chart hy ((extChartAt 𝓘(ℝ,Plane) c).map_target hy),
    he.fderiv_eq,(extChartAt 𝓘(ℝ,Plane) c).right_inv hy,fderiv_id]
  rfl

theorem extendedCoefficient_chartSupported {c : M} {f : Plane → ℝ}
    (hz : ∀ y, y ∉ (extChartAt 𝓘(ℝ,Plane) c).target → f y=0) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => chartSupportedTwoForm c (fun z => f z • planarArea)) (0,y) = f y := by
  classical
  by_cases hy : y ∈ (extChartAt 𝓘(ℝ,Plane) c).target
  · change (if y ∈ _ then chartTwoForm (chartSupportedTwoForm c (fun z => f z • planarArea)) c y (1,0) (0,1) else 0)=f y
    rw [ite_eq_left hy,chartSupportedTwoForm_own_chart hy]
    simp only [smul_apply,smul_eq_mul,planarArea]
    norm_num
  · change (if y ∈ _ then _ else 0)=f y
    rw [ite_eq_right hy,hz y hy]

theorem chartMass_chartSupported {c : M} {f : Plane → ℝ}
    (hz : ∀ y, y ∉ (extChartAt 𝓘(ℝ,Plane) c).target → f y=0) :
    chartMass c (chartSupportedTwoForm c (fun z => f z • planarArea)) = ∫ y, f y := by
  unfold chartMass
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (extendedCoefficient_chartSupported hz)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartCoefficient_integrable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {c : M} {Ω : P → ManifoldTwoForm Plane M}
    (hΩ : ContDiffOn ℝ ∞ (fun q : P × Plane => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (extChartAt 𝓘(ℝ,Plane) c).source)
    (hz : ∀ p x, x ∉ K → Ω p x=0) (p : P) :
    Integrable (fun y => extendedChartCoefficient c Ω (p,y)) := by
  have hf := extendedChartCoefficient_smooth hΩ hK hKc hz
  have hc : HasCompactSupport (fun y => extendedChartCoefficient c Ω (p,y)) := by
    apply HasCompactSupport.intro (hK.image_of_continuousOn
      ((continuousOn_extChartAt (I := 𝓘(ℝ,Plane)) c).mono hKc))
    exact fun y hy => extendedChartCoefficient_zero hz p hy
  exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport hc

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem extendedChartCoefficient_add (c : M) (Ω Λ : ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => Ω+Λ) (0,y) =
      extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)+extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y) := by
  unfold extendedChartCoefficient spatialZeroExtension
  split_ifs <;> simp only [chartTwoForm_add,add_apply,zero_add]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartMass_add {c : M} {Ω Λ : ManifoldTwoForm Plane M}
    (hΩ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)))
    (hΛ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y))) :
    chartMass c (Ω+Λ) = chartMass c Ω + chartMass c Λ := by
  unfold chartMass
  simp_rw [extendedChartCoefficient_add]
  exact integral_add hΩ hΛ

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartMass_smul (c : M) (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    chartMass c (a • Ω) = a*chartMass c Ω := by
  have he (y : Plane) : extendedChartCoefficient c (fun _ : ℝ => a • Ω) (0,y) =
      a*extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y) := by
    unfold extendedChartCoefficient spatialZeroExtension
    split_ifs <;> simp only [chartTwoForm_smul,smul_apply,smul_eq_mul,mul_zero]
  unfold chartMass
  simp_rw [he]
  exact integral_const_mul a _

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem chartMass_sub {c : M} {Ω Λ : ManifoldTwoForm Plane M}
    (hΩ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)))
    (hΛ : Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y))) :
    chartMass c (Ω-Λ) = chartMass c Ω - chartMass c Λ := by
  have he (y : Plane) : extendedChartCoefficient c (fun _ : ℝ => Ω-Λ) (0,y) =
      extendedChartCoefficient c (fun _ : ℝ => Ω) (0,y)-extendedChartCoefficient c (fun _ : ℝ => Λ) (0,y) := by
    unfold extendedChartCoefficient spatialZeroExtension
    split_ifs
    · rfl
    · exact (sub_self 0).symm
  unfold chartMass
  simp_rw [he]
  exact integral_sub hΩ hΛ


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def SmoothOneFormFamily (α : P → ManifoldOneForm E M) : Prop :=
  ∀ c, ContDiffOn ℝ ∞ (fun q : P × E => chartOneForm (α q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)

def SmoothTwoFormFamily (Ω : P → ManifoldTwoForm E M) : Prop :=
  ∀ c, ContDiffOn ℝ ∞ (fun q : P × E => chartTwoForm (Ω q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)

def HasCompactPrimitiveFamily (Ω : P → ManifoldTwoForm E M) : Prop :=
  ∃ (K : Set M) (_ : IsCompact K) (α : P → ManifoldOneForm E M),
    SmoothOneFormFamily α ∧ (∀ p x, x ∉ K → α p x=0) ∧
      ∀ p c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target →
        euclideanExteriorOneForm (chartOneForm (α p) c) y = chartTwoForm (Ω p) c y

theorem SmoothOneFormFamily.spatial_smooth {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (p : P) (c : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (chartOneForm (α p) c) y :=
  ((hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds ⟨mem_univ p,hy⟩)).comp y
    (contDiffAt_const.prodMk contDiffAt_id)

theorem HasCompactPrimitiveFamily.zero : HasCompactPrimitiveFamily (0 : P → ManifoldTwoForm E M) := by
  refine ⟨∅,isCompact_empty,0,?_,?_,?_⟩
  · intro c
    simpa only [Pi.zero_apply,chartOneForm_zero] using
      (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P × E => (0 : E →L[ℝ] ℝ)) _)
  · intro p x _; rfl
  · intro p c y _
    change euclideanExteriorOneForm (chartOneForm 0 c) y = chartTwoForm 0 c y
    rw [show chartOneForm (0 : ManifoldOneForm E M) c = fun _ => 0 from funext fun z => chartOneForm_zero c z]
    simp only [chartTwoForm_zero,euclideanExteriorOneForm,fderiv_const_apply,ContinuousLinearMap.flip_zero]
    exact sub_self (0 : E →L[ℝ] E →L[ℝ] ℝ)

theorem HasCompactPrimitiveFamily.add {Ω Λ : P → ManifoldTwoForm E M}
    (hΩ : HasCompactPrimitiveFamily Ω) (hΛ : HasCompactPrimitiveFamily Λ) :
    HasCompactPrimitiveFamily (Ω+Λ) := by
  obtain ⟨K,hK,α,hα,hα0,hαd⟩ := hΩ
  obtain ⟨L,hL,β,hβ,hβ0,hβd⟩ := hΛ
  refine ⟨K∪L,hK.union hL,α+β,?_,?_,?_⟩
  · intro c
    simpa only [Pi.add_apply,chartOneForm_add] using (hα c).add (hβ c)
  · intro p x hx
    change α p x+β p x=0
    rw [hα0 p x (fun hk => hx (Or.inl hk)),hβ0 p x (fun hl => hx (Or.inr hl)),add_zero]
  · intro p c y hy
    simp only [Pi.add_apply,chartTwoForm_add]
    rw [show chartOneForm (α p + β p) c =
      chartOneForm (α p) c + chartOneForm (β p) c from funext fun z => chartOneForm_add _ _ c z]
    rw [euclideanExteriorOneForm_add ((hα.spatial_smooth p c hy).differentiableAt (by simp))
      ((hβ.spatial_smooth p c hy).differentiableAt (by simp)),hαd p c y hy,hβd p c y hy]

theorem HasCompactPrimitiveFamily.smul {Ω : P → ManifoldTwoForm E M}
    (hΩ : HasCompactPrimitiveFamily Ω) {f : P → ℝ} (hf : ContDiff ℝ ∞ f) :
    HasCompactPrimitiveFamily (fun p => f p • Ω p) := by
  obtain ⟨K,hK,α,hα,hα0,hαd⟩ := hΩ
  refine ⟨K,hK,fun p => f p • α p,?_,?_,?_⟩
  · intro c
    simpa only [chartOneForm_smul,Function.comp_apply,Pi.smul_def'] using (hf.comp contDiff_fst).contDiffOn.smul (hα c)
  · intro p x hx
    change f p • α p x=0
    rw [hα0 p x hx,smul_zero]
  · intro p c y hy
    simp only [chartTwoForm_smul]
    rw [show chartOneForm (f p • α p) c = f p • chartOneForm (α p) c from
      funext fun z => chartOneForm_smul _ _ c z]
    rw [euclideanExteriorOneForm_smul _ ((hα.spatial_smooth p c hy).differentiableAt (by simp)),
      hαd p c y hy]

theorem HasCompactPrimitiveFamily.sum {I : Type*} (s : Finset I)
    {Ω : I → P → ManifoldTwoForm E M} (hΩ : ∀ i ∈ s, HasCompactPrimitiveFamily (Ω i)) :
    HasCompactPrimitiveFamily (∑ i ∈ s, Ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using HasCompactPrimitiveFamily.zero (P := P) (E := E) (M := M)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hΩ i (Finset.mem_insert_self i s)).add (ih (fun j hj => hΩ j (Finset.mem_insert_of_mem hj)))




def SmoothTwoForm (Ω : ManifoldTwoForm E M) : Prop :=
  ∀ c, ContDiffOn ℝ ∞ (chartTwoForm Ω c) (extChartAt 𝓘(ℝ,E) c).target

theorem SmoothTwoFormFamily.const {Ω : ManifoldTwoForm E M} (hΩ : SmoothTwoForm Ω) :
    SmoothTwoFormFamily (fun _ : P => Ω) := by
  intro c
  exact (hΩ c).comp contDiffOn_snd (fun _ hq => hq.2)

theorem SmoothTwoFormFamily.eval {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) (p : P) : SmoothTwoForm (Ω p) := by
  intro c
  apply (hΩ c).comp (f := fun y : E => (p,y))
    (contDiffOn_const.prodMk contDiffOn_id)
  exact fun y hy => ⟨mem_univ p,hy⟩

theorem SmoothTwoFormFamily.add {Ω Λ : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) (hΛ : SmoothTwoFormFamily Λ) : SmoothTwoFormFamily (Ω+Λ) := by
  intro c
  simpa only [Pi.add_apply,chartTwoForm_add] using (hΩ c).add (hΛ c)

theorem SmoothTwoFormFamily.smul {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) {f : P → ℝ} (hf : ContDiff ℝ ∞ f) :
    SmoothTwoFormFamily (fun p => f p • Ω p) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  intro c
  simpa only [chartTwoForm_smul,Function.comp_apply,Pi.smul_def'] using
    (hf.comp contDiff_fst).contDiffOn.smul (hΩ c)

theorem SmoothTwoFormFamily.neg {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) : SmoothTwoFormFamily (-Ω) := by
  have he : -Ω = fun p => (-1:ℝ) • Ω p := by ext p x u v; simp
  rw [he]
  exact hΩ.smul contDiff_const

theorem SmoothTwoFormFamily.sub {Ω Λ : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) (hΛ : SmoothTwoFormFamily Λ) : SmoothTwoFormFamily (Ω-Λ) := by
  have he : Ω-Λ = Ω+(-Λ) := sub_eq_add_neg Ω Λ
  rw [he]
  exact hΩ.add hΛ.neg

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem chartTwoForm_spatial_smul (ρ : M → ℝ) (Ω : ManifoldTwoForm E M) (c : M) (y : E) :
    chartTwoForm (fun x => ρ x • Ω x) c y =
      ρ ((extChartAt 𝓘(ℝ,E) c).symm y) • chartTwoForm Ω c y := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem SmoothTwoFormFamily.spatial_smul [IsManifold 𝓘(ℝ,E) ∞ M]
    {Ω : P → ManifoldTwoForm E M} (hΩ : SmoothTwoFormFamily Ω) {ρ : M → ℝ}
    (hρ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ρ) :
    SmoothTwoFormFamily (fun p x => ρ x • Ω p x) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  intro c q hq
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hrs := (hρ.contMDiffAt.comp q.2 hi).contDiffAt.comp q contDiffAt_snd
  have hfs := (hΩ c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)
  simpa only [chartTwoForm_spatial_smul,Pi.smul_def',Function.comp_apply] using (hrs.smul hfs).contDiffWithinAt


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

def PositivePlaneTransitions (M : Type*) [TopologicalSpace M] [ChartedSpace Plane M] : Prop :=
  ∀ (b c : M) (y : Plane), y ∈ (extChartAt 𝓘(ℝ,Plane) b).target →
    (extChartAt 𝓘(ℝ,Plane) b).symm y ∈ (extChartAt 𝓘(ℝ,Plane) c).source →
      0 < (fderiv ℝ (extChartAt 𝓘(ℝ,Plane) c ∘ (extChartAt 𝓘(ℝ,Plane) b).symm) y).det

structure BoxUnitBump (B : SurfaceCoordinateBox M) where
  form : ManifoldTwoForm Plane M
  smooth : SmoothTwoForm form
  skew : ∀ x u v, form x u v = -form x v u
  supportSet : Set M
  compact_supportSet : IsCompact supportSet
  support_subset : supportSet ⊆ B.carrier
  zero_off : ∀ x, x ∉ supportSet → form x=0
  unit_mass : chartMass B.center form=1

namespace SurfaceCoordinateBox

theorem exists_unit_bump [T2Space M] (B : SurfaceCoordinateBox M) : Nonempty (BoxUnitBump B) := by
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let : IsBoundedSMul ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := Plane →L[ℝ] Plane →L[ℝ] ℝ)
  obtain ⟨ρ,hρ,hρpos,hρc,hρzero,hρmass⟩ := exists_planar_unit_bump (show 0<B.radius/2 by linarith [B.radius_pos])
  let f : Plane → ℝ := fun z => ρ (z-B.point)
  have hf : ContDiff ℝ ∞ f := hρ.comp (contDiff_id.sub contDiff_const)
  let C := Metric.closedBall B.point (B.radius/2)
  have hC : C ⊆ (extChartAt 𝓘(ℝ,Plane) B.center).target :=
    (Metric.closedBall_subset_closedBall (show B.radius/2≤B.radius by linarith [B.radius_pos])).trans B.closed_subset
  have hfzero (z : Plane) (hz : z ∉ C) : f z=0 := by
    have hh : B.radius/2 < max |z.1-B.point.1| |z.2-B.point.2| := by
      simpa only [C,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
        Real.norm_eq_abs,not_le] using hz
    exact hρzero _ _ ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  let Ω := chartSupportedTwoForm B.center (fun z => f z • planarArea)
  let K := (extChartAt 𝓘(ℝ,Plane) B.center).symm '' C
  have hK : IsCompact K := (isCompact_closedBall B.point (B.radius/2)).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := 𝓘(ℝ,Plane)) B.center).mono hC)
  have hKB : K ⊆ B.carrier := by
    rintro x ⟨z,hz,rfl⟩
    refine ⟨(extChartAt 𝓘(ℝ,Plane) B.center).map_target (hC hz),?_⟩
    change extChartAt 𝓘(ℝ,Plane) B.center ((extChartAt 𝓘(ℝ,Plane) B.center).symm z) ∈ Metric.ball B.point B.radius
    rw [(extChartAt 𝓘(ℝ,Plane) B.center).right_inv (hC hz)]
    exact Metric.closedBall_subset_ball (by linarith [B.radius_pos]) hz
  have hΩzero (x : M) (hx : x ∉ K) : Ω x=0 :=
    chartSupportedTwoForm_zero (fun z hz => by rw [hfzero z hz,zero_smul]) hx
  have hΩsmooth : SmoothTwoForm Ω := by
    have hsm : ContDiff ℝ ∞ (fun q : ℝ × Plane => f q.2 • planarArea) :=
      (hf.comp contDiff_snd).smul contDiff_const
    intro b
    have hs := chartSupportedTwoForm_smooth (P := ℝ) (E := Plane) (M := M) (c := B.center)
      (α := fun q : ℝ × Plane => f q.2 • planarArea) hsm
      (K := C) (isCompact_closedBall B.point (B.radius/2)) hC
      (fun _ z hz => by rw [hfzero z hz,zero_smul]) b
    exact hs.comp (f := fun y : Plane => ((0:ℝ),y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨mem_univ _,hy⟩)
  have hΩskew (x : M) (u v : Plane) : Ω x u v = -Ω x v u := by
    unfold Ω chartSupportedTwoForm
    split_ifs <;> simp only [ContinuousLinearMap.bilinearComp_apply,smul_apply,smul_eq_mul,zero_apply,neg_zero]
    simp only [planarArea_apply]
    ring
  have hmass : chartMass B.center Ω=1 := by
    rw [chartMass_chartSupported (fun z hz => hfzero z (fun hc => hz (hC hc)))]
    change (∫ z, ρ (z-B.point))=1
    rw [MeasureTheory.integral_sub_right_eq_self]
    exact hρmass
  exact ⟨⟨Ω,hΩsmooth,hΩskew,K,hK,hKB,hΩzero,hmass⟩⟩

end SurfaceCoordinateBox

theorem BoxUnitBump.mass_in_chart (hpos : PositivePlaneTransitions M)
    {B : SurfaceCoordinateBox M} (β : BoxUnitBump B) (c : M)
    (hc : β.supportSet ⊆ (extChartAt 𝓘(ℝ,Plane) c).source) : chartMass c β.form=1 := by
  rw [← β.unit_mass]
  apply chartMass_change β.skew β.compact_supportSet hc
    (fun x hx => (β.support_subset hx).1) β.zero_off
  rintro y ⟨x,hx,rfl⟩
  apply hpos c B.center _ ((extChartAt 𝓘(ℝ,Plane) c).map_source (hc hx))
  simpa only [(extChartAt 𝓘(ℝ,Plane) c).left_inv (hc hx)] using (β.support_subset hx).1



end PackingSufficiencySupport.Hamiltonian
end

end OAI
