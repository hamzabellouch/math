import Mathlib
import OAI.Analysis.HardSphere.Model

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
@[simp] lemma project_representative (N : ℕ) (L : Length) (X : Configuration N L) :
    project N L (representative N L X) = X := by
  funext i j
  exact AddCircle.coe_equivIco

@[simp] lemma project_add {N : ℕ} {L : Length} (X Y : LiftedConfiguration N) :
    project N L (X + Y) = project N L X + project N L Y := by
  funext i j
  exact map_add (QuotientAddGroup.mk' _) _ _

@[simp] lemma project_sub {N : ℕ} {L : Length} (X Y : LiftedConfiguration N) :
    project N L (X - Y) = project N L X - project N L Y := by
  funext i j
  exact map_sub (QuotientAddGroup.mk' _) _ _

lemma continuous_project (N : ℕ) (L : Length) : Continuous (project N L) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (AddCircle.continuous_mk' L.val).comp
    ((continuous_apply j).comp (continuous_apply i))

lemma isQuotientMap_project (N : ℕ) (L : Length) :
    Topology.IsQuotientMap (project N L) := by
  have hcircle : Function.Surjective (fun t : ℝ ↦ (t : AddCircle L.val)) := by
    intro x
    exact ⟨(AddCircle.equivIco L.val 0 x).val, AddCircle.coe_equivIco⟩
  have hopen : IsOpenMap (fun X : Fin 3 → ℝ ↦ fun j ↦ (X j : AddCircle L.val)) :=
    IsOpenMap.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe)
      (Filter.Eventually.of_forall (fun _ ↦ hcircle))
  have hsurj : Function.Surjective
      (fun X : Fin 3 → ℝ ↦ fun j ↦ (X j : AddCircle L.val)) := by
    intro X
    exact ⟨fun j ↦ (AddCircle.equivIco L.val 0 (X j)).val,
      funext (fun _ ↦ AddCircle.coe_equivIco)⟩
  exact (IsOpenMap.piMap (fun _ : Fin N ↦ hopen)
    (Filter.Eventually.of_forall (fun _ ↦ hsurj))).isQuotientMap
      (continuous_project N L) (fun X ↦ ⟨representative N L X, project_representative N L X⟩)

lemma continuous_of_continuous_lift {N : ℕ} {L : Length}
    {E : Type*} [TopologicalSpace E] {f : Configuration N L → E}
    (hf : Continuous (fun X : LiftedConfiguration N ↦ f (project N L X))) :
    Continuous f :=
  (isQuotientMap_project N L).continuous_iff.mpr hf

lemma fderiv_lift_eq {N : ℕ} {L : Length} (f : Configuration N L → ℂ)
    {X Y : LiftedConfiguration N} (hXY : project N L X = project N L Y) :
    fderiv ℝ (fun Z ↦ f (project N L Z)) X =
      fderiv ℝ (fun Z ↦ f (project N L Z)) Y := by
  have hfun : (fun Z ↦ f (project N L (Z + (X - Y)))) =
      (fun Z ↦ f (project N L Z)) := by
    funext Z
    rw [project_add, project_sub, hXY, sub_self, add_zero]
  have h := congrArg (fun g : LiftedConfiguration N → ℂ ↦ fderiv ℝ g Y) hfun
  have he := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun Z ↦ f (project N L Z)) (x := Y) (X - Y)
  rw [he] at h
  simpa only [show Y + (X - Y) = X by abel] using h

lemma coordDerivative_project {N : ℕ} {L : Length} (f : Configuration N L → ℂ)
    (p : Direction N) (X : LiftedConfiguration N) :
    coordDerivative N L f p (project N L X) =
      fderiv ℝ (fun Y ↦ f (project N L Y)) X
        (Pi.single p.1 (Pi.single p.2 1)) := by
  unfold coordDerivative
  rw [fderiv_lift_eq f (project_representative N L (project N L X))]

lemma continuous_coordDerivative {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X))) (p : Direction N) :
    Continuous (coordDerivative N L f p) := by
  apply continuous_of_continuous_lift
  simp_rw [coordDerivative_project]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

lemma SmoothTest.continuous {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    Continuous f.toFun := continuous_of_continuous_lift f.smooth.continuous

lemma SmoothTest.continuous_partial {N : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest N L a) (p : Direction N) :
    Continuous (coordDerivative N L f.toFun p) := continuous_coordDerivative f.smooth p

def coordinateLine {N : ℕ} {L : Length} (X : Configuration N L)
    (p : Direction N) (t : AddCircle L.val) : Configuration N L :=
  X + Pi.single p.1 (Pi.single p.2 t)

lemma project_coordinateLine {N : ℕ} {L : Length} (X : Configuration N L)
    (p : Direction N) (t : ℝ) :
    project N L (representative N L X + t • (Pi.single p.1 (Pi.single p.2 1) : LiftedConfiguration N)) =
      coordinateLine X p (t : AddCircle L.val) := by
  rw [project_add, project_representative]
  congr 1
  funext i j
  by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;>
    simp [project, hi, hj]

lemma hasDerivAt_coordinateLine {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (X : Configuration N L) (p : Direction N) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (coordinateLine X p (s : AddCircle L.val)))
      (coordDerivative N L f p (coordinateLine X p (t : AddCircle L.val))) t := by
  let e : LiftedConfiguration N := Pi.single p.1 (Pi.single p.2 1)
  have he : HasDerivAt (fun s : ℝ ↦ representative N L X + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add (representative N L X)
  have h := (hf (representative N L X + t • e)).hasFDerivAt.comp_hasDerivAt t he
  have hfun : (fun s : ℝ ↦ f (project N L (representative N L X + s • e))) =
      (fun s : ℝ ↦ f (coordinateLine X p (s : AddCircle L.val))) := by
    funext s
    rw [project_coordinateLine]
  change HasDerivAt (fun s ↦ f (project N L (representative N L X + s • e)))
    (fderiv ℝ (fun Y ↦ f (project N L Y)) (representative N L X + t • e) e) t at h
  rw [hfun] at h
  rw [← coordDerivative_project f p (representative N L X + t • e),
    project_coordinateLine] at h
  exact h

lemma continuous_coordinateLine {N : ℕ} {L : Length}
    (X : Configuration N L) (p : Direction N) : Continuous (coordinateLine X p) := by
  unfold coordinateLine
  apply Continuous.add continuous_const
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;>
    simp only [Pi.single_apply, hi, hj, ↓reduceIte]
  · exact continuous_id
  all_goals exact continuous_const

lemma integral_partial_coordinateLine {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (X : Configuration N L) (p : Direction N) :
    (∫ t : AddCircle L.val, coordDerivative N L f p (coordinateLine X p t)) = 0 := by
  rw [← AddCircle.intervalIntegral_preimage L.val 0]
  have hcont : Continuous (fun t : ℝ ↦
      coordDerivative N L f p (coordinateLine X p (t : AddCircle L.val))) :=
    (continuous_coordDerivative hf p).comp
      ((continuous_coordinateLine X p).comp (AddCircle.continuous_mk' L.val))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_coordinateLine (hf.differentiable (by simp)) X p t)
    (hcont.intervalIntegrable _ _)]
  rw [zero_add, AddCircle.coe_period, AddCircle.coe_zero, sub_self]

lemma integral_coordDerivative {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X))) (p : Direction N) :
    (∫ X : Configuration N L, coordDerivative N L f p X) = 0 := by
  let : BorelSpace (Configuration N L) := Pi.borelSpace
  have hcont : Continuous (fun z : AddCircle L.val × Configuration N L ↦
      coordDerivative N L f p (coordinateLine z.2 p z.1)) := by
    apply (continuous_coordDerivative hf p).comp
    unfold coordinateLine
    apply Continuous.add continuous_snd
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hi : i = p.1 <;> by_cases hj : j = p.2 <;>
      simp [hi, hj, continuous_const, continuous_fst]
  have hint : Integrable (fun z : AddCircle L.val × Configuration N L ↦
      coordDerivative N L f p (coordinateLine z.2 p z.1)) (volume.prod volume) := by
    exact integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact isCompact_univ)
  have hswap := integral_integral_swap
    (f := fun t X ↦ coordDerivative N L f p (coordinateLine X p t)) hint
  have hcir := integral_partial_coordinateLine hf
  simp_rw [hcir] at hswap
  simp only [integral_zero] at hswap
  let : (volume : Measure (Torus L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddLeftInvariant := by
    rw [volume_pi]
    exact Measure.pi.isAddLeftInvariant _
  let : (volume : Measure (Configuration N L)).IsAddRightInvariant :=
    IsAddLeftInvariant.isAddRightInvariant
  have hc : ∀ t : AddCircle L.val,
      (∫ X : Configuration N L, coordDerivative N L f p (coordinateLine X p t)) =
        ∫ X : Configuration N L, coordDerivative N L f p X := fun t ↦
    integral_add_right_eq_self _ _
  simp_rw [hc] at hswap
  have hvol : (volume (univ : Set (AddCircle L.val))).toReal = L.val := by
    rw [AddCircle.measure_univ, ENNReal.toReal_ofReal L.property.le]
  simp only [integral_const, Measure.real, hvol, Complex.real_smul] at hswap
  exact (mul_eq_zero.mp hswap).resolve_left (Complex.ofReal_ne_zero.mpr L.property.ne')

open scoped ComplexConjugate

lemma coordDerivative_mul {N : ℕ} {L : Length} {f g : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (hg : Differentiable ℝ (fun X : LiftedConfiguration N ↦ g (project N L X)))
    (p : Direction N) :
    coordDerivative N L (f * g) p = f * coordDerivative N L g p + g * coordDerivative N L f p := by
  funext X
  simp only [coordDerivative, Pi.mul_apply]
  rw [fderiv_fun_mul hf.differentiableAt hg.differentiableAt]
  simp only [add_apply, smul_apply,
    smul_eq_mul, project_representative, Pi.add_apply, Pi.mul_apply]
  rfl

lemma coordDerivative_conj {N : ℕ} {L : Length} {f : Configuration N L → ℂ}
    (hf : Differentiable ℝ (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (p : Direction N) :
    coordDerivative N L (fun X ↦ conj (f X)) p = fun X ↦ conj (coordDerivative N L f p X) := by
  funext X
  unfold coordDerivative
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (representative N L X)
    (hf _).hasFDerivAt
  exact congrArg (fun A : LiftedConfiguration N →L[ℝ] ℂ ↦
    A (Pi.single p.1 (Pi.single p.2 1))) h.fderiv

section

local instance complexTopologicalSemiring : IsTopologicalSemiring ℂ := inferInstance

local instance configurationContinuousMapStarModule (N : ℕ) (L : Length) :
    StarModule ℂ C(Configuration N L, ℂ) := inferInstance

def smoothAlgebra (N : ℕ) (L : Length) : StarSubalgebra ℂ C(Configuration N L, ℂ) where
  carrier := {f | ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ f (project N L X))}
  mul_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at *
    exact hf.mul hg
  add_mem' := by
    intro f g hf hg
    simp only [Set.mem_ofPred_eq] at *
    exact hf.add hg
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_ofPred_eq, algebraMap_apply]
    exact contDiff_const
  star_mem' := by
    intro f hf
    simp only [Set.mem_ofPred_eq] at *
    exact Complex.conjCLE.contDiff.comp hf
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.zero_apply]
    exact contDiff_const
  one_mem' := by
    simp only [Set.mem_ofPred_eq, ContinuousMap.one_apply]
    exact contDiff_const

end

def coordinateCharacter {N : ℕ} {L : Length} (p : Direction N) : C(Configuration N L, ℂ) :=
  (fourier 1).comp ⟨fun X ↦ X p.1 p.2,
    (continuous_apply p.2).comp (continuous_apply p.1)⟩

lemma coordinateCharacter_smooth {N : ℕ} {L : Length} (p : Direction N) :
    coordinateCharacter p ∈ smoothAlgebra N L := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun X : LiftedConfiguration N ↦ fourier 1 (X p.1 p.2 : AddCircle L.val))
  simp_rw [fourier_coe_apply]
  exact Complex.contDiff_exp.comp
    ((((contDiff_const.mul contDiff_const).mul contDiff_const).mul contDiff_const).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply ℝ ℝ p.1 p.2)) |>.div_const _)

lemma smoothAlgebra_separatesPoints (N : ℕ) (L : Length) :
    (smoothAlgebra N L).SeparatesPoints := by
  intro X Y hXY
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hXY
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  refine ⟨_, ⟨coordinateCharacter (i,j), coordinateCharacter_smooth (i,j), rfl⟩, ?_⟩
  change fourier 1 (X i j) ≠ fourier 1 (Y i j)
  rw [fourier_one, fourier_one]
  intro he
  apply hj
  exact AddCircle.injective_toCircle L.property.ne' (Subtype.ext he)

lemma smoothAlgebra_dense (N : ℕ) (L : Length) :
    Dense (smoothAlgebra N L : Set C(Configuration N L, ℂ)) := by
  have hh := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (smoothAlgebra N L) (smoothAlgebra_separatesPoints N L)
  rw [dense_iff_closure_eq]
  exact congrArg (fun A : StarSubalgebra ℂ C(Configuration N L, ℂ) ↦ (A : Set C(Configuration N L, ℂ))) hh

lemma smoothAlgebra_toLp_dense (N : ℕ) (L : Length) :
    DenseRange (fun f : smoothAlgebra N L ↦
      ContinuousMap.toLp 2 volume ℂ (f : C(Configuration N L, ℂ))) := by
  exact (ContinuousMap.toLp_denseRange ℂ volume ℂ (by simp : (2 : ℝ≥0∞) ≠ ∞)).comp
    (smoothAlgebra_dense N L).denseRange_val (ContinuousMap.toLp 2 volume ℂ).continuous

lemma integral_integration_by_parts {N : ℕ} {L : Length}
    {f g : Configuration N L → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ f (project N L X)))
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun X : LiftedConfiguration N ↦ g (project N L X))) (p : Direction N) :
    (∫ X, conj (f X) * coordDerivative N L g p X) +
      (∫ X, conj (coordDerivative N L f p X) * g X) = 0 := by
  have hconj := Complex.conjCLE.contDiff.comp hf
  have h := integral_coordDerivative (f := (fun X ↦ conj (f X)) * g)
    (hconj.mul hg) p
  rw [coordDerivative_mul (hconj.differentiable (by simp)) (hg.differentiable (by simp)),
    coordDerivative_conj (hf.differentiable (by simp))] at h
  have hfg : Integrable (fun X ↦ conj (f X) * coordDerivative N L g p X) := by
    exact integrableOn_univ.mp
      ((((continuous_of_continuous_lift hf.continuous).star).mul
        (continuous_coordDerivative hg p)).continuousOn.integrableOn_compact isCompact_univ)
  have hgf : Integrable (fun X ↦ g X * conj (coordDerivative N L f p X)) := by
    exact integrableOn_univ.mp
      (((continuous_of_continuous_lift hg.continuous).mul
        (continuous_coordDerivative hf p).star).continuousOn.integrableOn_compact isCompact_univ)
  simp only [Pi.add_apply, Pi.mul_apply] at h
  rw [integral_add hfg hgf] at h
  simpa only [Pi.mul_apply, mul_comm (g _)] using h

def smoothPartial {N : ℕ} {L : Length} (f : smoothAlgebra N L) (p : Direction N) :
    C(Configuration N L, ℂ) :=
  ⟨coordDerivative N L f.val p, continuous_coordDerivative f.property p⟩

section

local instance configurationProductBorel (N : ℕ) (L : Length) :
    BorelSpace (Configuration N L) := Pi.borelSpace

lemma SmoothTest.weak_derivative {N : ℕ} {L : Length} {a : ℝ}
    (u : SmoothTest N L a) (f : smoothAlgebra N L) (p : Direction N) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f.val) (u.jet.2 p) +
      inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) u.jet.1 = 0 := by
  rw [L2.inner_def, L2.inner_def]
  have h₁ : (∫ X, inner ℂ ((ContinuousMap.toLp 2 volume ℂ f.val) X) ((u.jet.2 p) X)) =
      ∫ X, conj (f.val X) * coordDerivative N L u.toFun p X := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume f.val, (u.partial_memLp p).coeFn_toLp]
      with X hX hY
    change inner ℂ _ ((u.partial_memLp p).toLp _ X) = _
    rw [hX, hY, RCLike.inner_apply, mul_comm]
  have h₂ : (∫ X, inner ℂ ((ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) X) (u.jet.1 X)) =
      ∫ X, conj (coordDerivative N L f.val p X) * u.toFun X := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume (smoothPartial f p), u.memLp.coeFn_toLp]
      with X hX hY
    change inner ℂ _ (u.memLp.toLp _ X) = _
    rw [hX, hY, RCLike.inner_apply, mul_comm]
    rfl
  rw [h₁, h₂]
  exact integral_integration_by_parts f.property u.smooth p

lemma weak_derivative {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) (f : smoothAlgebra N L) (p : Direction N) :
    inner ℂ (ContinuousMap.toLp 2 volume ℂ f.val) (u.2 p) +
      inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) u.1 = 0 := by
  have hc : IsClosed {v : Jet N L |
      inner ℂ (ContinuousMap.toLp 2 volume ℂ f.val) (v.2 p) +
      inner ℂ (ContinuousMap.toLp 2 volume ℂ (smoothPartial f p)) v.1 = 0} :=
    isClosed_eq ((continuous_const.inner ((continuous_apply p).comp continuous_snd)).add
      (continuous_const.inner continuous_fst)) continuous_const
  exact closure_minimal (by rintro _ ⟨v, rfl⟩; exact v.weak_derivative f p) hc hu

end

lemma derivative_zero_of_scalar_zero {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : u ∈ dirichletDomain N L a) (hz : u.1 = 0) : u.2 = 0 := by
  funext p
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  refine (smoothAlgebra_toLp_dense N L).induction_on
    (p := fun w ↦ inner ℂ w (u.2 p) = 0) (u.2 p)
    (isClosed_eq (continuous_id.inner continuous_const) continuous_const) ?_
  intro f
  have h := weak_derivative hu f p
  simpa only [hz, inner_zero_right, add_zero] using h

end HardSphere

end

end OAI
