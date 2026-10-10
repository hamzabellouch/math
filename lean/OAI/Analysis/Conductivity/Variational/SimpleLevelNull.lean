import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch
import OAI.Analysis.Conductivity.Flux.AntisymmetricFlux
import OAI.Analysis.Conductivity.Fourier.AngularPeriodization

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

lemma simple_zeros_countable {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (U : Set ℝ)
    (hn : ∀ x∈U,f x=0 → deriv f x≠0) : ({x | x∈U ∧ f x=0} : Set ℝ).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  have he := (hf.hasStrictDerivAt (by norm_num) (x:=x)).eventually_left_inverse (hn x hx.1 hx.2)
  obtain ⟨V,hVs,hV,hxV⟩ := mem_nhds_iff.mp he
  refine ⟨V,hV,?_⟩
  ext y
  constructor
  · intro hy
    have hxy := hVs hy.1
    change HasStrictDerivAt.localInverse f (deriv f x) x _ _ (f y)=y at hxy
    exact hxy.symm.trans ((congrArg (HasStrictDerivAt.localInverse f (deriv f x) x _ _)
      (hy.2.2.trans hx.2.symm)).trans he.self_of_nhds)
  · intro hy
    subst y
    exact ⟨hxV,hx⟩

lemma simple_wall_zero_null {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {U : Set Box3} (hU : MeasurableSet U)
    (hn : ∀ x∈U,f x=0 → wallDerivative f x≠0) : volume ({x | x∈U ∧ f x=0})=0 := by
  change (volume.prod volume) ({x : Box3 | x∈U ∧ f x=0})=0
  apply Measure.measure_prod_null_of_ae_null (hU.inter (isClosed_eq hf.continuous continuous_const).measurableSet)
  apply Filter.Eventually.of_forall
  intro q
  have hs : ContDiff ℝ 1 (fun z : ℝ => f (q,z)) :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).of_le (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by norm_cast)
  have hh := simple_zeros_countable hs {z | (q,z)∈U} (by
    intro z hz he
    simpa only [←wallDerivative_slice (hf.differentiable (by simp))] using hn (q,z) hz he)
  exact hh.measure_zero volume

lemma wallDerivative_boxPullback {f : Coord3 → ℝ} (hf : Differentiable ℝ f) (p : Box3) :
    wallDerivative (fun y => f (boxCoordinates.symm y)) p=
      direction (Pi.single 2 1) f (boxCoordinates.symm p) := by
  have he := ((hf (boxCoordinates.symm p)).hasFDerivAt.comp p boxCoordinates.symm.hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ boxCoordinates.symm) p (0,1)=_
  rw [he,ContinuousLinearMap.comp_apply]
  have hh : (boxCoordinates.symm : Box3 →L[ℝ] Coord3) (0,1)=Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp [boxCoordinates_symm_apply]
  rw [hh]
  rfl

lemma simple_coord_zero_ae {f : Coord3 → ℝ} (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f)
    {U : Set Coord3} (hU : MeasurableSet U)
    (hn : ∀ x∈U,f x=0 → direction (Pi.single 2 1) f x≠0) :
    ∀ᵐ x : Coord3,x∈U → f x≠0 := by
  have hh := simple_wall_zero_null (hf.comp boxCoordinates.symm.contDiff)
    (hU.preimage boxCoordinates.symm.continuous.measurable) (by
      intro p hp hz
      change wallDerivative (fun y => f (boxCoordinates.symm y)) p≠0
      rw [wallDerivative_boxPullback (hf.differentiable (by simp))]
      exact hn _ hp hz)
  have ha := boxCoordinates_volume.quasiMeasurePreserving.ae (compl_mem_ae_iff.mpr hh)
  filter_upwards [ha] with x hx
  simpa only [mem_compl_iff,mem_ofPred_eq,mem_preimage,Function.comp_def,boxCoordinates.symm_apply_apply,not_and] using hx

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def pairMinor (u : Coord3 → Fin 2 → ℝ) (x : Coord3) : ℝ :=
  fderiv ℝ u x (Pi.single 0 1) 0*fderiv ℝ u x (Pi.single 2 1) 1-
    fderiv ℝ u x (Pi.single 2 1) 0*fderiv ℝ u x (Pi.single 0 1) 1

lemma pairMinor_rank {u : Coord3 → Fin 2 → ℝ} {x : Coord3} (hn : pairMinor u x≠0) :
    LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    apply hn
    have h0 := congrFun hz 0
    have h2 := congrFun hz 2
    change fderiv ℝ u x (Pi.single 0 1) 1=0 at h0
    change fderiv ℝ u x (Pi.single 2 1) 1=0 at h2
    simp only [pairMinor,h0,h2,mul_zero,sub_self]
  · intro a he
    apply hn
    have h0 := congrFun he 0
    have h2 := congrFun he 2
    change a*fderiv ℝ u x (Pi.single 0 1) 1=fderiv ℝ u x (Pi.single 0 1) 0 at h0
    change a*fderiv ℝ u x (Pi.single 2 1) 1=fderiv ℝ u x (Pi.single 2 1) 0 at h2
    simp only [pairMinor,←h0,←h2]
    ring

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma familySpatialDerivative_smooth {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => fderiv ℝ (fun y => u (z.1,y)) z.2) := by
  have hh : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : (P×Coord3)×Coord3 => u (z.1.1,z.2)) :=
    hu.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact hh.fderiv contDiff_snd (by simp)

lemma familyPairMinor_smooth {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => pairMinor (fun y => u (z.1,y)) z.2) := by
  have hh (i : Fin 3) (j : Fin 2) : ContDiff ℝ (↑(⊤:ℕ∞))
      (fun z : P×Coord3 => fderiv ℝ (fun y => u (z.1,y)) z.2 (Pi.single i 1) j) :=
    (contDiff_apply ℝ ℝ j).comp ((familySpatialDerivative_smooth hu).clm_apply contDiff_const)
  exact ((hh 0 0).mul (hh 2 1)).sub ((hh 2 0).mul (hh 0 1))

lemma pairMinor_smooth {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (pairMinor u) := by
  have hh (i : Fin 3) (j : Fin 2) : ContDiff ℝ (↑(⊤:ℕ∞))
      (fun x => fderiv ℝ u x (Pi.single i 1) j) :=
    (contDiff_apply ℝ ℝ j).comp ((hu.fderiv_right (by simp)).clm_apply contDiff_const)
  exact ((hh 0 0).mul (hh 2 1)).sub ((hh 2 0).mul (hh 0 1))

lemma AngularPeriodic.pairMinor {T : ℝ} {u : Coord3 → Fin 2 → ℝ}
    (hu : AngularPeriodic T u) : AngularPeriodic T (pairMinor u) := by
  intro n x
  unfold ScalarConductivity.pairMinor
  rw [hu.fderiv n x]

lemma regularRegion_ae_of_simple_minor {u : Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {A : Coord3 → Symmetric3}
    (hA : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val))
    {U : Set Coord3} (hU : IsOpen U)
    (hn : ∀ x∈U,pairMinor u x=0 → direction (Pi.single 2 1) (pairMinor u) x≠0) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion u A U := by
  have hm := pairMinor_smooth hu
  have ha := simple_coord_zero_ae hm hU.measurableSet hn
  let O := U∩{x | pairMinor u x≠0}
  have hO : IsOpen O := hU.inter (isOpen_ne_fun hm.continuous continuous_const)
  have hr : RegularPatch u A O :=
    ⟨hO,hu.contDiffOn,hA.contDiffOn,Or.inl (fun x hx => pairMinor_rank hx.2)⟩
  filter_upwards [ha] with x hx
  intro hxU
  exact mem_regularRegion_iff.mpr ⟨O,inter_subset_left,hr,⟨hxU,hx hxU⟩⟩

end ScalarConductivity

end
end

end OAI
