import Mathlib
import OAI.Probability.SKValue.GroundState.ConstantFatou

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def boolSign (x : ℝ) : Bool := if 0≤x then true else false

lemma measurable_boolSign : Measurable boolSign :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma spin_boolSign_eq {x : ℝ} (hx : x≠0) : SKValueG.spin (boolSign x)=Real.sign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [boolSign,SKValueG.spin,not_le.mpr h,Real.sign_of_neg h]
  · simp [boolSign,SKValueG.spin,h.le,Real.sign_of_pos h]

lemma gaussian_rounding_nonzero (a : ℝ) :
    ∀ᵐ z ∂standardGaussian,a+2*cdf standardGaussian z-1≠0 := by
  have hh : ∀ᵐ z ∂standardGaussian,cdf standardGaussian z≠(1-a)/2 :=
    (standardGaussian_cdf_hasLaw_uniform.ae_iff (measurableSet_setOfPred.mp ((measurableSet_eq_fun measurable_id measurable_const).compl))).mpr
      ((volume.restrict (Ioc (0 : ℝ) 1)).ae_ne ((1-a)/2))
  filter_upwards [hh] with z hz
  intro h
  apply hz
  linarith

lemma independent_rounding_nonzero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {U Z : Ω → ℝ}
    (hU : Measurable U) (hZ : HasLaw Z standardGaussian μ) (hind : IndepFun U Z μ) :
    ∀ᵐ ω ∂μ,U ω+2*cdf standardGaussian (Z ω)-1≠0 := by
  have hLaw : HasLaw U (μ.map U) μ := ⟨hU.aemeasurable,rfl⟩
  have hJoint := hind.hasLaw_prod hLaw hZ
  have hm : Measurable (fun p : ℝ×ℝ ↦ p.1+2*cdf standardGaussian p.2-1) :=
    (measurable_fst.add (((monotone_cdf _).measurable.comp measurable_snd).const_mul 2)).sub_const 1
  apply (hJoint.ae_iff (measurableSet_setOfPred.mp ((measurableSet_eq_fun hm measurable_const).compl))).mpr
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun hm measurable_const).compl)).mpr
  exact Eventually.of_forall gaussian_rounding_nonzero

lemma finite_rounding_signed_spin {N : ℕ} {U : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) (hUp : DependsBefore N U) :
    (fun z ↦ SKValueG.spin (boolSign (U z+2*cdf standardGaussian (coordinate N N z)-1)))
      =ᵐ[gaussianProduct (Fin (N+1))]
    (fun z ↦ Real.sign (U z+2*cdf standardGaussian (coordinate N N z)-1)) := by
  have := gaussianProduct_probability (Fin (N+1))
  exact (independent_rounding_nonzero hU (coordinate_hasLaw N N)
    (hUp.independent (by omega) hU)).mono (fun _ ↦ spin_boolSign_eq)

end SKValue

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

theorem normalized_shifted_sum_le_groundState {N : ℕ}
    (H : Fin N → (Fin (N+1) → ℝ) → ℝ) (U : (Fin (N+1) → ℝ) → ℝ)
    (hm : ∀ j,Measurable (H j)) (hp : ∀ j : Fin N,DependsBefore j (H j))
    (hL : ∀ j,MemLp (H j) 2 (gaussianProduct (Fin (N+1))))
    (hpos : ∀ j,0<∫ z,(H j z)^2 ∂gaussianProduct (Fin (N+1)))
    (hU : Measurable U) (hUp : DependsBefore N U) :
    (∑ j : Fin N,(∫ z,finiteRounded U z*
      normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1)))*
      (∫ z,finiteRounded U z*coordinate N (j+1) z ∂gaussianProduct (Fin (N+1))))≤groundStateValue := by
  let f := fun j : ℕ ↦ if hj : j<N then
    normalizedIncrement (H ⟨j,hj⟩) (coordinate N j) (gaussianProduct (Fin (N+1))) else fun _ ↦ 0
  let F := fun z ↦ boolSign (U z+2*cdf standardGaussian (coordinate N N z)-1)
  have hfm (j : ℕ) : Measurable (f j) := by
    dsimp only [f]
    split_ifs with hj
    · exact measurable_normalizedIncrement (hm ⟨j,hj⟩)
    · exact measurable_const
  have hfa (l : ℕ) (x y : Fin (N+1) → ℝ)
      (he : ∀ i : Fin (N+1),i.val≤l → x i=y i) : f l x=f l y := by
    dsimp only [f]
    split_ifs with hl
    · apply normalizedIncrement_dependsBefore (by omega) (hp ⟨l,hl⟩)
      intro i hi
      change i.val<l+1 at hi
      exact he i (by omega)
    · rfl
  have hfL (j : ℕ) (hj : j<N) : MemLp (f j) 2 (SKValueG.gaussianProduct (Fin (N+1))) := by
    simp only [f,dite_eq_left hj]
    exact normalizedIncrement_memLp_two (hL ⟨j,hj⟩) (coordinate_hasLaw N j)
      ((hp ⟨j,hj⟩).independent (by omega) (hm ⟨j,hj⟩))
  have hfu (j : ℕ) (hj : j<N) : (∫ z,(f j z)^2 ∂SKValueG.gaussianProduct (Fin (N+1)))=1 := by
    simp only [f,dite_eq_left hj]
    exact normalizedIncrement_second_moment (hm ⟨j,hj⟩).aestronglyMeasurable (coordinate_hasLaw N j)
      ((hp ⟨j,hj⟩).independent (by omega) (hm ⟨j,hj⟩)) (hpos ⟨j,hj⟩)
  have hfo (i j : ℕ) (hij : i<j) (hj : j<N) :
      (∫ z,f i z*f j z ∂SKValueG.gaussianProduct (Fin (N+1)))=0 := by
    have hi : i<N := hij.trans hj
    simp only [f,dite_eq_left hi,dite_eq_left hj]
    exact normalizedIncrements_orthogonal hij (by omega) (hm ⟨i,hi⟩) (hm ⟨j,hj⟩)
      (hp ⟨i,hi⟩) (hp ⟨j,hj⟩)
  have hFm : Measurable F := measurable_boolSign.comp
    ((hU.add (((monotone_cdf _).measurable.comp (measurable_coordinate N N)).const_mul 2)).sub_const 1)
  have he : (fun z ↦ SKValueG.spin (F z))=ᵐ[gaussianProduct (Fin (N+1))] finiteRounded U :=
    finite_rounding_signed_spin hU hUp
  have hb := SKValueG.predictable_coefficients_le_groundState N f F hfm hfa hfL hfu hfo hFm
  change _≤SKValueG.groundStateValue
  convert hb using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  · apply integral_congr_ae
    filter_upwards [he] with z hz
    simp only [f,dite_eq_left j.isLt,hz]
    exact mul_comm _ _
  · apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz,coordinate_eq_apply (by omega)]

end SKValue

end

end OAI
