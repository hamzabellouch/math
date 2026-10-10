import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkRadialLimit
import OAI.Probability.Perceptron.Cavity.CavityQuadraticDrop

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

def cavityVectorField (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (y : Fin M→Spin L) : Spin L :=
  t • ∑ i,a i • y i

lemma cavityLinearField_inner (M L : ℕ) (a : Fin M→ℝ) (t : ℝ) (z : Spin L) (y : Fin M→Spin L) :
    cavityLinearField M L a t z y=inner ℝ (cavityVectorField M L a t y) z := by
  simp only [cavityLinearField,cavityVectorField,real_inner_smul_left, sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm z (y i)]

lemma sphericalExp_square_le (n : ℕ) (R : ℝ) (x : Spin (n+1)) :
    sphericalExp n x R ^2 ≤ sphericalExp n x (2*R) := by
  let F : NormalizedSpin (n+1)→ℝ:=fun u=>Real.exp (R*inner ℝ x u.val)
  have hm : MemLp F 2 (unitSphereLaw (n+1)) := by
    apply (memLp_two_iff_integrable_sq (show AEStronglyMeasurable F _ from
      (show Continuous F from by unfold F; fun_prop).aestronglyMeasurable)).mpr
    exact unitSphere_continuous_integrable (by unfold F; fun_prop)
  have hv:=variance_nonneg F (unitSphereLaw (n+1))
  rw [variance_eq_sub hm] at hv
  have he : (∫ u,F u^2 ∂unitSphereLaw (n+1))=sphericalExp n x (2*R) := by
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [F]
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  change 0≤(∫ u,F u^2 ∂unitSphereLaw (n+1))-(∫ u,F u ∂unitSphereLaw (n+1))^2 at hv
  rw [he] at hv
  exact sub_nonneg.mp hv

lemma cavitySphericalExp_average (M n : ℕ) (a : Fin M→ℝ) (t R : ℝ) :
    (∫ y,sphericalExp n (cavityVectorField M (n+1) a t y) R
      ∂Measure.pi (fun _=>stdGaussian (Spin (n+1))))=
      Real.exp (R^2*t^2/2*∑ i,(a i)^2) := by
  let μ:=unitSphereLaw (n+1)
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin (n+1)))
  let F : NormalizedSpin (n+1)×(Fin M→Spin (n+1))→ℝ:=
    fun p=>Real.exp (cavityLinearField M (n+1) a t (R • p.1.val) p.2)
  have hF : Continuous F := by unfold F cavityLinearField; fun_prop
  have he u : (∫ y,F (u,y) ∂P)=Real.exp (R^2*t^2/2*∑ i,(a i)^2) := by
    have hh:=cavityLinearField_exp_moment M (n+1) a t (R • u.val) 1
    have hu : ‖u.val‖=1 := by simp
    simpa [F,P,hu,norm_smul,Real.norm_eq_abs,sq_abs,mul_comm,mul_left_comm,mul_assoc] using hh
  have hi : Integrable F (μ.prod P) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun u=>by
        simpa [F,P] using cavityLinearField_exp_integrable M (n+1) a t (R • u.val) 1
    · have hn : (fun u=>∫ y,‖F (u,y)‖ ∂P)=fun _ : NormalizedSpin (n+1)=>
          Real.exp (R^2*t^2/2*∑ i,(a i)^2) := by
        ext u
        simp only [F,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact he u
      rw [hn]
      exact integrable_const _
  calc
    _ = ∫ y,∫ u,F (u,y) ∂μ ∂P := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [F,cavityLinearField_inner,real_inner_smul_right]
    _ = ∫ u,∫ y,F (u,y) ∂P ∂μ := (integral_integral_swap hi).symm
    _ = _ := by simp only [he]; simp [μ]

lemma cavitySphericalExp_second_moment (M n : ℕ) (a : Fin M→ℝ) (t R : ℝ) :
    (∫ y,sphericalExp n (cavityVectorField M (n+1) a t y) R ^2
      ∂Measure.pi (fun _=>stdGaussian (Spin (n+1))))≤
      Real.exp (2*R^2*t^2*∑ i,(a i)^2) := by
  let P:=Measure.pi (fun _ : Fin M=>stdGaussian (Spin (n+1)))
  have hi : Integrable (fun y=>sphericalExp n (cavityVectorField M (n+1) a t y) (2*R)) P := by
    by_contra he
    have hh:=cavitySphericalExp_average M n a t (2*R)
    rw [integral_undef he] at hh
    exact (Real.exp_pos _).ne' hh.symm
  have hm : Continuous (fun y=>sphericalExp n (cavityVectorField M (n+1) a t y) R) :=
    (sphericalExp_continuous n R).comp (by unfold cavityVectorField; fun_prop)
  have hs : Integrable (fun y=>sphericalExp n (cavityVectorField M (n+1) a t y) R ^2) P :=
    hi.mono' (hm.pow 2).aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact sphericalExp_square_le n R _)
  have hb:=integral_mono hs hi (fun y=>sphericalExp_square_le n R (cavityVectorField M (n+1) a t y))
  rw [cavitySphericalExp_average] at hb
  convert hb using 1
  congr 1
  ring


lemma cavityLinearField_abs_bound (M L : ℕ) (a : Fin M→ℝ) (t : ℝ)
    (z : Spin L) (y : Fin M→Spin L) {A D : ℝ} (hA : 0≤A)
    (ha : ∀ i,|a i|≤A) (hz : ‖z‖≤D) :
    |cavityLinearField M L a t z y|≤|t| * ∑ i,A*D*‖y i‖ := by
  unfold cavityLinearField
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  calc
    _≤A*(‖z‖*‖y i‖) := mul_le_mul (ha i) (abs_real_inner_le_norm z (y i))
      (abs_nonneg _) hA
    _≤A*(D*‖y i‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) hA
    _=_ := by ring

lemma cavity_angular_denominator {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M n : ℕ)
    (a : S→Fin M→ℝ) (R W : S→ℝ) (ha : Measurable a) (hR : Measurable R)
    (hW : Measurable W) (t : ℝ) {A C D : ℝ} (hA : 0≤A)
    (haB : ∀ s i,|a s i|≤A) (hRB : ∀ s,|R s|≤D) (hWB : ∀ s,|W s|≤C)
    (y : Fin M→Spin (n+1)) :
    Real.exp (-C)≤∫ p : S×NormalizedSpin (n+1),
      Real.exp (W p.1+cavityLinearField M (n+1) (a p.1) t (R p.1 •p.2.val) y)
      ∂μ.prod (unitSphereLaw (n+1)) := by
  let F : S×NormalizedSpin (n+1)→ℝ:=fun p=>
    Real.exp (W p.1+cavityLinearField M (n+1) (a p.1) t (R p.1 •p.2.val) y)
  have hm : Measurable F := by
    have ham : Measurable (fun p : S×NormalizedSpin (n+1)=>a p.1) := ha.comp measurable_fst
    have hRm : Measurable (fun p : S×NormalizedSpin (n+1)=>R p.1) := hR.comp measurable_fst
    have hWm : Measurable (fun p : S×NormalizedSpin (n+1)=>W p.1) := hW.comp measurable_fst
    unfold F cavityLinearField
    fun_prop
  have hi : Integrable F (μ.prod (unitSphereLaw (n+1))) := by
    apply Integrable.of_bound hm.aestronglyMeasurable
      (Real.exp (C+|t| * ∑ i,A*D*‖y i‖))
    filter_upwards [] with p
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply add_le_add (abs_le.mp (hWB p.1)).2
    have hu : ‖p.2.val‖=1 := by simp
    exact (le_abs_self _).trans (cavityLinearField_abs_bound M (n+1) (a p.1) t _ y hA
      (haB p.1) (by simpa [norm_smul,hu,Real.norm_eq_abs] using hRB p.1))
  change Real.exp (-C)≤∫ p,F p ∂μ.prod (unitSphereLaw (n+1))
  rw [integral_prod _ hi]
  apply (show Real.exp (-C)=∫ _ : S,Real.exp (-C) ∂μ by simp).trans_le
  apply integral_mono (integrable_const _) hi.integral_prod_left
  intro s
  have he : (∫ v,F (s,v) ∂unitSphereLaw (n+1))=
      Real.exp (W s)*sphericalExp n (cavityVectorField M (n+1) (a s) t y) (R s) := by
    simp only [F,cavityLinearField_inner,real_inner_smul_right,Real.exp_add,integral_const_mul]
    rfl
  change Real.exp (-C)≤∫ v,F (s,v) ∂unitSphereLaw (n+1)
  rw [he]
  calc
    _≤Real.exp (W s) := Real.exp_le_exp.mpr (abs_le.mp (hWB s)).1
    _≤_ := le_mul_of_one_le_right (Real.exp_pos _).le (one_le_sphericalExp n _ _)

theorem cavity_angular_Q_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (M n : ℕ)
    (a b : S→Fin M→ℝ) (R W : S→ℝ) (ha : Measurable a) (hb : Measurable b)
    (hR : Measurable R) (hW : Measurable W) (t u : ℝ)
    {A B C D : ℝ} (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (haB : ∀ s i,|a s i|≤A) (hbB : ∀ s i,|b s i|≤B)
    (hRB : ∀ s,|R s|≤D) (hWB : ∀ s,|W s|≤C) :
    (∫ y,(∫ p : S×NormalizedSpin (n+1),
        Real.exp (W p.1+cavityLinearField M (n+1) (a p.1) t (R p.1 •p.2.val) y)*
        |cavityQuadraticField M (n+1) (b p.1) u (R p.1 •p.2.val) y|
          ∂μ.prod (unitSphereLaw (n+1)))/
      (∫ p : S×NormalizedSpin (n+1),
        Real.exp (W p.1+cavityLinearField M (n+1) (a p.1) t (R p.1 •p.2.val) y)
          ∂μ.prod (unitSphereLaw (n+1)))
      ∂Measure.pi (fun _=>stdGaussian (Spin (n+1))))≤
      Real.exp (2*C+t^2*D^2*M*A^2)*
        Real.sqrt (u^2*(D^2)^2*squareGaussianVariance*M*B^2) := by
  have hz : Measurable (fun p : S×NormalizedSpin (n+1)=>R p.1 •p.2.val) := by
    have hRm : Measurable (fun p : S×NormalizedSpin (n+1)=>R p.1) := hR.comp measurable_fst
    fun_prop
  have hzB (p : S×NormalizedSpin (n+1)) : ‖R p.1 •p.2.val‖^2≤D^2 := by
    have hu : ‖p.2.val‖=1 := by simp
    simp only [norm_smul,Real.norm_eq_abs,hu,mul_one]
    exact (sq_le_sq₀ (abs_nonneg _) hD).2 (hRB p.1)
  exact cavity_Q_normalized_bound (μ.prod (unitSphereLaw (n+1))) M (n+1)
    (fun p=>a p.1) (fun p=>b p.1) (fun p=>R p.1 •p.2.val) (fun p=>W p.1)
    (ha.comp measurable_fst) (hb.comp measurable_fst) hz (hW.comp measurable_fst)
    t u hA hB (sq_nonneg D) (fun p=>haB p.1) (fun p=>hbB p.1) hzB (fun p=>hWB p.1)
    (cavity_angular_denominator μ M n a R W ha hR hW t hA haB hRB hWB)

end SphericalPerceptronFreeEnergy
end

end OAI
