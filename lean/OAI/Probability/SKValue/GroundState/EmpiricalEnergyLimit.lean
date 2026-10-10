import Mathlib
import OAI.Probability.SKValue.Processes.UnitMomentMartingale
import OAI.Probability.SKValue.GroundState.QuadraticSK

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG

lemma gaussian_coordinate_memLp {κ : Type*} [Fintype κ] (i : κ) :
    MemLp (fun x : κ → ℝ ↦ x i) 2 (gaussianProduct κ) :=
  SKValue.gaussian_memLp (measurePreserving_eval (fun _ : κ ↦ standardGaussian) i).hasLaw 2 (by norm_num)

lemma gaussian_coordinate_sq_mean {κ : Type*} [Fintype κ] (i : κ) :
    (∫ x : κ → ℝ,(x i)^2 ∂gaussianProduct κ)=1 :=
  SKValue.gaussian_second_moment (measurePreserving_eval (fun _ : κ ↦ standardGaussian) i).hasLaw

lemma predictable_coordinate_mean_zero (K : ℕ) (f : ℕ → (Fin (K+1) → ℝ) → ℝ)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    {i j : ℕ} (hij : i≤j) (hj : j<K) :
    (∫ y,f i y*y ⟨j+1,by omega⟩ ∂gaussianProduct (Fin (K+1)))=0 := by
  have hd : SKValue.DependsBefore (j+1) (f i) := by
    intro x y he
    exact ha i x y (fun k hk ↦ he k (by omega))
  have hh := (hd.independent (by omega) (hm i)).integral_mul_eq_mul_integral
    (hm i).aestronglyMeasurable (SKValue.measurable_coordinate K (j+1)).aestronglyMeasurable
  rw [SKValue.gaussian_mean (SKValue.coordinate_hasLaw K (j+1)),mul_zero] at hh
  simpa only [Pi.mul_apply,SKValue.gaussianProduct,gaussianProduct,SKValue.standardGaussian,standardGaussian,SKValue.coordinate_eq_apply (show j+1<K+1 by omega)] using hh

lemma unit_function_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) (hm : Measurable F) (hF : ∀ x,(F x)^2=1) :
    MemLp F 2 μ := by
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  have hh := hF x
  nlinarith [sq_abs (F x),abs_nonneg (F x)]

theorem empiricalColumnEnergy_ae_tendsto (K : ℕ)
    (f : ℕ → (Fin (K+1) → ℝ) → ℝ) (F : (Fin (K+1) → ℝ) → ℝ)
    (hm : ∀ i,Measurable (f i))
    (ha : ∀ l x y,(∀ i : Fin (K+1),i.val≤l → x i=y i) → f l x=f l y)
    (hL : ∀ i<K,MemLp (f i) 2 (gaussianProduct (Fin (K+1))))
    (hu : ∀ i<K,(∫ y,(f i y)^2 ∂gaussianProduct (Fin (K+1)))=1)
    (ho : ∀ i j,i<j → j<K →(∫ y,f i y*f j y ∂gaussianProduct (Fin (K+1)))=0)
    (hFm : Measurable F) (hF : ∀ y,(F y)^2=1) {j : ℕ} (hj : j<K) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ gaussianProduct (Fin (K+1))),
      Tendsto (fun n ↦ empiricalColumnEnergy K n f x F j) atTop
        (𝓝 ((∫ y,f j y*F y ∂gaussianProduct (Fin (K+1)))*
          (∫ y,F y*y ⟨j+1,by omega⟩ ∂gaussianProduct (Fin (K+1))))) := by
  let μ := gaussianProduct (Fin (K+1))
  let Z : (Fin (K+1) → ℝ) → ℝ := fun y ↦ y ⟨j+1,by omega⟩
  have hF2 := unit_function_memLp μ F hFm hF
  have hZ2 : MemLp Z 2 μ := gaussian_coordinate_memLp _
  have hZi : Integrable (fun y ↦ (Z y)^2) μ := by
    simpa only [sq,Pi.mul_def] using hZ2.integrable_mul hZ2
  have hFi : Integrable (fun y ↦ (F y)^2) μ := by
    simpa only [sq,Pi.mul_def] using hF2.integrable_mul hF2
  have hn : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i≤j,
      Tendsto (fun n ↦ ‖empiricalVector (f i) x n‖) atTop (𝓝 1) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro hi
    apply empirical_norm_tendsto_one μ (f i) (hm i)
    · simpa only [sq,Pi.mul_def] using (hL i (by omega)).integrable_mul (hL i (by omega))
    · exact hu i (by omega)
  have hi : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i l,i<l → l≤j →
      Tendsto (fun n ↦ ⟪empiricalVector (f i) x n,empiricalVector (f l) x n⟫) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro l
    apply ae_all_iff.mpr
    intro hil
    apply ae_all_iff.mpr
    intro hl
    simpa only [μ,ho i l hil (by omega)] using empirical_inner_tendsto μ (f i) (f l)
      ((hm i).mul (hm l)) ((hL i (by omega)).integrable_mul (hL l (by omega)))
  have haf : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i≤j,
      Tendsto (fun n ↦ ⟪empiricalVector (f i) x n,empiricalVector F x n⟫) atTop
        (𝓝 (∫ y,f i y*F y ∂μ)) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro hi
    exact empirical_inner_tendsto μ (f i) F ((hm i).mul hFm)
      ((hL i (by omega)).integrable_mul hF2)
  have haz : ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),∀ i≤j,
      Tendsto (fun n ↦ ⟪empiricalVector (f i) x n,empiricalVector Z x n⟫) atTop (𝓝 0) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro hi
    simpa only [Z,μ,predictable_coordinate_mean_zero K f hm ha hi hj] using
      empirical_inner_tendsto μ (f i) Z ((hm i).mul (measurable_pi_apply _))
        ((hL i (by omega)).integrable_mul hZ2)
  filter_upwards [hn,hi,haf,haz,
    empirical_norm_tendsto_one μ F hFm hFi (by simp only [hF]; simp),
    empirical_norm_tendsto_one μ Z (measurable_pi_apply _) hZi (gaussian_coordinate_sq_mean _),
    empirical_inner_tendsto μ F Z (hFm.mul (measurable_pi_apply _)) (hF2.integrable_mul hZ2)]
    with x hn hi haf haz hFn hZn hb
  have he (n : ℕ) : empiricalColumnEnergy K n f x F j=
      ⟪gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j,empiricalVector F x n⟫*
        ⟪orthogonalRemainder (gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n))
          (empiricalVector F x n) (j+1),empiricalVector Z x n⟫+
      (⟪gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j,empiricalVector F x n⟫^2/
        Real.sqrt 2)*⟪gramSchmidtNormed ℝ (fun l ↦ empiricalVector (f l) x n) j,
          empiricalVector Z x n⟫ := by
    unfold empiricalColumnEnergy
    simp only [dite_eq_left (show j+1<K+1 by omega)]
    exact column_revealed_energy _ _ _ _ (fun i hi ↦
      gramSchmidtNormed_pairwise_orthogonal _ (Ne.symm (Nat.ne_of_lt hi)))
  simpa only [he] using normalized_column_energy_tendsto
    (fun n l ↦ empiricalVector (f l) x n) (fun n ↦ empiricalVector F x n)
    (fun n ↦ empiricalVector Z x n) j (fun i ↦ ∫ y,f i y*F y ∂μ)
    (∫ y,F y*Z y ∂μ) hn hi hFn hZn haf haz hb

end SKValueG

end

end OAI
