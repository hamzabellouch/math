import Mathlib
import OAI.Probability.SKRatio.FiniteChain.CutoffScale
import OAI.Probability.SKRatio.Matrices.GoeMatrixQuadCoeff
import OAI.Probability.SKRatio.Matrices.GaussianRows
import OAI.Probability.SKRatio.Variational.UniformGap

namespace OAI

section
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Gaussian
open Calculus
variable {n : ℕ}

lemma coupling_bridge (g : Disorder n) : coupling g = SKRatioGaussian.coupling g := by
  funext i j
  unfold coupling SKRatioGaussian.coupling
  split_ifs <;> rfl

lemma continuous_operator_norm : Continuous (fun g : Disorder n => euclideanOpNorm (coupling g)) := by
  exact continuous_norm.comp
    (((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional).comp
      (continuous_pi (fun i => continuous_pi (fun k => continuous_coupling i k))))

def matrixGood (β δ : ℝ) (n : ℕ) : Set (Disorder n) :=
  {g | euclideanOpNorm (coupling g) ≤ 2*β+δ ∧
    (∀ i k, |coupling g i k| ≤ δ) ∧
    (∀ i, ∑ k, coupling g i k^2 ≤ β^2+δ)}

lemma matrixGood_measurable (β δ : ℝ) (n : ℕ) : MeasurableSet (matrixGood β δ n) := by
  unfold matrixGood
  apply (measurableSet_le continuous_operator_norm.measurable measurable_const).inter
  apply MeasurableSet.inter
  · change MeasurableSet {g : Disorder n | ∀ i k, |coupling g i k| ≤ δ}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
      measurableSet_le (continuous_coupling i k).abs.measurable measurable_const
  · change MeasurableSet {g : Disorder n | ∀ i, ∑ k, coupling g i k ^ 2 ≤ β^2+δ}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const

lemma deleted_diagonal_norm_bound (r d R : ℝ) (hd : 0 ≤ d)
    (g : SKRatioGaussian.MatrixCoordinates (Fin n) → ℝ)
    (hR : ‖SKRatioGaussian.matrixOperator (SKRatioGaussian.goeMatrix r g)‖ ≤ R)
    (hdiag : ∀ i, |SKRatioGaussian.goeMatrix r g i i| ≤ d) :
    euclideanOpNorm (coupling (SKRatioGaussian.goeDisorder r g)) ≤ R+d := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (Matrix.of (SKRatioGaussian.coupling (SKRatioGaussian.goeDisorder r g)))‖ ≤ _
  rw [SKRatioGaussian.coupling_goeDisorder,map_sub]
  have hh : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (Matrix.diagonal (fun i => SKRatioGaussian.goeMatrix r g i i))‖ ≤ d := by
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact SKRatioGaussian.diagonal_norm_le hd _ hdiag
  exact (norm_sub_le _ _).trans (add_le_add hR hh)

lemma disorder_goe_hasLaw (β : ℝ) (n : ℕ) :
    HasLaw (SKRatioGaussian.goeDisorder (n := n) (β^2/(n:ℝ))) (disorderLaw β n)
      (SKRatioGaussian.gaussianCoordinates (SKRatioGaussian.MatrixCoordinates (Fin n))) :=
  SKRatioGaussian.goe_actual_disorder_hasLaw β n

lemma coupling_norm_tail {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hn : 0 < n) :
    (disorderLaw β n).real {g | 2*β+δ < euclideanOpNorm (coupling g)} ≤
      2*exp (-((δ/2)^2/(Real.pi^2*β^2))*(n:ℝ)) +
      2*(n:ℝ)*exp (-((δ/2)^2/(8*β^2))*(n:ℝ)) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hm : MeasurableSet {g : Disorder n | 2*β+δ < euclideanOpNorm (coupling g)} :=
    measurableSet_lt measurable_const continuous_operator_norm.measurable
  rw [←(disorder_goe_hasLaw β n).measureReal_eq hm]
  let r := β^2/(n:ℝ)
  let E₁ := {g : SKRatioGaussian.MatrixCoordinates (Fin n) → ℝ |
    2*β+δ/2 < ‖SKRatioGaussian.matrixOperator (SKRatioGaussian.goeMatrix r g)‖}
  let E₂ := {g : SKRatioGaussian.MatrixCoordinates (Fin n) → ℝ | ∃ i, δ/2 < |SKRatioGaussian.goeMatrix r g i i|}
  have hs : {g : SKRatioGaussian.MatrixCoordinates (Fin n) → ℝ |
      2*β+δ < euclideanOpNorm (coupling (SKRatioGaussian.goeDisorder r g))} ⊆ E₁ ∪ E₂ := by
    intro g hg
    by_contra hh
    have hh₁ : ¬g ∈ E₁ := fun h => hh (Or.inl h)
    have hh₂ : ¬g ∈ E₂ := fun h => hh (Or.inr h)
    have hb := deleted_diagonal_norm_bound r (δ/2) (2*β+δ/2) (by positivity) g
      (not_lt.mp hh₁) (fun i => not_lt.mp (fun hi => hh₂ ⟨i,hi⟩))
    change 2*β+δ < _ at hg
    linarith
  have h₁ : (SKRatioGaussian.gaussianCoordinates (SKRatioGaussian.MatrixCoordinates (Fin n))).real E₁ ≤
      2*exp (-((δ/2)^2/(Real.pi^2*β^2))*(n:ℝ)) := by
    have ht := SKRatioGaussian.goe_norm_tail (ι := Fin n) (sq_pos_of_pos hβ) (by positivity : 0 ≤ δ/2)
    simpa only [Fintype.card_fin,sqrt_sq hβ.le,show -(δ/2)^2*(n:ℝ)/(Real.pi^2*β^2) =
      -((δ/2)^2/(Real.pi^2*β^2))*(n:ℝ) by ring] using ht
  have h₂ : (SKRatioGaussian.gaussianCoordinates (SKRatioGaussian.MatrixCoordinates (Fin n))).real E₂ ≤
      2*(n:ℝ)*exp (-((δ/2)^2/(8*β^2))*(n:ℝ)) := by
    have ht := SKRatioGaussian.goe_diagonal_tail (ι := Fin n) (div_pos (sq_pos_of_pos hβ) hnr)
      (by positivity : 0 ≤ δ/2)
    have he : -(δ/2)^2/(8*(β^2/(n:ℝ))) = -((δ/2)^2/(8*β^2))*(n:ℝ) := by field_simp
    simpa only [Fintype.card_fin,he] using ht
  exact (measureReal_mono hs).trans ((measureReal_union_le E₁ E₂).trans (add_le_add h₁ h₂))

lemma coupling_entries_tail {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hn : 0 < n) :
    (disorderLaw β n).real {g | ∃ i k, δ < |coupling g i k|} ≤
      2*(n:ℝ)^2*exp (-(δ^2/(4*β^2))*(n:ℝ)) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hm : MeasurableSet {g : Disorder n | ∃ i k, δ < |coupling g i k|} :=
    by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k =>
        measurableSet_lt measurable_const (continuous_coupling i k).abs.measurable
  rw [←(disorder_goe_hasLaw β n).measureReal_eq hm]
  simp only [coupling_bridge]
  convert SKRatioGaussian.coupling_goe_max_entry_tail (n := n) (sq_pos_of_pos hβ) hδ using 1
  congr 2
  ring

lemma coupling_rows_tail {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hn : 0 < n) :
    (disorderLaw β n).real {g | ∃ i, β^2+δ < ∑ k, coupling g i k^2} ≤
      (n:ℝ)*exp (-(2*(sqrt (β^2+δ)-β)^2/(Real.pi^2*β^2))*(n:ℝ)) := by
  have hm : MeasurableSet {g : Disorder n | ∃ i, β^2+δ < ∑ k, coupling g i k^2} :=
    by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun i => measurableSet_lt measurable_const (by fun_prop)
  rw [←(disorder_goe_hasLaw β n).measureReal_eq hm]
  simpa only [coupling_bridge,sqrt_sq hβ.le] using SKRatioGaussian.coupling_goe_all_rows_tight_tail hn (sq_pos_of_pos hβ) hδ

lemma nat_pow_exp_neg_tendsto {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^k*exp (-a*(n:ℝ))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => a*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).div_const (a^k)
  simp only [zero_div] at h
  convert h using 1
  ext n
  simp only [Function.comp_apply,mul_pow,neg_mul]
  field_simp

lemma matrixGood_compl_bound {β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hn : 0 < n) :
    (disorderLaw β n).real (matrixGood β δ n)ᶜ ≤
      (2*exp (-((δ/2)^2/(Real.pi^2*β^2))*(n:ℝ)) +
       2*(n:ℝ)*exp (-((δ/2)^2/(8*β^2))*(n:ℝ))) +
      (2*(n:ℝ)^2*exp (-(δ^2/(4*β^2))*(n:ℝ)) +
       (n:ℝ)*exp (-(2*(sqrt (β^2+δ)-β)^2/(Real.pi^2*β^2))*(n:ℝ))) := by
  let E₁ := {g : Disorder n | 2*β+δ < euclideanOpNorm (coupling g)}
  let E₂ := {g : Disorder n | ∃ i k, δ < |coupling g i k|}
  let E₃ := {g : Disorder n | ∃ i, β^2+δ < ∑ k, coupling g i k^2}
  have he : (matrixGood β δ n)ᶜ = E₁ ∪ (E₂ ∪ E₃) := by
    ext g
    simp only [matrixGood,Set.mem_compl_iff,Set.mem_ofPred_eq,not_and_or,not_forall,not_le,
      Set.mem_union,E₁,E₂,E₃]
  rw [he]
  apply (measureReal_union_le E₁ (E₂ ∪ E₃)).trans
  apply add_le_add (coupling_norm_tail hβ hδ hn)
  exact (measureReal_union_le E₂ E₃).trans
    (add_le_add (coupling_entries_tail hβ hδ hn) (coupling_rows_tail hβ hδ hn))

theorem matrixGood_probability {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => disorderLaw β n (matrixGood β δ n)ᶜ) atTop (𝓝 0) := by
  rcases hβ.eq_or_lt with he | hpos
  · subst β
    have hz (n : ℕ) : disorderLaw 0 n (matrixGood 0 δ n)ᶜ = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [disorderLaw_zero_ae n] with g hg
      subst g
      simp only [Set.mem_compl_iff,not_not]
      unfold matrixGood
      have hc : coupling (0 : Disorder n) = 0 := by ext i k; simp [coupling]
      have he : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (0 : Interaction n) = 0 := by
        exact map_zero (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv
      simp [hc,euclideanOpNorm,he,hδ.le]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ≥0∞)) atTop (𝓝 0))
  apply (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _) ENNReal.zero_ne_top).mp
  have ha : 0 < (δ/2)^2/(Real.pi^2*β^2) := by positivity
  have hb : 0 < (δ/2)^2/(8*β^2) := by positivity
  have hc : 0 < δ^2/(4*β^2) := by positivity
  have hs : 0 < sqrt (β^2+δ)-β := by
    have := sqrt_lt_sqrt (sq_nonneg β) (show β^2 < β^2+δ by linarith)
    rw [sqrt_sq hpos.le] at this
    linarith
  have hd : 0 < 2*(sqrt (β^2+δ)-β)^2/(Real.pi^2*β^2) := by positivity
  have ht := ((nat_pow_exp_neg_tendsto ha 0).const_mul 2 |>.add
    ((nat_pow_exp_neg_tendsto hb 1).const_mul 2)).add
    (((nat_pow_exp_neg_tendsto hc 2).const_mul 2).add (nat_pow_exp_neg_tendsto hd 1))
  simp only [pow_zero,one_mul,pow_one,mul_zero,zero_add,←mul_assoc] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg))
    ?_ ht
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact matrixGood_compl_bound hpos hδ.le hn

theorem uniform_gap_high_probability {β : ℝ} (hβ : 0 ≤ β) (hβhalf : β < 1/2) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧
      Tendsto (fun n : ℕ => disorderLaw β n (matrixGood β δ n)ᶜ) atTop (𝓝 0) ∧
      ∀ n : ℕ, ∀ g ∈ matrixGood β δ n,
        ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ h : Fin n → ℝ,
          (∀ f, ρ*Fields.variance (s • g) h f ≤ Fields.dirichlet (s • g) h f) ∧
          (∀ a, Fields.variance (s • g) h (Fields.linearObservable a) ≤
              ρ⁻¹*(∑ i, a i^2)) := by
  obtain ⟨δ,ρ,hd,hr,hgap⟩ := Fields.exists_uniform_gap_tolerance hβ hβhalf
  exact ⟨δ,ρ,hd,hr,matrixGood_probability hβ hd,
    fun n g hg => hgap n g hg.1 hg.2.1 hg.2.2⟩

end SKRatio.Gaussian

end
end

end OAI
