import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal Topology Matrix

namespace Problem336.DenseBrownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {X : ℝ≥0 → Ω → ℝ}

def evaluationChar {ι : Type*} [Fintype ι] (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (a : ι → ℝ) (t : ι → ℝ≥0) : ℂ :=
  ∫ ω, Complex.exp ((((∑ i, a i * X (t i) ω) : ℝ) : ℂ) * Complex.I) ∂P

def brownianChar {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ι → ℝ≥0) : ℂ :=
  Complex.exp (-(((∑ i, ∑ j, a i * a j * min (t i : ℝ) (t j : ℝ)) : ℝ) : ℂ) / 2)

lemma continuous_evaluationChar [IsFiniteMeasure P] {ι : Type*} [Fintype ι]
    (hX : ∀ t, Measurable (X t)) (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (a : ι → ℝ) : Continuous (evaluationChar X P a) := by
  classical
  unfold evaluationChar
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t
    apply Measurable.aestronglyMeasurable
    fun_prop
  · intro t
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Complex.norm_exp_ofReal_mul_I])
  · exact integrable_const 1
  · filter_upwards [hc] with ω hω
    have hi (i : ι) : Continuous (fun t : ι → ℝ≥0 => a i * X (t i) ω) :=
      continuous_const.mul (hω.comp (continuous_apply i))
    fun_prop

lemma continuous_brownianChar {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Continuous (brownianChar a) := by
  unfold brownianChar
  fun_prop

theorem characteristic_of_dense [IsFiniteMeasure P] {D : Set ℝ≥0} (hD : Dense D)
    (hX : ∀ t, Measurable (X t)) (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (hd : ∀ t : ι → ℝ≥0, (∀ i, t i ∈ D) →
      evaluationChar X P a t = brownianChar a t) :
    ∀ t : ι → ℝ≥0, evaluationChar X P a t = brownianChar a t := by
  have hpi : Dense (Set.pi Set.univ (fun _ : ι => D)) :=
    dense_pi Set.univ (fun _ _ => hD)
  have heq := Continuous.ext_on hpi (continuous_evaluationChar hX hc a)
    (continuous_brownianChar a) (fun t ht => hd t (fun i => ht i (Set.mem_univ i)))
  exact fun t => congrFun heq t

lemma evaluationChar_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : κ → ℝ) (t : κ → ℝ≥0) :
    evaluationChar X P (a ∘ e) (t ∘ e) = evaluationChar X P a t := by
  unfold evaluationChar
  congr 1
  funext ω
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun i => a i * X (t i) ω)]

lemma brownianChar_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : κ → ℝ) (t : κ → ℝ≥0) :
    brownianChar (a ∘ e) (t ∘ e) = brownianChar a t := by
  unfold brownianChar
  simp only [Function.comp_apply]
  have hs : (∑ i : ι, ∑ j : ι,
      a (e i) * a (e j) * min (t (e i) : ℝ) (t (e j) : ℝ)) =
      ∑ i : κ, ∑ j : κ, a i * a j * min (t i : ℝ) (t j : ℝ) := by
    calc
      _ = ∑ i : ι, ∑ j : κ, a (e i) * a j * min (t (e i) : ℝ) (t j : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact e.sum_comp (fun j => a (e i) * a j * min (t (e i) : ℝ) (t j : ℝ))
      _ = _ := e.sum_comp (fun i => ∑ j : κ, a i * a j * min (t i : ℝ) (t j : ℝ))
  rw [hs]

def timeCovariance {ι : Type*} (t : ι → ℝ≥0) : Matrix ι ι ℝ :=
  Matrix.of (fun i j => min (t i : ℝ) (t j : ℝ))

lemma timeCovariance_posSemidef {ι : Type*} [Fintype ι] (t : ι → ℝ≥0) :
    (timeCovariance t).PosSemidef := by
  have heq : timeCovariance t = Matrix.of (fun i j =>
      volume.real ((Set.Icc 0 (t i : ℝ)) ∩ (Set.Icc 0 (t j : ℝ)))) := by
    ext i j
    simp [timeCovariance, Set.Icc_inter_Icc]
  rw [heq]
  exact posSemidef_matrix_measure_inter (fun _ => measurableSet_Icc)
    (fun _ => isCompact_Icc.measure_ne_top)

lemma characteristic_of_gaussian_hasLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ≥0) (a : ι → ℝ)
    (h : HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω))
      (multivariateGaussian 0 (timeCovariance t)) P) :
    evaluationChar X P a t = brownianChar a t := by
  classical
  have heq : evaluationChar X P a t =
      charFun (multivariateGaussian 0 (timeCovariance t)) (WithLp.toLp 2 a) := by
    have hi := h.integral_comp (f := fun x : EuclideanSpace ℝ ι =>
      Complex.exp ((inner (𝕜 := ℝ) x (WithLp.toLp 2 a) : ℂ) * Complex.I))
      (by fun_prop)
    simpa [evaluationChar, charFun_apply, Function.comp_def, PiLp.inner_apply] using hi
  rw [heq, charFun_multivariateGaussian (timeCovariance_posSemidef t)]
  unfold brownianChar
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    dotProduct, Matrix.mulVec, timeCovariance, Matrix.of_apply]
  simp_rw [Finset.mul_sum]
  have hs : (∑ i : ι, ∑ j : ι, a i * (min (t i : ℝ) (t j : ℝ) * a j)) =
      ∑ i : ι, ∑ j : ι, a i * a j * min (t i : ℝ) (t j : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem isPreBrownian_of_characteristic [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t))
    (hchar : ∀ (I : Finset ℝ≥0) (a : I → ℝ),
      evaluationChar X P a (fun i => i.val) = brownianChar a (fun i => i.val)) :
    IsPreBrownianReal X P := by
  classical
  refine ⟨fun I => ?_⟩
  have hm : Measurable (fun ω => I.restrict (X · ω)) := by
    exact Measurable.of_eval (fun i => hX i.val)
  refine ⟨hm.aemeasurable, ?_⟩
  apply (MeasurableEquiv.toLp 2 (I → ℝ)).map_measurableEquiv_injective
  rw [Measure.map_map (MeasurableEquiv.measurable _) hm]
  rw [MeasurableEquiv.coe_toLp]
  rw [(BrownianReal.measurePreserving_toLp_projectiveFamily I).map_eq]
  apply Measure.ext_of_charFun
  funext a
  rw [charFun_apply, integral_map]
  · rw [charFun_multivariateGaussian (BrownianReal.posSemidef_covMatrix I)]
    have hinner (ω : Ω) :
        inner (𝕜 := ℝ) (WithLp.toLp 2 (I.restrict (X · ω))) a =
          ∑ i : I, a i * X i.val ω := by
      simp [PiLp.inner_apply, Finset.restrict_def]
    simp_rw [Function.comp_apply, hinner]
    change evaluationChar X P (fun i => a i) (fun i => i.val) = _
    rw [hchar]
    unfold brownianChar
    congr 1
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    simp only [dotProduct, Matrix.mulVec, BrownianReal.covMatrix_apply]
    simp_rw [Finset.mul_sum]
    have hsum : (∑ i : I, ∑ j : I, a i * a j * min (i.val : ℝ) (j.val : ℝ)) =
        ∑ i : I, ∑ j : I, a i * ((min i.val j.val : ℝ≥0) * a j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [NNReal.coe_min]
      ring
    rw [hsum]
    ring
  · simpa only [MeasurableEquiv.coe_toLp] using
      ((MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp hm).aemeasurable
  · fun_prop

theorem isBrownian_of_dense_characteristic [IsProbabilityMeasure P]
    {D : Set ℝ≥0} (hD : Dense D) (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hchar : ∀ (I : Finset ℝ≥0) (a : I → ℝ) (t : I → ℝ≥0),
      (∀ i, t i ∈ D) → evaluationChar X P a t = brownianChar a t) :
    IsBrownianReal X P := by
  refine ⟨isPreBrownian_of_characteristic hX ?_, hc⟩
  intro I a
  exact characteristic_of_dense hD hX hc a (hchar I a) (fun i => i.val)

theorem isBrownian_of_dense_characteristic_fin [IsProbabilityMeasure P]
    {D : Set ℝ≥0} (hD : Dense D) (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hchar : ∀ (n : ℕ) (a : Fin n → ℝ) (t : Fin n → ℝ≥0),
      (∀ i, t i ∈ D) → evaluationChar X P a t = brownianChar a t) :
    IsBrownianReal X P := by
  apply isBrownian_of_dense_characteristic hD hX hc
  intro I a t ht
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have h := hchar (Fintype.card I) (a ∘ e) (t ∘ e) (fun i => ht (e i))
  rwa [evaluationChar_reindex e a t, brownianChar_reindex e a t] at h

def dyadicTimes : Set ℝ≥0 :=
  {t | ∃ n k : ℕ, t = (k : ℝ≥0) / (2 : ℝ≥0) ^ n}

lemma dense_dyadicTimes : Dense dyadicTimes := by
  intro t
  let q : ℕ → ℝ≥0 := fun n =>
    (⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊ : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hq : Filter.Tendsto q Filter.atTop (nhds t) := by
    apply NNReal.tendsto_coe.mp
    have h := (tendsto_nat_floor_mul_div_atTop t.property).comp
      (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))
    convert h using 1 <;> simp [q, Function.comp_def]
  apply mem_closure_of_tendsto hq
  exact Filter.Eventually.of_forall (fun n => ⟨n, ⌊(t : ℝ) * (2 : ℝ) ^ n⌋₊, rfl⟩)

theorem isBrownian_of_dyadic_characteristic_fin [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t)) (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hchar : ∀ (n : ℕ) (a : Fin n → ℝ) (t : Fin n → ℝ≥0),
      (∀ i, t i ∈ dyadicTimes) → evaluationChar X P a t = brownianChar a t) :
    IsBrownianReal X P :=
  isBrownian_of_dense_characteristic_fin dense_dyadicTimes hX hc hchar

theorem isBrownian_of_dyadic_gaussian_fin [IsProbabilityMeasure P]
    (hX : ∀ t, Measurable (X t)) (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hlaw : ∀ (n : ℕ) (t : Fin n → ℝ≥0), (∀ i, t i ∈ dyadicTimes) →
      HasLaw (fun ω => WithLp.toLp 2 (fun i => X (t i) ω))
        (multivariateGaussian 0 (timeCovariance t)) P) :
    IsBrownianReal X P := by
  apply isBrownian_of_dyadic_characteristic_fin hX hc
  intro n a t ht
  exact characteristic_of_gaussian_hasLaw t a (hlaw n t ht)

end Problem336.DenseBrownian

end

end OAI
