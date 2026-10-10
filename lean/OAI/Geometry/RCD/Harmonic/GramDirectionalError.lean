import OAI.Geometry.RCD.Harmonic.MeanGramControl

namespace OAI

/-! # From coordinatewise Gram errors to every constant direction -/

open Set MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

private theorem gamma_sum_left {ι : Type*} (s : Finset ι)
    (u : ι → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) :
    localGamma μ hQ (∑ i ∈ s, u i) g =ᵐ[μ]
      fun x => ∑ i ∈ s, localGamma μ hQ (u i) g x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, zero_smul, zero_mul] using
      localGamma_smul_left μ hQ 0 (0 : SobolevSpace μ hQ) g
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [localGamma_add_left μ hQ (u a) (∑ i ∈ s, u i) g, ih] with x hx hi
    exact hx.trans (congrArg (fun r => localGamma μ hQ (u a) g x + r) hi)

private theorem gamma_sum_right {ι : Type*} (s : Finset ι)
    (u : ι → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) :
    localGamma μ hQ g (∑ i ∈ s, u i) =ᵐ[μ]
      fun x => ∑ i ∈ s, localGamma μ hQ g (u i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, zero_smul, zero_mul] using
      localGamma_smul_right μ hQ 0 g (0 : SobolevSpace μ hQ)
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [localGamma_add_right μ hQ g (u a) (∑ i ∈ s, u i), ih] with x hx hi
    exact hx.trans (congrArg (fun r => localGamma μ hQ g (u a) x + r) hi)

/-- Finite coordinate expansion of the actual local carré du champ. -/
theorem localGamma_column_pair {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (v w : Euclidean n) :
    localGamma μ hQ (sobolevColumnMap μ hQ u v) (sobolevColumnMap μ hQ u w) =ᵐ[μ]
      fun x => ∑ i : Fin n, ∑ j : Fin n, (v i * w j) * localGamma μ hQ (u i) (u j) x := by
  classical
  have hleft := gamma_sum_left μ hQ Finset.univ (fun i => v i • u i) (∑ j, w j • u j)
  have hright (i : Fin n) :=
    gamma_sum_right μ hQ Finset.univ (fun j => w j • u j) (v i • u i)
  have hscalar (i j : Fin n) :
      localGamma μ hQ (v i • u i) (w j • u j) =ᵐ[μ]
        fun x => (v i * w j) * localGamma μ hQ (u i) (u j) x := by
    filter_upwards [localGamma_smul_left μ hQ (v i) (u i) (w j • u j),
      localGamma_smul_right μ hQ (w j) (u i) (u j)] with x hx hy
    rw [hx, hy]
    ring
  have hr : ∀ᵐ x ∂μ, ∀ i : Fin n,
      localGamma μ hQ (v i • u i) (∑ j, w j • u j) x =
        ∑ j, localGamma μ hQ (v i • u i) (w j • u j) x := by
    simpa only [Finset.mem_univ, forall_true_left] using
      (Filter.eventually_all_finset Finset.univ).mpr (fun i _ => hright i)
  have hs : ∀ᵐ x ∂μ, ∀ i j : Fin n,
      localGamma μ hQ (v i • u i) (w j • u j) x =
        (v i * w j) * localGamma μ hQ (u i) (u j) x := by
    suffices hh : ∀ᵐ x ∂μ, ∀ i ∈ (Finset.univ : Finset (Fin n)),
        ∀ j ∈ (Finset.univ : Finset (Fin n)),
          localGamma μ hQ (v i • u i) (w j • u j) x =
            (v i * w j) * localGamma μ hQ (u i) (u j) x by
      simpa only [Finset.mem_univ, forall_true_left] using hh
    apply (Filter.eventually_all_finset Finset.univ).mpr
    intro i _
    apply (Filter.eventually_all_finset Finset.univ).mpr
    intro j _
    exact hscalar i j
  simp only [sobolevColumnMap_apply]
  filter_upwards [hleft, hr, hs] with x hl hr hs
  rw [hl]
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i]
  exact Finset.sum_congr rfl (fun j _ => hs i j)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
private theorem integral_abs_sum_le {ι : Type*} (s : Finset ι) (F : ι → X → ℝ)
    (hF : ∀ i ∈ s, Integrable (F i) μ) :
    (∫ x, |∑ i ∈ s, F i x| ∂μ) ≤ ∑ i ∈ s, ∫ x, |F i x| ∂μ := by
  have hh := integral_mono_ae (integrable_finsetSum s hF).abs
    (integrable_finsetSum s (fun i hi => (hF i hi).abs))
    (Filter.Eventually.of_forall fun x => Finset.abs_sum_le_sum_abs _ _)
  rw [integral_finsetSum s (fun i hi => (hF i hi).abs)] at hh
  exact hh

/-- Coordinatewise L1 Gram errors control the error in every constant
direction, with one dimension-dependent factor and the squared norm of
the direction. This supplies the directional premise of the mass estimate. -/
theorem directional_gram_error_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (S : Set X) (hSfin : μ S ≠ ∞) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (herror : ∀ i j : Fin n, ∫ x in S,
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ epsilon)
    (v : Euclidean n) :
    (∫ x in S, |localGamma μ hQ (sobolevColumnMap μ hQ u v)
      (sobolevColumnMap μ hQ u v) x - ‖v‖ ^ 2| ∂μ) ≤
      (n : ℝ) ^ 2 * epsilon * ‖v‖ ^ 2 := by
  classical
  let : IsFiniteMeasure (μ.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hSfin.lt_top⟩
  let F := fun (i j : Fin n) (x : X) => (v i * v j) *
    (localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0))
  have hF (i j : Fin n) : IntegrableOn (F i j) S μ :=
    ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub
      (integrable_const _)).const_mul _
  have hdiag : (∑ i : Fin n, ∑ j : Fin n,
      (v i * v j) * (if i = j then (1 : ℝ) else 0)) = ‖v‖ ^ 2 := by
    calc
      _ = ∑ i : Fin n, (v i) ^ 2 := by simp [mul_ite, pow_two]
      _ = _ := (EuclideanSpace.real_norm_sq_eq v).symm
  have hpoint : (fun x => localGamma μ hQ (sobolevColumnMap μ hQ u v)
      (sobolevColumnMap μ hQ u v) x - ‖v‖ ^ 2) =ᵐ[μ]
      fun x => ∑ i : Fin n, ∑ j : Fin n, F i j x := by
    filter_upwards [localGamma_column_pair μ hQ u v v] with x hx
    dsimp only [F]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hx, hdiag]
  have hterm (i j : Fin n) : (∫ x in S, |F i j x| ∂μ) ≤ epsilon * ‖v‖ ^ 2 := by
    have hi : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    have hj : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v j
    have hc : |v i * v j| ≤ ‖v‖ ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
    calc
      _ = |v i * v j| * ∫ x in S,
          |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ := by
        simp only [F, abs_mul, integral_const_mul]
      _ ≤ |v i * v j| * epsilon := mul_le_mul_of_nonneg_left (herror i j) (abs_nonneg _)
      _ ≤ _ := by nlinarith
  calc
    _ = ∫ x in S, |∑ i : Fin n, ∑ j : Fin n, F i j x| ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hpoint] with x hx
      rw [hx]
    _ ≤ ∑ i : Fin n, ∫ x in S, |∑ j : Fin n, F i j x| ∂μ :=
      integral_abs_sum_le (μ.restrict S) Finset.univ _
        (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hF i j))
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∫ x in S, |F i j x| ∂μ :=
      Finset.sum_le_sum fun i _ => integral_abs_sum_le (μ.restrict S) Finset.univ _
        (fun j _ => hF i j)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, epsilon * ‖v‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp; ring

end RegularPointCoordinates

end

end OAI
