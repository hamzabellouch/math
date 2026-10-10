import OAI.Probability.FreeIsing.Estimates.InfiniteBlockIndependence
import OAI.Probability.FreeIsing.Gaussian.Attenuation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem367.GaussianAttenuation

def pathTail (i : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun j => x (i + 1 + j)

def pathProduct (θ : ℝ) (n : ℕ) (shift : ℕ → (ℕ → ℝ) → ℝ)
    (x : ℕ → ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, responseAttenuation θ (x i + shift i (pathTail i x)) ^ 2

@[fun_prop] lemma measurable_pathTail (i : ℕ) : Measurable (pathTail i) := by
  exact Measurable.of_eval (fun index => measurable_pi_apply _)

lemma measurable_pathProduct (θ : ℝ) (n : ℕ)
    {shift : ℕ → (ℕ → ℝ) → ℝ} (hs : ∀ i, Measurable (shift i)) :
    Measurable (pathProduct θ n shift) := by
  unfold pathProduct
  apply Finset.measurable_fun_prod
  intro i hi
  have h := (measurable_pi_apply i).add ((hs i).comp (measurable_pathTail i))
  simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
  fun_prop

lemma pathProduct_nonneg (θ : ℝ) (n : ℕ) (shift : ℕ → (ℕ → ℝ) → ℝ)
    (x : ℕ → ℝ) : 0 ≤ pathProduct θ n shift x := by
  exact Finset.prod_nonneg (fun i _ => sq_nonneg _)

lemma pathProduct_le_one {θ : ℝ} (hθ : θ ^ 2 ≤ 1) (n : ℕ)
    (shift : ℕ → (ℕ → ℝ) → ℝ) (x : ℕ → ℝ) : pathProduct θ n shift x ≤ 1 := by
  exact Finset.prod_le_one₀ (fun index _ => sq_nonneg _)
    (fun i _ => attenuation_sq_le_one hθ _)

lemma integrable_pathProduct_comp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) {θ : ℝ} (hθ : θ ^ 2 ≤ 1) (n : ℕ)
    {shift : ℕ → (ℕ → ℝ) → ℝ} (hs : ∀ i, Measurable (shift i)) :
    Integrable (fun ω => pathProduct θ n shift (fun i => X i ω)) P := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_pathProduct θ n hs).comp (Measurable.of_eval hX)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (pathProduct_nonneg _ _ _ _)]
    exact pathProduct_le_one hθ _ _ _

lemma pathProduct_succ (θ : ℝ) (n : ℕ) (shift : ℕ → (ℕ → ℝ) → ℝ)
    (x : ℕ → ℝ) :
    pathProduct θ (n + 1) shift x =
      responseAttenuation θ (x 0 + shift 0 (pathTail 0 x)) ^ 2 *
        pathProduct θ n (fun i => shift (i + 1)) (pathTail 0 x) := by
  unfold pathProduct
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hh : pathTail 0 x i = x (i + 1) := by
    simp only [pathTail, Nat.zero_add, Nat.add_comm]
  have ht : pathTail i (pathTail 0 x) = pathTail (i + 1) x := by
    funext j
    simp only [pathTail]
    congr 1
    omega
  rw [hh, ht]

lemma head_indep_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) :
    IndepFun (X 0) (fun ω j => X (j + 1) ω) P := by
  have h := indepFun_of_disjoint_blocks hind hX ({0} : Set ℕ) (Set.Ioi 0)
    (by simp : Disjoint ({0} : Set ℕ) (Set.Ioi 0))
    (fun y => y ⟨0, by simp⟩)
    (fun y : Set.Ioi (0 : ℕ) → ℝ => fun j => y ⟨j + 1, show 0 < j + 1 from Nat.succ_pos j⟩)
    (measurable_pi_apply _) (by fun_prop)
  exact h

theorem integral_pathProduct_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    {m : ℕ → ℝ} {v : ℕ → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    {θ : ℝ} (hθ : θ ^ 2 < 1) {δ : ℝ≥0} (hδ : 0 < δ)
    (hv : ∀ i, δ ≤ v i) (n : ℕ)
    {shift : ℕ → (ℕ → ℝ) → ℝ} (hs : ∀ i, Measurable (shift i)) :
    (∫ ω, pathProduct θ n shift (fun i => X i ω) ∂P) ≤
      (1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2) ^ n := by
  let q := 1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2
  have hq : 0 ≤ q := by
    have ht := Real.tanh_sq_lt_one (gaussianSmallRadius δ)
    have hp := mul_nonneg (sq_nonneg θ) (sq_nonneg (Real.tanh (gaussianSmallRadius δ)))
    dsimp [q]
    nlinarith
  change (∫ ω, pathProduct θ n shift (fun i => X i ω) ∂P) ≤ q ^ n
  induction n generalizing X m v shift with
  | zero => simp [pathProduct]
  | succ n ih =>
      have hi := ih (fun i => hX (i + 1)) (hind.precomp (g := fun i : ℕ => i + 1) (by intro i j hij; exact Nat.add_right_cancel hij))
        (fun i => hlaw (i + 1)) (fun i => hv (i + 1)) (fun i => hs (i + 1))
      have he := integral_shifted_attenuation_sq_mul_le_of_indepFun (hlaw 0)
        (show AEMeasurable (fun ω j => X (j + 1) ω) P from
          (Measurable.of_eval (fun index => hX (index + 1))).aemeasurable)
        (head_indep_tail hX hind) (hs 0)
        (measurable_pathProduct θ n (fun i => hs (i + 1)))
        (integrable_pathProduct_comp (fun i => hX (i + 1)) hθ.le n (fun i => hs (i + 1)))
        (pathProduct_nonneg θ n (fun i => shift (i + 1))) hθ hδ (hv 0)
      calc
        (∫ ω, pathProduct θ (n + 1) shift (fun i => X i ω) ∂P) =
            ∫ ω, responseAttenuation θ (X 0 ω + shift 0 (fun j => X (j + 1) ω)) ^ 2 *
              pathProduct θ n (fun i => shift (i + 1)) (fun j => X (j + 1) ω) ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            have hz : pathTail 0 (fun i => X i ω) = (fun j => X (j + 1) ω) := by
              funext j
              simp only [pathTail, Nat.zero_add, Nat.add_comm]
            simpa only [hz] using pathProduct_succ θ n shift (fun i => X i ω)
        _ ≤ q * ∫ ω, pathProduct θ n (fun i => shift (i + 1))
            (fun j => X (j + 1) ω) ∂P := he
        _ ≤ q * q ^ n := mul_le_mul_of_nonneg_left hi hq
        _ = q ^ (n + 1) := (pow_succ' q n).symm

lemma measurable_pathProduct_parameter {Y : Type*} [MeasurableSpace Y]
    (θ : ℝ) (n : ℕ) {shift : Y → ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ i, Measurable (fun p : Y × (ℕ → ℝ) => shift p.1 i p.2)) :
    Measurable (fun p : Y × (ℕ → ℝ) => pathProduct θ n (shift p.1) p.2) := by
  unfold pathProduct
  apply Finset.measurable_fun_prod
  intro i hi
  have ha : Measurable (fun z : ℝ => responseAttenuation θ z ^ 2) := by
    simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
    fun_prop
  exact ha.comp (((measurable_pi_apply i).comp measurable_snd).add
    ((hs i).comp (measurable_fst.prodMk ((measurable_pathTail i).comp measurable_snd))))

theorem integral_pathProduct_parameter_le
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    {m : ℕ → ℝ} {v : ℕ → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    {θ : ℝ} (hθ : θ ^ 2 < 1) {δ : ℝ≥0} (hδ : 0 < δ)
    (hv : ∀ i, δ ≤ v i) (n : ℕ)
    {shift : Y → ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ i, Measurable (fun p : Y × (ℕ → ℝ) => shift p.1 i p.2)) :
    (∫ p : Y × Ω, pathProduct θ n (shift p.1) (fun i => X i p.2) ∂ν.prod P) ≤
      (1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2) ^ n := by
  let F : Y × Ω → ℝ := fun p => pathProduct θ n (shift p.1) (fun i => X i p.2)
  have hFm : Measurable F := by
    dsimp only [F, pathProduct]
    apply Finset.measurable_fun_prod
    intro i hi
    have ha : Measurable (fun z : ℝ => responseAttenuation θ z ^ 2) := by
      simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
      fun_prop
    have hg : Measurable (fun p : Y × Ω => (p.1, pathTail i (fun j => X j p.2))) := by
      apply Measurable.prodMk measurable_fst
      apply Measurable.of_eval
      intro j
      exact (hX (i + 1 + j)).comp measurable_snd
    exact ha.comp (((hX i).comp measurable_snd).add ((hs i).comp hg))
  have hFi : Integrable F (ν.prod P) := by
    apply (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖pathProduct θ n (shift p.1) (fun i => X i p.2)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (pathProduct_nonneg _ _ _ _)]
      exact pathProduct_le_one hθ.le _ _ _
  let q := 1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2
  change (∫ p, F p ∂ν.prod P) ≤ q ^ n
  rw [integral_prod F hFi]
  calc
    (∫ y, ∫ ω, F (y, ω) ∂P ∂ν) ≤ ∫ _y, q ^ n ∂ν := by
      apply integral_mono hFi.integral_prod_left (integrable_const _)
      intro y
      have hsy (i : ℕ) : Measurable (shift y i) := by
        exact (hs i).comp (show Measurable (fun x : ℕ → ℝ => (y, x)) from
          measurable_const.prodMk measurable_id)
      change (∫ ω, pathProduct θ n (shift y) (fun i => X i ω) ∂P) ≤ q ^ n
      exact integral_pathProduct_le (X := X) (m := m) (v := v) hX hind hlaw hθ hδ hv n
        (shift := shift y) hsy
    _ = q ^ n := by simp

theorem exists_uniform_path_attenuation_gap
    {θ : ℝ} (hθ : θ ^ 2 < 1) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
      ∀ (n : ℕ) (m : ℕ → ℝ) (v : ℕ → ℝ≥0), (∀ i, δ ≤ v i) →
        ∀ (shift : ℕ → (ℕ → ℝ) → ℝ), (∀ i, Measurable (shift i)) →
          (∫ x, pathProduct θ n shift x
            ∂Measure.infinitePi (fun i => gaussianReal (m i) (v i))) ≤ (1 - κ) ^ n := by
  let κ := ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2
  have ht : 0 < Real.tanh (gaussianSmallRadius δ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (gaussianSmallRadius_pos hδ)) (Real.cosh_pos _)
  refine ⟨κ, by dsimp [κ]; positivity, ?_, ?_⟩
  · have hp := mul_nonneg (sq_nonneg θ) (sq_nonneg (Real.tanh (gaussianSmallRadius δ)))
    have hlt := Real.tanh_sq_lt_one (gaussianSmallRadius δ)
    dsimp [κ]
    nlinarith
  · intro n m v hv shift hs
    apply integral_pathProduct_le (m := m) (v := v) (fun i => measurable_pi_apply i)
      (iIndepFun_infinitePi (fun _ => measurable_id)) _ hθ hδ hv n hs
    intro i
    exact ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

theorem integral_pathProduct_environment_le
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Z : Ω → Y}
    (hX : ∀ i, Measurable (X i)) (hZ : Measurable Z) (hind : iIndepFun X P)
    (henv : IndepFun Z (fun ω i => X i ω) P)
    {m : ℕ → ℝ} {v : ℕ → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    {θ : ℝ} (hθ : θ ^ 2 < 1) {δ : ℝ≥0} (hδ : 0 < δ)
    (hv : ∀ i, δ ≤ v i) (n : ℕ)
    {shift : Y → ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ i, Measurable (fun p : Y × (ℕ → ℝ) => shift p.1 i p.2)) :
    (∫ ω, pathProduct θ n (shift (Z ω)) (fun i => X i ω) ∂P) ≤
      (1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2) ^ n := by
  let μ := Measure.infinitePi (fun i => gaussianReal (m i) (v i))
  have hXm : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
  have harray : HasLaw (fun ω i => X i ω) μ P :=
    hind.hasLaw_infinitePi hlaw hXm.aemeasurable
  have hpair : HasLaw (fun ω => (Z ω, fun i => X i ω)) ((P.map Z).prod μ) P := by
    refine ⟨(hZ.prodMk hXm).aemeasurable, ?_⟩
    rw [henv.map_prod_eq_prod_map_map hZ.aemeasurable hXm.aemeasurable, harray.map_eq]
  have heval (i : ℕ) : HasLaw (fun x : ℕ → ℝ => x i) (gaussianReal (m i) (v i)) μ :=
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hb := integral_pathProduct_parameter_le (P := μ) (P.map Z)
    (fun i => measurable_pi_apply i) (iIndepFun_infinitePi (fun _ => measurable_id))
    heval hθ hδ hv n (shift := shift) hs
  calc
    (∫ ω, pathProduct θ n (shift (Z ω)) (fun i => X i ω) ∂P) =
        ∫ p : Y × (ℕ → ℝ), pathProduct θ n (shift p.1) p.2 ∂(P.map Z).prod μ :=
      hpair.integral_comp (measurable_pathProduct_parameter θ n hs).aestronglyMeasurable
    _ ≤ _ := hb

def pathResponse (θ : ℝ) (n : ℕ) (shift : ℕ → (ℕ → ℝ) → ℝ)
    (x : ℕ → ℝ) : ℝ :=
  θ ^ n * ∏ i ∈ Finset.range n, responseAttenuation θ (x i + shift i (pathTail i x))

lemma pathResponse_sq (θ : ℝ) (n : ℕ) (shift : ℕ → (ℕ → ℝ) → ℝ)
    (x : ℕ → ℝ) : pathResponse θ n shift x ^ 2 = (θ ^ 2) ^ n * pathProduct θ n shift x := by
  simp only [pathResponse, pathProduct, mul_pow, Finset.prod_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]

theorem integral_pathResponse_sq_environment_le
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Z : Ω → Y}
    (hX : ∀ i, Measurable (X i)) (hZ : Measurable Z) (hind : iIndepFun X P)
    (henv : IndepFun Z (fun ω i => X i ω) P)
    {m : ℕ → ℝ} {v : ℕ → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    {θ : ℝ} (hθ : θ ^ 2 < 1) {δ : ℝ≥0} (hδ : 0 < δ)
    (hv : ∀ i, δ ≤ v i) (n : ℕ)
    {shift : Y → ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ i, Measurable (fun p : Y × (ℕ → ℝ) => shift p.1 i p.2)) :
    (∫ ω, pathResponse θ n (shift (Z ω)) (fun i => X i ω) ^ 2 ∂P) ≤
      (θ ^ 2 * (1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2)) ^ n := by
  simp_rw [pathResponse_sq]
  rw [integral_const_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left
    (integral_pathProduct_environment_le (X := X) (Z := Z) hX hZ hind henv hlaw hθ hδ hv n hs)
    (pow_nonneg (sq_nonneg θ) n)

lemma integrable_pathResponse_sq_environment
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {Z : Ω → Y}
    (hX : ∀ i, Measurable (X i)) (hZ : Measurable Z)
    {θ : ℝ} (hθ : θ ^ 2 ≤ 1) (n : ℕ)
    {shift : Y → ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ i, Measurable (fun p : Y × (ℕ → ℝ) => shift p.1 i p.2)) :
    Integrable (fun ω => pathResponse θ n (shift (Z ω)) (fun i => X i ω) ^ 2) P := by
  simp_rw [pathResponse_sq]
  apply Integrable.const_mul
  have hm : Measurable (fun ω => pathProduct θ n (shift (Z ω)) (fun i => X i ω)) := by
    unfold pathProduct
    apply Finset.measurable_fun_prod
    intro i hi
    have ha : Measurable (fun z : ℝ => responseAttenuation θ z ^ 2) := by
      simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
      fun_prop
    have hg : Measurable (fun ω => (Z ω, pathTail i (fun j => X j ω))) := by
      apply Measurable.prodMk hZ
      exact Measurable.of_eval (fun index => hX (i + 1 + index))
    exact ha.comp ((hX i).add ((hs i).comp hg))
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pathProduct_nonneg _ _ _ _)]
    exact pathProduct_le_one hθ _ _ _

end Problem367.GaussianAttenuation

end

end OAI
