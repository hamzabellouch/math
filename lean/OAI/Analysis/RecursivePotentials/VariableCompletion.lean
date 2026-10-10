import OAI.Analysis.RecursivePotentials.VariableEstimates

namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

namespace VariableTree

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma P_eq_zero_off_head (v : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hv : v.support ⊆ H) {s : ι} (hs : s ∉ H) : P T e v s = 0 := by
  apply extend_not_mem
  exact fun hh => hs (T.ancestorClosure_subset_of_initial hH hv hh)

lemma Q_eq_zero_off_head (v : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hv : v.support ⊆ H) {s : ι} (hs : s ∉ H) : Q T e v s = 0 := by
  apply extend_not_mem
  exact fun hh => hs (T.ancestorClosure_subset_of_initial hH hv hh)

lemma potentials_le_normSum (v : ι →₀ ℝ) (s : ι) :
    P T e v s ≤ normSum T e v ∧ Q T e v s ≤ normSum T e v := by
  have hp := (P_upper T e v).le_root T e (P_nonneg T e v) s
  have hq := (Q_upper T e v).le_root T e (Q_nonneg T e v) s
  have hp0 := P_nonneg T e v T.root
  have hq0 := Q_nonneg T e v T.root
  unfold normSum
  constructor <;> linarith

lemma potentials_lipschitz (v w : ι →₀ ℝ) (s : ι) :
    |P T e v s - P T e w s| ≤ normSum T e (v - w) ∧
    |Q T e v s - Q T e w s| ≤ normSum T e (v - w) := by
  have h₁ := potentials_add_le T e (v - w) w s
  have h₂ := potentials_add_le T e (w - v) v s
  rw [sub_add_cancel] at h₁ h₂
  have hk₁ := potentials_le_normSum T e (v - w) s
  have hk₂ := potentials_le_normSum T e (w - v) s
  have hn : normSum T e (w - v) = normSum T e (v - w) := by
    rw [← neg_sub v w, normSum_neg T e]
  rw [hn] at hk₂
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, hk₁.1, hk₁.2, hk₂.1, hk₂.2]

def projectHead (_T : FiniteRootedTree ι) (H : Finset ι) (v : ι →₀ ℝ) : ι →₀ ℝ := v.filter (· ∈ H)

lemma projectHead_apply (H : Finset ι) (v : ι →₀ ℝ) (s : ι) :
    projectHead T H v s = if s ∈ H then v s else 0 := Finsupp.filter_apply _ _ _

lemma projectHead_bound (H : Finset ι) (hH : T.Initial H) (v : ι →₀ ℝ) :
    normSum T e (projectHead T H v) ≤ normSum T e v := by
  let p := extend H (fun s => P T e v s.1)
  let q := extend H (fun s => Q T e v s.1)
  have hdiff : ∀ s, p s - q s = projectHead T H v s := by
    intro s
    rw [projectHead_apply T]
    by_cases hs : s ∈ H
    · simp only [p, q, extend_mem _ _ hs, ite_eq_left hs, P_sub_Q T e]
    · simp only [p, q, extend_not_mem _ _ hs, ite_eq_right hs, sub_zero]
  have h := potentials_minimal T e _ p q
    (extend_nonneg _ _ (fun s => P_nonneg T e v s.1))
    (extend_nonneg _ _ (fun s => Q_nonneg T e v s.1)) hdiff
    (extend_upper T e H hH _ ((P_upper T e v).restrict T e H hH))
    (extend_upper T e H hH _ ((Q_upper T e v).restrict T e H hH)) T.root
  simp only [p, q, extend_mem _ _ hH.1] at h
  unfold normSum
  exact add_le_add h.1 h.2

end VariableTree

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma norm_def (v : AggregationVector T e) : ‖v‖ = VariableTree.normSum T e v := rfl

@[simp] lemma coordinate_apply (s : ι) (v : AggregationVector T e) : coordinate T e s v = v s := rfl

lemma lipschitz_P (s : ι) :
    LipschitzWith 1 (fun v : AggregationVector T e => VariableTree.P T e v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (VariableTree.potentials_lipschitz T e v w s).1

lemma lipschitz_Q (s : ι) :
    LipschitzWith 1 (fun v : AggregationVector T e => VariableTree.Q T e v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (VariableTree.potentials_lipschitz T e v w s).2

def projectionLinear (H : Finset ι) : AggregationVector T e →ₗ[ℝ] AggregationVector T e where
  toFun := VariableTree.projectHead T H
  map_add' v w := by
    change ι →₀ ℝ at v w
    apply Finsupp.ext
    intro s
    change VariableTree.projectHead T H (v + w) s = (VariableTree.projectHead T H v + VariableTree.projectHead T H w) s
    by_cases hs : s ∈ H <;> simp [VariableTree.projectHead, hs]
  map_smul' a v := by
    change ι →₀ ℝ at v
    apply Finsupp.ext
    intro s
    change VariableTree.projectHead T H (a • v) s = (a • VariableTree.projectHead T H v) s
    by_cases hs : s ∈ H <;> simp [VariableTree.projectHead, hs]

noncomputable def projection (H : Finset ι) (hH : T.Initial H) :
    AggregationVector T e →L[ℝ] AggregationVector T e :=
  (projectionLinear T e H).mkContinuous 1 (fun v => by
    change VariableTree.normSum T e (VariableTree.projectHead T H v) ≤ 1 * VariableTree.normSum T e v
    rw [one_mul]
    exact VariableTree.projectHead_bound T e H hH v)

@[simp] lemma projection_apply (H : Finset ι) (hH : T.Initial H) (v : AggregationVector T e) :
    projection T e H hH v = VariableTree.projectHead T H v := rfl

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (v : AggregationVector T e) :
    ‖projection T e H hH v‖ ≤ ‖v‖ := VariableTree.projectHead_bound T e H hH v

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (v : AggregationVector T e) :
    projection T e H hH (projection T e H hH v) = projection T e H hH v := by
  change ι →₀ ℝ at v
  apply Finsupp.ext
  intro s
  change VariableTree.projectHead T H (VariableTree.projectHead T H v) s = VariableTree.projectHead T H v s
  simp [VariableTree.projectHead, Finsupp.filter_apply]
  intro hs hs'
  exact (hs hs').elim

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

@[simp] lemma coordinate_coe (s : ι) (v : AggregationVector T e) :
    coordinate T e s (v : AggregationSpace T e) = v s := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _ v

@[simp] lemma P_coe (s : ι) (v : AggregationVector T e) :
    P T e s (v : AggregationSpace T e) = VariableTree.P T e v s :=
  Completion.extension_coe (AggregationVector.lipschitz_P T e s).uniformContinuous v

@[simp] lemma Q_coe (s : ι) (v : AggregationVector T e) :
    Q T e s (v : AggregationSpace T e) = VariableTree.Q T e v s :=
  Completion.extension_coe (AggregationVector.lipschitz_Q T e s).uniformContinuous v

@[continuity, fun_prop] lemma continuous_P (s : ι) : Continuous (P T e s) :=
  Completion.continuous_extension

@[continuity, fun_prop] lemma continuous_Q (s : ι) : Continuous (Q T e s) :=
  Completion.continuous_extension

lemma P_nonneg (s : ι) (x : AggregationSpace T e) : 0 ≤ P T e s x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (continuous_P T e s)
  | ih v => simpa using VariableTree.P_nonneg T e v s

lemma Q_nonneg (s : ι) (x : AggregationSpace T e) : 0 ≤ Q T e s x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (continuous_Q T e s)
  | ih v => simpa using VariableTree.Q_nonneg T e v s

lemma P_sub_Q (s : ι) (x : AggregationSpace T e) : P T e s x - Q T e s x = coordinate T e s x := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq ((continuous_P T e s).sub (continuous_Q T e s))
        (coordinate T e s).continuous
  | ih v => simpa using VariableTree.P_sub_Q T e v s

theorem norm_eq (x : AggregationSpace T e) : ‖x‖ = P T e T.root x + Q T e T.root x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq continuous_norm ((continuous_P T e T.root).add (continuous_Q T e T.root))
  | ih v => simp [AggregationVector.norm_def, VariableTree.normSum]

lemma abs_coordinate_le (s : ι) (x : AggregationSpace T e) : |coordinate T e s x| ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (continuous_abs.comp (coordinate T e s).continuous) continuous_norm
  | ih v => simpa only [coordinate_coe, Completion.norm_coe, AggregationVector.norm_def] using
      VariableTree.abs_coordinate_le_normSum T e v s

lemma fields_lipschitz (s : ι) (x y : AggregationSpace T e) :
    |P T e s x - P T e s y| ≤ ‖x - y‖ ∧ |Q T e s x - Q T e s y| ≤ ‖x - y‖ := by
  induction x, y using Completion.induction_on₂ with
  | hp =>
      have hp : IsClosed {p : AggregationSpace T e × AggregationSpace T e |
          |P T e s p.1 - P T e s p.2| ≤ ‖p.1 - p.2‖} :=
        isClosed_le (by fun_prop) (by fun_prop)
      have hq : IsClosed {p : AggregationSpace T e × AggregationSpace T e |
          |Q T e s p.1 - Q T e s p.2| ≤ ‖p.1 - p.2‖} :=
        isClosed_le (by fun_prop) (by fun_prop)
      exact hp.inter hq
  | ih v w =>
      simp only [P_coe, Q_coe, ← Completion.coe_sub, Completion.norm_coe,
        AggregationVector.norm_def]
      exact VariableTree.potentials_lipschitz T e v w s

def projection (H : Finset ι) (hH : T.Initial H) :
    AggregationSpace T e →L[ℝ] AggregationSpace T e :=
  (AggregationVector.projection T e H hH).completion

@[simp] lemma projection_coe (H : Finset ι) (hH : T.Initial H) (v : AggregationVector T e) :
    projection T e H hH (v : AggregationSpace T e) = (AggregationVector.projection T e H hH v : AggregationSpace T e) :=
  ContinuousLinearMap.completion_apply_coe _ v

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (x : AggregationSpace T e) :
    ‖projection T e H hH x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (continuous_norm.comp (projection T e H hH).continuous) continuous_norm
  | ih v => simpa only [projection_coe, Completion.norm_coe] using
      AggregationVector.projection_contracts T e H hH v

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (x : AggregationSpace T e) :
    projection T e H hH (projection T e H hH x) = projection T e H hH x := by
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v => simp only [projection_coe, AggregationVector.projection_idem]

lemma coordinate_projection (H : Finset ι) (hH : T.Initial H) (s : ι) (x : AggregationSpace T e) :
    coordinate T e s (projection T e H hH x) = if s ∈ H then coordinate T e s x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
      · simp only [ite_eq_right hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
      rw [projection_coe, coordinate_coe, coordinate_coe]
      exact VariableTree.projectHead_apply T H v s

def tail (H : Finset ι) (hH : T.Initial H) : Submodule ℝ (AggregationSpace T e) :=
  (projection T e H hH).ker

lemma tail_closed (H : Finset ι) (hH : T.Initial H) :
    IsClosed (tail T e H hH : Set (AggregationSpace T e)) :=
  (projection T e H hH).isClosed_ker

theorem finite_tail_dense (H : Finset ι) (hH : T.Initial H) (x : AggregationSpace T e)
    (hx : x ∈ tail T e H hH) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : AggregationVector T e, AggregationVector.projection T e H hH v = 0 ∧
      ‖(v : AggregationSpace T e) - x‖ < ε := by
  have hx0 : projection T e H hH x = 0 := hx
  obtain ⟨v, hv⟩ := Completion.denseRange_coe.exists_dist_lt x (half_pos hε)
  let w : AggregationVector T e := v - AggregationVector.projection T e H hH v
  refine ⟨w, ?_, ?_⟩
  · change AggregationVector.projection T e H hH (v - AggregationVector.projection T e H hH v) = 0
    rw [map_sub, AggregationVector.projection_idem, sub_self]
  · have he : (w : AggregationSpace T e) - x =
        ((v : AggregationSpace T e) - x) - projection T e H hH ((v : AggregationSpace T e) - x) := by
      change (↑(v - AggregationVector.projection T e H hH v) : AggregationSpace T e) - x = _
      simp only [Completion.coe_sub, ← projection_coe, map_sub, hx0, sub_zero]
      abel
    rw [he]
    have hp := projection_contracts T e H hH ((v : AggregationSpace T e) - x)
    have hv' : ‖(v : AggregationSpace T e) - x‖ < ε / 2 := by
      simpa only [dist_comm x, dist_eq_norm] using hv
    exact (norm_sub_le _ _).trans_lt (by linarith)

end AggregationSpace

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def ofHeadLinear (H : Finset ι) : (H → ℝ) →ₗ[ℝ] AggregationVector T e where
  toFun := FiniteRootedTree.extend H
  map_add' f g := by
    change FiniteRootedTree.extend H (f + g) = FiniteRootedTree.extend H f + FiniteRootedTree.extend H g
    ext s
    by_cases hs : s ∈ H
    · simp [FiniteRootedTree.extend, hs]
    · simp [FiniteRootedTree.extend, hs]
  map_smul' a f := by
    change FiniteRootedTree.extend H (a • f) = a • FiniteRootedTree.extend H f
    ext s
    by_cases hs : s ∈ H
    · simp [FiniteRootedTree.extend, hs]
    · simp [FiniteRootedTree.extend, hs]

def ofHead (H : Finset ι) : (H → ℝ) →L[ℝ] AggregationVector T e :=
  (ofHeadLinear T e H).toContinuousLinearMap

lemma ofHead_apply (H : Finset ι) (f : H → ℝ) (s : ι) :
    ofHead T e H f s = if hs : s ∈ H then f ⟨s, hs⟩ else 0 := by
  change FiniteRootedTree.extend H f s = _
  simp [FiniteRootedTree.extend]

lemma ofHead_support (H : Finset ι) (f : H → ℝ) :
    (show ι →₀ ℝ from ofHead T e H f).support ⊆ H := by
  intro s hs
  by_contra hh
  have he : (ofHead T e H f) s = 0 := by rw [ofHead_apply, dite_eq_right hh]
  exact (Finsupp.mem_support_iff.mp hs) he

lemma basisVector_apply (s c : ι) : basisVector T e s c = if s = c then 1 else 0 :=
  Finsupp.single_apply

lemma not_finite_dimensional {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent) [Infinite ι] : ¬Module.Finite ℝ (AggregationVector T e) := by
  intro h
  let : Module.Finite ℝ (ι →₀ ℝ) := h
  exact Infinite.not_finite (Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ι ℝ (ι →₀ ℝ)))

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

def headCoordinates (H : Finset ι) : AggregationSpace T e →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun s : H => coordinate T e s.1)

@[simp] lemma headCoordinates_apply (H : Finset ι) (x : AggregationSpace T e) (s : H) :
    headCoordinates T e H x s = coordinate T e s.1 x := rfl

theorem projection_reconstructs (H : Finset ι) (hH : T.Initial H) (x : AggregationSpace T e) :
    projection T e H hH x = ((AggregationVector.ofHead T e H (headCoordinates T e H x)) : AggregationSpace T e) := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (projection T e H hH).continuous
      · exact ((Completion.toComplL : AggregationVector T e →L[ℝ] AggregationSpace T e).comp
          ((AggregationVector.ofHead T e H).comp (headCoordinates T e H))).continuous
  | ih v =>
      rw [projection_coe]
      apply congrArg ((↑) : AggregationVector T e → AggregationSpace T e)
      apply Finsupp.ext
      intro s
      change VariableTree.projectHead T H v s = AggregationVector.ofHead T e H (headCoordinates T e H (v : AggregationSpace T e)) s
      rw [AggregationVector.ofHead_apply]
      have hp := VariableTree.projectHead_apply T H (show ι →₀ ℝ from v) s
      rw [hp]
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs, dite_eq_left hs, headCoordinates_apply, coordinate_coe]
      · simp only [ite_eq_right hs, dite_eq_right hs]

lemma tail_eq_coordinate_kernel (H : Finset ι) (hH : T.Initial H) :
    tail T e H hH = (headCoordinates T e H).ker := by
  ext x
  constructor
  · intro hx
    change headCoordinates T e H x = 0
    ext s
    have hz : projection T e H hH x = 0 := hx
    have he := coordinate_projection T e H hH s.1 x
    rw [hz, map_zero, ite_eq_left s.2] at he
    exact he.symm
  · intro hx
    change projection T e H hH x = 0
    rw [projection_reconstructs]
    have hz : headCoordinates T e H x = 0 := hx
    rw [hz, map_zero, Completion.coe_zero]

theorem tail_finite_codimension (H : Finset ι) (hH : T.Initial H) :
    Module.Finite ℝ (AggregationSpace T e ⧸ tail T e H hH) := by
  rw [tail_eq_coordinate_kernel]
  exact Submodule.CoFG.ker (headCoordinates T e H).toLinearMap

theorem supported_is_finite (H : Finset ι) (hH : T.Initial H) (x : AggregationSpace T e)
    (hx : projection T e H hH x = x) :
    ∃ v : AggregationVector T e, (v : AggregationSpace T e) = x ∧ (show ι →₀ ℝ from v).support ⊆ H := by
  refine ⟨AggregationVector.ofHead T e H (headCoordinates T e H x), ?_, AggregationVector.ofHead_support T e H _⟩
  rw [← projection_reconstructs T e H hH x, hx]

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (AggregationSpace T e) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : AggregationVector T e →L[ℝ] AggregationSpace T e).toLinearMap
    (Completion.coe_injective (AggregationVector T e))
  exact AggregationVector.not_finite_dimensional T e hf

end AggregationSpace

namespace VariableExponent

lemma cubicConstant_pos : 0 < cubicConstant := by unfold cubicConstant; positivity

lemma cubicConstant_le_one : cubicConstant ≤ 1 := by
  have he : 1 ≤ 6 * Real.exp 1 := by linarith [Real.exp_one_gt_two]
  have hi : (6 * Real.exp 1)⁻¹ ≤ (1 : ℝ) := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) he
  exact (pow_le_pow_left₀ (by positivity) hi 3).trans_eq (one_pow 3)

lemma sixthConstant_pos : 0 < sixthConstant := by unfold sixthConstant; positivity

lemma sixthConstant_le_twice_cubic : sixthConstant ≤ 2 * cubicConstant := by
  have he : Real.exp (-(Real.exp 1 - 1)) ≤ (1/2:ℝ) := by
    calc
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith [Real.exp_one_gt_two])
      _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
      _ ≤ (1/2:ℝ) := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) Real.exp_one_gt_two.le
  rw [neg_sub] at he
  have hc6 : sixthConstant ≤ (1/4096:ℝ) := by
    unfold sixthConstant
    norm_num
    linarith
  have hi : (1/18:ℝ) ≤ (6*Real.exp 1)⁻¹ := by
    have hh : 6 * Real.exp 1 ≤ (18:ℝ) := by linarith [Real.exp_one_lt_three]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ)<6*Real.exp 1) hh
  have hc3 : (1/5832:ℝ) ≤ cubicConstant := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/18) hi 3
    norm_num only at hh
    exact hh
  linarith

lemma sixth_of_cubic {a b B Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hBm : B ≤ (a+b)/2) (hYm : Y ≤ (a+b)/2)
    (hcubic : cubicConstant * Y ^ 3 ≤ ((a+b)/2-B) * max a b ^ 2) :
    sixthConstant * Y ^ 6 ≤ (a^2+b^2-2*B^2) * (a^2+b^2)^2 := by
  let M := max a b
  let D := (a+b)/2-B
  let E := a^2+b^2-2*B^2
  let S := a^2+b^2
  have hM : 0 ≤ M := ha.trans (le_max_left _ _)
  have hMsum : M ≤ a+b := max_le (by linarith) (by linarith)
  have hD : 0 ≤ D := sub_nonneg.mpr hBm
  have hE : D*M ≤ E := by
    have hh := mul_nonneg hD (show 0 ≤ a+b-M by linarith)
    have hx := mul_nonneg hD hB
    dsimp [D,E] at *
    nlinarith [sq_nonneg (a-b)]
  have hEM : cubicConstant * Y^3 ≤ E*M := by
    apply hcubic.trans
    have hh := mul_le_mul_of_nonneg_right hE hM
    simpa only [M, pow_two, mul_assoc] using hh
  have hE0 : 0 ≤ E := (mul_nonneg hD hM).trans hE
  have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hMY : M*Y ≤ S := by
    have hh := mul_le_mul hMsum hYm hY (add_nonneg ha hb)
    dsimp [S]
    nlinarith [sq_nonneg (a-b)]
  have hY2 : 2*Y^2 ≤ S := by
    have hh := pow_le_pow_left₀ hY hYm 2
    dsimp [S]
    nlinarith [sq_nonneg (a-b)]
  have hSY : 2*M*Y^3 ≤ S^2 := by
    have hh := mul_le_mul hMY hY2 (by positivity) hS
    nlinarith
  calc
    sixthConstant * Y^6 ≤ (2*cubicConstant)*Y^6 :=
      mul_le_mul_of_nonneg_right sixthConstant_le_twice_cubic (by positivity)
    _ = (cubicConstant*Y^3)*(2*Y^3) := by ring
    _ ≤ (E*M)*(2*Y^3) := mul_le_mul_of_nonneg_right hEM (by positivity)
    _ = E*(2*M*Y^3) := by ring
    _ ≤ E*S^2 := mul_le_mul_of_nonneg_left hSY hE0

end VariableExponent

namespace VariableTree

open VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem normSum_cubic (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hx : x.support ⊆ H) (hz : ∀ s ∈ H, z s = 0) :
    cubicConstant * normSum T e z ^ 3 ≤
      ((normSum T e (x+z) + normSum T e (x-z))/2 - normSum T e x) *
        max (normSum T e (x+z)) (normSum T e (x-z)) ^ 2 := by
  let K := T.ancestorClosure (x.support ∪ z.support)
  have hK : T.Initial K := T.ancestorClosure_initial _
  have hxK : x.support ⊆ K := (Finset.subset_union_left).trans (T.subset_ancestorClosure _)
  have hzK : z.support ⊆ K := (Finset.subset_union_right).trans (T.subset_ancestorClosure _)
  have hpK : (x+z).support ⊆ K := Finsupp.support_add.trans (Finset.union_subset hxK hzK)
  have hmK : (x-z).support ⊆ K := Finsupp.support_sub.trans (Finset.union_subset hxK hzK)
  let U := T.restrict K hK
  let xf : K → ℝ := fun c => x c.1
  let zf : K → ℝ := fun c => z c.1
  have hxf : ∀ s ∉ Finset.univ.filter (fun s : K => s.1 ∈ H), xf s = 0 := by
    intro s hs
    have hsH : s.1 ∉ H := by simpa using hs
    exact Finsupp.notMem_support_iff.mp (fun hs => hsH (hx hs))
  have hzf : ∀ s ∈ Finset.univ.filter (fun s : K => s.1 ∈ H), zf s = 0 := by
    intro s hs; exact hz s.1 (Finset.mem_filter.mp hs).2
  have hstepU : ∀ c, c ≠ U.root → U.depth c = U.depth (U.parent c) + 1 := by
    intro c hc
    exact hstep c.1 (fun heq => hc (Subtype.ext heq))
  have hheightU : ∀ s, U.depth s ≤ h.val := fun s => hheight s.1
  have hh := finite_cubic U e h he (T.restrict_initial K hK H hH) hxf hzf hstepU hheightU
  have hn₁ : normSum T e x = U.pRootSum e xf := normSum_on_head T e x K hK hxK
  have hn₂ : normSum T e z = U.pRootSum e zf := normSum_on_head T e z K hK hzK
  have hn₃ : normSum T e (x+z) = U.pRootSum e (xf+zf) := normSum_on_head T e (x+z) K hK hpK
  have hn₄ : normSum T e (x-z) = U.pRootSum e (xf-zf) := normSum_on_head T e (x-z) K hK hmK
  rwa [hn₁, hn₂, hn₃, hn₄]

end VariableTree

namespace AggregationSpace

open UniformSpace VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem cubic_projected_tail (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x : AggregationVector T e) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : AggregationSpace T e) :
    cubicConstant * ‖z - projection T e H hH z‖ ^ 3 ≤
      ((‖(x : AggregationSpace T e) + (z-projection T e H hH z)‖ +
          ‖(x : AggregationSpace T e) - (z-projection T e H hH z)‖)/2 - ‖(x : AggregationSpace T e)‖) *
        max ‖(x : AggregationSpace T e) + (z-projection T e H hH z)‖
          ‖(x : AggregationSpace T e) - (z-projection T e H hH z)‖ ^ 2 := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih v =>
    simp only [projection_coe, ← Completion.coe_sub, ← Completion.coe_add, Completion.norm_coe,
      AggregationVector.norm_def]
    apply VariableTree.normSum_cubic T e h he hstep hheight x _ hH hx
    intro s hs
    change v s - VariableTree.projectHead T H v s = 0
    exact sub_eq_zero.mpr ((VariableTree.projectHead_apply T H (show ι →₀ ℝ from v) s).trans (ite_eq_left hs)).symm

theorem cubic_tail (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x : AggregationVector T e) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : AggregationSpace T e)
    (hz : z ∈ tail T e H hH) :
    cubicConstant * ‖z‖ ^ 3 ≤
      ((‖(x : AggregationSpace T e)+z‖ + ‖(x : AggregationSpace T e)-z‖)/2 - ‖(x : AggregationSpace T e)‖) *
        max ‖(x : AggregationSpace T e)+z‖ ‖(x : AggregationSpace T e)-z‖ ^ 2 := by
  have hh := cubic_projected_tail T e h he hstep hheight x hH hx z
  have hz0 : projection T e H hH z = 0 := hz
  simpa only [hz0,sub_zero] using hh

theorem cubic_supported (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : AggregationSpace T e) {H : Finset ι} (hH : T.Initial H)
    (hx : projection T e H hH x = x) (hz : z ∈ tail T e H hH) :
    cubicConstant * ‖z‖ ^ 3 ≤
      ((‖x+z‖ + ‖x-z‖)/2 - ‖x‖) * max ‖x+z‖ ‖x-z‖ ^ 2 := by
  obtain ⟨v,rfl,hv⟩ := supported_is_finite T e H hH x hx
  exact cubic_tail T e h he hstep hheight v hH hv z hz

lemma norm_lens_average (x z : AggregationSpace T e) :
    ‖x‖ ≤ (‖x+z‖+‖x-z‖)/2 ∧ ‖z‖ ≤ (‖x+z‖+‖x-z‖)/2 := by
  have hx := norm_add_le (x+z) (x-z)
  have hz := norm_sub_le (x+z) (x-z)
  have h₁ : x+z+(x-z) = (2:ℝ) • x := by module
  have h₂ : x+z-(x-z) = (2:ℝ) • z := by module
  rw [h₁, norm_smul] at hx
  rw [h₂, norm_smul] at hz
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hx hz
  constructor <;> linarith

theorem cubic_component (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : AggregationSpace T e) {H : Finset ι} (hH : T.Initial H)
    (hx : projection T e H hH x = x) (hz : z ∈ tail T e H hH) :
    cubicConstant * ‖z‖ ^ 3 / max ‖x+z‖ ‖x-z‖ ^ 2 ≤
      (‖x+z‖ + ‖x-z‖)/2 - ‖x‖ := by
  have hh := cubic_supported T e h he hstep hheight x z hH hx hz
  have hm : 0 ≤ max ‖x+z‖ ‖x-z‖ := (norm_nonneg _).trans (le_max_left _ _)
  by_cases hm0 : max ‖x+z‖ ‖x-z‖ = 0
  · simp only [hm0,zero_pow (by decide : 2 ≠ 0),div_zero]
    exact sub_nonneg.mpr (norm_lens_average T e x z).1
  exact (div_le_iff₀ (sq_pos_of_pos (lt_of_le_of_ne hm (Ne.symm hm0)))).mpr hh

theorem sixth_supported (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : AggregationSpace T e) {H : Finset ι} (hH : T.Initial H)
    (hx : projection T e H hH x = x) (hz : z ∈ tail T e H hH) :
    sixthConstant * ‖z‖ ^ 6 ≤
      (‖x+z‖^2 + ‖x-z‖^2 - 2*‖x‖^2) * (‖x+z‖^2 + ‖x-z‖^2)^2 := by
  have hh := norm_lens_average T e x z
  exact sixth_of_cubic (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hh.1 hh.2 (cubic_supported T e h he hstep hheight x z hH hx hz)

lemma cubic_zero (z : AggregationSpace T e) :
    cubicConstant * ‖z‖ ^ 3 ≤
      ((‖(0 : AggregationSpace T e)+z‖ + ‖(0 : AggregationSpace T e)-z‖)/2 - ‖(0 : AggregationSpace T e)‖) *
        max ‖(0 : AggregationSpace T e)+z‖ ‖(0 : AggregationSpace T e)-z‖ ^ 2 := by
  simp only [zero_add,zero_sub,norm_neg,norm_zero,sub_zero,max_self]
  have hh := mul_le_mul_of_nonneg_right cubicConstant_le_one (pow_nonneg (norm_nonneg z) 3)
  nlinarith

lemma sixth_zero (z : AggregationSpace T e) :
    sixthConstant * ‖z‖ ^ 6 ≤
      (‖(0 : AggregationSpace T e)+z‖^2 + ‖(0 : AggregationSpace T e)-z‖^2 - 2*‖(0 : AggregationSpace T e)‖^2) *
        (‖(0 : AggregationSpace T e)+z‖^2 + ‖(0 : AggregationSpace T e)-z‖^2)^2 := by
  have hh := norm_lens_average T e 0 z
  exact sixth_of_cubic (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    hh.1 hh.2 (cubic_zero T e z)

theorem sixth_component (h : ℕ+) (he : e.val = heightExponent h)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (hheight : ∀ s, T.depth s ≤ h.val)
    (x z : AggregationSpace T e) {H : Finset ι} (hH : T.Initial H)
    (hx : projection T e H hH x = x) (hz : z ∈ tail T e H hH) :
    sixthConstant * ‖z‖ ^ 6 / (‖x+z‖^2 + ‖x-z‖^2)^2 ≤
      ‖x+z‖^2 + ‖x-z‖^2 - 2*‖x‖^2 := by
  have hh := sixth_supported T e h he hstep hheight x z hH hx hz
  have hS : 0 ≤ ‖x+z‖^2 + ‖x-z‖^2 := by positivity
  by_cases hS0 : ‖x+z‖^2 + ‖x-z‖^2 = 0
  · have hb := (norm_lens_average T e x z).1
    have hxp : ‖x+z‖ = 0 := by nlinarith [norm_nonneg (x+z),sq_nonneg ‖x-z‖]
    have hxm : ‖x-z‖ = 0 := by nlinarith [norm_nonneg (x-z),sq_nonneg ‖x+z‖]
    have hx0 : ‖x‖ = 0 := by rw [hxp,hxm] at hb; linarith [norm_nonneg x]
    simp only [hS0,hx0,zero_pow (by decide : 2 ≠ 0),div_zero,mul_zero,sub_self,le_refl]
  exact (div_le_iff₀ (sq_pos_of_pos (lt_of_le_of_ne hS (Ne.symm hS0)))).mpr hh

end AggregationSpace

end RecursivePotentials

end

end OAI
