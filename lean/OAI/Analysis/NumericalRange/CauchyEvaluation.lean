import OAI.Analysis.NumericalRange.PolynomialCalculus

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder

section IntegralJets
open MeasureTheory Set Metric Complex Filter
open scoped Topology
variable {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]

def cauchyJet (s v : α → ℂ) (k : ℕ) (z : ℂ) (t : α) : ℂ :=
  (k.factorial : ℂ)*v t/(s t-z)^(k+1)

lemma cauchyJet_hasDerivAt
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hn : s t ≠ z) :
    HasDerivAt (fun w => cauchyJet s v k w t) (cauchyJet s v (k+1) z t) z := by
  have he := (hasDerivAt_const z ((k.factorial : ℂ)*v t)).div
    (((hasDerivAt_id z).const_sub (s t)).pow (k+1))
    (pow_ne_zero _ (sub_ne_zero.mpr hn))
  convert he using 1 <;> try rfl
  change ((k+1).factorial : ℂ)*v t/(s t-z)^(k+1+1) = _
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [id_eq, zero_mul, mul_neg_one, zero_sub]
  simp only [Pi.pow_apply, Nat.add_sub_cancel, pow_succ]
  field_simp

lemma cauchyJet_continuousOn
    {α : Type u_108} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ) :
    ContinuousOn (Function.uncurry (cauchyJet s v k)) (U ×ˢ univ) := by
  exact (continuous_const.mul (hv.comp continuous_snd)).continuousOn.div
    (((hs.comp continuous_snd).continuousOn.sub continuousOn_fst).pow (k+1))
    (fun p hp => pow_ne_zero _ (sub_ne_zero.mpr (hne p.1 hp.1 p.2)))

lemma cauchyJet_integrable {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {z : ℂ} (hne : ∀ t, s t ≠ z) (k : ℕ) :
    Integrable (cauchyJet s v k z) μ := by
  exact ((continuous_const.mul hv).div ((hs.sub continuous_const).pow (k+1))
    (fun t => pow_ne_zero _ (sub_ne_zero.mpr (hne t)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma iteratedDeriv_cauchyIntegral {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hne : ∀ z ∈ U, ∀ t, s t ≠ z) (k : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) z = ∫ t, cauchyJet s v k z t ∂μ := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => ∫ t, v t/(s t-w) ∂μ) =ᶠ[nhds z]
        fun w => ∫ t, cauchyJet s v k w t ∂μ :=
      Filter.Eventually.mono (hU.mem_nhds hz) fun w hw => ih hw
    rw [he.deriv_eq]
    exact (compact_parametric_hasDerivAt hU (cauchyJet_continuousOn hs hv hne k)
      (cauchyJet_continuousOn hs hv hne (k+1))
      (fun w hw t => cauchyJet_hasDerivAt s v k (hne w hw t)) hz).deriv

lemma iteratedDeriv_cauchyKernel (s v : α → ℂ) (k : ℕ) {z : ℂ} {t : α}
    (hne : s t ≠ z) :
    iteratedDeriv k (fun w => v t/(s t-w)) z = cauchyJet s v k z t := by
  induction k generalizing z with
  | zero => simp [cauchyJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun w => v t/(s t-w)) =ᶠ[nhds z]
        fun w => cauchyJet s v k w t :=
      Filter.Eventually.mono (isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({s t} : Set ℂ)ᶜ from
        fun h => hne h.symm)) fun w hw => ih (fun h => hw h.symm)
    rw [he.deriv_eq]
    exact (cauchyJet_hasDerivAt s v k hne).deriv

end IntegralJets

section
open MeasureTheory Set Filter Module
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_109} [MeasurableSpace α] {μ : Measure α}
  {n : Type u_110} [Fintype n] [DecidableEq n]

lemma matrix_integral_mulVec {F : α → Matrix n n ℂ} (hF : Integrable F μ) (x : n → ℂ) :
    (∫ t, F t ∂μ) *ᵥ x = ∫ t, F t *ᵥ x ∂μ := by
  let L : Matrix n n ℂ →L[ℂ] (n → ℂ) :=
    (show Matrix n n ℂ →ₗ[ℂ] (n → ℂ) from
      { toFun := fun B => B *ᵥ x
        map_add' := fun B C => Matrix.add_mulVec B C x
        map_smul' := fun c B => Matrix.smul_mulVec c B x }).toContinuousLinearMap
  exact (L.integral_comp_comm hF).symm

lemma matrixAnalyticEval_integral (A : Matrix n n ℂ) {F : ℂ → α → ℂ}
    (hi : Integrable (fun t => matrixAnalyticEval A (fun z => F z t)) μ)
    (hj : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      Integrable (fun t => iteratedDeriv k (fun z => F z t) β) μ)
    (hd : ∀ β ∈ spectrum ℂ A, ∀ k < Fintype.card n,
      iteratedDeriv k (fun z => ∫ t, F z t ∂μ) β =
        ∫ t, iteratedDeriv k (fun z => F z t) β ∂μ) :
    matrixAnalyticEval A (fun z => ∫ t, F z t ∂μ) =
      ∫ t, matrixAnalyticEval A (fun z => F z t) ∂μ := by
  apply Matrix.toLinAlgEquiv'.injective
  apply primary_end_ext_spectrum (T := Matrix.toLinAlgEquiv' A)
  intro β hβ x
  have hb : β ∈ spectrum ℂ A := by simpa only [AlgEquiv.spectrum_eq] using hβ
  have he (f : ℂ → ℂ) :
      Matrix.toLinAlgEquiv' (matrixAnalyticEval A f) (x : n → ℂ) =
        ∑ k ∈ Finset.range (Fintype.card n),
          (iteratedDeriv k f β / (k.factorial : ℂ)) •
          (((primaryNilpotent (Matrix.toLinAlgEquiv' A) β)^k) x : n → ℂ) := by
    simp only [matrixAnalyticEval, AlgEquiv.apply_symm_apply, primaryEval_coe,
      scalarJetEval, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    simp
  rw [he, Matrix.toLinAlgEquiv'_apply, matrix_integral_mulVec hi]
  simp_rw [← Matrix.toLinAlgEquiv'_apply,he]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [hd β hb k (Finset.mem_range.mp hk),integral_smul_const,integral_div]
  · intro k hk
    exact ((hj β hb k (Finset.mem_range.mp hk)).div_const _).smul_const _

lemma matrixAnalyticEval_resolvent (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) :
    matrixAnalyticEval A (fun z => (s-z)⁻¹) = (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hn (z : ℂ) (hz : z ∈ spectrum ℂ A) : s-z ≠ 0 :=
    sub_ne_zero.mpr (fun h => hs (h ▸ hz))
  have hf (z : ℂ) (_ : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => s-z) z :=
    analyticAt_const.sub analyticAt_id
  have hg (z : ℂ) (hz : z ∈ spectrum ℂ A) : AnalyticAt ℂ (fun z => (s-z)⁻¹) z :=
    (hf z hz).inv (hn z hz)
  have he : matrixAnalyticEval A (fun _ => 1) =
      matrixAnalyticEval A (fun z => (s-z)⁻¹*(s-z)) := by
    apply matrixAnalyticEval_eventuallyEq
    intro z hz
    filter_upwards [(hf z hz).continuousAt.eventually_ne (hn z hz)] with w hw
    exact (inv_mul_cancel₀ hw).symm
  rw [matrixAnalyticEval_const, map_one, matrixAnalyticEval_mul A hg hf,
    matrixAnalyticEval_sub A (f := fun _ => s) (g := fun z => z)
      (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_id),
    matrixAnalyticEval_const,matrixAnalyticEval_id,Algebra.algebraMap_eq_smul_one] at he
  exact (Matrix.inv_eq_left_inv he.symm).symm

lemma matrixAnalyticEval_cauchyKernel (A : Matrix n n ℂ) {s : ℂ}
    (hs : s ∉ spectrum ℂ A) (v : ℂ) :
    matrixAnalyticEval A (fun z => v/(s-z)) = v • (s • (1 : Matrix n n ℂ)-A)⁻¹ := by
  have hg : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ (fun z => (s-z)⁻¹) z := by
    intro z hz
    have hn : s ≠ z := fun h => hs (h ▸ hz)
    exact (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hn)
  simp_rw [div_eq_mul_inv]
  rw [matrixAnalyticEval_mul A (fun _ _ => analyticAt_const) hg,
    matrixAnalyticEval_const,matrixAnalyticEval_resolvent A hs]
  simp only [Algebra.smul_def]

end

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator
variable {α : Type u_111} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_112} [Fintype n] [DecidableEq n]

lemma matrix_resolvent_analytic (A : Matrix n n ℂ) {s : ℂ} (hs : s ∉ spectrum ℂ A) :
    AnalyticAt ℂ (fun z : ℂ => (z • (1 : Matrix n n ℂ)-A)⁻¹) s := by
  have hu : IsUnit (s • (1 : Matrix n n ℂ)-A) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hs
  have ha : AnalyticAt ℂ (fun z : ℂ => z • (1 : Matrix n n ℂ)-A) s := by fun_prop
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse] using
    (show AnalyticAt ℂ Ring.inverse (s • (1 : Matrix n n ℂ)-A) from by
      simpa only [hu.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hu.unit)).comp
      (f := fun z : ℂ => z • (1 : Matrix n n ℂ)-A) ha

theorem matrix_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    matrixAnalyticEval A (fun z => ∫ t, v t/(s t-z) ∂μ) =
      ∫ t, v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹ ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have he (t : α) := matrixAnalyticEval_cauchyKernel A (hn t) (v t)
  have hi : Integrable (fun t => matrixAnalyticEval A (fun z => v t/(s t-z))) μ := by
    simp_rw [he]
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply hv.smul
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (matrix_resolvent_analytic A (hn t)).continuousAt.comp hs.continuousAt
  rw [matrixAnalyticEval_integral A hi]
  · exact integral_congr_ae (Filter.Eventually.of_forall he)
  · intro β hβ k _
    have hd : (fun t => iteratedDeriv k (fun z => v t/(s t-z)) β) = cauchyJet s v k β :=
      funext fun t => iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)
    rw [hd]
    exact cauchyJet_integrable hs hv (hne β (hAU hβ)) k
  · intro β hβ k _
    rw [iteratedDeriv_cauchyIntegral hs hv hU hne k (hAU hβ)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      (iteratedDeriv_cauchyKernel s v k (hne β (hAU hβ) t)).symm)

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker
variable {α : Type u_113} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {n : Type u_114} {m : Type u_115} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma matrix_resolvent_continuous
    {α : Type u_113} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α] [BorelSpace α]
    {n : Type u_114} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) {s : α → ℂ}
    (hs : Continuous s) (hn : ∀ t, s t ∉ spectrum ℂ A) :
    Continuous (fun t => (s t • (1 : Matrix n n ℂ)-A)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (matrix_resolvent_analytic A (hn t)).continuousAt.comp hs.continuousAt

theorem complete_cauchy_integral_evaluation (A : Matrix n n ℂ)
    {s v : α → ℂ} (hs : Continuous s) (hv : Continuous v)
    {B : α → Matrix m m ℂ} (hB : Continuous B)
    {U : Set ℂ} (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hne : ∀ z ∈ U, ∀ t, s t ≠ z) :
    completeAnalyticEval A (fun z i j => ∫ t, v t*B t i j/(s t-z) ∂μ) =
      ∫ t, (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t ∂μ := by
  have hn (t : α) : s t ∉ spectrum ℂ A := fun h => hne _ (hAU h) t rfl
  have hrc := hv.smul (matrix_resolvent_continuous A hs hn)
  have hbc (i j : m) : Continuous (fun t => B t i j) := (entryCLM i j).continuous.comp hB
  have hri : Integrable (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) ⊗ₖ B t) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply continuous_matrix
    intro i j
    change Continuous (fun t => (v t • (s t • (1 : Matrix n n ℂ)-A)⁻¹) i.1 j.1 * B t i.2 j.2)
    exact ((entryCLM i.1 j.1).continuous.comp hrc).mul (hbc i.2 j.2)
  ext i j
  dsimp only [completeAnalyticEval]
  have he := matrix_cauchy_integral_evaluation (μ := μ) A (s := s) (v := fun t => v t*B t i.2 j.2) hs (hv.mul (hbc i.2 j.2)) hU hAU hne
  rw [he,
    matrix_integral_entry hri]
  have ht : Integrable (fun t => (v t*B t i.2 j.2) • (s t • (1 : Matrix n n ℂ)-A)⁻¹) μ :=
    ((hv.mul (hbc i.2 j.2)).smul (matrix_resolvent_continuous A hs hn)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [matrix_integral_entry ht]
  apply integral_congr_ae
  filter_upwards [] with t
  change (v t*B t i.2 j.2) * (s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1 =
    (v t*(s t • (1 : Matrix n n ℂ)-A)⁻¹ i.1 j.1)*B t i.2 j.2
  ring


end CompleteCrouzeix

end

end OAI
