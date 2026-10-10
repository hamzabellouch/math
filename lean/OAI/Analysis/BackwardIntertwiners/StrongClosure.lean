import OAI.Analysis.BackwardIntertwiners.DiagonalSymbols

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

lemma L2_norm_eq_sqrt {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (f : Lp E 2 μ) :
    ‖f‖ = Real.sqrt (∫ x, ‖f x‖^2 ∂μ) := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ENNReal) ≠ 0)
      (by norm_num : (2:ENNReal) ≠ ∞) (Lp.aestronglyMeasurable f)]
  simp [Real.sqrt_eq_rpow]

lemma L2_tendsto_zero_of_dominated {X E ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (F : ι → Lp E 2 μ) (b : X → ℝ)
    (hb : Integrable (fun x => b x ^ 2) μ)
    (hB : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) l (𝓝 0)) :
    Tendsto F l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hi : Tendsto (fun n => ∫ x, ‖F n x‖^2 ∂μ) l (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence (f:=fun _ : X => (0:ℝ))
      (fun x => b x^2)
      (Eventually.of_forall fun n => ((Lp.aestronglyMeasurable (F n)).norm.aemeasurable.pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun n => (hB n).mono fun x hx => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2) hb
      (hlim.mono fun x hx => by simpa using hx.norm.pow 2)
  simpa only [Function.comp_def, Real.sqrt_zero, L2_norm_eq_sqrt] using Real.continuous_sqrt.continuousAt.tendsto.comp hi

lemma fiber_norm_sq (v : Fiber) : ‖v‖^2 = ∑' j, ‖v j‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ) < (2:ENNReal).toReal) v
lemma fiber_tendsto_zero_of_dominated {ι : Type*} {l : Filter ι} (v : ι → Fiber) (b : ℤ → ℝ)
    (hb : Summable (fun j => b j^2))
    (hB : ∀ n j, ‖v n j‖ ≤ b j)
    (hlim : ∀ j, Tendsto (fun n => v n j) l (𝓝 0)) :
    Tendsto v l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hi : Tendsto (fun n => ‖v n‖^2) l (𝓝 0) := by
    simp_rw [fiber_norm_sq]
    simpa using tendsto_tsum_of_dominated_convergence (g:=fun _ : ℤ => (0:ℝ)) hb
      (fun j => by simpa using (hlim j).norm.pow 2)
      (Filter.Eventually.of_forall fun n j => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB n j) 2)
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
    using Real.continuous_sqrt.continuousAt.tendsto.comp hi
lemma diagonalFiber_bound (a : DiagonalSymbol) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x j, ‖a x j‖ ≤ C) (x : Base) (v : Fiber) :
    ‖diagonalFiber a x v‖ ≤ C*‖v‖ := by
  calc
    _ ≤ ‖(C:ℂ) • v‖ := by
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      simp only [diagonalFiber_apply,lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_mul,
        Complex.norm_real,Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha x j) (norm_nonneg _)
    _ = C*‖v‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]

lemma diagonalFiber_tendsto_zero {ι : Type*} {l : Filter ι} (a : ι → DiagonalSymbol) {C : ℝ}
    (ha : ∀ n x j, ‖a n x j‖ ≤ C) (x : Base) (v : Fiber)
    (hlim : ∀ j, Tendsto (fun n => a n x j) l (𝓝 0)) :
    Tendsto (fun n => diagonalFiber (a n) x v) l (𝓝 0) := by
  apply fiber_tendsto_zero_of_dominated _ (fun j => C*‖v j‖)
  · have hv : Summable (fun j => ‖v j‖^2) := by
      simpa using (lp.memℓp v).summable (by norm_num : (0:ℝ) < (2:ENNReal).toReal)
    simpa only [mul_pow] using hv.mul_left (C^2)
  · intro n j
    rw [diagonalFiber_apply,norm_mul]
    exact mul_le_mul_of_nonneg_right (ha n x j) (norm_nonneg _)
  · intro j
    simpa using (hlim j).mul_const (v j)
lemma L2_integrable_bound_sq (f : GlobalHilbert) (C : ℝ) :
    Integrable (fun x => (C*‖f x‖)^2) baseMeasure := by
  have hf : Integrable (fun x => ‖f x‖^2) baseMeasure :=
    (Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  simpa only [mul_pow] using hf.const_mul (C^2)
lemma diagonalOperator_tendsto_zero {ι : Type*} [Countable ι] {l : Filter ι} [l.IsCountablyGenerated] (a : ι → DiagonalSymbol) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n x j, ‖a n x j‖ ≤ C)
    (hlim : ∀ᵐ x ∂baseMeasure, ∀ j, Tendsto (fun n => a n x j) l (𝓝 0))
    (f : GlobalHilbert) : Tendsto (fun n => diagonalOperator (a n) f) l (𝓝 0) := by
  apply L2_tendsto_zero_of_dominated _ (fun x => C*‖f x‖) (L2_integrable_bound_sq f C)
  · intro n
    filter_upwards [diagonalOperator_ae (a n) f] with x hx
    rw [hx]
    exact diagonalFiber_bound _ hC (ha n) _ _
  · filter_upwards [hlim,ae_all_iff.mpr (fun n => diagonalOperator_ae (a n) f)] with x hx hn
    have he : (fun n => diagonalOperator (a n) f x) = (fun n => diagonalFiber (a n) x (f x)) := funext hn
    rw [he]
    exact diagonalFiber_tendsto_zero a ha x (f x) hx
lemma diagonalOperator_tendsto {ι : Type*} [Countable ι] {l : Filter ι} [l.IsCountablyGenerated] (a : ι → DiagonalSymbol) (b : DiagonalSymbol)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ n x j, ‖a n x j‖ ≤ C)
    (hb : ∀ x j, ‖b x j‖ ≤ C)
    (hlim : ∀ᵐ x ∂baseMeasure, ∀ j, Tendsto (fun n => a n x j) l (𝓝 (b x j)))
    (f : GlobalHilbert) :
    Tendsto (fun n => diagonalOperator (a n) f) l (𝓝 (diagonalOperator b f)) := by
  have hB : ∀ n x j, ‖(a n-b) x j‖ ≤ 2*C := fun n x j =>
    (norm_sub_le _ _).trans ((add_le_add (ha n x j) (hb x j)).trans_eq (by ring))
  have hl : ∀ᵐ x ∂baseMeasure, ∀ j, Tendsto (fun n => (a n-b) x j) l (𝓝 0) := by
    filter_upwards [hlim] with x hx j
    simpa only [DiagonalSymbol.sub_apply,sub_self] using (hx j).sub_const (b x j)
  have hh := diagonalOperator_tendsto_zero (fun n => a n-b) (mul_nonneg (by norm_num) hC) hB hl f
  have he (n : ι) : diagonalOperator (a n-b) f = diagonalOperator (a n) f - diagonalOperator b f :=
    congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T f) (map_sub diagonalRepresentation (a n) b)
  simp_rw [he] at hh
  exact tendsto_sub_nhds_zero_iff.mp hh

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpace : CompleteSpace H]

@[instance_reducible]
def strongOperatorTopology : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun T : H →L[ℂ] H => (fun v : H => T v)) inferInstance

def StronglyClosed (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  @IsClosed (H →L[ℂ] H) strongOperatorTopology A

omit completeSpace in
lemma strong_continuous_apply [CompleteSpace H] (v : H) :
    @Continuous (H →L[ℂ] H) H strongOperatorTopology inferInstance (fun T => T v) := by
  let := strongOperatorTopology (H:=H)
  exact (continuous_apply v).comp continuous_induced_dom

lemma StronglyClosed.mem_of_tendsto {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : StronglyClosed A) {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → H →L[ℂ] H} {S : H →L[ℂ] H}
    (hT : ∀ᶠ i in l, T i ∈ A) (hlim : ∀ v, Tendsto (fun i => T i v) l (𝓝 (S v))) :
    S ∈ A := by
  let := strongOperatorTopology (H:=H)
  refine IsClosed.mem_of_tendsto hA (f:=T) ?_ hT
  change Tendsto T l (@nhds (H →L[ℂ] H) (TopologicalSpace.induced _ _) S)
  rw [nhds_induced,Filter.tendsto_comap_iff]
  exact tendsto_pi_nhds.mpr hlim


def strongGenerated (s : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  sInf {A | StronglyClosed A ∧ s ⊆ A}
lemma mem_strongGenerated {s : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} :
    T ∈ strongGenerated s ↔ ∀ A : StarSubalgebra ℂ (H →L[ℂ] H),
      StronglyClosed A → s ⊆ A → T ∈ A := by
  simp [strongGenerated,StarSubalgebra.mem_sInf]
lemma subset_strongGenerated (s : Set (H →L[ℂ] H)) : s ⊆ strongGenerated s := by
  intro T hT
  exact mem_strongGenerated.mpr fun _ _ hs => hs hT
lemma strongGenerated_le {s : Set (H →L[ℂ] H)} {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : StronglyClosed A) (hs : s ⊆ A) : strongGenerated s ≤ A :=
  fun _ hT => mem_strongGenerated.mp hT A hA hs
lemma strongGenerated_closed (s : Set (H →L[ℂ] H)) : StronglyClosed (strongGenerated s) := by
  let := strongOperatorTopology (H:=H)
  have he : (strongGenerated s : Set (H →L[ℂ] H)) =
      ⋂ A : StarSubalgebra ℂ (H →L[ℂ] H), ⋂ (_ : StronglyClosed A ∧ s ⊆ A), (A : Set _) := by
    ext T
    simp [mem_strongGenerated]
  rw [StronglyClosed,he]
  exact isClosed_iInter fun A => isClosed_iInter fun h => h.1
lemma strongGenerated_mono {s t : Set (H →L[ℂ] H)} (hst : s ⊆ t) :
    strongGenerated s ≤ strongGenerated t :=
  strongGenerated_le (strongGenerated_closed t) (hst.trans (subset_strongGenerated t))

lemma strong_centralizer_closed (s : Set (H →L[ℂ] H)) :
    StronglyClosed (StarSubalgebra.centralizer ℂ s) := by
  let := strongOperatorTopology (H:=H)
  have he : (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) =
      ⋂ A ∈ s ∪ star s, ⋂ v : H, {T | A (T v) = T (A v)} := by
    ext T
    change (∀ A ∈ s ∪ star s, A*T=T*A) ↔ _
    simp only [mem_iInter,mem_ofPred_eq]
    exact forall₂_congr fun A hA => ⟨fun h v => DFunLike.congr_fun h v,
      fun h => ContinuousLinearMap.ext h⟩
  rw [StronglyClosed,he]
  exact isClosed_iInter fun A => isClosed_iInter fun _ => isClosed_iInter fun v =>
    isClosed_eq (A.continuous.comp (strong_continuous_apply v)) (strong_continuous_apply (A v))


lemma strongGenerated_commutative {s : Set (H →L[ℂ] H)}
    (hs : ∀ A ∈ s, IsSelfAdjoint A) (hc : ∀ A ∈ s, ∀ B ∈ s, A*B=B*A) :
    ∀ A ∈ strongGenerated s, ∀ B ∈ strongGenerated s, A*B=B*A := by
  have hle : strongGenerated s ≤ StarSubalgebra.centralizer ℂ s := by
    apply strongGenerated_le (strong_centralizer_closed s)
    intro B hB
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    exact ⟨hc A hA B hB, by rw [(hs A hA).star_eq]; exact hc A hA B hB⟩
  have hle' : strongGenerated s ≤ StarSubalgebra.centralizer ℂ (strongGenerated s : Set _) := by
    apply strongGenerated_le (strong_centralizer_closed _)
    intro B hB
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    refine ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA) B hB).1.symm, ?_⟩
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle ((strongGenerated s).star_mem' hA)) B hB).1.symm
  intro A hA B hB
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle' hB) A hA).1



end
end BackwardIntertwiners

end OAI
