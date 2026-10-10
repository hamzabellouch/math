import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

/-- Mapping both coordinates of a coupling gives a coupling of the mapped marginals. -/
theorem IsCoupling.map {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R) :
    IsCoupling (Measure.map Q μ) (Measure.map R ν)
      (Measure.map (Prod.map Q R) π) := by
  have hQR : Measurable (Prod.map Q R) :=
    (hQ.comp measurable_fst).prodMk (hR.comp measurable_snd)
  let : IsProbabilityMeasure π := hπ.1
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hQR, ← hπ.2.1,
      Measure.map_map hQ measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hQR, ← hπ.2.2,
      Measure.map_map hR measurable_snd]
    rfl

/-- Change of variables for the quadratic cost of a mapped coupling. -/
theorem quadraticPlanCost_map {d : ℕ} (π : Measure (E d × E d))
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R) :
    quadraticPlanCost (Measure.map (Prod.map Q R) π) =
      ∫⁻ p, ENNReal.ofReal (‖Q p.1 - R p.2‖ ^ 2) ∂π := by
  unfold quadraticPlanCost
  rw [lintegral_map]
  · rfl
  · fun_prop
  · exact (hQ.comp measurable_fst).prodMk (hR.comp measurable_snd)

/-- Almost-everywhere statements about either marginal pull back along a coupling. -/
theorem IsCoupling.ae_pair {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {P Q : E d → Prop} (hP : ∀ᵐ x ∂μ, P x) (hQ : ∀ᵐ y ∂ν, Q y) :
    ∀ᵐ p ∂π, P p.1 ∧ Q p.2 := by
  have hP' : ∀ᵐ p ∂π, P p.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (hπ.2.1.symm ▸ hP)
  have hQ' : ∀ᵐ p ∂π, Q p.2 :=
    ae_of_ae_map measurable_snd.aemeasurable (hπ.2.2.symm ▸ hQ)
  exact hP'.and hQ'

private theorem sqrt_lintegral_norm_sq_eq_lpNorm
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {σ : Measure α} {f : α → F} (hf : AEStronglyMeasurable f σ) :
    Real.sqrt ((∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂σ).toReal) =
      lpNorm f 2 σ := by
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (‖f x‖))) (hf.norm.pow 2)]
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  simp [Real.sqrt_eq_rpow]

private theorem lpNorm_two_le_of_ae_bound
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {σ : Measure α} [IsProbabilityMeasure σ] {f : α → F}
    (hf : AEStronglyMeasurable f σ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ᵐ x ∂σ, ‖f x‖ ≤ δ) : lpNorm f 2 σ ≤ δ := by
  have hc : MemLp (fun _ : α => δ) 2 σ := memLp_const δ
  calc
    lpNorm f 2 σ ≤ lpNorm (fun _ : α => δ) 2 σ := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      exact ENNReal.toReal_mono hc.eLpNorm_ne_top (eLpNorm_mono_ae_real hf hb)
    _ = δ := by simp [lpNorm_const', Real.norm_eq_abs, abs_of_nonneg hδ]

/-- The square root of a quadratic plan cost is the real-valued L² norm. -/
theorem sqrt_quadraticPlanCost_eq_lpNorm {d : ℕ} (π : Measure (E d × E d)) :
    Real.sqrt (quadraticPlanCost π).toReal =
      lpNorm (fun p : E d × E d => p.1 - p.2) 2 π := by
  exact sqrt_lintegral_norm_sq_eq_lpNorm (by fun_prop)

/-- A plan has finite quadratic cost exactly when its displacement belongs to L². -/
theorem quadraticPlanCost_ne_top_iff_memLp {d : ℕ}
    (π : Measure (E d × E d)) :
    quadraticPlanCost π ≠ ∞ ↔
      MemLp (fun p : E d × E d => p.1 - p.2) 2 π := by
  rw [memLp_two_iff_integrable_sq_norm (by fun_prop)]
  exact lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Filter.Eventually.of_forall (fun p => sq_nonneg (‖p.1 - p.2‖)))

/-- Perturbing the two coordinates by uniformly bounded errors changes root cost
by at most the sum of those errors. Only the original displacement needs an L² bound. -/
theorem sqrt_quadraticPlanCost_map_le_of_memLp {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : MemLp (fun p : E d × E d => p.1 - p.2) 2 π) :
    Real.sqrt (quadraticPlanCost (Measure.map (Prod.map Q R) π)).toReal ≤
      Real.sqrt (quadraticPlanCost π).toReal + ε + η := by
  let : IsProbabilityMeasure π := hπ.1
  let f : E d × E d → E d := fun p => p.1 - p.2
  let e : E d × E d → E d := fun p => (Q p.1 - p.1) - (R p.2 - p.2)
  have he : AEStronglyMeasurable e π := by dsimp [e]; fun_prop
  have heb : ∀ᵐ p ∂π, ‖e p‖ ≤ ε + η := by
    filter_upwards [hπ.ae_pair hQerr hRerr] with p hp
    exact (norm_sub_le _ _).trans (add_le_add hp.1 hp.2)
  have hel : lpNorm e 2 π ≤ ε + η :=
    lpNorm_two_le_of_ae_bound he (add_nonneg hε hη) heb
  rw [quadraticPlanCost_map π hQ hR,
    sqrt_lintegral_norm_sq_eq_lpNorm (by fun_prop),
    sqrt_quadraticPlanCost_eq_lpNorm]
  have hdecomp : (fun p : E d × E d => Q p.1 - R p.2) = f + e := by
    funext p
    dsimp [f, e]
    abel
  rw [hdecomp]
  exact (lpNorm_add_le hfinite (by norm_num)).trans (by linarith)

/-- Uniformly bounded changes of coordinates preserve finite quadratic cost. -/
theorem quadraticPlanCost_map_ne_top {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ}
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : quadraticPlanCost π ≠ ∞) :
    quadraticPlanCost (Measure.map (Prod.map Q R) π) ≠ ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  let f : E d × E d → E d := fun p => p.1 - p.2
  let e : E d × E d → E d := fun p => (Q p.1 - p.1) - (R p.2 - p.2)
  have hf : MemLp f 2 π := (quadraticPlanCost_ne_top_iff_memLp π).1 hfinite
  have he : MemLp e 2 π := by
    apply MemLp.of_bound (by dsimp [e]; fun_prop) (ε + η)
    filter_upwards [hπ.ae_pair hQerr hRerr] with p hp
    exact (norm_sub_le _ _).trans (add_le_add hp.1 hp.2)
  have hdecomp : (fun p : E d × E d => Q p.1 - R p.2) = f + e := by
    funext p
    dsimp [f, e]
    abel
  have hmem : MemLp (fun p : E d × E d => Q p.1 - R p.2) 2 π := by
    rw [hdecomp]
    exact hf.add he
  rw [quadraticPlanCost_map π hQ hR]
  apply (lintegral_ofReal_ne_top_iff_integrable (hmem.aestronglyMeasurable.norm.pow 2)
    (Filter.Eventually.of_forall (fun p => sq_nonneg (‖Q p.1 - R p.2‖)))).2
  exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem

/-- Finite-cost version of `sqrt_quadraticPlanCost_map_le_of_memLp`. -/
theorem sqrt_quadraticPlanCost_map_le {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    {Q R : E d → E d} (hQ : Measurable Q) (hR : Measurable R)
    {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hQerr : ∀ᵐ x ∂μ, ‖Q x - x‖ ≤ ε)
    (hRerr : ∀ᵐ y ∂ν, ‖R y - y‖ ≤ η)
    (hfinite : quadraticPlanCost π ≠ ∞) :
    Real.sqrt (quadraticPlanCost (Measure.map (Prod.map Q R) π)).toReal ≤
      Real.sqrt (quadraticPlanCost π).toReal + ε + η :=
  sqrt_quadraticPlanCost_map_le_of_memLp hπ hQ hR hε hη hQerr hRerr
    ((quadraticPlanCost_ne_top_iff_memLp π).1 hfinite)

end Problem358

end

end OAI
