import OAI.Analysis.AncientFlat.Kernel.ClassicalBase

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology ZeroAtInfty BoundedContinuousFunction
namespace SourceFrozenOrder
open SchwartzTimeScale SourceFrozenCancellation
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma normalized_one (K : SchwartzMap V E) (A : V → ℝ)
    (hAp : ∀ y, 0 < A y) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    value K A 1 f j x = ∫ z, f (x-z) • atTime K (Module.finrank ℝ V+j) (A (x-z)) z := by
  simpa only [inv_one,one_pow,one_smul] using normalized K A hAp 1 zero_lt_one f j x

lemma integrable_normalized_one (K : SchwartzMap V E) (j : ℕ)
    (α β : ℝ) (hα : 0 < α) (A : V → ℝ) (hA : Continuous A)
    (hAr : ∀ y, A y ∈ Icc α β) (f : V →ᵇ ℂ) (x : V) :
    Integrable (fun z => f (x-z) • atTime K (Module.finrank ℝ V+j) (A (x-z)) z) := by
  obtain ⟨B,hB,_,hBp,hb⟩ := parameter_envelope K (Module.finrank ℝ V+j) α β hα
  apply (hB.const_mul ‖f‖).mono'
  · exact ((f.continuous.comp (continuous_const.sub continuous_id)).smul
      (continuous_variable K _ (fun z => A (x-z)) (hA.comp (continuous_const.sub continuous_id))
        (fun z => hα.trans_le (hAr _).1))).aestronglyMeasurable
  · filter_upwards with z
    rw [norm_smul]
    exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)

lemma exists_norm_difference_bound (K : SchwartzMap V E) (j : ℕ)
    (α β : ℝ) (hα : 0 < α) : ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (A B : V →ᵇ ℝ) (_hA : ∀ y, A y ∈ Icc α β) (_hB : ∀ y, B y ∈ Icc α β)
        (f g : V →ᵇ ℂ) (x : V),
        ‖value K A 1 f j x-value K B 1 g j x‖ ≤ C*‖f-g‖+D*‖g‖*‖A-B‖ := by
  obtain ⟨P,hP,_,hPp,hPb⟩ := parameter_envelope K (Module.finrank ℝ V+j) α β hα
  obtain ⟨Q,hQ,_,hQp,hQb⟩ := parameter_lipschitz_envelope K (Module.finrank ℝ V+j) α β hα
  refine ⟨∫ z, P z, ∫ z, Q z,integral_nonneg hPp,integral_nonneg hQp,?_⟩
  intro A B hA hB f g x
  rw [normalized_one K A (fun y => hα.trans_le (hA y).1),
    normalized_one K B (fun y => hα.trans_le (hB y).1),
    ← integral_sub (integrable_normalized_one K j α β hα A A.continuous hA f x)
      (integrable_normalized_one K j α β hα B B.continuous hB g x)]
  calc
    _ ≤ ∫ z, P z*‖f-g‖+Q z*‖g‖*‖A-B‖ := by
      apply norm_integral_le_of_norm_le ((hP.mul_const _).add ((hQ.mul_const _).mul_const _))
      filter_upwards with z
      have hd : f (x-z) • atTime K (Module.finrank ℝ V+j) (A (x-z)) z-
          g (x-z) • atTime K (Module.finrank ℝ V+j) (B (x-z)) z =
          (f (x-z)-g (x-z)) • atTime K (Module.finrank ℝ V+j) (A (x-z)) z+
          g (x-z) • (atTime K (Module.finrank ℝ V+j) (A (x-z)) z-
            atTime K (Module.finrank ℝ V+j) (B (x-z)) z) := by module
      rw [hd]
      apply (norm_add_le _ _).trans
      simp only [norm_smul]
      have hf : ‖f (x-z)-g (x-z)‖ ≤ ‖f-g‖ := (f-g).norm_coe_le_norm _
      have ha : ‖A (x-z)-B (x-z)‖ ≤ ‖A-B‖ := (A-B).norm_coe_le_norm _
      have h1 := mul_le_mul hf (hPb _ (hA (x-z)) z) (norm_nonneg _) (norm_nonneg _)
      have h2 := mul_le_mul (g.norm_coe_le_norm (x-z)) ((hQb _ (hA (x-z)) _ (hB (x-z)) z).trans
        (mul_le_mul_of_nonneg_left ha (hQp z))) (norm_nonneg _) (norm_nonneg _)
      simpa only [Pi.add_apply,mul_assoc,mul_comm,mul_left_comm] using add_le_add h1 h2
    _ = _ := by rw [integral_add (hP.mul_const _) ((hQ.mul_const _).mul_const _),
        integral_mul_const,integral_mul_const,integral_mul_const]

lemma continuous_value (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0 < α)
    (A : V →ᵇ ℝ) (hAr : ∀ y, A y ∈ Icc α β) (f : V →ᵇ ℂ) :
    Continuous (value K A 1 f j) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_value K A A.continuous α β hα hAr 1 zero_lt_one f j x).continuousAt

def bcf (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0 < α)
    (A : V →ᵇ ℝ) (hAr : ∀ y, A y ∈ Icc α β) (f : V →ᵇ ℂ) : V →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (value K A 1 f j)
    (continuous_value K j α β hα A hAr f)
    (‖f‖*(exists_norm_bound K j α β hα).choose)
    (fun x => by simpa only [inv_one,one_pow,one_mul] using
      (exists_norm_bound K j α β hα).choose_spec.2 A A.continuous hAr 1 zero_lt_one f x)

lemma bcf_apply (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0 < α)
    (A : V →ᵇ ℝ) (hAr : ∀ y, A y ∈ Icc α β) (f : V →ᵇ ℂ) (x : V) :
    bcf K j α β hα A hAr f x = value K A 1 f j x := rfl

lemma continuousAt_of_value {X : Type*} [TopologicalSpace X]
    (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0 < α)
    (A : X → V →ᵇ ℝ) (f : X → V →ᵇ ℂ) (R : X → V →ᵇ E) (p : X)
    (hA : ContinuousAt A p) (hf : ContinuousAt f p)
    (hAr : ∀ᶠ q in 𝓝 p, ∀ y, A q y ∈ Icc α β)
    (he : ∀ᶠ q in 𝓝 p, ∀ x, R q x = value K (A q) 1 (f q) j x) :
    ContinuousAt R p := by
  obtain ⟨C,D,hC,hD,hb⟩ := exists_norm_difference_bound K j α β hα
  have hAp := hAr.self_of_nhds
  have hep := he.self_of_nhds
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun q => norm_nonneg (R q-R p)))
  · filter_upwards [hAr,he] with q hq heq
    apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ C*‖f q-f p‖+D*‖f p‖*‖A q-A p‖)).mpr
    intro x
    change ‖R q x-R p x‖ ≤ _
    rw [heq,hep]
    exact hb (A q) (A p) hq hAp (f q) (f p) x
  · have hh : ContinuousAt (fun q => C*‖f q-f p‖+D*‖f p‖*‖A q-A p‖) p :=
      (continuousAt_const.mul ((hf.sub continuousAt_const).norm)).add
        (continuousAt_const.mul ((hA.sub continuousAt_const).norm))
    simpa using hh.tendsto
end SourceFrozenOrder

namespace SourceFrozenRows
open SourceFrozenOrder
variable {V : Type} [NormedAddCommGroup V]
variable {α β : ℝ}

def realCoefficient (a : V →ᵇ Icc α β) : V →ᵇ ℝ :=
  a.comp Subtype.val isometry_subtype_coe.lipschitzWith

lemma continuous_realCoefficient : Continuous (realCoefficient (V := V) (α := α) (β := β)) :=
  BoundedContinuousFunction.continuous_comp isometry_subtype_coe.lipschitzWith

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma row_eq_order_scaled (K : SchwartzMap V ℂ) (a : V →ᵇ Icc α β)
    (hα : 0 < α) (q : ℝ) (hq : 0 < q) (f : V →ᵇ ℂ) (j : ℕ) :
    row K (fun y => (a y).val) (q^(1/4 : ℝ)) f j =
      SourceFrozenOrder.value (SchwartzDerivatives.iterated K j) (q • realCoefficient a) 1 f j := by
  unfold row SourceFrozenOrder.value
  congr 1
  funext y
  change q^(1/4 : ℝ)*(a y).val^(1/4 : ℝ) = 1*(q*(a y).val)^(1/4 : ℝ)
  rw [one_mul,Real.mul_rpow hq.le (hα.trans_le (a y).property.1).le]

def timeBCF (K : SchwartzMap V ℂ) (hα : 0 < α) (a : V →ᵇ Icc α β)
    (q : ℝ) (hq : 0 < q) (f : V →ᵇ ℂ) (j : ℕ) : V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  SourceFrozenOrder.bcf (SchwartzDerivatives.iterated K j) j (q*α) (q*β)
    (mul_pos hq hα) (q • realCoefficient a)
    (fun y => ⟨mul_le_mul_of_nonneg_left (a y).property.1 hq.le,
      mul_le_mul_of_nonneg_left (a y).property.2 hq.le⟩) f

lemma timeBCF_apply (K : SchwartzMap V ℂ) (hα : 0 < α) (a : V →ᵇ Icc α β)
    (q : ℝ) (hq : 0 < q) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    timeBCF K hα a q hq f j x = row K (fun y => (a y).val) (q^(1/4 : ℝ)) f j x := by
  rw [row_eq_order_scaled K a hα q hq f j]
  rfl

lemma continuous_timeBCF {X : Type*} [TopologicalSpace X]
    (K : SchwartzMap V ℂ) (hα : 0 < α) (a : X → V →ᵇ Icc α β)
    (q : X → ℝ) (hq : ∀ p, 0 < q p) (f : X → V →ᵇ ℂ) (j : ℕ)
    (ha : Continuous a) (hc : Continuous q) (hf : Continuous f) :
    Continuous (fun p => timeBCF K hα (a p) (q p) (hq p) (f p) j) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let lo := q p/2*α
  let hi := (q p+1)*β
  have haβ : 0 < β := hα.trans_le ((a p 0).property.1.trans (a p 0).property.2)
  apply SourceFrozenOrder.continuousAt_of_value
    (SchwartzDerivatives.iterated K j) j lo hi (mul_pos (half_pos (hq p)) hα)
    (fun r => q r • realCoefficient (a r)) f _ p
    ((hc.smul (continuous_realCoefficient.comp ha)).continuousAt) hf.continuousAt
  · filter_upwards [hc.continuousAt (Ioo_mem_nhds (by linarith [hq p] : q p/2<q p)
      (by linarith : q p<q p+1))] with r hr
    intro y
    change q r*(a r y).val ∈ Icc lo hi
    exact ⟨(mul_le_mul_of_nonneg_right hr.1.le hα.le).trans
        (mul_le_mul_of_nonneg_left (a r y).property.1 (hq r).le),
      (mul_le_mul_of_nonneg_left (a r y).property.2 (hq r).le).trans
        (mul_le_mul_of_nonneg_right hr.2.le haβ.le)⟩
  · exact Eventually.of_forall (fun _ _ => rfl)
end SourceFrozenRows

end

end OAI
