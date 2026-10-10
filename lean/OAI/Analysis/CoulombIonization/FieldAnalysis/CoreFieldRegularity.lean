import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CorePriceExcess
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchTF
import OAI.Analysis.CoulombIonization.Variational.PatchMeasurable

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoreFieldRegularity_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma coreCoulombAt_nonneg {N : ℕ} (ψ : FormVector N) (z : Space) :
    0 ≤ coreCoulombAt ψ z := by
  apply Finset.sum_nonneg
  intro s _
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg (fun x => div_nonneg (sq_nonneg _) (norm_nonneg _))

lemma coreCoulombTerm_measurable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (s : Spins N) (i : Fin N) :
    Measurable (fun z : Space => ∫ x, ‖ψ.value s x‖^2/‖x i-z‖) := by
  let h := (hψ.1 s).aestronglyMeasurable
  let v := h.mk (ψ.value s)
  have hv : Measurable v := h.stronglyMeasurable_mk.measurable
  have hm : StronglyMeasurable (fun q : Space × Configuration N => ‖v q.2‖^2/‖q.2 i-q.1‖) :=
    (((hv.comp measurable_snd).norm.pow_const 2).div (by fun_prop)).stronglyMeasurable
  have hh : Measurable (fun z : Space => ∫ x, ‖v x‖^2/‖x i-z‖) := hm.integral_prod_right.measurable
  convert hh using 1
  funext z
  apply integral_congr_ae
  filter_upwards [h.ae_eq_mk] with x hx
  rw [hx]

lemma coreCoulombAt_measurable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ) :
    Measurable (coreCoulombAt ψ) :=
  Finset.measurable_sum _ (fun s _ => Finset.measurable_sum _ (fun i _ => coreCoulombTerm_measurable hψ s i))

lemma normalizedCoreField_measurable {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (Z lam : ℝ) : Measurable (normalizedCoreField Z lam ψ) :=
  (((measurable_const.div continuous_norm.measurable).sub
    (coreCoulombAt_measurable hψ)).div_const _).sub_const _

lemma coreCoulombTerm_le_separated {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    {d : ℝ} (hd : 0 < d) (z : Space) (hsep : ∀ a ∈ A, d ≤ ‖a-z‖)
    (s : Spins N) (i : Fin N) :
    (∫ x, ‖ψ.value s x‖^2/‖x i-z‖) ≤ (∫ x, ‖ψ.value s x‖^2)/d := by
  rw [←integral_div]
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (norm_nonneg _)
  · exact ((hψ.1 s).integrable_norm_pow (by decide)).div_const d
  · apply Eventually.of_forall
    intro x
    dsimp only
    by_cases hi : x i ∈ A
    · exact div_le_div_of_nonneg_left (sq_nonneg _) hd (hsep _ hi)
    · rw [(hc x i hi s).1]
      simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]

lemma coreCoulombAt_le_separated {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    {d : ℝ} (hd : 0 < d) (z : Space) (hsep : ∀ a ∈ A, d ≤ ‖a-z‖) :
    coreCoulombAt ψ z ≤ N*formMass ψ/d := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => coreCoulombTerm_le_separated hψ A hc hd z hsep s i))
  simpa only [coreCoulombAt,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ←mul_div_assoc,←Finset.sum_div,←Finset.mul_sum,formMass] using hh

lemma normalizedCoreField_abs_le {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    {d : ℝ} (hd : 0 < d) (z : Space) (hsep : ∀ a ∈ A, d ≤ ‖a-z‖)
    {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z‖) (Z lam : ℝ) :
    |normalizedCoreField Z lam ψ z| ≤ |Z|/r+|lam|+N/d := by
  by_cases hm : formMass ψ = 0
  · simp only [normalizedCoreField,hm,mul_zero,zero_div,zero_sub,div_zero,abs_neg]
    have : 0 ≤ (N:ℝ)/d := div_nonneg (Nat.cast_nonneg _) hd.le
    have : 0 ≤ |Z|/r := div_nonneg (abs_nonneg _) hr.le
    linarith
  · have hmass : 0 < formMass ψ := lt_of_le_of_ne (formMass_nonneg ψ) (Ne.symm hm)
    have hn := coreCoulombAt_nonneg ψ z
    have hu := coreCoulombAt_le_separated hψ A hc hd z hsep
    have he : normalizedCoreField Z lam ψ z = Z/‖z‖-coreCoulombAt ψ z/formMass ψ-lam := by
      unfold normalizedCoreField
      field_simp
    rw [he]
    have hab := abs_sub (Z/‖z‖-coreCoulombAt ψ z/formMass ψ) lam
    have hab' := abs_sub (Z/‖z‖) (coreCoulombAt ψ z/formMass ψ)
    have hZ : |Z/‖z‖| ≤ |Z|/r := by
      rw [abs_div,abs_of_nonneg (norm_nonneg _)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hr hz
    have hc' : |coreCoulombAt ψ z/formMass ψ| ≤ N/d := by
      rw [abs_of_nonneg (div_nonneg hn hmass.le)]
      apply (div_le_iff₀ hmass).mpr
      simpa only [mul_div_assoc, mul_comm (formMass ψ), div_mul_eq_mul_div] using hu
    linarith

open CoulombAnalysis

lemma normalizedCoreField_memLp_patch {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (A : Set Space) (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ) :
    MemLp (fun x => normalizedCoreField Z lam ψ (y+x)) (5/2) (ballMeasure R) := by
  apply MemLp.of_bound
    (((normalizedCoreField_measurable hψ Z lam).comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    (|Z|/r+|lam|+N/d)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hz : y+x ∈ closedBall y R := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using
      (show ‖x‖ ≤ R from (by simpa only [mem_ball,dist_eq_norm,sub_zero] using hx : ‖x‖ < R).le)
  rw [Real.norm_eq_abs]
  exact normalizedCoreField_abs_le hψ A hc hd (y+x) (fun a ha => hsep a ha _ hz)
    hr (hnuc _ hz) Z lam

end Work_CoreFieldRegularity_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

open CoulombAnalysis

lemma coreSlice_field_measurable_rep {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) :
    ∃ F : Configuration M × Space → ℝ, Measurable F ∧
      ∀ᵐ u : Configuration M, ∀ z : Space,
        F (u,z) = normalizedCoreField Z lam (coreSlice ψ t u) z := by
  let d : Spins N → Configuration N × Configuration M → ℝ :=
    fun s q => ‖ψ.value (joinLists s t) (joinLists q.1 q.2)‖^2
  have hd (s : Spins N) : AEStronglyMeasurable (d s) :=
    (integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq).aestronglyMeasurable
  let v : Spins N → Configuration N × Configuration M → ℝ := fun s => (hd s).mk (d s)
  have hv (s : Spins N) : Measurable (v s) := (hd s).stronglyMeasurable_mk.measurable
  have he (s : Spins N) : ∀ᵐ u : Configuration M, ∀ᵐ x : Configuration N,
      d s (x,u) = v s (x,u) := by
    have hh : d s =ᵐ[volume] v s := (hd s).ae_eq_mk
    rw [Measure.volume_eq_prod] at hh
    exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh)
  let m : Configuration M → ℝ := fun u => ∑ s : Spins N, ∫ x : Configuration N, v s (x,u)
  have hm : Measurable m := by
    apply Finset.measurable_sum
    intro s _
    exact (StronglyMeasurable.integral_prod_left (f := fun x u => v s (x,u))
      (hv s).stronglyMeasurable).measurable
  let V : Configuration M × Space → ℝ := fun q =>
    ∑ s : Spins N, ∑ i : Fin N, ∫ x : Configuration N, v s (x,q.1)/‖x i-q.2‖
  have hV : Measurable V := by
    apply Finset.measurable_sum
    intro s _
    apply Finset.measurable_sum
    intro i _
    have hh : Measurable (fun q : (Configuration M × Space) × Configuration N =>
        v s (q.2,q.1.1)/‖q.2 i-q.1.2‖) :=
      ((hv s).comp (measurable_snd.prodMk (measurable_fst.fst))).div (by fun_prop)
    exact hh.stronglyMeasurable.integral_prod_right.measurable
  refine ⟨fun q => (Z*m q.1/‖q.2‖-V q)/m q.1-lam, ?_, ?_⟩
  · exact (((measurable_const.mul (hm.comp measurable_fst)).div
      (continuous_norm.measurable.comp measurable_snd)).sub hV).div
        (hm.comp measurable_fst) |>.sub_const lam
  · filter_upwards [ae_all_iff.mpr he] with u hu
    have hm' : m u = formMass (coreSlice ψ t u) := by
      apply Finset.sum_congr rfl
      intro s _
      apply integral_congr_ae
      filter_upwards [hu s] with x hx
      exact hx.symm
    have hV' (z : Space) : V (u,z) = coreCoulombAt (coreSlice ψ t u) z := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [hu s] with x hx
      exact congrArg (fun a : ℝ => a/‖x i-z‖) hx.symm
    intro z
    rw [hm',hV']
    rfl

local instance : Fact ((5/2:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩

local instance (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

def conditionalPatchField {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : TFField R :=
  toLpOrZero (ballMeasure R) (5/2) (fun u z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)) u

lemma conditionalPatchField_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (conditionalPatchField ψ t Z lam y R) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ t Z lam
  have hm : Measurable (fun q : Configuration M × Space => F (q.1,y+q.2)) :=
    hF.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))
  have hh := measurable_toLpOrZero (μ := ballMeasure R) (p := 5/2)
    (f := fun u z => F (u,y+z)) hm
  apply hh.aemeasurable.congr
  filter_upwards [he] with u hu
  apply toLpOrZero_congr (f := fun u z => F (u,y+z))
    (g := fun u z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z))
  exact ae_of_all _ (fun z => hu (y+z))

lemma conditionalPatchMinimizer_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (fun u => tfPatchMinimizer R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u)) :=
  (tfPatchMinimizer_measurable R tfKinetic tfKinetic_pos).comp_aemeasurable
    (conditionalPatchField_aemeasurable hψ t Z lam y R)

end CoulombAtom

end

end OAI
