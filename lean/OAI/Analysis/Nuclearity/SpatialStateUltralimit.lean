import OAI.Analysis.TracialSplitting.Model
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Ultralimits of unit-vector states. This supplies the compactness step
after the finite spatial approximations, without claiming normality of the
limiting state or continuity of a nonnormal expectation. -/

noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def spatialStateUltraValue (U : Ultrafilter ι) (ξ : ι → H) (T : H →L[ℂ] H) : ℂ :=
  limUnder (U : Filter ι) (fun i => inner ℂ (ξ i) (T (ξ i)))

lemma spatialStateUltraValue_tendsto (U : Ultrafilter ι) (ξ : ι → H)
    (hξ : ∀ i, ‖ξ i‖ = 1) (T : H →L[ℂ] H) :
    Tendsto (fun i => inner ℂ (ξ i) (T (ξ i))) (U : Filter ι)
      (𝓝 (spatialStateUltraValue U ξ T)) := by
  apply CurrentMain.bounded_ultrafilter_tendsto U _ ‖T‖
  intro i
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [hξ i, one_mul, mul_one] using T.le_opNorm (ξ i))

def spatialStateUltra (U : Ultrafilter ι) (ξ : ι → H) (hξ : ∀ i, ‖ξ i‖ = 1) :
    (H →L[ℂ] H) →ₚ[ℂ] ℂ where
  toFun := spatialStateUltraValue U ξ
  map_add' S T := by
    apply tendsto_nhds_unique (spatialStateUltraValue_tendsto U ξ hξ (S + T))
    simpa only [add_apply, inner_add_right] using
      (spatialStateUltraValue_tendsto U ξ hξ S).add
        (spatialStateUltraValue_tendsto U ξ hξ T)
  map_smul' c T := by
    apply tendsto_nhds_unique (spatialStateUltraValue_tendsto U ξ hξ (c • T))
    simpa only [smul_apply, inner_smul_right, smul_eq_mul, RingHom.id_apply] using
      (spatialStateUltraValue_tendsto U ξ hξ T).const_mul c
  monotone' := by
    intro S T hST
    apply le_of_tendsto_of_tendsto
      (spatialStateUltraValue_tendsto U ξ hξ S)
      (spatialStateUltraValue_tendsto U ξ hξ T)
    apply Eventually.of_forall
    intro i
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hST)).inner_nonneg_right (ξ i)
    simpa only [sub_apply, inner_sub_right, sub_nonneg] using hp

@[simp] lemma spatialStateUltra_one (U : Ultrafilter ι) (ξ : ι → H)
    (hξ : ∀ i, ‖ξ i‖ = 1) : spatialStateUltra U ξ hξ 1 = 1 := by
  apply tendsto_nhds_unique (spatialStateUltraValue_tendsto U ξ hξ 1)
  convert (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℂ)) (U : Filter ι) (𝓝 1)) using 1
  ext i
  simp only [one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ i, one_pow, RCLike.ofReal_one]

lemma spatialStateUltra_norm_apply_le (U : Ultrafilter ι) (ξ : ι → H)
    (hξ : ∀ i, ‖ξ i‖ = 1) (T : H →L[ℂ] H) :
    ‖spatialStateUltra U ξ hξ T‖ ≤ ‖T‖ := by
  apply le_of_tendsto (spatialStateUltraValue_tendsto U ξ hξ T).norm
  apply Eventually.of_forall
  intro i
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [hξ i, one_mul, mul_one] using T.le_opNorm (ξ i))

lemma spatialStateUltra_eq_of_tendsto (U : Ultrafilter ι) (ξ : ι → H)
    (hξ : ∀ i, ‖ξ i‖ = 1) (T : H →L[ℂ] H) (c : ℂ)
    (hc : Tendsto (fun i => inner ℂ (ξ i) (T (ξ i))) (U : Filter ι) (𝓝 c)) :
    spatialStateUltra U ξ hξ T = c :=
  tendsto_nhds_unique (spatialStateUltraValue_tendsto U ξ hξ T) hc

/-- Compactness for finite unit-vector approximations. The limit is a state,
but need not be normal. In particular, this construction makes no continuity
claim about an expectation in the weak operator topology. -/
theorem exists_spatial_state_of_finite_approximation {κ : Type*}
    (T : κ → (H →L[ℂ] H)) (c : κ → ℂ)
    (h : ∀ (s : Finset κ) (ε : ℝ), 0 < ε →
      ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ k ∈ s, ‖inner ℂ ξ (T k ξ) - c k‖ < ε) :
    ∃ φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ, φ 1 = 1 ∧ ∀ k, φ (T k) = c k := by
  classical
  let I := Finset κ × ℕ
  have hex (i : I) : ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ k ∈ i.1,
      ‖inner ℂ ξ (T k ξ) - c k‖ < 1 / ((i.2 : ℝ) + 1) :=
    h i.1 _ (by positivity)
  choose ξ hξ he using hex
  let U := Ultrafilter.of (atTop : Filter I)
  refine ⟨spatialStateUltra U ξ hξ, spatialStateUltra_one U ξ hξ, ?_⟩
  intro k
  apply spatialStateUltra_eq_of_tendsto
  apply Filter.Tendsto.mono_left ?_ (Ultrafilter.of_le (atTop : Filter I))
  have hfst : Tendsto (fun i : I => i.1) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (fun i : I => i.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hδ : Tendsto (fun i : I => 1 / ((i.2 : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hfst.eventually (eventually_finset_mem_atTop k),
    hδ.eventually (gt_mem_nhds hε)] with i hik hiε
  simpa only [dist_eq_norm] using (he i k hik).trans hiε

end WeakPureInfiniteness

end

end OAI
