import Mathlib
import OAI.Analysis.HardSphere.Geometry.NormSqIntegral
import OAI.Analysis.HardSphere.PathBounds.ConfigurationTailLp

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

lemma integral_configuration_cons {n : ℕ} {L : Length} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Configuration (n+1) L → E)
    (hF : Integrable F volume) :
    ∫ X, F X = ∫ Y : Configuration n L, ∫ x : Torus L, F (Fin.cons x Y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  rw [← he.integral_comp' F]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero', Function.comp_def] at hi ⊢
  exact integral_prod_symm _ hi

lemma coe_weightedTail {n : ℕ} {L : Length} (h : Configuration (n+1) L → ℂ)
    (hh : MemLp h ∞ volume) (u : ScalarL2 n L) :
    L2Multiplier.clm h hh (configurationTailCLM n L u) =ᵐ[volume] fun X ↦ h X*u (Fin.tail X) := by
  filter_upwards [coe_configurationTailCLM u,
    L2Multiplier.coe_clm h hh (configurationTailCLM n L u)] with X h1 h2
  exact h2.trans (by rw [h1])

lemma weightedTail_pairing {n : ℕ} {L : Length}
    (f g : Configuration (n+1) L → ℂ) (hf : MemLp f ∞ volume) (hg : MemLp g ∞ volume)
    (u v : ScalarL2 n L) :
    inner ℂ (L2Multiplier.clm f hf (configurationTailCLM n L u))
      (L2Multiplier.clm g hg (configurationTailCLM n L v)) =
      ∫ Y : Configuration n L, (conj (u Y)*v Y)*
        ∫ x : Torus L, conj (f (Fin.cons x Y))*g (Fin.cons x Y) := by
  have hfm : MemLp (fun X : Configuration (n+1) L ↦ f X*u (Fin.tail X)) 2 volume :=
    hf.mul (memLp_configurationTail (Lp.memLp u))
  have hgm : MemLp (fun X : Configuration (n+1) L ↦ g X*v (Fin.tail X)) 2 volume :=
    hg.mul (memLp_configurationTail (Lp.memLp v))
  have hi : Integrable (fun X : Configuration (n+1) L ↦
      conj (f X*u (Fin.tail X))*(g X*v (Fin.tail X))) volume := by
    have h := (hfm.inner_const (𝕜 := ℂ) (1:ℂ)).integrable_mul hgm
    exact h.congr (Eventually.of_forall fun X ↦ by
      dsimp only [Pi.mul_apply]
      rw [RCLike.inner_apply,one_mul])
  rw [L2.inner_def]
  calc
    _ = ∫ X : Configuration (n+1) L, conj (f X*u (Fin.tail X))*(g X*v (Fin.tail X)) := by
      apply integral_congr_ae
      filter_upwards [coe_weightedTail f hf u,coe_weightedTail g hg v] with X h1 h2
      simp only [h1,h2,RCLike.inner_apply']
    _ = ∫ Y : Configuration n L, ∫ x : Torus L,
        conj (f (Fin.cons x Y)*u Y)*(g (Fin.cons x Y)*v Y) := by
      simpa only [Fin.tail_cons] using integral_configuration_cons _ hi
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun Y ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by simp only [map_mul]; ring

lemma norm_weightedTail_sq {n : ℕ} {L : Length}
    (f : Configuration (n+1) L → ℂ) (hf : MemLp f ∞ volume) (u : ScalarL2 n L) :
    ‖L2Multiplier.clm f hf (configurationTailCLM n L u)‖^2 =
      ∫ Y : Configuration n L, ‖u Y‖^2 * ∫ x : Torus L, ‖f (Fin.cons x Y)‖^2 := by
  have hm : MemLp (fun X : Configuration (n+1) L ↦ f X*u (Fin.tail X)) 2 volume :=
    hf.mul (memLp_configurationTail (Lp.memLp u))
  rw [IndicatorStrong.norm_sq_integral]
  calc
    _ = ∫ X : Configuration (n+1) L, ‖f X*u (Fin.tail X)‖^2 := by
      exact integral_congr_ae ((coe_weightedTail f hf u).mono fun _ h ↦ by dsimp only at h ⊢; rw [h])
    _ = ∫ Y : Configuration n L, ∫ x : Torus L, ‖f (Fin.cons x Y)*u Y‖^2 := by
      simpa only [Fin.tail_cons] using integral_configuration_cons _ (hm.integrable_norm_pow (by decide : (2:ℕ)≠0))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun Y ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.norm_insertionScalar_sq {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (u : ScalarL2 n L) : ‖f.insertionScalar u‖^2=‖u‖^2 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    norm_weightedTail_sq,IndicatorStrong.norm_sq_integral]
  simp only [hn,mul_one]

lemma SmoothMultiplier.norm_insertionScalar {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (u : ScalarL2 n L) : ‖f.insertionScalar u‖=‖u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (f.norm_insertionScalar_sq hn u)

lemma SmoothMultiplier.insertion_cross_zero {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (p : Direction (n+1))
    (ho : ∀ Y : Configuration n L, ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun p (Fin.cons x Y)=0)
    (u v : ScalarL2 n L) :
    inner ℂ (f.insertionScalar u)
      (L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L v))=0 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    weightedTail_pairing]
  simp only [ho,mul_zero,integral_zero]

end HardSphere

end

end OAI
