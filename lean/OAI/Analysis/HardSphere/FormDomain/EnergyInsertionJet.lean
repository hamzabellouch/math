import Mathlib
import OAI.Analysis.HardSphere.Geometry.IntegralConfigurationCons

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

lemma SmoothMultiplier.energy_insertionJet {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (u : Jet n L) :
    energy (f.insertionJet u)=energy u + ∑ p : Direction (n+1),
      ‖L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L u.1)‖^2 := by
  have hz (j : Fin 3) : (f.insertionJet u).2 (0,j)=
      L2Multiplier.clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1) := by
    change f.insertionScalar 0 + _ = _
    rw [map_zero,zero_add]
    rfl
  have hs (i : Fin n) (j : Fin 3) : ‖(f.insertionJet u).2 (i.succ,j)‖^2=
      ‖u.2 (i,j)‖^2+
      ‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 := by
    change ‖f.insertionScalar (u.2 (i,j)) +
      L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 = _
    rw [@norm_add_sq ℂ, f.insertion_cross_zero (i.succ,j) (ho i j),map_zero,
      mul_zero,add_zero,f.norm_insertionScalar hn]
  unfold energy
  simp only [Fintype.sum_prod_type,Fin.sum_univ_succ,hz,hs,Finset.sum_add_distrib]
  ring

lemma SmoothMultiplier.insertion_derivative_integrable {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) (p : Direction (n+1)) :
    Integrable (fun Y : Configuration n L ↦ ‖u Y‖^2 *
      ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2) volume := by
  have hm := ((memLp_configurationTail (Lp.memLp u)).mul (f.partial_memLp_top p)).integrable_norm_pow
    (by decide : (2:ℕ)≠0)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hm
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero',Function.comp_def,Pi.mul_apply,Fin.tail_cons] at hi
  convert hi.integral_prod_right using 1
  funext Y
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.energy_insertionJet_integral {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (u : Jet n L) :
    energy (f.insertionJet u)=energy u + ∫ Y : Configuration n L,
      ‖u.1 Y‖^2 * ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
  rw [f.energy_insertionJet hn ho]
  simp_rw [norm_weightedTail_sq,Finset.mul_sum]
  rw [integral_finsetSum _ (fun p _ ↦ f.insertion_derivative_integrable u.1 p)]

lemma SmoothMultiplier.energy_insertionJet_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L)
    (hn : ∀ Y : Configuration n L, ∫ x : Torus L, ‖f.toFun (Fin.cons x Y)‖^2=1)
    (ho : ∀ (i : Fin n) (j : Fin 3) (Y : Configuration n L), ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (C : ℝ) (hC : ∀ Y : Configuration n L,
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C)
    (u : Jet n L) : energy (f.insertionJet u)≤energy u + C*‖u.1‖^2 := by
  rw [f.energy_insertionJet_integral hn ho,IndicatorStrong.norm_sq_integral,← integral_const_mul]
  apply add_le_add_right
  apply integral_mono
  · simpa only [Finset.mul_sum] using integrable_finsetSum _
      (fun p _ ↦ f.insertion_derivative_integrable u.1 p)
  · exact (Lp.memLp u.1).integrable_norm_pow (by decide : (2:ℕ)≠0) |>.const_mul C
  · intro Y
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hC Y) (sq_nonneg ‖u.1 Y‖)

end HardSphere

end

end OAI
