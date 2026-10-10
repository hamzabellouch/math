import Mathlib
import OAI.Analysis.HardSphere.FormDomain.EnergyInsertionJet
import OAI.Analysis.HardSphere.PathBounds.FiberDerivativeMulTailLocal

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

lemma SmoothMultiplier.insertion_mass_integrable {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L) :
    Integrable (fun Y : Configuration n L ↦ ‖u Y‖^2 * f.fiberMass Y) volume := by
  have hm := ((memLp_configurationTail (Lp.memLp u)).mul f.memLp_top).integrable_norm_pow
    (by decide : (2:ℕ)≠0)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hm
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero',Function.comp_def,Pi.mul_apply,Fin.tail_cons] at hi
  convert hi.integral_prod_right using 1
  funext Y
  rw [SmoothMultiplier.fiberMass,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by dsimp only; rw [norm_mul,mul_pow,mul_comm]

lemma SmoothMultiplier.norm_insertionScalar_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hn : ∀ Y, f.fiberMass Y≤1) (u : ScalarL2 n L) :
    ‖f.insertionScalar u‖^2≤‖u‖^2 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    norm_weightedTail_sq,IndicatorStrong.norm_sq_integral]
  exact integral_mono (f.insertion_mass_integrable u)
    ((Lp.memLp u).integrable_norm_pow (by decide : (2:ℕ)≠0))
    (fun Y ↦ mul_le_of_le_one_right (sq_nonneg _) (hn Y))

lemma SmoothMultiplier.norm_insertionScalar_local {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : ScalarL2 n L)
    (hn : ∀ᵐ Y ∂volume, u Y≠0 → f.fiberMass Y=1) :
    ‖f.insertionScalar u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    norm_weightedTail_sq,IndicatorStrong.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hn] with Y hY
  by_cases hz : u Y=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
  · change ‖u Y‖^2*f.fiberMass Y=_
    rw [hY hz,mul_one]

lemma SmoothMultiplier.insertion_cross_zero_local {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (p : Direction (n+1)) (u v : ScalarL2 n L)
    (ho : ∀ᵐ Y ∂volume, v Y≠0 → ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun p (Fin.cons x Y)=0) :
    inner ℂ (f.insertionScalar u)
      (L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L v))=0 := by
  rw [SmoothMultiplier.insertionScalar,ContinuousLinearMap.comp_apply,SmoothMultiplier.onScalar,
    weightedTail_pairing]
  apply integral_eq_zero_of_ae
  filter_upwards [ho] with Y hY
  simp only [Pi.zero_apply]
  by_cases hz : v Y=0
  · rw [hz,mul_zero,zero_mul]
  · rw [hY hz,mul_zero]

lemma SmoothMultiplier.energy_insertionJet_local_le_sum {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : Jet n L)
    (hn : ∀ Y, f.fiberMass Y≤1)
    (ho : ∀ (i : Fin n) (j : Fin 3), ∀ᵐ Y ∂volume, u.1 Y≠0 → ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0) :
    energy (f.insertionJet u)≤energy u + ∑ p : Direction (n+1),
      ‖L2Multiplier.clm _ (f.partial_memLp_top p) (configurationTailCLM n L u.1)‖^2 := by
  have hz (j : Fin 3) : (f.insertionJet u).2 (0,j)=
      L2Multiplier.clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1) := by
    change f.insertionScalar 0 + _ = _
    rw [map_zero,zero_add]
    rfl
  have hs (i : Fin n) (j : Fin 3) : ‖(f.insertionJet u).2 (i.succ,j)‖^2≤
      ‖u.2 (i,j)‖^2+
      ‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 := by
    change ‖f.insertionScalar (u.2 (i,j)) +
      L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2 ≤ _
    rw [@norm_add_sq ℂ, f.insertion_cross_zero_local (i.succ,j) (u.2 (i,j)) u.1 (ho i j),map_zero,
      mul_zero,add_zero]
    exact add_le_add_left (f.norm_insertionScalar_le hn (u.2 (i,j)))
      (‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2)
  simp only [energy,Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ (f := fun i : Fin (n+1) ↦ ∑ j : Fin 3, ‖(f.insertionJet u).2 (i,j)‖^2),
    Fin.sum_univ_succ (f := fun i : Fin (n+1) ↦ ∑ j : Fin 3,
      ‖L2Multiplier.clm _ (f.partial_memLp_top (i,j)) (configurationTailCLM n L u.1)‖^2)]
  simp only [hz]
  calc
    _ ≤ (∑ j : Fin 3, ‖L2Multiplier.clm _ (f.partial_memLp_top (0,j)) (configurationTailCLM n L u.1)‖^2)+
        ∑ i : Fin n, ∑ j : Fin 3, (‖u.2 (i,j)‖^2+
        ‖L2Multiplier.clm _ (f.partial_memLp_top (i.succ,j)) (configurationTailCLM n L u.1)‖^2) := by
      exact add_le_add_right (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hs i j) _
    _ = _ := by simp only [Finset.sum_add_distrib]; ring

lemma SmoothMultiplier.energy_insertionJet_local_le {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (u : Jet n L)
    (hn : ∀ Y, f.fiberMass Y≤1)
    (ho : ∀ (i : Fin n) (j : Fin 3), ∀ᵐ Y ∂volume, u.1 Y≠0 → ∫ x : Torus L,
      conj (f.toFun (Fin.cons x Y))*coordDerivative (n+1) L f.toFun (i.succ,j) (Fin.cons x Y)=0)
    (C : ℝ) (hC : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C) :
    energy (f.insertionJet u)≤energy u+C*‖u.1‖^2 := by
  apply (f.energy_insertionJet_local_le_sum u hn ho).trans
  apply add_le_add_right
  simp_rw [norm_weightedTail_sq]
  rw [← integral_finsetSum _ (fun p _ ↦ f.insertion_derivative_integrable u.1 p),
    IndicatorStrong.norm_sq_integral,← integral_const_mul]
  apply integral_mono_ae
  · exact integrable_finsetSum _ (fun p _ ↦ f.insertion_derivative_integrable u.1 p)
  · exact (Lp.memLp u.1).integrable_norm_pow (by decide : (2:ℕ)≠0) |>.const_mul C
  · filter_upwards [hC] with Y hY
    rw [← Finset.mul_sum]
    by_cases hz : u.1 Y=0
    · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_mul,le_refl]
    · simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hY hz) (sq_nonneg ‖u.1 Y‖)

lemma SmoothMultiplier.insertion_from_raw_local {n : ℕ} {L : Length} {a C z : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hz : 1/2<z)
    {u : Jet n L} (hu : u∈dirichletDomain n L a)
    (hZ : ∀ᵐ Y ∂volume, u.1 Y≠0 → z≤f.fiberMass Y)
    (hC : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C) :
    ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L a ∧
      ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C/z)*‖u.1‖^2 := by
  refine ⟨(f.localNormalization hr).insertionJet u,?_,?_,?_⟩
  · exact (f.localNormalization hr).insertionJet_mem_domain (f.localNormalization_clearance hr hc) hu
  · apply (f.localNormalization hr).norm_insertionScalar_local
    filter_upwards [hZ] with Y hY
    intro hne
    exact f.localNormalization_mass_eq hr Y (hz.le.trans (hY hne))
  · apply (f.localNormalization hr).energy_insertionJet_local_le u (f.localNormalization_mass_le hr)
    · intro i j
      filter_upwards [hZ] with Y hY
      intro hne
      exact (f.localNormalization hr).insertion_orthogonal_local (f.localNormalization_real hr)
        i j Y (f.localNormalization_mass_eventually hr Y (hz.trans_le (hY hne)))
    · filter_upwards [hZ,hC] with Y hY hCY
      intro hne
      have hz0 : 0<z := by linarith
      rw [le_div_iff₀ hz0,mul_comm]
      calc
        z * ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2 ≤
          f.fiberMass Y * ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2 := by
          apply mul_le_mul_of_nonneg_right (hY hne)
          exact Finset.sum_nonneg fun p _ ↦ integral_nonneg fun x ↦ sq_nonneg _
        _ ≤ ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun p _ ↦ f.localNormalization_derivative_le hr p Y (hz.trans_le (hY hne))
        _ ≤ C := hCY hne

end HardSphere

end

end OAI
