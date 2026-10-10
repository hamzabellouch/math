import Mathlib
import OAI.Analysis.HardSphere.FormDomain.Slice

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
open MeasureTheory Filter Set

lemma integrable_comp_insertNth {n : ℕ} {L : Length} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Configuration (n+1) L → E}
    (hF : Integrable F volume) (j : Fin (n+1)) :
    Integrable (fun z : Torus L × Configuration n L ↦ F (j.insertNth z.1 z.2)) (volume.prod volume) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) j
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) j).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Function.comp_def,MeasureTheory.Measure.volume_eq_prod] using hi

lemma integral_configuration_insertNth {n : ℕ} {L : Length} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Configuration (n+1) L → E)
    (hF : Integrable F volume) (j : Fin (n+1)) :
    ∫ X, F X = ∫ x : Torus L, ∫ Y : Configuration n L, F (j.insertNth x Y) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) j).symm
  rw [← he.integral_comp' F]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk]
  exact integral_prod _ (integrable_comp_insertNth hF j)

lemma SmoothTest.slice_norm_sq_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    Integrable (fun x : Torus L ↦ ‖(f.slice j x).jet.1‖^2) volume := by
  simp only [smoothTest_norm_sq,SmoothTest.slice]
  exact (integrable_comp_insertNth (f.memLp.integrable_norm_pow (by decide : (2:ℕ)≠0)) j).integral_prod_left

lemma SmoothTest.integral_slice_norm_sq {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    (∫ x : Torus L, ‖(f.slice j x).jet.1‖^2)=‖f.jet.1‖^2 := by
  simp only [smoothTest_norm_sq,SmoothTest.slice]
  exact (integral_configuration_insertNth _ (f.memLp.integrable_norm_pow (by decide : (2:ℕ)≠0)) j).symm

lemma SmoothTest.slice_partial_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) (p : Direction n) :
    Integrable (fun x : Torus L ↦ ‖(f.slice j x).jet.2 p‖^2) volume := by
  simp only [smoothTest_partial_norm_sq,SmoothTest.slice,coordDerivative_slice]
  exact (integrable_comp_insertNth ((f.partial_memLp (j.succAbove p.1,p.2)).integrable_norm_pow
    (by decide : (2:ℕ)≠0)) j).integral_prod_left

lemma SmoothTest.integral_slice_partial {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) (p : Direction n) :
    (∫ x : Torus L, ‖(f.slice j x).jet.2 p‖^2)=‖f.jet.2 (j.succAbove p.1,p.2)‖^2 := by
  simp only [smoothTest_partial_norm_sq,SmoothTest.slice,coordDerivative_slice]
  exact (integral_configuration_insertNth _ ((f.partial_memLp (j.succAbove p.1,p.2)).integrable_norm_pow
    (by decide : (2:ℕ)≠0)) j).symm

lemma SmoothTest.slice_energy_integrable {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    Integrable (fun x : Torus L ↦ energy (f.slice j x).jet) volume :=
  integrable_finsetSum _ (fun p _ ↦ f.slice_partial_integrable j p)

lemma SmoothTest.integral_slice_energy {n : ℕ} {L : Length} {a : ℝ}
    (f : SmoothTest (n+1) L a) (j : Fin (n+1)) :
    (∫ x : Torus L, energy (f.slice j x).jet)=
      energy f.jet - ∑ q : Fin 3, ‖f.jet.2 (j,q)‖^2 := by
  simp only [energy]
  rw [integral_finsetSum _ (fun p _ ↦ f.slice_partial_integrable j p)]
  simp only [f.integral_slice_partial,Fintype.sum_prod_type]
  rw [Fin.sum_univ_succAbove (fun i : Fin (n+1) ↦ ∑ q : Fin 3, ‖f.jet.2 (i,q)‖^2) j]
  ring

lemma rayleigh_successor {n : ℕ} {L : Length} {a c : ℝ} (hn : 0 < n)
    (h : ∀ u : Jet n L, u∈dirichletDomain n L a → c*(n:ℝ)*‖u.1‖^2≤energy u) :
    ∀ v : Jet (n+1) L, v∈dirichletDomain (n+1) L a → c*((n+1:ℕ):ℝ)*‖v.1‖^2≤energy v := by
  have htest (f : SmoothTest (n+1) L a) : c*((n+1:ℕ):ℝ)*‖f.jet.1‖^2≤energy f.jet := by
    have hi (j : Fin (n+1)) : c*(n:ℝ)*‖f.jet.1‖^2≤energy f.jet-∑ q : Fin 3, ‖f.jet.2 (j,q)‖^2 := by
      have hh := integral_mono ((f.slice_norm_sq_integrable j).const_mul (c*(n:ℝ)))
        (f.slice_energy_integrable j) (fun x ↦ h (f.slice j x).jet (subset_closure ⟨f.slice j x,rfl⟩))
      rw [integral_const_mul,f.integral_slice_norm_sq,f.integral_slice_energy] at hh
      exact hh
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n+1)))) (fun j _ ↦ hi j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Finset.sum_sub_distrib] at hs
    have he : (∑ j : Fin (n+1), ∑ q : Fin 3, ‖f.jet.2 (j,q)‖^2)=energy f.jet := by
      rw [energy,Fintype.sum_prod_type]
    rw [he] at hs
    rw [Nat.cast_add,Nat.cast_one] at hs ⊢
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    nlinarith
  intro v hv
  have hc : IsClosed {v : Jet (n+1) L | c*((n+1:ℕ):ℝ)*‖v.1‖^2≤energy v} := by
    apply isClosed_le
    · exact continuous_const.mul (continuous_fst.norm.pow 2)
    · exact continuous_finsetSum _ (fun p _ ↦ ((continuous_apply p).comp continuous_snd).norm.pow 2)
  exact hc.closure_subset_iff.mpr (by rintro _ ⟨f,rfl⟩; exact htest f) hv

end HardSphere

end

end OAI
