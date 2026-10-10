import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletionHardCell
import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletionMixed
import OAI.NumberTheory.Ostmann.Construction.SourcePriorGridDeletionPair

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Ostmann.Construction.SourcePriorGridDeletion

theorem deletionCap_le_two (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (hE : E.card≤2) : deletionCap G E≤2*Real.exp (1-G)/logCellMass G E := by
  unfold deletionCap pointCap
  have hcard : (E.card:ℝ)≤2 := by exact_mod_cast hE
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hcard
    (div_nonneg (Real.exp_pos _).le hZ.le)

theorem deletionCap_eventually_le_one :
    ∀ᶠ G : ℝ in atTop,∀E : Finset ℕ,E.card≤2→
      0<logCellMass G E ∧ deletionCap G E≤1 := by
  have ht : Tendsto (fun G : ℝ => 4*G*Real.exp (1-G)) atTop (𝓝 0) := by
    convert logCell_two_point_error_tendsto.const_mul 2 using 1 <;> ring_nf
  have he := (tendsto_order.mp ht).2 1 (by norm_num)
  filter_upwards [logCell_normalization_eventually,he,eventually_ge_atTop (0:ℝ)]
    with G hZ hsmall hG
  intro E hE
  obtain ⟨hz,hlo,hhi⟩ := hZ E hE
  refine ⟨hz,le_trans ?_ hsmall.le⟩
  calc
    _ ≤ 2*Real.exp (1-G)/logCellMass G E := deletionCap_le_two G E hz hE
    _ = (2*Real.exp (1-G))*(logCellMass G E)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (2*Real.exp (1-G))*(2*G) :=
      mul_le_mul_of_nonneg_left hhi (by positivity)
    _ = _ := by ring

theorem integer_prime_grid_deletion_le_uniform (G : ℝ) (hG : 0≤G)
    (E : Finset ℕ) (hZ : 0<logCellMass G E) (H : ℕ→ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hH : ∀n∈integerPivotCell G,externalPivotWeight G n≠0→
      ∀p∈logCellPrimes G,logCellWeight G p≠0→‖H n p‖≤A) :
    ‖(∑n∈integerPivotCell G,(externalPivotWeight G n:ℂ)*gridMean G E (H n))-
      (∑n∈integerPivotCell G,(externalPivotWeight G n:ℂ)*
        (logCellPrimeSource G E hZ).law.cmean (fun p => H n p))‖≤
      (Real.exp 1+1)*deletionCap G E*A := by
  refine (integer_prime_grid_deletion_le G E hZ H hA hH).trans ?_
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (externalPivotWeight_mass_le hG)
    (mul_nonneg (deletionCap_nonneg G E hZ) hA)

end Ostmann.Construction.SourcePriorGridDeletion

end

end OAI
