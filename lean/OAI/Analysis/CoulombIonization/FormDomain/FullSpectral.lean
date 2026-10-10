import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoulombCoercivity
import OAI.Analysis.CoulombIonization.FormDomain.ShiftedFormBottom
import OAI.Analysis.CoulombIonization.FormDomain.TrialSmoothTest

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

instance fermionSpace_nontrivial (N : ℕ) : Nontrivial (fermionSpace N) := by
  obtain ⟨ψ, hψ⟩ := formDomain_nonempty N
  let x : fermionSpace N := fermionGraphValue N (admissibleGraph ψ hψ)
  have hx : x ≠ 0 := by
    intro hz
    have hn := admissibleGraph_norm ψ hψ
    change ‖x‖ ^ 2 = 1 at hn
    simp [hz] at hn
  exact ⟨⟨x, 0, hx⟩⟩

def coulombResolvent (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    fermionSpace N →L[ℂ] fermionSpace N :=
  formResolvent (fermionGraphValue N) (shiftedCoulombFormOperator Z N)
    (by norm_num : (0 : ℝ) < 1 / 4) (shiftedCoulombFormOperator_coercive hZ N)

def coulombHamiltonian (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    fermionSpace N →ₗ.[ℂ] fermionSpace N :=
  inverseShift (coulombResolvent Z hZ N) ((N : ℝ) * Z ^ 2 + 1)

lemma coulombResolvent_injective (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    Function.Injective (coulombResolvent Z hZ N) :=
  formResolvent_injective (fermionGraphValue N) (fermionGraphValue_injective N)
    (fermionGraphValue_denseRange N) _ _ _

lemma coulombResolvent_selfAdjoint (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    IsSelfAdjoint (coulombResolvent Z hZ N) :=
  formResolvent_selfAdjoint (fermionGraphValue N) (shiftedCoulombFormOperator Z N)
    (shiftedCoulombFormOperator_selfAdjoint Z N) _ _

theorem coulombHamiltonian_selfAdjoint (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    IsSelfAdjoint (coulombHamiltonian Z hZ N) :=
  inverseShift_selfAdjoint _ (coulombResolvent_selfAdjoint Z hZ N)
    (coulombResolvent_injective Z hZ N) _

lemma shiftedCoulombFormOperator_pair (Z : ℝ) (N : ℕ) (F G : fermionGraph N) :
    ⟪G, shiftedCoulombFormOperator Z N F⟫_ℂ =
      ⟪G, coulombFormOperator Z N F⟫_ℂ +
        ((((N : ℝ) * Z ^ 2 + 1) : ℝ) : ℂ) * ⟪fermionGraphValue N G, fermionGraphValue N F⟫_ℂ := by
  simp only [shiftedCoulombFormOperator, add_apply, smul_apply, inner_add_right,
    inner_smul_right, ContinuousLinearMap.comp_apply, (fermionGraphValue N).adjoint_inner_right, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one]

theorem coulombHamiltonian_graph (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ)
    (x y : fermionSpace N) :
    (x, y) ∈ (coulombHamiltonian Z hZ N).graph ↔
      ∃ F : fermionGraph N, fermionGraphValue N F = x ∧
        ∀ G : fermionGraph N, ⟪G, coulombFormOperator Z N F⟫_ℂ =
          ⟪fermionGraphValue N G, y⟫_ℂ := by
  exact shifted_representedOperator_graph (fermionGraphValue N)
    (fermionGraphValue_injective N) (fermionGraphValue_denseRange N)
    (shiftedCoulombFormOperator Z N) (coulombFormOperator Z N) _
    (shiftedCoulombFormOperator_pair Z N) _ (shiftedCoulombFormOperator_coercive hZ N) x y

def spectralEnergy (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) : ℝ :=
  sInf {r : ℝ | (r : ℂ) ∈ unboundedSpectrum (coulombHamiltonian Z hZ N)}

theorem coulombHamiltonian_spectrum_real (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) {z : ℂ}
    (hz : z ∈ unboundedSpectrum (coulombHamiltonian Z hZ N)) : z.im = 0 :=
  inverseShift_spectrum_real _ (coulombResolvent_selfAdjoint Z hZ N)
    (coulombResolvent_injective Z hZ N) _ hz

theorem spectralEnergy_eq_energy (Z : ℝ) (hZ : 0 ≤ Z) (N : ℕ) :
    spectralEnergy Z hZ N = energy Z N := by
  unfold spectralEnergy coulombHamiltonian coulombResolvent
  rw [shifted_form_spectral_infimum _ (fermionGraphValue_injective N)
    (fermionGraphValue_denseRange N) _ (shiftedCoulombFormOperator_selfAdjoint Z N)]
  have he : {e : ℝ | ∃ F : fermionGraph N, ‖fermionGraphValue N F‖ ^ 2 = 1 ∧
      (⟪F, shiftedCoulombFormOperator Z N F⟫_ℂ).re - ((N : ℝ) * Z ^ 2 + 1) = e} =
      {e : ℝ | ∃ F : fermionGraph N, ‖fermionGraphValue N F‖ ^ 2 = 1 ∧
        (⟪F, coulombFormOperator Z N F⟫_ℂ).re = e} := by
    ext e
    constructor
    · rintro ⟨F, hF, he⟩
      refine ⟨F, hF, ?_⟩
      simpa only [shiftedCoulombFormOperator_inner, hF, mul_one, add_sub_cancel_right] using he
    · rintro ⟨F, hF, he⟩
      refine ⟨F, hF, ?_⟩
      simpa only [shiftedCoulombFormOperator_inner, hF, mul_one, add_sub_cancel_right] using he
  rw [he, ← full_form_value_set]
  unfold energy
  split_ifs with hN
  · subst N
    have hz : {e : ℝ | ∃ ψ : FormVector 0, FormAdmissible ψ ∧ formEnergy Z ψ = e} = {0} := by
      ext e
      constructor
      · rintro ⟨ψ, _, he⟩
        simpa only [formEnergy, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero,
          add_zero, Finset.sum_const_zero, Set.mem_singleton_iff] using he.symm
      · intro he
        obtain ⟨ψ, hψ⟩ := formDomain_nonempty 0
        refine ⟨ψ, hψ, ?_⟩
        simpa [formEnergy] using he.symm
    rw [hz, csInf_singleton]
  · rfl

end CoulombAtom

end

end OAI
