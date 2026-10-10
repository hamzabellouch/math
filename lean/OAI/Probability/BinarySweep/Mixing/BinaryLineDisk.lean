import Mathlib
import OAI.Probability.BinarySweep.Processes.PointMassOne
import OAI.Probability.BinarySweep.Analytic.FiniteAverageGap

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

def complexLineLaw (d : ℕ) (z : ℂ) (g : Equiv.Perm (Slot d)) : ℂ :=
  (1-z)*(uniformLaw (Equiv.Perm (Slot d)) g:ℂ)+z*(binaryLaw d g:ℂ)

lemma complexLineLaw_real (d : ℕ) (z : ℝ) (g : Equiv.Perm (Slot d)) :
    complexLineLaw d (z:ℂ) g=(lineLaw d z g:ℂ) := by
  simp [complexLineLaw,lineLaw]

lemma complexLine_average {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Slot d)) V)
    (z : ℂ) : complexAverage ρ (complexLineLaw d z)=
      complexAverage ρ (fun g => (uniformLaw (Equiv.Perm (Slot d)) g:ℂ))+
        z • (complexAverage ρ (fun g => (binaryLaw d g:ℂ))-
          complexAverage ρ (fun g => (uniformLaw (Equiv.Perm (Slot d)) g:ℂ))) := by
  ext v
  simp only [complexAverage_apply,complexLineLaw,add_smul,mul_smul,
    Finset.sum_add_distrib,←Finset.smul_sum,add_apply,
    smul_apply,sub_apply]
  module

theorem binary_line_disk (d : ℕ) : ∃ R : ℝ, 1<R ∧
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖≤R →
        ‖complexAverage ρ (complexLineLaw d z)‖ ≤ 1 := by
  have he : ∀ᶠ n in Filter.atTop,
      totalVariation (sweepLaw d n) (uniformLaw (Equiv.Perm (Slot d)))<1/4 :=
    (fixed_dimension_sweep_convergence d).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  have ht := (hN (max N 1) (le_max_left _ _)).le
  have hp : IsProbability (binaryLaw d) :=
    ⟨finiteLaw_nonneg _,finiteLaw_sum _⟩
  have hp1 : 0<binaryLaw d 1 := by
    rw [binaryLaw,←binarySweep_zero d]
    exact finiteLaw_pos_of_mem _ _
  obtain ⟨R,hR,h⟩ := finite_average_disk hp hp1 (by omega : 0 < max N 1) ht
  refine ⟨R,hR,?_⟩
  intro V _ _ _ ρ hρ z hz
  rw [complexLine_average]
  exact h V ρ hρ z hz

theorem binary_lines_disk (m : ℕ) : ∃ R : ℝ, 1<R ∧ ∀ d, d ≤ m →
    ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Slot d)) V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖≤R →
        ‖complexAverage ρ (complexLineLaw d z)‖ ≤ 1 := by
  induction m with
  | zero =>
    obtain ⟨R,hR,h⟩ := binary_line_disk 0
    refine ⟨R,hR,?_⟩
    intro d hd
    have : d=0 := by omega
    subst d
    exact h
  | succ m ih =>
    obtain ⟨R,hR,h⟩ := ih
    obtain ⟨S,hS,k⟩ := binary_line_disk (m+1)
    refine ⟨min R S,lt_min hR hS,?_⟩
    intro d hd V _ _ _ ρ hρ z hz
    by_cases he : d=m+1
    · subst d
      exact k V ρ hρ z (hz.trans (min_le_right _ _))
    · exact h d (by omega) V ρ hρ z (hz.trans (min_le_left _ _))

end BinaryCoordinateSweeps

end

end OAI
