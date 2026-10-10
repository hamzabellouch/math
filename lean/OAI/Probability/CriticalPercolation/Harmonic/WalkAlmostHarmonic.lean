import Mathlib
import OAI.Probability.CriticalPercolation.Growth.WordLengthGeometry
import OAI.Probability.CriticalPercolation.Growth.SparseEnergyRatio
import OAI.Probability.CriticalPercolation.Harmonic.LazyWalkProbability
import OAI.Probability.CriticalPercolation.Harmonic.WalkEnergyLower

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma walkState_energy_antitone : Antitone (fun n => W.walkEnergy (W.walkState n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := W.walkEnergy_dissipation (W.walkState n)
  rw [←W.walkState_succ] at h
  nlinarith [sq_nonneg ‖W.walkState n-W.lazyWalk (W.walkState n)‖]

lemma walk_energy_inverse_sparse [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    ∃ C : ℝ, 0≤C ∧ ∀ R, ∃ m≥R,
      (W.walkEnergy (W.walkState m))⁻¹≤C*(m:ℝ)^(2*d+2) := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨36*(W.generators.card:ℝ)*(C:ℝ)^2,by positivity,?_⟩
  intro R
  obtain ⟨n,hn,hvol⟩ := hC (max R 1)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hnR : R≤n := (le_max_left R 1).trans hn
  refine ⟨2*n,by omega,?_⟩
  have hV : ((W.ball n).card:ℝ)≤(C:ℝ)*(n:ℝ)^d := by exact_mod_cast hvol
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpoly : ((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.generators.card:ℝ)≤
      (36*(W.generators.card:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2) := by
    calc
      _ ≤ ((C:ℝ)*(n:ℝ)^d)^2*(3*(n:ℝ))^2*4*(W.generators.card:ℝ) := by
        gcongr
        linarith
      _ = (36*(W.generators.card:ℝ)*(C:ℝ)^2)*(n:ℝ)^(2*d+2) := by
        rw [pow_add,pow_mul]
        ring
      _ ≤ _ := by
        gcongr
        linarith
  have hb := W.walkState_energy_lower n
  have hh := mul_le_mul_of_nonneg_right hpoly (W.walkState_energy_pos (2*n)).le
  have hf : 1≤((36*(W.generators.card:ℝ)*(C:ℝ)^2)*((2*n:ℕ):ℝ)^(2*d+2))*
      W.walkEnergy (W.walkState (2*n)) := hb.trans hh
  exact (inv_le_iff_one_le_mul₀ (W.walkState_energy_pos (2*n))).mpr hf

theorem exists_walk_small_relative_residual [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) (ε : ℝ) (hε : 0<ε) :
    ∃ n, 0<W.walkEnergy (W.walkState n) ∧
      ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2≤ε*W.walkEnergy (W.walkState n) := by
  obtain ⟨C,hC,hpoly⟩ := W.walk_energy_inverse_sparse d hg
  obtain ⟨n,hn⟩ := exists_small_relative_dissipation
    (fun n => W.walkEnergy (W.walkState n))
    (fun n => ‖W.walkState n-W.lazyWalk (W.walkState n)‖^2)
    W.walkState_energy_pos W.walkState_energy_antitone
    (fun n => by simpa only [W.walkState_succ] using W.walkEnergy_dissipation (W.walkState n))
    (2*d+2) C hC hpoly ε hε
  exact ⟨n,W.walkState_energy_pos n,hn⟩

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
