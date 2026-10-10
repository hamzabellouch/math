import OAI.NumberTheory.Ostmann.Dirichlet.SmoothedExplicitInversion

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Dirichlet
open Complex Set
open scoped SchwartzMap

theorem exists_smooth_kernel_bounds (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ s : ℂ, s.re ∈ Icc (1/4:ℝ) 2 → ‖mellin (ρ:ℝ→ℂ) s‖ ≤ C/(1+|s.im|)^A) ∧
      (∀ s : ℂ, s.re ∈ Icc (1/4:ℝ) 2 → ‖mellin (ρ:ℝ→ℂ) s‖ ≤ C) ∧
      (∀ σ ∈ Icc (1/4:ℝ) 2, ∀ t : ℝ,
        (1+|t|)^(A+2)*‖mellin (ρ:ℝ→ℂ) ((σ:ℂ)+t*Complex.I)‖ ≤ C) := by
  obtain ⟨C,hC,hb⟩ := schwartz_mellin_strip_weighted_bound (A+2) ρ (1/4) 2
    (by norm_num) (by norm_num)
  have hdec (s : ℂ) (hs : s.re ∈ Icc (1/4:ℝ) 2) :
      ‖mellin (ρ:ℝ→ℂ) s‖ ≤ C/(1+|s.im|)^A := by
    have h := hb s.re hs s.im
    rw [re_add_im] at h
    have hp : (1+|s.im|)^A ≤ (1+|s.im|)^(A+2) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg s.im]) (by omega)
    apply (le_div_iff₀ (by positivity)).mpr
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans
      (by simpa only [mul_comm] using h)
  refine ⟨C,hC,hdec,?_,hb⟩
  intro s hs
  exact (hdec s hs).trans (div_le_self hC.le (one_le_pow₀ (by linarith [abs_nonneg s.im])))

theorem smooth_kernel_at_height {ρ : 𝓢(ℝ, ℂ)} {A : ℕ} {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 < T)
    (hker : ∀ s : ℂ, s.re ∈ Icc (1/4:ℝ) 2 → ‖mellin (ρ:ℝ→ℂ) s‖ ≤ C/(1+|s.im|)^A)
    {s : ℂ} (hs : s.re ∈ Icc (1/4:ℝ) 2) (him : T ≤ |s.im|) :
    ‖mellin (ρ:ℝ→ℂ) s‖ ≤ C/T^A := by
  apply (hker s hs).trans
  exact div_le_div_of_nonneg_left hC (by positivity)
    (pow_le_pow_left₀ hT.le (by linarith) A)

end Ostmann.Dirichlet

end

end OAI
