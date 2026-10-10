import OAI.Geometry.RCD.Heat.GaussianBridgeTail

namespace OAI

/-! # A uniform Gaussian bound for a normalized heat-kernel bridge -/

noncomputable section
namespace RegularPointCoordinates

theorem gaussian_bridge_kernel_bound (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {A a B c s t d E u v w : ℝ},
      0 ≤ A → 0 < a → 0 < c → c ≤ 1 → 0 < s → 0 < t → s ≤ c → t ≤ c →
      1 ≤ d → 20*E ≤ d^2 → 0 ≤ v →
      u ≤ A*(Real.sqrt s)⁻¹^n*Real.exp (-d^2/(20*s)+B) →
      v ≤ A*(Real.sqrt t)⁻¹^n*Real.exp (-d^2/(20*t)+B) →
      a*Real.exp (-E/c) ≤ w →
      u*v ≤ (A^2/a*Real.exp (2*B)*C^2)*Real.exp (-d^2/40)*w := by
  obtain ⟨C,hC,htail⟩ := gaussian_bridge_tail n
  refine ⟨C,hC,?_⟩
  intro A a B c s t d E u v w hA ha hc hc1 hs ht hsc htc hd hE hv hu hvb hw
  have hprod := mul_le_mul hu hvb hv (by positivity)
  have he := htail hc hc1 hs ht hsc htc hd hE
  have hup : u*v*Real.exp (E/c) ≤ (A^2*Real.exp (2*B))*
      (((Real.sqrt s)⁻¹^n*Real.exp (-d^2/(20*s)))*
        ((Real.sqrt t)⁻¹^n*Real.exp (-d^2/(20*t)))*Real.exp (E/c)) := by
    calc
      _ ≤ (A*(Real.sqrt s)⁻¹^n*Real.exp (-d^2/(20*s)+B))*
          (A*(Real.sqrt t)⁻¹^n*Real.exp (-d^2/(20*t)+B))*Real.exp (E/c) :=
        mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = _ := by
        rw [show 2*B=B+B by ring]
        simp only [Real.exp_add]
        ring
  have hb : u*v*Real.exp (E/c) ≤
      (A^2*Real.exp (2*B))*(C^2*Real.exp (-d^2/40)) :=
    hup.trans (mul_le_mul_of_nonneg_left he (by positivity))
  calc
    u*v = (u*v*Real.exp (E/c))*Real.exp (-E/c) := by
      rw [show -E/c=-(E/c) by ring,Real.exp_neg]
      field_simp
    _ ≤ ((A^2*Real.exp (2*B))*(C^2*Real.exp (-d^2/40)))*Real.exp (-E/c) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = ((A^2/a*Real.exp (2*B)*C^2)*Real.exp (-d^2/40))*(a*Real.exp (-E/c)) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

end RegularPointCoordinates

end

end OAI
