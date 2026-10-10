import OAI.MeasureTheory.Falconer.Recursion.RelativeScaleBudget
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionWidths

namespace OAI

/-! # Uniform radial freezing from the integer contact margin -/

namespace Falconer

theorem middle_freeze_bound {b s : ℝ} (hb : 0 < b) (hs : 0 < s)
    {p v : ℕ} (hpv : p ≤ v) (hvp : v ≤ 2*p)
    (hlarge : 1/(2*b*s) ≤ (2:ℝ)^(2*p-v)) :
    (1/2:ℝ)/(b*(2:ℝ)^p*s) ≤ 1/(2:ℝ)^(v-p) := by
  have he : (2:ℝ)^(2*p-v)*(2:ℝ)^(v-p) = (2:ℝ)^p := by
    rw [← pow_add,show 2*p-v+(v-p) = p by omega]
  have hh : (1/2:ℝ) ≤ (2:ℝ)^(2*p-v)*b*s := by
    have h := (div_le_iff₀ (show 0 < 2*b*s by positivity)).mp hlarge
    nlinarith
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  calc
    (1/2:ℝ)*(2:ℝ)^(v-p) ≤ ((2:ℝ)^(2*p-v)*b*s)*(2:ℝ)^(v-p) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = b*(2:ℝ)^p*s := by rw [← he]; ring

theorem eventually_uniform_middle_freeze {b s γ : ℝ}
    (hb : 0 < b) (hs : 0 < s) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p v : ℕ, p ≤ v →
      γ*(N:ℝ) ≤ 2*(p:ℝ)-(v:ℝ) →
      (1/2:ℝ)/(b*(2:ℝ)^p*s) ≤ 1/(2:ℝ)^(v-p) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hγ (1/(2*b*s))
  refine ⟨N₀,fun N hN p v hpv hmargin => ?_⟩
  have hvp : v ≤ 2*p := by
    have hnonneg : 0 ≤ γ*(N:ℝ) := mul_nonneg hγ.le (Nat.cast_nonneg N)
    have hh : (v:ℝ) ≤ (2*p:ℕ) := by push_cast; linarith
    exact_mod_cast hh
  apply middle_freeze_bound hb hs hpv hvp
  apply (hN₀ N hN).trans
  have hh : (N:ℝ)*γ ≤ ((2*p-v:ℕ):ℝ)*1 := by
    rw [Nat.cast_sub hvp]
    push_cast
    nlinarith
  simpa only [Real.rpow_one] using dyadic_relative_scale_bound N (2*p-v) hh

theorem eventually_integer_margin {γ : ℝ} (hγ : 0 < γ) (L : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, γ*(N:ℝ) ≤ (n:ℝ) → L ≤ n := by
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt ((L:ℝ)/γ)
  refine ⟨N₀,fun N hN n hn => ?_⟩
  have hN' : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hL : (L:ℝ) < γ*(N₀:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hN₀
    nlinarith
  have hn' : (L:ℝ) ≤ n := by
    have hh := mul_le_mul_of_nonneg_left hN' hγ.le
    linarith
  exact_mod_cast hn'

theorem middle_width_rounding {b H C : ℝ} (p v J : ℕ) (hpv : p ≤ v)
    (hJ : J ≤ v-p) (hC : b*H*C ≤ (2:ℝ)^J) :
    (b*(2:ℝ)^p*H)*(C/(2:ℝ)^v) ≤ 1/(2:ℝ)^((v-p)-J) := by
  have hv : (2:ℝ)^v = (2:ℝ)^p*(2:ℝ)^(v-p) := by
    rw [← pow_add,Nat.add_sub_of_le hpv]
  have hw : (2:ℝ)^(v-p) = (2:ℝ)^J*(2:ℝ)^((v-p)-J) := by
    rw [← pow_add,Nat.add_sub_of_le hJ]
  calc
    _ = (b*H*C)/(2:ℝ)^(v-p) := by rw [hv]; field_simp
    _ ≤ (2:ℝ)^J/(2:ℝ)^(v-p) := div_le_div_of_nonneg_right hC (by positivity)
    _ = _ := by rw [hw]; field_simp

theorem eventually_contact_middle_depth {γ : ℝ} (hγ : 0 < γ) (J M₀ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ, ∀ Δ : ℝ,
      γ ≤ Δ → Δ*(N:ℝ)-1 ≤ (k:ℝ) →
      M₀ ≤ k-J ∧ (N:ℝ)*Δ ≤ 2*((k-J:ℕ):ℝ) := by
  let L : ℕ := max (J+M₀+1) (2*J+2)
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt ((L:ℝ)/γ)
  refine ⟨N₀,fun N hN k Δ hγΔ hgap => ?_⟩
  have hNN : (N₀:ℝ) ≤ N := by exact_mod_cast hN
  have hlarge : (L:ℝ) < γ*(N:ℝ) := by
    have hh := (div_lt_iff₀ hγ).mp hN₀
    nlinarith
  have hγN : γ*(N:ℝ) ≤ Δ*(N:ℝ) :=
    mul_le_mul_of_nonneg_right hγΔ (Nat.cast_nonneg N)
  have hfirst : J+M₀ ≤ k := by
    have hL : ((J+M₀+1:ℕ):ℝ) ≤ L := by exact_mod_cast le_max_left (J+M₀+1) (2*J+2)
    have hh : ((J+M₀:ℕ):ℝ) ≤ k := by push_cast at hL ⊢; linarith
    exact_mod_cast hh
  have hsecond : 2*J+1 ≤ k := by
    have hL : ((2*J+2:ℕ):ℝ) ≤ L := by exact_mod_cast le_max_right (J+M₀+1) (2*J+2)
    have hh : ((2*J+1:ℕ):ℝ) ≤ k := by push_cast at hL ⊢; linarith
    exact_mod_cast hh
  refine ⟨by omega,?_⟩
  rw [Nat.cast_sub (by omega : J ≤ k)]
  have hh : 2*(J:ℝ)+1 ≤ k := by exact_mod_cast hsecond
  nlinarith

end Falconer

end OAI
