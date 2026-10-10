import Mathlib

namespace OAI

section
noncomputable section
open Function

namespace CriticalPercolation.LinearGrowth
variable {K V G : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V] [Group G]

lemma equiv_eigenvalue_ne_zero (T : V ≃L[K] V) {v : V} (hv : v≠0) {a : K}
    (he : T v=a • v) : a≠0 := by
  intro ha
  apply hv
  apply T.injective
  simpa only [ha,zero_smul,map_zero] using he

lemma representation_pow_eigenvector (ρ : G →* (V ≃L[K] V)) (g : G)
    {v : V} {a : K} (he : ρ g v=a • v) (n : ℕ) : ρ (g^n) v=a^n • v := by
  induction n with
  | zero => rw [pow_zero,map_one,pow_zero,one_smul]; rfl
  | succ n ih =>
    rw [pow_succ,map_mul]
    change ρ (g^n) (ρ g v)=_
    rw [he,map_smul,ih,smul_smul]
    congr 1
    rw [pow_succ,mul_comm]

lemma eigenvalue_ratio_norm_le_one (ρ : G →* (V ≃L[K] V))
    (δ : ℝ) (hδ : 0<δ)
    (hb : ∀ g : G, ∀ x : V, δ*‖(ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖)
    (g : G) {v w : V} (hv : v≠0) (hw : w≠0) {a b : K}
    (ha : ρ g v=a • v) (hb' : ρ g w=b • w) : ‖a/b‖≤1 := by
  have hb0 : b≠0 := equiv_eigenvalue_ne_zero _ hw hb'
  have hvp : 0<‖v‖ := norm_pos_iff.mpr hv
  have hwp : 0<‖w‖ := norm_pos_iff.mpr hw
  have hbp : 0<‖b‖ := norm_pos_iff.mpr hb0
  have hpow (n : ℕ) : ‖a/b‖^n≤1/δ := by
    have hu := (ρ (g^n)).toContinuousLinearMap.le_opNorm v
    change ‖ρ (g^n) v‖≤‖(ρ (g^n)).toContinuousLinearMap‖*‖v‖ at hu
    rw [representation_pow_eigenvector ρ g ha n,norm_smul,norm_pow] at hu
    have hu' : ‖a‖^n≤‖(ρ (g^n)).toContinuousLinearMap‖ := (mul_le_mul_iff_left₀ hvp).mp hu
    have hl := hb (g^n) w
    rw [representation_pow_eigenvector ρ g hb' n,norm_smul,norm_pow] at hl
    have hl' : δ*‖(ρ (g^n)).toContinuousLinearMap‖≤‖b‖^n := (mul_le_mul_iff_left₀ hwp).mp hl
    rw [norm_div,div_pow]
    apply (div_le_div_iff₀ (pow_pos hbp n) hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hu' hδ.le]
  by_contra hn
  obtain ⟨n,hn'⟩ := pow_unbounded_of_one_lt (1/δ) (lt_of_not_ge hn)
  exact hn'.not_ge (hpow n)

end CriticalPercolation.LinearGrowth
end
end

end OAI
