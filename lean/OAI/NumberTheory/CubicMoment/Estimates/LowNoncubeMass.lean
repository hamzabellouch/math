import OAI.NumberTheory.CubicMoment.Estimates.LowCoreSupport

namespace OAI

/-! The actual finite low-noncube frequency mass follows from the raw
published prime estimate, with its cube multiplicity proved by lattice count. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem low_noncube_mass
    (hSW : KummerPrimeSiegelWalfisz) {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c d₁ d₂ R : ℝ} (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    (hR : 1 ≤ R) (a k U : ℕ) (ha : 0 < a) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      L₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) → 0 ≤ J → J ≤ (L r)^d₂ →
      H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ (L r)^d₁ → ∀ u : ℝ,
      |u| ≤ (1+Real.log (L r))^U →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 1 e u (W r) X‖^2) ≤
        C*J*(L r)^2/(1+Real.log (L r))^k := by
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  obtain ⟨C,L₀,hC,hpoint⟩ := rough_noncube_low_height hSW hW hlo hc hd₁ hd₂ hR ha'
    (a+k+1) U (by omega)
  refine ⟨324*C^2,L₀,by positivity,?_⟩
  intro r X J H hL hprod hrough hJ hJL hH e he heL u hu
  have hLone := hW.length_one (r,Classical.arbitrary ι)
  have hlog : 0 ≤ Real.log (L r) := Real.log_nonneg hLone
  have hz : 1 ≤ 1+Real.log (L r) := by linarith
  have hcard : (H.card:ℝ) ≤ 324*(1+Real.log (L r))^a*J := by
    calc
      _ ≤ ((lowNoncubeSupport ((Real.log (L r))^a) J).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hH)
      _ ≤ 324*(Real.log (L r))^a*J := lowNoncubeSupport_card (pow_nonneg hlog _) hJ
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog (by linarith) _) (by norm_num)) hJ
  apply low_core_mass_bound hJ hz hcard
  calc
    _ ≤ ∑ _h ∈ H, (C*L r/(1+Real.log (L r))^(a+k+1))^2 := by
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨hn,v,j,hv,hj,hvN,hjN,hid⟩ := mem_lowNoncubeSupport (hH hh)
      have hnon : ¬∃ z : Eisenstein, z^3 = v*j^3 := by simpa only [← hid] using hn
      have hp := hpoint r X hL hprod hrough v j hv hj hnon
        (by simpa only [Real.rpow_natCast] using hvN) (hjN.trans hJL) e he heL u hu
      rw [hid]
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) hp 2
    _ = _ := by simp

end CubicFirstMoment

end

end OAI
