import OAI.MeasureTheory.Falconer.Angular.InheritedAngularSymbols

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem sourceAngularRadius_inv (N : ℕ) (sig : ℝ) (l : ℕ) :
    (sourceAngularRadius N sig l)⁻¹ = max 1 ((2:ℝ)^l*((2:ℝ)^N)^(-50*sig)) := by
  have hp : 0 < 1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig) := by positivity
  have he : (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig))⁻¹ =
      (2:ℝ)^l*((2:ℝ)^N)^(-50*sig) := by
    rw [mul_inv_rev,inv_div,div_one,show -50*sig = -(50*sig) by ring,Real.rpow_neg (by positivity)]
    ring
  unfold sourceAngularRadius
  rcases le_total 1 (1/(2:ℝ)^l*((2:ℝ)^N)^(50*sig)) with h | h
  · rw [min_eq_left h,inv_one,← he,max_eq_left (by simpa using inv_anti₀ zero_lt_one h)]
  · rw [min_eq_right h,he,← he,max_eq_right (by simpa using inv_anti₀ hp h)]

 theorem sourceAngularRadius_inv_mono (N : ℕ) (sig : ℝ) {l L : ℕ} (h : l ≤ L) :
    (sourceAngularRadius N sig l)⁻¹ ≤ (sourceAngularRadius N sig L)⁻¹ := by
  rw [sourceAngularRadius_inv,sourceAngularRadius_inv]
  apply max_le_max_left
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (by positivity)

noncomputable def sourceSymbolScale (N : ℕ) (sig : ℝ) (L : ℕ) : ℝ :=
  ((2:ℝ)^N)^sig * max 1 ((2:ℝ)^L*((2:ℝ)^N)^(-50*sig))

 theorem sourceSymbolScale_pos (N : ℕ) (sig : ℝ) (L : ℕ) : 0 < sourceSymbolScale N sig L := by
  unfold sourceSymbolScale
  positivity

 theorem uniform_inheritedMaskProduct_bound {sig : ℝ} (hsig : 0 < sig) (K j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    S.card ≤ (N+1)^3+1 → (∑ a ∈ S, k a) ≤ K →
    ∀ L : ℕ, (∀ a ∈ S, descriptorLength (b a) ≤ L) →
    ∀ Q : DyadicSquare, 0 < Q.side → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (J i : ℕ) (x : ι → Plane) (θ : ℝ),
    ‖iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x) θ‖ ≤
      symbolDerivativeConstant (K+j)^(K+j) * sourceSymbolScale N sig L^j := by
  obtain ⟨N₁,h₁⟩ := fixed_polynomial_subpower 3 (half_pos hsig)
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (half_pos hsig) 2
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i x θ
  have hpol : (S.card:ℝ) ≤ ((2:ℝ)^N)^sig := by
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    have hc : (S.card:ℝ) ≤ ((N:ℝ)+1)^3+1 := by exact_mod_cast hcard
    have hc' : ((N:ℝ)+1)^3+1 ≤ 2*(4*(N:ℝ)+1)^3 := by
      nlinarith [pow_le_pow_left₀ (by positivity : 0 ≤ (N:ℝ)+1)
        (by linarith : (N:ℝ)+1 ≤ 4*(N:ℝ)+1) 3,
        one_le_pow₀ (by linarith : (1:ℝ) ≤ 4*(N:ℝ)+1) (n := 3)]
    apply (hc.trans hc').trans
    calc
      _ ≤ ((2:ℝ)^N)^(sig/2)*((2:ℝ)^N)^(sig/2) :=
        mul_le_mul (h₂ N ((le_max_right _ _).trans hN))
          (h₁ N ((le_max_left _ _).trans hN)) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hd := sourceAngularRadius_pos N sig L
  apply (inheritedMaskProduct_bound S b k Q hQ ρ m N lam sig J i x K j hK
    (sourceAngularRadius N sig L)⁻¹ (by positivity)
    (fun a ha => sourceAngularRadius_inv_mono N sig (hL a ha)) θ).trans
  have hC : 0 ≤ symbolDerivativeConstant (K+j) := zero_le_one.trans (symbolDerivativeConstant_one_le _)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
  apply pow_le_pow_left₀ (by positivity)
  rw [sourceSymbolScale,← sourceAngularRadius_inv]
  exact mul_le_mul_of_nonneg_right hpol (by positivity)

end PlanarFalconer

end OAI
