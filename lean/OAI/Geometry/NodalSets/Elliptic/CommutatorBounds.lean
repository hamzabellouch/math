import OAI.Geometry.NodalSets.Coefficients.ResidualProduct
import OAI.Geometry.NodalSets.Elliptic.CutoffAnnulus

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma DerivativeBound.sub {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (h : DerivativeBound k f x A) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h' : DerivativeBound k g x B) : DerivativeBound k (fun z ↦ f z - g z) x (A+B) := by
  have hn : DerivativeBound k (fun z ↦ -g z) x B := by
    intro j hj
    change ‖iteratedFDeriv ℝ j (-g) x‖ ≤ B
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact h' j hj
  simpa only [sub_eq_add_neg] using h.add hf hg.neg hn

lemma secondOrder_derivative_bound (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (f : Coord → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : Coord) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hgb : ∀ i j, DerivativeBound k (g i j) x C)
    (hbb : ∀ i, DerivativeBound k (b i) x C)
    (hfb : DerivativeBound (k+2) f x D) :
    DerivativeBound k (smoothSecondOrder g b f) x (20*2^k*C*D) := by
  have hh := (DerivativeBound.sum Finset.univ
    (fun i _ ↦ ContDiff.sum (fun j _ ↦ (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)))
    (fun i _ ↦ DerivativeBound.sum Finset.univ
      (fun j _ ↦ (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i))
      (fun j _ ↦ (hgb i j).mul (hg i j) (coordPartial_contDiff (coordPartial_contDiff hf j) i)
        hC hD ((hfb.coordPartial hf j).coordPartial (coordPartial_contDiff hf j) i)))).add
    (ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
      (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i))))
    (ContDiff.sum (fun i _ ↦ (hb i).mul (coordPartial_contDiff hf i)))
    (DerivativeBound.sum Finset.univ (fun i _ ↦ (hb i).mul (coordPartial_contDiff hf i))
      (fun i _ ↦ (hbb i).mul (hb i) (coordPartial_contDiff hf i) hC hD
        ((hfb.mono (by omega : k+1 ≤ k+2)).coordPartial hf i)))
  apply hh.enlarge
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

lemma real_smul_derivative_bound {beta : Coord → ℝ} {u : Coord → ℂ}
    (hb : ContDiff ℝ ∞ beta) (hu : ContDiff ℝ ∞ u) (k : ℕ) (x : Coord)
    {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hbeta : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j beta x‖ ≤ B)
    (huB : DerivativeBound k u x A) :
    DerivativeBound k (fun z ↦ beta z • u z) x (2^k*B*A) := by
  intro j hj
  have h := Yau.Waves.smul_derivative_power_bound hb hu j x hB hA
    (N := 1) (w := 1) (by norm_num) (by norm_num)
    (fun i hi ↦ by simpa using hbeta i (hi.trans hj))
    (fun i hi ↦ by simpa using huB i (hi.trans hj))
  simp only [one_pow, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hB) hA)

def cutoffCommutator (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) (N : ℝ) (y : Coord) : Coord → ℂ :=
  fun x ↦ smoothSecondOrder g b (fun z ↦ Yau.Waves.scaledCutoff N y z • u z) x -
    Yau.Waves.scaledCutoff N y x • smoothSecondOrder g b u x

lemma cutoffCommutator_contDiff (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hu : ContDiff ℝ ∞ u) (N : ℝ) (y : Coord) :
    ContDiff ℝ ∞ (cutoffCommutator g b u N y) :=
  (smoothSecondOrder_contDiff hg hb ((Yau.Waves.scaledCutoff_contDiff N y).smul hu)).sub
    ((Yau.Waves.scaledCutoff_contDiff N y).smul (smoothSecondOrder_contDiff hg hb hu))

theorem cutoffCommutator_polynomial_bound (k : ℕ) : ∃ B > 0,
    ∀ (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ),
    (∀ i j, ContDiff ℝ ∞ (g i j)) → (∀ i, ContDiff ℝ ∞ (b i)) → ContDiff ℝ ∞ u →
    ∀ (N : ℝ) (y x : Coord) (C A p w : ℝ), 1 ≤ N → 0 ≤ C → 0 ≤ A → 0 ≤ w →
    (∀ i j, DerivativeBound k (g i j) x C) →
    (∀ i, DerivativeBound k (b i) x C) →
    DerivativeBound (k+2) u x (A * N^p * w) →
    DerivativeBound k (cutoffCommutator g b u N y) x
      (B*C*A*N^(p+k+2)*w) := by
  obtain ⟨B, hB, hcut⟩ := Yau.Waves.scaledCutoff_all_derivatives (E := Coord) (k+2)
  refine ⟨20*2^k*2^(k+2)*B + 2^k*B*20*2^k, by positivity, ?_⟩
  intro g b u hg hb hu N y x C A p w hN hC hA hw hgb hbb hub
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hbeta (j : ℕ) (hj : j ≤ k+2) :
      ‖iteratedFDeriv ℝ j (Yau.Waves.scaledCutoff N y) x‖ ≤ B*N^(k+2) := by
    exact (hcut j hj N hN y x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hN hj) hB.le)
  have hcu := real_smul_derivative_bound (Yau.Waves.scaledCutoff_contDiff N y) hu
    (k+2) x (by positivity : 0 ≤ B*N^(k+2)) (by positivity : 0 ≤ A*N^p*w) hbeta hub
  have hLcu := secondOrder_derivative_bound g b _ hg hb
    ((Yau.Waves.scaledCutoff_contDiff N y).smul hu) k x hC (by positivity) hgb hbb hcu
  have hLu := secondOrder_derivative_bound g b u hg hb hu k x hC (by positivity) hgb hbb hub
  have hcuL := real_smul_derivative_bound (Yau.Waves.scaledCutoff_contDiff N y)
    (smoothSecondOrder_contDiff hg hb hu) k x (by positivity : 0 ≤ B*N^(k+2))
    (by positivity) (fun j hj ↦ hbeta j (by omega)) hLu
  have h := hLcu.sub (smoothSecondOrder_contDiff hg hb ((Yau.Waves.scaledCutoff_contDiff N y).smul hu))
    ((Yau.Waves.scaledCutoff_contDiff N y).smul (smoothSecondOrder_contDiff hg hb hu)) hcuL
  apply h.enlarge
  have hpow : N^(p+k+2) = N^(k+2:ℕ)*N^p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNp]
    congr 1
    push_cast
    ring
  rw [hpow]
  exact le_of_eq (by ring)

open Filter
open scoped Topology

lemma coordPartial_eventuallyEq {f u : Coord → ℂ} {x : Coord}
    (h : f =ᶠ[𝓝 x] u) (i : Fin 4) : coordPartial i f =ᶠ[𝓝 x] coordPartial i u :=
  (h.fderiv (𝕜 := ℝ)).mono (fun _ hz ↦ congrArg (fun L : Coord →L[ℝ] ℂ ↦ L (Pi.single i 1)) hz)

lemma smoothSecondOrder_eventuallyEq (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) {f u : Coord → ℂ} {x : Coord} (h : f =ᶠ[𝓝 x] u) :
    smoothSecondOrder g b f =ᶠ[𝓝 x] smoothSecondOrder g b u := by
  have h1 : ∀ᶠ z in 𝓝 x, ∀ i, coordPartial i f z = coordPartial i u z :=
    Filter.eventually_all.mpr (fun i ↦ coordPartial_eventuallyEq h i)
  have h2 : ∀ᶠ z in 𝓝 x, ∀ i j, coordPartial i (coordPartial j f) z = coordPartial i (coordPartial j u) z :=
    Filter.eventually_all.mpr (fun i ↦ Filter.eventually_all.mpr
      (fun j ↦ coordPartial_eventuallyEq (coordPartial_eventuallyEq h j) i))
  filter_upwards [h1,h2] with z hz1 hz2
  simp only [smoothSecondOrder, hz1, hz2]

theorem cutoffCommutator_derivative_zero_near (g : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) {N : ℝ} (hN : 0 < N)
    (y x : Coord) (k : ℕ) (hx : ‖x-y‖ < N^(-1/3:ℝ)) :
    iteratedFDeriv ℝ k (cutoffCommutator g b u N y) x = 0 := by
  have hnear : ∀ᶠ z in 𝓝 x, ‖z-y‖ < N^(-1/3:ℝ) :=
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hx
  have hbeta : Yau.Waves.scaledCutoff N y =ᶠ[𝓝 x] fun _ ↦ (1:ℝ) :=
    hnear.mono (fun z hz ↦ Yau.Waves.scaledCutoff_eq_one hN y z hz.le)
  have hprod : (fun z ↦ Yau.Waves.scaledCutoff N y z • u z) =ᶠ[𝓝 x] u := by
    filter_upwards [hbeta] with z hz
    rw [hz, one_smul]
  have hc : cutoffCommutator g b u N y =ᶠ[𝓝 x] fun _ ↦ (0:ℂ) := by
    filter_upwards [smoothSecondOrder_eventuallyEq g b hprod, hbeta] with z hz hz'
    simp only [cutoffCommutator, hz, hz', one_smul, sub_self]
  have h := (hc.iteratedFDeriv ℝ k).self_of_nhds
  simpa using h

theorem cutoffCommutator_gaussian_bound (k : ℕ) (c p K : ℝ) (hc : 0 < c) :
    ∃ B > 0, ∀ᶠ N : ℝ in atTop,
    ∀ (g : Fin 4 → Fin 4 → Coord → ℂ) (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ),
    (∀ i j, ContDiff ℝ ∞ (g i j)) → (∀ i, ContDiff ℝ ∞ (b i)) → ContDiff ℝ ∞ u →
    ∀ (y x : Coord) (C A S : ℝ), 0 ≤ C → 0 ≤ A →
    (∀ i j, DerivativeBound k (g i j) x C) →
    (∀ i, DerivativeBound k (b i) x C) →
    DerivativeBound (k+2) u x
      (A*N^p*Real.exp (N*S-c*N*‖x-y‖^2)) →
    ‖iteratedFDeriv ℝ k (cutoffCommutator g b u N y) x‖ ≤
      B*C*A*N^(-K)*Real.exp (N*S) := by
  obtain ⟨B, hB, hpoly⟩ := cutoffCommutator_polynomial_bound k
  refine ⟨B, hB, ?_⟩
  filter_upwards [Yau.Waves.gaussian_cutoff_bound c 1 hc (by norm_num) (p+k+2) K,
    eventually_ge_atTop (1:ℝ)] with N hgauss hN
  intro g b u hg hb hu y x C A S hC hA hgb hbb hub
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  by_cases hx : ‖x-y‖ < N^(-1/3:ℝ)
  · rw [cutoffCommutator_derivative_zero_near g b u hNp y x k hx, norm_zero]
    positivity
  have hrad : N^(-1/3:ℝ) ≤ ‖x-y‖ := le_of_not_gt hx
  have hann : N^(1/3:ℝ) ≤ N*‖x-y‖^2 := by
    have he : N * (N^(-1/3:ℝ))^2 = N^(1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
      nth_rw 1 [← Real.rpow_one N]
      rw [← Real.rpow_add hNp]
      congr 1
      norm_num
    rw [← he]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hrad 2) hNp.le
  have h := hpoly g b u hg hb hu N y x C A p
    (Real.exp (N*S-c*N*‖x-y‖^2)) hN hC hA (Real.exp_pos _).le hgb hbb hub k le_rfl
  apply h.trans
  simpa only [one_mul, mul_assoc] using hgauss S ‖x-y‖ (B*C*A) (by positivity) (by simpa using hann)

end
end Yau.Jets

end OAI
