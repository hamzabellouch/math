import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.CasimirOperatorPowBound
import OAI.MeasureTheory.FalconerCompletion.Estimates.ComplexIteratedDerivTsupport2

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def radialStationaryProfile (Ψ : ℝ → ℝ) (p : ℝ) (s : ℝ) : ℂ :=
  (Ψ s * s^p : ℝ)

theorem radialStationaryProfile_contDiff {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    ContDiff ℝ ∞ (radialStationaryProfile Ψ p) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hz : s = 0
  · subst s
    have he : radialStationaryProfile Ψ p =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0:ℝ) < 1/4)] with t ht
      have ht0 : Ψ t = 0 := by
        by_contra hn
        exact (not_lt_of_ge (hs t hn).1.le) ht
      simp [radialStationaryProfile,ht0]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp s
      (hΨ.contDiffAt.mul (contDiffAt_id.rpow_const_of_ne hz))

theorem radialStationaryProfile_tsupport {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) (p : ℝ) :
    tsupport (radialStationaryProfile Ψ p) ⊆ Icc (1/4:ℝ) 4 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hn : Ψ t ≠ 0 := by
    intro hz
    exact ht (by simp [radialStationaryProfile,hz])
  exact Ioo_subset_Icc_self (hs t hn)

theorem compact_complex_derivatives_bounded {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) {K : Set ℝ} (hK : IsCompact K) (hs : tsupport f ⊆ K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j f s‖ ≤ C := by
  have hc (j : ℕ) : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr (show (j:ℕ∞) ≤ ⊤ from le_top))
  choose C hC using fun j => hK.exists_bound_of_continuousOn (hc j).continuousOn
  let B := ∑ j ∈ Finset.range (n+1), max 0 (C j)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  refine ⟨B,hB,?_⟩
  intro j hj s
  by_cases hmem : s ∈ K
  · apply (hC j s hmem).trans
    apply (le_max_right 0 (C j)).trans
    exact Finset.single_le_sum (fun _ _ => le_max_left _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  · have hz : iteratedDeriv j f s = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hmem (hs (complex_iteratedDeriv_tsupport f j ht)))
    simpa only [hz,norm_zero] using hB

theorem radialStationaryProfile_derivatives {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (p : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ n, ∀ s, ‖iteratedDeriv j (radialStationaryProfile Ψ p) s‖ ≤ C :=
  compact_complex_derivatives_bounded (radialStationaryProfile_contDiff hΨ hs p)
    isCompact_Icc (radialStationaryProfile_tsupport hs p) n

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι]

noncomputable def normalizedDifferentialND (B : OrthonormalBasis ι ℝ V)
    (p : Polynomial ℂ) (j : ℕ) (b : SmoothFunctionND V) (Λ : ℝ) (w : V) : ℂ :=
  ((Λ⁻¹:ℝ):ℂ)^j * (differentialPolynomialND B p b).1 w

theorem normalizedDifferentialND_bound (B : OrthonormalBasis ι ℝ V)
    (p : Polynomial ℂ) (j : ℕ) (hp : p.natDegree ≤ j) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : SmoothFunctionND V) (A Λ : ℝ),
      1 ≤ A → 0 < Λ → A^2 ≤ Λ →
      (∀ k ≤ 2*j, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ∀ w, ‖w‖=1 → ‖normalizedDifferentialND B p j b Λ w‖ ≤ D := by
  obtain ⟨D,hD,hDb⟩ := differentialPolynomialND_bound B p j hp 0 C hC
  refine ⟨D,hD,?_⟩
  intro b A Λ hA hΛ hscale hb w hw
  have hh := hDb b A 0 hA (by simpa using hb) 0 le_rfl w hw
  simp only [norm_iteratedFDeriv_zero,zero_add] at hh
  have ht : (A^2/Λ)^j ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hΛ).mpr hscale)
  calc
    _ = (Λ⁻¹)^j*‖(differentialPolynomialND B p b).1 w‖ := by
      simp only [normalizedDifferentialND,norm_mul,norm_pow,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hΛ)]
    _ ≤ (Λ⁻¹)^j*(D*A^(2*j)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = D*(A^2/Λ)^j := by rw [div_pow,pow_mul]; ring
    _ ≤ D := by simpa using mul_le_mul_of_nonneg_left ht hD

noncomputable def radialDifferentialCoefficientND (Ψ : ℝ → ℝ)
    (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) (j : ℕ) (b : SmoothFunctionND V)
    (w : V) (Λ s : ℝ) : ℂ :=
  normalizedDifferentialND B p j b Λ w * radialStationaryProfile Ψ (-(j:ℝ)) s

theorem radialDifferentialCoefficientND_bound {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) (j : ℕ) (hp : p.natDegree ≤ j)
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (b : SmoothFunctionND V) (A Λ : ℝ),
      1 ≤ A → 0 < Λ → A^2 ≤ Λ →
      (∀ k ≤ 2*j, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b.1 w‖ ≤ C*A^k) →
      ∀ w, ‖w‖=1 →
      ContDiff ℝ ∞ (radialDifferentialCoefficientND Ψ B p j b w Λ) ∧
      tsupport (radialDifferentialCoefficientND Ψ B p j b w Λ) ⊆ Icc (1/4:ℝ) 4 ∧
      ∀ k ≤ m, ∀ s, ‖iteratedDeriv k (radialDifferentialCoefficientND Ψ B p j b w Λ) s‖ ≤ H := by
  obtain ⟨D,hD,hDb⟩ := normalizedDifferentialND_bound B p j hp C hC
  obtain ⟨P,hP,hPb⟩ := radialStationaryProfile_derivatives hΨ hs (-(j:ℝ)) m
  refine ⟨D*P,mul_nonneg hD hP,?_⟩
  intro b A Λ hA hΛ hscale hb w hw
  refine ⟨contDiff_const.mul (radialStationaryProfile_contDiff hΨ hs _),
    tsupport_mul_subset_right.trans (radialStationaryProfile_tsupport hs _),?_⟩
  intro k hk s
  change ‖iteratedDeriv k (fun t => normalizedDifferentialND B p j b Λ w *
    radialStationaryProfile Ψ (-(j:ℝ)) t) s‖ ≤ _
  rw [iteratedDeriv_const_mul_field,norm_mul]
  exact mul_le_mul (hDb b A Λ hA hΛ hscale hb w hw) (hPb k hk s) (norm_nonneg _) hD

omit [FiniteDimensional ℝ V] in
lemma radialDifferentialCoefficientND_exact (Ψ : ℝ → ℝ)
    (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) (j : ℕ) (b : SmoothFunctionND V)
    (w : V) (Λ s : ℝ) (hs : 0 < s) :
    radialDifferentialCoefficientND Ψ B p j b w Λ s =
      (Ψ s:ℂ) * ((Λ*s:ℂ)^(-(j:ℤ))) * (differentialPolynomialND B p b).1 w := by
  rw [radialDifferentialCoefficientND,radialStationaryProfile,normalizedDifferentialND,
    Real.rpow_neg hs.le,Real.rpow_natCast]
  push_cast
  rw [zpow_neg,zpow_natCast,mul_pow]
  ring

omit [FiniteDimensional ℝ V] in
lemma normalizedDifferentialND_support (B : OrthonormalBasis ι ℝ V)
    (p : Polynomial ℂ) (j : ℕ) (b : SmoothFunctionND V) (Λ : ℝ) :
    tsupport (normalizedDifferentialND B p j b Λ) ⊆ tsupport b.1 := by
  exact tsupport_mul_subset_right.trans (differentialPolynomialND_support B p b)

omit [FiniteDimensional ℝ V] in
lemma radialDifferentialCoefficientND_angular_support (Ψ : ℝ → ℝ)
    (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) (j : ℕ) (b : SmoothFunctionND V)
    (Λ s : ℝ) :
    tsupport (fun w => radialDifferentialCoefficientND Ψ B p j b w Λ s) ⊆ tsupport b.1 := by
  exact tsupport_mul_subset_left.trans (normalizedDifferentialND_support B p j b Λ)

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
