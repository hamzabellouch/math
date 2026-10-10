import OAI.MeasureTheory.Falconer.Graphs.GraphFixedCutoffs
import OAI.MeasureTheory.Falconer.Graphs.GraphBinDerivatives

namespace OAI

namespace PlanarFalconer
open Set Filter
open scoped ContDiff Topology ComplexConjugate

structure GraphDerivativeBound (n : ℕ) (f : (Plane × ℝ) → ℂ) (C D : ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ f graphSmoothDomain
  bound : ∀ j ≤ n, ∀ (η : Plane) (z : ℝ), ‖η‖ ≤ 8 → |z| ≤ 4 → 1/8 ≤ ‖η‖ →
    ‖iteratedFDeriv ℝ j f (η,z)‖ ≤ C*D^j

theorem GraphDerivativeBound.mul {n : ℕ} {f g : (Plane × ℝ) → ℂ} {C₁ C₂ D₁ D₂ : ℝ}
    (hf : GraphDerivativeBound n f C₁ D₁) (hg : GraphDerivativeBound n g C₂ D₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) :
    GraphDerivativeBound n (fun p => f p*g p) (C₁*C₂) (D₁+D₂) := by
  refine ⟨hf.smooth.mul hg.smooth,?_⟩
  intro j hj η z hhi hz hlo
  exact frechet_mul_scale_on graphSmoothDomain_isOpen hf.smooth hg.smooth
    (norm_pos_iff.mp (by linarith)) hC₁ hC₂ hD₁ hD₂ j
    (fun k hk => hf.bound k (hk.trans hj) η z hhi hz hlo)
    (fun k hk => hg.bound k (hk.trans hj) η z hhi hz hlo)

theorem GraphDerivativeBound.conj {n : ℕ} {f : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) : GraphDerivativeBound n (fun p => conj (f p)) C D := by
  refine ⟨Complex.conjCLE.contDiff.comp_contDiffOn hf.smooth,?_⟩
  intro j hj η z hhi hz hlo
  change ‖iteratedFDeriv ℝ j (fun p => star (f p)) (η,z)‖ ≤ _
  rw [frechet_conj_norm]
  exact hf.bound j hj η z hhi hz hlo

theorem GraphDerivativeBound.mono {n : ℕ} {f : (Plane × ℝ) → ℂ} {C C' D D' : ℝ}
    (hf : GraphDerivativeBound n f C D) (hC : C ≤ C') (hC' : 0 ≤ C')
    (hD : D ≤ D') (hD0 : 0 ≤ D) : GraphDerivativeBound n f C' D' := by
  refine ⟨hf.smooth,?_⟩
  intro j hj η z hhi hz hlo
  exact (hf.bound j hj η z hhi hz hlo).trans
    (mul_le_mul hC (pow_le_pow_left₀ hD0 hD _) (pow_nonneg hD0 _) hC')

theorem GraphDerivativeBound.congr {n : ℕ} {f g : (Plane × ℝ) → ℂ} {C D : ℝ}
    (hf : GraphDerivativeBound n f C D) (he : EqOn g f graphSmoothDomain) :
    GraphDerivativeBound n g C D := by
  have hevent {p : Plane × ℝ} (hp : p ∈ graphSmoothDomain) : g =ᶠ[𝓝 p] f :=
    Filter.eventuallyEq_of_mem (graphSmoothDomain_isOpen.mem_nhds hp) he
  refine ⟨?_,?_⟩
  · intro p hp
    exact ((hf.smooth p hp).contDiffAt (graphSmoothDomain_isOpen.mem_nhds hp)).congr_of_eventuallyEq
      (hevent hp) |>.contDiffWithinAt
  · intro j hj η z hhi hz hlo
    have hp : (η,z) ∈ graphSmoothDomain := norm_pos_iff.mp (by linarith)
    rw [((hevent hp).iteratedFDeriv ℝ j).eq_of_nhds]
    exact hf.bound j hj η z hhi hz hlo

theorem graph_fixed_derivative_budget {f : (Plane × ℝ) → ℂ}
    (hf : ∀ p, p.1 ≠ 0 → ContDiffAt ℝ ∞ f p) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ GraphDerivativeBound n f C 1 := by
  choose C hC hb using fun j => graph_compact_derivative_bound hf j
  let A := ∑ j ∈ Finset.range (n+1), C j
  refine ⟨A,Finset.sum_nonneg (fun j _ => hC j),fun p hp => (hf p hp).contDiffWithinAt,?_⟩
  intro j hj η z hhi hz hlo
  rw [one_pow,mul_one]
  exact (hb j η z hhi hz hlo).trans
    (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

theorem graph_periodic_derivative_budget {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f (2*Real.pi)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (plus : Bool) (c : ℝ),
      GraphDerivativeBound n (graphAngularPullback f plus c) C 1 := by
  have hj (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ θ, ‖iteratedDeriv j f θ‖ ≤ B := by
    obtain ⟨B,hB⟩ := ((complex_periodic_iteratedDeriv hp j).isBounded_of_continuous
      (by positivity : 2*Real.pi ≠ 0) (hf.continuous_iteratedDeriv j
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)))).exists_norm_le
    exact ⟨max 0 B,le_max_left _ _,fun θ => (hB _ ⟨θ,rfl⟩).trans (le_max_right _ _)⟩
  choose B hB hb using hj
  let C := ∑ j ∈ Finset.range (n+1), B j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => hB j)
  choose A hA ha using fun j => graph_mixed_composition_scale j
  let M := ∑ j ∈ Finset.range (n+1), A j
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ => hA j)
  refine ⟨M*C,mul_nonneg hM hC,?_⟩
  intro plus c
  refine ⟨fun p hp' => (graphAngularPullback_contDiffAt hf hp plus c hp').contDiffWithinAt,?_⟩
  intro j hj η z hhi hz hlo
  have he := ha j f hf hp C 1 hC le_rfl (fun k hk θ => by
    rw [one_pow,mul_one]
    exact (hb k θ).trans (Finset.single_le_sum (fun l _ => hB l)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk.trans hj))))) plus c η z hhi hz hlo
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun l _ => hA l) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) hC

end PlanarFalconer

end OAI
