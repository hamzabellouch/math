import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzLocalizationLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchwartzFrame
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteOperatorConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCoordinateMap

namespace OAI

/-! # Uniformly bounded torus frames from finitely many Schwartz functions -/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable def sampledSchwartzFrame (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (B : F →ₗ[ℝ] 𝓢(E, ℂ)) (L : Radius) : F →L[ℝ] FourierL2 :=
  ((Module.finBasis ℝ F).constr ℝ (fun i =>
    schwartzTorusSample a k L.1 ha1 hk L.2
      (radianFourierKernel (B ((Module.finBasis ℝ F) i))))).toContinuousLinearMap

theorem sampledSchwartzFrame_basis (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (B : F →ₗ[ℝ] 𝓢(E, ℂ)) (L : Radius) (i : Fin (Module.finrank ℝ F)) :
    sampledSchwartzFrame a k ha1 hk B L ((Module.finBasis ℝ F) i) =
      schwartzTorusSample a k L.1 ha1 hk L.2
        (radianFourierKernel (B ((Module.finBasis ℝ F) i))) := by
  exact (Module.finBasis ℝ F).constr_basis ℝ _ i

theorem sampledSchwartzFrame_uniform_bound (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (B : F →ₗ[ℝ] 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : Radius, ‖sampledSchwartzFrame a k ha1 hk B L‖ ≤ C := by
  classical
  let b := Module.finBasis ℝ F
  choose C hC hb using fun i => exists_schwartzTorusSample_norm_bound a k ha1 hk
    (radianFourierKernel (B (b i)))
  obtain ⟨D, hD, hDb⟩ := b.exists_opNorm_le (F := FourierL2)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨D * ∑ i, C i, mul_nonneg hD.le hsum, fun L => hDb hsum (fun i => ?_)⟩
  rw [sampledSchwartzFrame_basis]
  exact (hb i L.1 L.2).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

theorem sampledSchwartzFrame_coordinate_limit (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F) (B : F →ₗ[ℝ] 𝓢(E, ℂ))
    (hB : ∀ v, π (homogeneousSchwartzEmbedding a k ha ha1 hk (B v)) = v)
    (L : ℕ → Radius) (hLinf : Tendsto (fun n => (L n).1) atTop atTop) :
    Tendsto (fun n => (expandingCoordinates a k ha ha1 hk χ π (L n)).comp
      (sampledSchwartzFrame a k ha1 hk B (L n))) atTop
      (𝓝 (ContinuousLinearMap.id ℝ F)) := by
  apply tendsto_finite_domain_operator_of_basis (Module.finBasis ℝ F)
  intro i
  have h := schwartzSample_finite_coordinate_limit a k ha ha1 hk χ
    (B ((Module.finBasis ℝ F) i)) ρ hρ hχ (fun n => (L n).1)
    (fun n => (L n).2) hLinf π
  rw [hB] at h
  simpa only [ContinuousLinearMap.comp_apply, sampledSchwartzFrame_basis,
    expandingCoordinates_apply, ContinuousLinearMap.id_apply] using h

theorem sampledSchwartzFrame_coordinate_approximation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (π : HomogeneousY a k →L[ℝ] F) (B : F →ₗ[ℝ] 𝓢(E, ℂ))
    (hB : ∀ v, π (homogeneousSchwartzEmbedding a k ha ha1 hk (B v)) = v) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
      ‖(expandingCoordinates a k ha ha1 hk χ π L).comp
        (sampledSchwartzFrame a k ha1 hk B L) - ContinuousLinearMap.id ℝ F‖ < ε := by
  classical
  intro ε hε
  by_contra hn
  push Not at hn
  choose L hL hbad using fun n : ℕ => hn (n : ℝ)
  have hLinf : Tendsto (fun n => (L n).1) atTop atTop :=
    tendsto_atTop_mono hL tendsto_natCast_atTop_atTop
  have h := tendsto_iff_norm_sub_tendsto_zero.mp
    (sampledSchwartzFrame_coordinate_limit a k ha ha1 hk χ ρ hρ hχ π B hB L hLinf)
  obtain ⟨n, hn⟩ := (h.eventually (eventually_lt_nhds hε)).exists
  exact (not_lt_of_ge (hbad n)) hn

end DefocusingNLS

end OAI
