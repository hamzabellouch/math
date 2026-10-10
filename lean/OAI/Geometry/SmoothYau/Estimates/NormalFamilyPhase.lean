import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.AdmissibleCutoffWaveLocalizedDerivatives
import OAI.Geometry.SmoothYau.Smoothness.UniformJetBoundsFiberComp

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
variable {X P E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem all_admissible_composed_endpoint_ratio
    (partition : X → P) (hπ : Continuous partition)
    (ψ : P × E → (Fin 3 → ℝ)) (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ∀ p, ψ (partition p,0) = 0)
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C κ : ℝ) (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    let M := (2*D+3*m+6)+(D+m+1)+1
    let S := fun p z Q t => realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q M) (ψ (partition p,t))
    let U := fun p z Q n t => canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n (ψ (partition p,t))
    ∃ r₀ > 0, ∃ C₀ > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
      ∀ x y : E, ‖x‖ ≤ r → ‖y‖ ≤ r → n*‖y-x‖ ≤ 1 →
      ∀ L : E →L[ℝ] ℂ, ‖fderiv ℝ (S p z Q) 0-L‖ ≤ δ → C₀*r+δ ≤ 1/2 →
      ‖U p z Q n y-Complex.exp ((n : ℂ)*L (y-x))*U p z Q n x‖ ≤
        (10*(C₀*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U p z Q n x‖ := by
  dsimp only
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  have hW : IsCompact W := boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let πW : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hπW : Continuous πW := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hn (p : W) : ∑ i, z p i*z p i = -1 := p.property.2.1
  have hv (p : W) : PhaseMatrixValid (H (πW p)) (z p) κ C (Q p) := p.property.2.2
  have hgW (i j k) : Continuous (fun q : W × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g (πW q.1) i j) q.2) :=
    (hgc i j k).comp ((hπW.comp continuous_fst).prodMk continuous_snd)
  have hbW (i k) : Continuous (fun q : W × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b (πW q.1) i) q.2) :=
    (hbc i k).comp ((hπW.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r₀,hr₀,T,hT,hbound⟩ := generated_composed_wave_endpoint_ratio (partition ∘ πW) (hπ.comp hπW)
    ψ hψ (fun p => hψ0 (πW p)) (fun p => g (πW p)) (fun p => b (πW p))
    (fun p => hg (πW p)) (fun p => hb (πW p)) (fun p => hg0 (πW p)) (fun p => hdg0 (πW p))
    hgW hbW (fun p => (φ (πW p) 0 : ℂ)) (Complex.continuous_ofReal.comp (hφ0.comp hπW))
    z (fun i => (continuous_apply i).comp hz) Q
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p i j => congrFun (congrFun (hv p).1 j) i) hn
    (fun p k => phase_matrix_annihilation _ _ (hv p).2.1 k) ζ hζ m D
  refine ⟨r₀,hr₀,T,hT,?_⟩
  intro p z0 Q0 hz0 hn0 hQ0
  exact hbound (⟨((p,z0),Q0),⟨hz0,hn0,hQ0⟩⟩ : W)
end



open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

def normalFamilyPhase (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (q : NormalWaveParameter) (z : Fin 3 → ℂ) (Q : ComplexPhaseMatrix) (m D : ℕ) :
    (Fin 3 → ℝ) → ℂ :=
  realPolyEval (smoothPhasePolynomial (fun i j x => A (q,x) i j)
    (normalWaveProfile g φ q 0 : ℂ) z Q ((2*D+3*m+6)+(D+m+1)+1))

theorem normal_family_composed_endpoint_ratio (g : SmoothMetric NormalWaveSpace NormalWaveSpace)
    (φ : NormalWaveSpace → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {K : Set NormalWaveSpace} (hK : IsCompact K)
    (A : NormalWaveParameter × (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℂ)
    (b : NormalWaveParameter × (Fin 3 → ℝ) → Fin 3 → ℂ)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (hA0 : ∀ q ∈ metricFrameSet g K, ∀ i j, A (q,0) i j = if i = j then 1 else 0)
    (hAd : ∀ q ∈ metricFrameSet g K, ∀ i j, fderiv ℝ (fun x => A (q,x) i j) 0 = 0)
    (ψ : NormalWaveParameter × NormalWaveSpace → NormalWaveSpace)
    (hψ : ContDiff ℝ ∞ ψ) (hψ0 : ∀ q ∈ metricFrameSet g K, ψ (q,0) = 0)
    (B C κ : ℝ) (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    let S := fun q z Q t => normalFamilyPhase g φ A q z Q m D (normalWaveEquiv.symm (ψ (q,t)))
    let U := fun q z Q n t => normalFamilyWave g φ A b q z Q ζ m D n (normalWaveEquiv.symm (ψ (q,t)))
    ∃ r₀ > 0, ∃ T > 0, ∀ q ∈ metricFrameSet g K, ∀ z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (normalWaveProfile g φ q)) z κ C Q →
      ∀ (n r δ : ℝ), 1 ≤ n → 0 ≤ r → r < r₀ → 0 ≤ δ →
      ∀ x y : NormalWaveSpace, ‖x‖ ≤ r → ‖y‖ ≤ r → n*‖y-x‖ ≤ 1 →
      ∀ L : NormalWaveSpace →L[ℝ] ℂ, ‖fderiv ℝ (S q z Q) 0-L‖ ≤ δ → T*r+δ ≤ 1/2 →
      ‖U q z Q n y-Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖ ≤
        (10*(T*r+δ))*‖Complex.exp ((n : ℂ)*L (y-x))*U q z Q n x‖ := by
  let X := metricFrameSet g K
  let : CompactSpace X := isCompact_iff_compactSpace.mp (metricFrameSet_isCompact g hK)
  let G : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q i j x => A (q.val,x) i j
  let β : X → Fin 3 → (Fin 3 → ℝ) → ℂ := fun q j x => b (q.val,x) j
  let Φ : X → PhaseSpace → ℝ := fun q => normalWaveProfile g φ q.val
  have hG (q : X) (i j : Fin 3) : ContDiff ℝ ∞ (G q i j) :=
    (contDiff_pi.mp (contDiff_pi.mp hA i) j).comp (contDiff_const.prodMk contDiff_id)
  have hβ (q : X) (j : Fin 3) : ContDiff ℝ ∞ (β q j) :=
    (contDiff_pi.mp hb j).comp (contDiff_const.prodMk contDiff_id)
  have hG0 (q : X) (i j : Fin 3) : G q i j 0 = if i = j then 1 else 0 := hA0 q.val q.property i j
  have hGd (q : X) (i j : Fin 3) : fderiv ℝ (G q i j) 0 = 0 := hAd q.val q.property i j
  have hGc (i j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (G w.1 i j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => A w i j)
      (contDiff_pi.mp (contDiff_pi.mp hA i) j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hβc (j : Fin 3) (k : ℕ) : Continuous (fun w : X × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (β w.1 j) w.2) := by
    exact (continuous_parameter_iteratedFDeriv (fun w => b w j)
      (contDiff_pi.mp hb j) k).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hΦ (q : X) : ContDiff ℝ ∞ (Φ q) :=
    (contDiff_normalWaveProfile g hφ).comp (contDiff_const.prodMk contDiff_id)
  have hΦ0 : Continuous (fun q : X => Φ q 0) :=
    (contDiff_normalWaveProfile g hφ).continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hΦ2 : Continuous (fun w : X × PhaseSpace => iteratedFDeriv ℝ 2 (Φ w.1) w.2) :=
    continuous_normalWaveProfile_iteratedFDeriv g hφ K 2
  let Ψ := fun w : NormalWaveParameter × NormalWaveSpace => normalWaveEquiv.symm (ψ w)
  have hΨ : ContDiff ℝ ∞ Ψ := normalWaveEquiv.symm.contDiff.comp hψ
  have hΨ0 (q : X) : Ψ (q.val,0) = 0 := by dsimp [Ψ]; rw [hψ0 q.val q.property,map_zero]
  obtain ⟨r₀,hr₀,T,hT,hbound⟩ := all_admissible_composed_endpoint_ratio
    (fun q : X => q.val) continuous_subtype_val Ψ hΨ hΨ0 G β hG hβ hG0 hGd hGc hβc
    Φ hΦ0 hΦ2 B C κ ζ hζ m D
  exact ⟨r₀,hr₀,T,hT,fun q hq => hbound ⟨q,hq⟩⟩

end YauCounterexamples
end

end OAI
