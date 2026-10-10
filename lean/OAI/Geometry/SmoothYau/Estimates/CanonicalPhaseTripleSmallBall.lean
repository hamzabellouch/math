import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SelectedComplexJetMatrixScale
import OAI.Geometry.SmoothYau.Smoothness.UniformJetZeroDifference

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff

theorem all_admissible_waves_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ)
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C : ℝ) (κ : ℝ)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    ∃ r > 0, ∃ T > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ n : ℝ, 1 ≤ n → ∀ x : Fin 3 → ℝ, ‖x‖ < r → ‖x‖ ≤ 1/n →
        let S := realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q
          ((2*D+3*m+6)+(D+m+1)+1))
        let U := canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n
        ‖(Complex.exp ((n : ℂ)*S x))⁻¹*U x-1‖ ≤ T/n ∧
        ‖fun i => (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*S x))⁻¹*
          waveDeriv (Pi.single i 1) U x-z i‖ ≤ T/n := by
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp
    (boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C)
  let base : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hbase : Continuous base := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hgc' (i j : Fin 3) (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (base q.1) i j) q.2) :=
    (hgc i j k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  have hbc' (i : Fin 3) (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (b (base q.1) i) q.2) :=
    (hbc i k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r,hr,T,hT,h⟩ := generated_cutoff_waves_near_center
    (fun p : W => g (base p)) (fun p : W => b (base p))
    (fun p => hg (base p)) (fun p => hb (base p)) (fun p => hg0 (base p))
    (fun p => hdg0 (base p)) hgc' hbc' (fun p : W => (φ (base p) 0 : ℂ))
    (Complex.continuous_ofReal.comp (hφ0.comp hbase)) z
    (fun i => (continuous_apply i).comp hz) Q
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p : W => fun i j => congrFun (congrFun p.property.2.2.1 j) i) (fun p : W => p.property.2.1)
    (fun p : W => fun k => phase_matrix_annihilation _ _ p.property.2.2.2.1 k) ζ hζ m D
  refine ⟨r,hr,T,hT,?_⟩
  intro p z Q hz hn hQ n hn1 x hxr hx
  exact h ⟨((p,z),Q),hz,hn,hQ⟩ n hn1 x hxr hx


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff

theorem generated_phase_exp_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → ComplexPhaseMatrix) (hQ : ∀ i j, Continuous (fun p => Q p i j))
    (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = s p)
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (L : ℕ) (hL : 2 ≤ L) :
    ∃ c > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : Fin 3 → ℝ, ‖x‖ ≤ 1/n →
      c*Real.exp (n*(F p x).re) ≤
        ‖Complex.exp ((n : ℂ)*realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) L) x)‖ := by
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) L
  have hz0 (p) : z p ≠ 0 := phase_vector_ne_zero _ (hnull p)
  have hSc : CoeffContinuous S := smoothPhasePolynomial_coeffContinuous g s hs z hz hz0 Q hQ L
    (fun i j k _ => (hgc i j k).comp (continuous_id.prodMk continuous_const))
  have hSd (p) : (S p).totalDegree ≤ L := smoothPhasePolynomial_degree (g p) (hg p)
    (hg0 p) (hdg0 p) (s p) (z p) (Q p) (hz0 p) (hsym p) (hnull p) (hQz p) L hL
  have hS0 (p) : realPolyEval (S p) 0 = F p 0 := by
    rw [hF0]
    have hh := (smoothPhasePolynomial_spec (g p) (hg p) (hg0 p) (hdg0 p) (s p) (z p)
      (Q p) (hz0 p) (hsym p) (hnull p) (hQz p) L hL).1.constantCoeff_eq_zero (by decide)
    have hc : constantCoeff (S p) = constantCoeff (wavePhaseSeed (s p) (z p) (Q p)) := by
      simpa only [map_sub,sub_eq_zero] using hh
    rw [realPolyEval_at_zero]
    exact hc.trans (wavePhaseSeed_constantCoeff (s p) (z p) (Q p))
  exact phase_exp_near_weight (fun p => realPolyEval (S p)) F (fun p => contDiff_realPolyEval _)
    hF hS0 (uniformJetBounds_realPolyEval S hSc L hSd isCompact_univ (isCompact_closedBall 0 1))
    (uniformJetBounds_of_continuous_jets F hFc isCompact_univ (isCompact_closedBall 0 1))

theorem all_admissible_phase_near_weight {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (φ : X → PhaseSpace → ℝ)
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (B C κ : ℝ) (L : ℕ) (hL : 2 ≤ L) :
    ∃ c > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ n : ℝ, 1 ≤ n → ∀ x : Fin 3 → ℝ, ‖x‖ ≤ 1/n →
      c*Real.exp (n*(F p x).re) ≤
        ‖Complex.exp ((n : ℂ)*realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q L) x)‖ := by
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp
    (boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C)
  let base : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hbase : Continuous base := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hgc' (i j : Fin 3) (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (base q.1) i j) q.2) :=
    (hgc i j k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  have hFc' (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (F (base q.1)) q.2) :=
    (hFc k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨c,hc,h⟩ := generated_phase_exp_near_center
    (fun p : W => g (base p)) (fun p => hg (base p)) (fun p => hg0 (base p))
    (fun p => hdg0 (base p)) hgc' (fun p : W => (φ (base p) 0 : ℂ))
    (Complex.continuous_ofReal.comp (hφ0.comp hbase)) z
    (fun i => (continuous_apply i).comp hz) Q
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p : W => fun i j => congrFun (congrFun p.property.2.2.1 j) i)
    (fun p : W => p.property.2.1)
    (fun p : W => fun k => phase_matrix_annihilation _ _ p.property.2.2.2.1 k)
    (fun p : W => F (base p)) (fun p => hF (base p)) (fun p => hF0 (base p)) hFc' L hL
  refine ⟨c,hc,?_⟩
  intro p z Q hz hn hQ n hn1 x hx
  exact h ⟨((p,z),Q),hz,hn,hQ⟩ n hn1 x hx

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise

theorem canonical_phase_triple_smallBall {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b₀ : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb₀ : ∀ p i, ContDiff ℝ ∞ (b₀ p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b₀ q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ)
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (B C κ M η : ℝ) (hM : 1 ≤ M) (hη : 0 < η)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    ∃ r₀ > 0, ∃ c₀ > 0, ∃ ε > 0,
      ∀ p (n δ : ℝ), 1 ≤ n → 0 < δ → δ < ε → δ^2 = 1/n →
      ∀ a ν b c d : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
        inner ℝ ν b = 0 → inner ℝ ν c = 0 →
        ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
        ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
      let z := ![complexPhaseVector a b,complexPhaseVector a c,
        complexPhaseVector (a+δ • ν) d]
      ∀ Q : Fin 3 → ComplexPhaseMatrix,
        (∀ ℓ, ‖z ℓ‖ ≤ B) → (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) →
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (φ p)) (z ℓ) κ C (Q ℓ)) →
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*(F p x).re) →
      let W := Real.exp (n*(F p x).re)+R
      let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤
      ENNReal.ofReal (Real.sqrt η/2*δ*(c₀/2*(n^6)⁻¹)^4)⁻¹*(ENNReal.ofReal (2*r))^4 := by
  obtain ⟨r₀,hr₀,T,hT,hjets⟩ := all_admissible_waves_near_center g b₀ hg hb₀ hg0 hdg0 hgc hbc
    φ hφ0 hφ2 B C κ ζ hζ m D
  obtain ⟨c₀,hc₀,hweight⟩ := all_admissible_phase_near_weight g hg hg0 hdg0 hgc φ hφ0 hφ2
    F hF hF0 hFc B C κ ((2*D+3*m+6)+(D+m+1)+1) (by omega)
  obtain ⟨ε,hε,hsmall⟩ := physical_complex_wave_smallBall_uniform M T η hM hT.le hη
  refine ⟨r₀,hr₀,c₀,hc₀,ε,hε,?_⟩
  intro p n δ hn hδ hδε hδsq a ν b c d ha hν hb hc hbn hcn hbM hcM hang
  dsimp only at *
  intro Q hz hnull hQ x hxr hx R hR0 hR Ω _ μ _ noise hnoise r hr
  let z := ![complexPhaseVector a b,complexPhaseVector a c,complexPhaseVector (a+δ • ν) d]
  let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
  let S := fun ℓ => realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) (z ℓ) (Q ℓ)
    ((2*D+3*m+6)+(D+m+1)+1))
  let e := fun ℓ => Complex.exp ((n : ℂ)*S ℓ x)
  let W := Real.exp (n*(F p x).re)+R
  let w := fun ℓ => ‖e ℓ‖/W
  let J := fun ℓ => complexWaveJet n (e ℓ) (U ℓ) x
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hJ : ‖selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ‖ ≤ T*δ^2 := by
    rw [← selectedComplexJetMatrix_leading a ν b c d δ,hδsq]
    have heq : T*(1/n) = T/n := by ring
    rw [heq]
    apply selectedComplexJetMatrix_error _ _ _ (div_nonneg hT.le hn0.le)
    intro ℓ
    obtain ⟨hv,hd⟩ := hjets p (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ) n hn x hxr hx
    exact complexWaveJet_error n (e ℓ) (U ℓ) x (z ℓ) _ (div_nonneg hT.le hn0.le) hv hd
  have hw (ℓ) : c₀/2*(n^6)⁻¹ ≤ w ℓ :=
    phase_weight_lower c₀ n (F p x).re R hc₀ hn hR0 hR (e ℓ)
      (hweight p (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ) n hn x hx)
  have hf : (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) =
      (fun ℓ i => (Circle.exp (Complex.arg (e ℓ)) : ℂ)*((w ℓ : ℂ)*J ℓ i)) := by
    funext ℓ i
    rw [complexWaveJet_factor n W (e ℓ) (Complex.exp_ne_zero _) (U ℓ) x]
    exact mul_assoc _ _ _
  change (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
    {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
      Metric.closedBall 0 r} ≤ _
  rw [hf]
  exact hsmall δ hδ hδε a ν b c ha hν hb hc hbn hcn hbM hcM hang J hJ
    (c₀/2*(n^6)⁻¹) (by positivity) w hw (fun ℓ => Circle.exp (Complex.arg (e ℓ)))
    Ω μ noise hnoise r hr



end YauCounterexamples
end

end OAI
