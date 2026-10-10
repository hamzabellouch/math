import OAI.Analysis.FreeEntropy.TotalSecond

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem matrixHeatLaw_block_lower (hp : 2≤p) (hd : 0<d) {t v : ℝ} (ht : 0<t)
    (hv : 1≤v) (htv : t≤v) (hpt : 256*t≤p)
    (μ : Measure (MatrixCoordinates (p+1) d)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐa ∂μ,‖a‖≤2*Real.sqrt ((p:ℝ)*d) ∧
      ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      Real.sqrt ((p:ℝ)*d)/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖) :
    ENNReal.ofReal (1/2:ℝ)≤ matrixHeatLaw μ t
      (blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))) := by
  have htd : 0<t/(d:ℝ) := div_pos ht (by exact_mod_cast hd)
  let E := blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d))
  have hE : MeasurableSet E := (blockEvent_isClosed hd _ _).measurableSet
  change _≤(volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ (t/d) x))) E
  rw [← smoothedLaw_eq μ htd,Measure.map_apply (by fun_prop) hE]
  have : IsProbabilityMeasure (normalLaw (ι := MatrixIndex (p+1) d) (t/d)) := normalLaw_probability htd
  rw [Measure.prod_apply (hE.preimage (show Measurable (fun z : MatrixCoordinates (p+1) d × MatrixCoordinates (p+1) d => z.1+z.2) from by fun_prop))]
  calc
    _ = ∫⁻a : MatrixCoordinates (p+1) d,ENNReal.ofReal (1/2:ℝ) ∂μ := by simp
    _ ≤ _ := lintegral_mono_ae (hμ.mono (fun a ha => blockEvent_conditional_lower hp hd ht hv htv hpt a ha.1 ha.2))
namespace Model
variable (p : ℕ) [NeZero p]
 theorem diagonalMicrostates_blocks_eventually {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|)
    (hq : ∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2)
    {h : ℝ} (hh : spectralGood p δ Δ (wordMoment (τ p) (X p h))) (R : ℝ) :
    ∀ᶠk : ℕ in atTop,∀d : ℕ,0<d → ∀a : MatrixCoordinates (p+1) d,
      a∈diagonalMicrostates (τ p) (X p h) R k d →
      ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      Real.sqrt ((p:ℝ)*d)/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖ := by
  have he := diagonalMicrostates_uniform_open (τ p) (X p h) R {m | spectralGood p δ Δ m}
    (spectralGood_isOpen p δ Δ) hh
  filter_upwards [he] with k hk d hd a ha
  obtain ⟨f,hf,U,hU⟩ := spectralGood_blocks hd hδ hΔ hδΔ hsep hq a (hk d a ha)
  refine ⟨f,hf,U,?_⟩
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [div_pow,Real.sq_sqrt (by positivity : 0≤(p:ℝ)*d)]
  nlinarith
 theorem matrixHeatLaw_blocks_eventually (hp : 2≤p) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|)
    (hq : ∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2)
    {h t : ℝ} (hh0 : 0<h) (hh1 : h<1) (hh : spectralGood p δ Δ (wordMoment (τ p) (X p h)))
    (ht : 0<t) (hpt : 256*t≤p) (R : ℝ)
    (D : ℕ → ℕ) (hD : ∀k,0<D k)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (p+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (τ p) (X p h) R k (D k)) :
    ∀ᶠk in atTop,ENNReal.ofReal (1/2:ℝ)≤ matrixHeatLaw (μ k) t
      (blockEvent p (D k) (Real.sqrt ((p:ℝ)*D k)/4) (4*Real.sqrt ((1+h+t)*p*D k))) := by
  filter_upwards [diagonalMicrostates_norm_eventually p hp hh0.le hh1 R,
    diagonalMicrostates_blocks_eventually p hδ hΔ hδΔ hsep hq hh R] with k hk hb
  apply matrixHeatLaw_block_lower hp (hD k) ht (by linarith) (by linarith) hpt (μ k)
  filter_upwards [hμ k] with a ha
  exact ⟨hk (D k) (hD k) a ha,hb (D k) (hD k) a ha⟩
end Model
end FiniteEntropySeparation

end

end OAI
