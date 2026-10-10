import OAI.Analysis.Mahler.CompactFluxDifferentiation
import OAI.Analysis.Mahler.SphereFluxIntegral

namespace OAI

open Complex MeasureTheory Metric Set Filter
open scoped Topology BigOperators

namespace Mahler

lemma continuousOn_orientedDensity {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ)
    {B : X → E [⋀^Fin d]→ₗ[ℝ] ℂ} {x : X → E} {K : Set X}
    (hB : ∀ v, ContinuousOn (fun p => B p v) K) (hx : ContinuousOn x K) :
    ContinuousOn (fun p => orientedDensity b Ω (B p) (x p)) K := by
  unfold orientedDensity
  apply ContinuousOn.div_const
  apply continuousOn_finsetSum
  intro i hi
  have hc : ContinuousOn (fun p => (b.repr (x p) i : ℂ)) K :=
    Complex.continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj i).continuous.comp_continuousOn (b.repr.continuous.comp_continuousOn hx))
  exact (hc.mul continuousOn_const).mul (hB _)

lemma hasDerivAt_orientedDensity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {d : ℕ}
    (b : OrthonormalBasis (Fin (d+1)) ℝ E) (Ω : E [⋀^Fin (d+1)]→ₗ[ℝ] ℂ)
    {B : ℝ → E [⋀^Fin d]→ₗ[ℝ] ℂ} {D : E [⋀^Fin d]→ₗ[ℝ] ℂ} {t : ℝ}
    (hB : ∀ v, HasDerivAt (fun s => B s v) (D v) t) (x : E) :
    HasDerivAt (fun s => orientedDensity b Ω (B s) x) (orientedDensity b Ω D x) t := by
  unfold orientedDensity
  exact (HasDerivAt.fun_sum (fun i _ => (hB (i.removeNth b)).const_mul
    ((b.repr x i : ℂ) * (-1 : ℂ)^i.val))).div_const _

theorem sphereFlux_continuousOn {k : ℕ}
    {B : ℝ → ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ} {a b : ℝ}
    (hB : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => B p.1 p.2 v)
      (Icc a b ×ˢ univ)) :
    ContinuousOn (fun s => sphereFlux k (B s)) (Icc a b) := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  unfold sphereFlux
  apply CompactFluxDifferentiation.continuousOn_integral
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hB
      (continuous_subtype_val.comp continuous_snd).continuousOn)

theorem sphereFlux_continuous {k : ℕ}
    {B : ℝ → ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ}
    (hB : ∀ v, Continuous
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => B p.1 p.2 v)) :
    Continuous (fun s => sphereFlux k (B s)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (sphereFlux_continuousOn (a := t-1) (b := t+1)
    (fun v => (hB v).continuousOn)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- Differentiation of the actual outward unit-sphere flux. C1 means joint
continuity of every form coefficient and its parameter derivative on the
compact cylinder; all integral side conditions are derived. -/
theorem sphereFlux_hasDerivAt {k : ℕ}
    {B D : ℝ → ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ} {a b t : ℝ}
    (hB : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => B p.1 p.2 v)
      (Icc a b ×ˢ univ))
    (hD : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => D p.1 p.2 v)
      (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1, ∀ v,
      HasDerivAt (fun r => B r x v) (D s x v) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => sphereFlux k (B s)) (sphereFlux k (D t)) t := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  unfold sphereFlux
  apply CompactFluxDifferentiation.hasDerivAt_integral (a := a) (b := b)
    (G := fun s (x : sphere (0 : ComplexEuclidean (k+1)) 1) => (orientedDensity (sphereFrame k) (sphereVolume k) (D s x) x).re)
  · exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hB
        (continuous_subtype_val.comp continuous_snd).continuousOn)
  · exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hD
        (continuous_subtype_val.comp continuous_snd).continuousOn)
  · intro s hs x
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_orientedDensity (sphereFrame k) (sphereVolume k) (hd s hs x) x)
  · exact ht

/-- A tangent-restricted pointwise calculation can be supplied directly as a
density derivative; no ambient extension of that derivative is required. -/
theorem sphereFlux_hasDerivAt_of_density {k : ℕ}
    {B D : ℝ → ComplexEuclidean (k+1) →
      ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ} {a b t : ℝ}
    (hB : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => B p.1 p.2 v)
      (Icc a b ×ˢ univ))
    (hD : ∀ v, ContinuousOn
      (fun p : ℝ × sphere (0 : ComplexEuclidean (k+1)) 1 => D p.1 p.2 v)
      (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x : sphere (0 : ComplexEuclidean (k+1)) 1,
      HasDerivAt (fun r => orientedDensity (sphereFrame k) (sphereVolume k) (B r x) x)
        (orientedDensity (sphereFrame k) (sphereVolume k) (D s x) x) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => sphereFlux k (B s)) (sphereFlux k (D t)) t := by
  let : IsFiniteMeasure (sphereArea (k+1)) := by unfold sphereArea; infer_instance
  unfold sphereFlux
  apply CompactFluxDifferentiation.hasDerivAt_integral (a := a) (b := b)
    (G := fun s (x : sphere (0 : ComplexEuclidean (k+1)) 1) => (orientedDensity (sphereFrame k) (sphereVolume k) (D s x) x).re)
  · exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hB
        (continuous_subtype_val.comp continuous_snd).continuousOn)
  · exact Complex.continuous_re.comp_continuousOn
      (continuousOn_orientedDensity (sphereFrame k) (sphereVolume k) hD
        (continuous_subtype_val.comp continuous_snd).continuousOn)
  · intro s hs x
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hd s hs x)
  · exact ht

end Mahler

end OAI
