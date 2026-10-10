import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineProfileGluing
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowNeighborhoods
import Mathlib.Topology.Algebra.Module.LocallyConvex

namespace OAI

/-! # Affine flow lines and finite derivative labels give global profile affinity -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Module

theorem global_affine_of_finite_derivative_and_flow_lines
    {V W I J L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype I] [Finite L]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
    (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
    (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
    (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
    (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)
    [MeasurableSpace (PolynomialCoordinateGroup (dynkinProduct a B) hg)]
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a B) hg)) [μ.IsOpenPosMeasure]
    (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W) (hf : ContinuousOn f Ω)
    (π : PolynomialCoordinateGroup (dynkinProduct a B) hg →* Multiplicative W)
    (p : V →L[ℝ] W) (hp : Function.Surjective p)
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (A : L → W →L[ℝ] W)
    (hline : ∀ i T, 0 < T → ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (X i) T,
      ∀ t ∈ Icc 0 T, f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)) =
        f g + t • flowLineSlope f (PolynomialCoordinateGroup.exp _ hg) (X i) T g)
    (hderiv : ∀ᵐ g ∂μ, g ∈ Ω → ∃ l, ∀ i,
      HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)))
        (A l (p (X i))) 0) :
    ∃ l b, ∀ g ∈ Ω, f g = A l (π g).toAdd + b := by
  let G := PolynomialCoordinateGroup (dynkinProduct a B) hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph _ hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => B) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  let : LocallyConnectedSpace G := e.symm.isOpenEmbedding.locallyConnectedSpace
  have hπopen : IsOpenMap (fun g : G => (π g).toAdd) := by
    have heq : (fun g : G => (π g).toAdd) = p ∘ e.symm := by
      funext g
      have h := hπExp (e.symm g)
      change (π (e (e.symm g))).toAdd = p (e.symm g) at h
      simpa only [e.apply_symm_apply, Function.comp_apply] using h
    rw [heq]
    exact (p.toLinearMap.isOpenMap_of_finiteDimensional hp).comp e.symm.isOpenMap
  apply exists_global_affine_of_local (fun g => (π g).toAdd) hπopen A f hconn hne
  intro g hgΩ
  obtain ⟨T, hT, N, hNo, hgN, hNc, hNΩ, hstay⟩ :=
    exists_connected_flow_neighborhood Ω hΩ (PolynomialCoordinateGroup.exp _ hg)
      e.continuous (by rfl) X hgΩ
  have hd : ∀ᵐ x ∂μ, x ∈ N → ∃ l, ∀ i,
      HasDerivAt (fun t : ℝ => f (x * PolynomialCoordinateGroup.exp _ hg (t • X i)))
        (A l (p (X i))) 0 := by
    filter_upwards [hderiv] with x hx hxN
    exact hx (hNΩ hxN)
  obtain ⟨l, b, hab⟩ := affine_on_flow_neighborhood a B hB hg hc X b₀ w₀ hw₀
    μ Ω N hNo hNc.isPreconnected hNc.nonempty f hf π p hπExp A hT hstay
    (fun i x hx t ht => hline i T hT x (hstay i hx) t ht) hd
  exact ⟨N, hNo, hgN, hNΩ, l, b, hab⟩

end PolycyclicRecognition

end

end OAI
