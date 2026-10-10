import OAI.GroupTheory.PolycyclicRecognition.Algebra.LocalGeneratorAccessibility
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalFlowLabel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowStepIteration

namespace OAI

/-! # Local profile affinity from the actual finite flow labels

The proof uses admissible generator words and the inverse function theorem;
it does not assume a smooth profile or a hypoellipticity conclusion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory Module

variable {V W I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype I]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {c : ℕ} (a : DynkinCoefficients c 2) (B : V →L[ℝ] V →L[ℝ] V)
  (hB : IsLieBracket B) (hg : PolynomialGroupLaws (dynkinProduct a B))
  (hc : ExponentialConjugationLaw (dynkinProduct a B) B)
  (X : I → V) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma I)
  (hw₀ : ∀ j, evalBilinearWord B X (w₀ j) = b₀ j)

include hB hc hw₀

theorem affine_of_small_generator_increments
    (U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W)
    (π : PolynomialCoordinateGroup (dynkinProduct a B) hg →* Multiplicative W)
    (p : V →L[ℝ] W)
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (A : W →L[ℝ] W) {T : ℝ} (hT : 0 < T)
    (hstep : ∀ g ∈ U, ∀ i s, s ∈ Icc 0 T →
      f (g * PolynomialCoordinateGroup.exp _ hg (s • X i)) = f g + s • A (p (X i))) :
    ∃ b : W, ∀ g ∈ U, f g = A (π g).toAdd + b := by
  let Exp := PolynomialCoordinateGroup.exp (dynkinProduct a B) hg
  let F := fun g => f g - A (π g).toAdd
  have hFstep (i : I) (g) (hgU : g ∈ U) (s : ℝ) (hs : s ∈ Icc 0 T) :
      F (g * Exp (s • X i)) = F g := by
    have hp : (π (g * Exp (s • X i))).toAdd = (π g).toAdd + s • p (X i) := by
      rw [map_mul]
      change (π g).toAdd + (π (Exp (s • X i))).toAdd = _
      rw [hπExp, map_smul]
    dsimp [F]
    rw [hstep g hgU i s hs, hp, map_add, map_smul]
    abel
  have hflow (i : I) (g) (t : ℝ)
      (hst : g ∈ flowLineBase U Exp (t • X i) 1) : F (g * Exp (t • X i)) = F g :=
    eq_on_flow_of_small_steps F U Exp (by rfl)
      (PolynomialCoordinateGroup.exp_add_smul _ hg) (X i) hT (hFstep i) hst
  obtain ⟨x, hx⟩ := hne
  refine ⟨F x, ?_⟩
  intro g hgU
  have he : F g = F x := eq_of_generator_flow_invariance a B hB hg hc X b₀ w₀ hw₀
    U hU hconn F hflow hgU hx
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem affine_on_flow_neighborhood
    {L : Type*} [Finite L]
    [MeasurableSpace (PolynomialCoordinateGroup (dynkinProduct a B) hg)]
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a B) hg)) [μ.IsOpenPosMeasure]
    (Ω U : Set (PolynomialCoordinateGroup (dynkinProduct a B) hg))
    (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : PolynomialCoordinateGroup (dynkinProduct a B) hg → W) (hf : ContinuousOn f Ω)
    (π : PolynomialCoordinateGroup (dynkinProduct a B) hg →* Multiplicative W)
    (p : V →L[ℝ] W)
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (A : L → W →L[ℝ] W) {T : ℝ} (hT : 0 < T)
    (hstay : ∀ i, U ⊆ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (X i) T)
    (hline : ∀ i g, g ∈ U → ∀ t ∈ Icc 0 T,
      f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)) =
        f g + t • flowLineSlope f (PolynomialCoordinateGroup.exp _ hg) (X i) T g)
    (hderiv : ∀ᵐ g ∂μ, g ∈ U → ∃ l, ∀ i,
      HasDerivAt (fun t : ℝ => f (g * PolynomialCoordinateGroup.exp _ hg (t • X i)))
        (A l (p (X i))) 0) :
    ∃ l b, ∀ g ∈ U, f g = A l (π g).toAdd + b := by
  let : IsTopologicalGroup (PolynomialCoordinateGroup (dynkinProduct a B) hg) :=
    PolynomialCoordinateGroup.isTopologicalGroup _ hg
      (continuous_dynkinProduct a (fun _ => B) Prod.fst Prod.snd
        continuous_const continuous_fst continuous_snd)
  obtain ⟨l, hl⟩ := exists_single_label_on_flow_neighborhood
    (G := PolynomialCoordinateGroup (dynkinProduct a B) hg) μ
    (PolynomialCoordinateGroup.exp (dynkinProduct a B) hg)
    (PolynomialCoordinateGroup.expHomeomorph _ hg).continuous (by rfl)
    X (fun l => (A l).comp p) Ω U hU hconn hne f hf hT hstay hline hderiv
  obtain ⟨b, hb⟩ := affine_of_small_generator_increments a B hB hg hc X b₀ w₀ hw₀
    U hU hconn hne f π p hπExp (A l) hT (fun g hg i s hs => hl g hg i s hs)
  exact ⟨l, b, hb⟩

end PolycyclicRecognition

end

end OAI
