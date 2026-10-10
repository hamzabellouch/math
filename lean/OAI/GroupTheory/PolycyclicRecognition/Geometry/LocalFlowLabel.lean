import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteFlowSlopes
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace OAI

/-! # One finite label on a connected family of admissible flow lines -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter

theorem exists_label_of_continuous_slopes
    {X W J L : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype J] [Finite L]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    {U : Set X} (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (c : X → J → W) (hc : ∀ j, ContinuousOn (fun x => c x j) U)
    (A : L → J → W)
    (hae : ∀ᵐ x ∂μ, x ∈ U → ∃ l, ∀ j, c x j = A l j) :
    ∃ l, ∀ x ∈ U, ∀ j, c x j = A l j := by
  have hc' : ContinuousOn c U := continuousOn_pi.mpr hc
  have hmaps : MapsTo c U (range A) := by
    apply mapsTo_closed_of_ae μ hU hc' (finite_range A).isClosed
    filter_upwards [hae] with x hx hxU
    obtain ⟨l, hl⟩ := hx hxU
    exact ⟨l, (funext hl).symm⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, hl⟩ := hmaps hx
  refine ⟨l, ?_⟩
  intro y hy j
  have he := hconn.constant_of_mapsTo (finite_range A).isDiscrete hc' hmaps hy hx
  exact congrFun (he.trans hl.symm) j

theorem flowLineSlope_eq_of_hasDerivAt
    {G V W : Type*} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : G → W) (Exp : V → G) (hExp0 : Exp 0 = 1) (v : V) (g : G)
    {T : ℝ} (hT : 0 < T) {q : W}
    (hline : ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g)
    (hd : HasDerivAt (fun t : ℝ => f (g * Exp (t • v))) q 0) :
    flowLineSlope f Exp v T g = q := by
  have ha : HasDerivAt (fun t : ℝ => f g + t • flowLineSlope f Exp v T g)
      (flowLineSlope f Exp v T g) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (flowLineSlope f Exp v T g)).const_add (f g)
  have hb := ha.hasDerivWithinAt.congr hline (by simp [hExp0])
  exact (uniqueDiffOn_Icc hT 0 ⟨le_rfl, hT.le⟩).eq_deriv _ hb hd.hasDerivWithinAt

theorem exists_single_label_on_flow_neighborhood
    {G V W J L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype J] [Finite L]
    (μ : Measure G) [μ.IsOpenPosMeasure]
    (Exp : V → G) (hExp : Continuous Exp) (hExp0 : Exp 0 = 1)
    (v : J → V) (A : L → V →L[ℝ] W)
    (Ω U : Set G) (hU : IsOpen U) (hconn : IsPreconnected U) (hne : U.Nonempty)
    (f : G → W) (hf : ContinuousOn f Ω) {T : ℝ} (hT : 0 < T)
    (hstay : ∀ j, U ⊆ flowLineBase Ω Exp (v j) T)
    (hline : ∀ j g, g ∈ U → ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v j)) = f g + t • flowLineSlope f Exp (v j) T g)
    (hderiv : ∀ᵐ g ∂μ, g ∈ U → ∃ l, ∀ j,
      HasDerivAt (fun t : ℝ => f (g * Exp (t • v j))) (A l (v j)) 0) :
    ∃ l, ∀ g ∈ U, ∀ j t, t ∈ Icc 0 T →
      f (g * Exp (t • v j)) = f g + t • A l (v j) := by
  have hc (j : J) : ContinuousOn (fun g => flowLineSlope f Exp (v j) T g) U :=
    (continuousOn_flowLineSlope hExp hExp0 hT.le hf).mono (hstay j)
  have hlabels : ∀ᵐ g ∂μ, g ∈ U → ∃ l, ∀ j,
      flowLineSlope f Exp (v j) T g = A l (v j) := by
    filter_upwards [hderiv] with g hg hgU
    obtain ⟨l, hl⟩ := hg hgU
    exact ⟨l, fun j => flowLineSlope_eq_of_hasDerivAt f Exp hExp0 (v j) g
      hT (hline j g hgU) (hl j)⟩
  obtain ⟨l, hl⟩ := exists_label_of_continuous_slopes μ hU hconn hne
    (fun g j => flowLineSlope f Exp (v j) T g) hc (fun l j => A l (v j)) hlabels
  refine ⟨l, ?_⟩
  intro g hg j t ht
  rw [hline j g hg t ht, hl g hg j]

end PolycyclicRecognition

end

end OAI
