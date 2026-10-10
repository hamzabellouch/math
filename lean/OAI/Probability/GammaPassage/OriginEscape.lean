import OAI.Probability.GammaPassage.UniformShape

namespace OAI

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.UniformShapeBridge
open MeasureTheory Filter Set
open scoped Topology

theorem pathCost_take_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (i : ℕ) :
    pathCost w p (ds.take i) ≤ pathCost w p ds := by
  have he := pathCost_append w p (ds.take i) (ds.drop i)
  rw [List.take_append_drop] at he
  have hn := pathCost_nonneg hw (p+displacement (ds.take i)) (ds.drop i)
  linarith

/-- Every vertex of a finite path, including the final vertex, is tested. -/
def PathIn (p : Vertex) (ds : List Step) (S : Set Vertex) : Prop :=
  ∀ i ≤ ds.length, p+displacement (ds.take i) ∈ S

theorem path_confined_of_escape (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (R a : ℝ)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hcost : pathCost w p ds < a) :
    PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  intro i _
  change ‖latticeEmbed (p+displacement (ds.take i)-p)‖ < R
  by_contra hn
  have he := hescape (p+displacement (ds.take i)) (le_of_not_gt hn)
  have hp := passageTime_le_cost w hw p (p+displacement (ds.take i)) (ds.take i) rfl
  have ht := pathCost_take_le w hw p ds i
  linarith

/-- Approximate passage-time minimizers with any positive error bound control
the cost of escaping a ball. -/
theorem exists_confined_near_optimal (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R a ε : ℝ) (hε : 0 < ε)
    (hescape : ∀ z, R ≤ ‖latticeEmbed (z-p)‖ → a ≤ passageTime w p z)
    (hshort : passageTime w p q + ε ≤ a) :
    ∃ ds, p+displacement ds=q ∧ pathCost w p ds < passageTime w p q+ε ∧
      PathIn p ds {z | ‖latticeEmbed (z-p)‖ < R} := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  exact ⟨ds,hend,hcost,path_confined_of_escape w hw p ds R a hescape (hcost.trans_le hshort)⟩

/-- The origin escape lower bound in cr:local-travel follows from the exact
outside-ball estimate. The radius and scale are real, as in the source. -/
theorem eventually_escape_of_uniformShape (w : Edge → ℝ) (μ : Plane → ℝ)
    (hu : UniformShape w μ) (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hlower : ∀ v, α*‖v‖ ≤ μ v) :
    ∀ᶠ s : ℝ in atTop, ∀ z : Vertex, δ*s/3 ≤ ‖latticeEmbed z‖ →
      α*δ*s/6 ≤ passageTime w 0 z := by
  obtain ⟨R,hR,hr⟩ := hu (α/2) (by linarith)
  filter_upwards [eventually_ge_atTop (3*R/δ)] with s hs
  intro z hz
  have hRz : R ≤ ‖latticeEmbed z‖ := by
    have ht := (div_le_iff₀ hδ).mp hs
    nlinarith
  have he := (abs_le.mp (hr z hRz)).1
  have hl := hlower (latticeEmbed z)
  have ht := mul_le_mul_of_nonneg_left hz hα.le
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- A lower bound for the Gamma mean norm gives an eventual origin-escape
estimate on a probability-one event. -/
theorem ae_eventually_origin_escape
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hlower : ∀ v, α*‖v‖ ≤ gammaMeanNorm h hs hr v) :
    ∀ᵐ ω ∂P, ∀ᶠ s : ℝ in atTop, ∀ z : Vertex,
      δ*s/3 ≤ ‖latticeEmbed z‖ → α*δ*s/6 ≤ passageTime (fun e => τ e ω) 0 z := by
  filter_upwards [h.uniform_shape hs hr] with ω hω
  exact eventually_escape_of_uniformShape _ _ hω α δ hα hδ hlower

end GammaFPP.IntervalTravelBridge

end OAI
