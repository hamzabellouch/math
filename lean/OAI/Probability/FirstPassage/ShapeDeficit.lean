import OAI.Probability.FirstPassage.LocalTravel

namespace OAI

namespace PlanarFPP
open MeasureTheory Filter Set
open scoped Topology

theorem UniformShape.no_linear_deficit (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (μ f : Plane → ℝ) (hu : UniformShape w μ) (hf : ∀ v, f v ≤ μ v)
    (z : ℕ → Vertex) (ds : ℕ → List Step) (C a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hescape : Tendsto (fun n => ‖latticeEmbed (z n)‖) atTop atTop)
    (hbound : ∀ n, ‖latticeEmbed (z n)‖ ≤ B*((n : ℝ)+1))
    (hend : ∀ n, displacement (ds n)=z n)
    (hcost : ∀ n, pathCost w 0 (ds n) ≤ f (latticeEmbed (z n))+C-a*n) : False := by
  obtain ⟨R,hR,hr⟩ := hu (a/(2*B)) (by positivity)
  have hlarge : ∀ᶠ n : ℕ in atTop, 2*C/a+2 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨n,hnR,hn⟩ := ((hescape.eventually (eventually_ge_atTop R)).and hlarge).exists
  have he := hr (z n) hnR
  have hlow := (abs_le.mp he).1
  have hpass := passageTime_le_cost w hw 0 (z n) (ds n) (by simpa using hend n)
  have hprod := mul_le_mul_of_nonneg_left (hbound n) (show 0 ≤ a/(2*B) by positivity)
  have hid : a/(2*B)*(B*((n : ℝ)+1))=a/2*((n : ℝ)+1) := by field_simp
  rw [hid] at hprod
  have hn' := (div_lt_iff₀ ha).mp (show 2*C/a < (n : ℝ)-2 by linarith)
  have hs := hf (latticeEmbed (z n))
  have hc := hcost n
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_no_linear_deficit (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (f : Plane → ℝ) (hf : ∀ v, f v ≤ μ v) :
    ∀ᵐ ω ∂P, ¬∃ (z : ℕ → Vertex) (ds : ℕ → List Step) (C a B : ℝ),
      0 < a ∧ 0 < B ∧
      Tendsto (fun n => ‖latticeEmbed (z n)‖) atTop atTop ∧
      (∀ n, ‖latticeEmbed (z n)‖ ≤ B*((n : ℝ)+1)) ∧
      (∀ n, displacement (ds n)=z n) ∧
      (∀ n, pathCost (fun e => τ e ω) 0 (ds n) ≤ f (latticeEmbed (z n))+C-a*n) := by
  filter_upwards [h.ae_positive,exponential_uniform_shape h μ hμ ht] with ω hw hu
  rintro ⟨z,ds,C,a,B,ha,hB,hesc,hbound,hend,hcost⟩
  exact hu.no_linear_deficit _ (fun e => (hw e).le) μ f hf z ds C a B ha hB hesc hbound hend hcost

end PlanarFPP

end OAI
