import OAI.Probability.GammaPassage.UniformShape

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

abbrev UniformShape := UniformShapeBridge.UniformShape

@[simp] theorem uniformShape_iff_gamma (w : Edge → ℝ) (μ : Plane → ℝ) :
    UniformShape w μ ↔ UniformShapeBridge.UniformShape w μ := Iff.rfl

/-- A supporting functional cannot be beaten by a linear amount along a
linearly bounded escaping sequence of endpoints, even if that sequence was
chosen after seeing the weights. -/
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

end GammaFPP.CrossingBridge

end OAI
