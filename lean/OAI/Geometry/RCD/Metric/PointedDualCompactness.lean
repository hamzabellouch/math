import OAI.Geometry.RCD.Metric.PointedDualLimit
import OAI.Geometry.RCD.Metric.CountablePointedCompactness

namespace OAI

/-! # A common Euclidean limit of two source potentials -/

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem pointed_dual_compactness {n : ℕ} {S A : ℝ} (hS : 0≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsPointedApproximation (p k) 0 (r k) S (ε k) (v k))
    (φ ψ : ℕ → X → ℝ) (L : ℝ≥0)
    (hφb : ∀ k x, dist x (p k)≤S*r k → |φ k x|≤A)
    (hψb : ∀ k x, dist x (p k)≤S*r k → |ψ k x|≤A)
    (hφl : ∀ k x y, dist x (p k)≤S*r k → dist y (p k)≤S*r k →
      |φ k x-φ k y|≤(L:ℝ)*(dist x y/r k))
    (hψl : ∀ k x y, dist x (p k)≤S*r k → dist y (p k)≤S*r k →
      |ψ k x-ψ k y|≤(L:ℝ)*(dist x y/r k))
    (had : ∀ k x y, φ k x+ψ k y≤(dist x y/r k)^2/2) :
    ∃ (f g : Euclidean n → ℝ) (t : ℕ → ℕ),
      StrictMono t ∧ LipschitzWith L f ∧ LipschitzWith L g ∧
      (∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
        dist x (p (t k))≤S*r (t k) → |φ (t k) x-f (v (t k) x)|<δ) ∧
      (∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ x,
        dist x (p (t k))≤S*r (t k) → |ψ (t k) x-g (v (t k) x)|<δ) ∧
      (∀ a b : Euclidean n, ‖a‖<S → ‖b‖<S → f a+g b≤dist a b^2/2) := by
  classical
  let u := fun m : ℕ => if m=0 then φ else ψ
  have hu (m k : ℕ) (x : X) (hx : dist x (p k)≤S*r k) : |u m k x|≤A := by
    dsimp only [u]
    split_ifs <;> first | exact hφb k x hx | exact hψb k x hx
  have hl (m k : ℕ) (x y : X) (hx : dist x (p k)≤S*r k)
      (hy : dist y (p k)≤S*r k) : |u m k x-u m k y|≤(L:ℝ)*(dist x y/r k) := by
    dsimp only [u]
    split_ifs <;> first | exact hφl k x y hx hy | exact hψl k x y hx hy
  obtain ⟨F,t,ht,hF⟩ := countable_pointed_function_compactness hS p r ε v hr hε hε1
    hεlim hv u (fun _ => L) (fun _ => A) hu hl
  have hf := hF 0
  have hg := hF 1
  simp only [u,ite_true,show ¬(1:ℕ)=0 from by decide,ite_false] at hf hg
  refine ⟨F 0,F 1,t,ht,hf.1,hg.1,hf.2,hg.2,?_⟩
  intro a b ha hb
  exact pointed_dual_limit (p ∘ t) (r ∘ t) (ε ∘ t) (v ∘ t)
    (hεlim.comp ht.tendsto_atTop) (fun k => hv (t k)) (fun k => φ (t k))
    (fun k => ψ (t k)) hf.1.continuous hg.1.continuous hf.2 hg.2
    (fun k => had (t k)) ha hb

end RegularPointCoordinates

end

end OAI
