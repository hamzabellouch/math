import OAI.Probability.BenjaminiSchramm.HeightMaximumSlices
import OAI.Probability.BenjaminiSchramm.TruncatedFractionalSummation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem layer_fractional_of_truncated_moments
    (p : unitInterval) (D I : Set E) (W : Set V) (f : V → ℝ) (s : ℝ) (hs : 0 < s)
    (x : V) (hx : f x=0) (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (C B : ℝ≥0∞) (t : ℝ)
    (htrunc : ∀ n : ℕ, (∫⁻ ω,
      (restrictedHit G D x {z | s*((n : ℝ)+1) ≤ f z})ᶜ.indicator
        (fun ω => restrictedLayerCount G I W ω x) ω ∂law p) ≤
        C*ENNReal.ofReal (Real.exp (t*n)))
    (hhit : ∀ n : ℕ, law p (restrictedHit G D x {z | s*n ≤ f z}) ≤
      B*ENNReal.ofReal (Real.exp (-s*n)))
    {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hδ : 0 ≤ δ) (hδa : δ ≤ 1-a) :
    (∫⁻ ω, (restrictedLayerCount G I W ω x)^a ∂law p) ≤
      C^a*B^δ*(∑' n : ℕ, ENNReal.ofReal (Real.exp ((t*a-s*δ)*n))) := by
  let S := fun n => heightMaximumSlice G D f s n x
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_heightMaximumSlice G D f s n x
  have hfirst (n : ℕ) : (∫⁻ ω in S n, restrictedLayerCount G I W ω x ∂law p) ≤
      C*ENNReal.ofReal (Real.exp (t*n)) := by
    have hm := (measurableSet_restrictedHit G D x {z | s*((n : ℝ)+1) ≤ f z}).compl
    apply le_trans (lintegral_mono_set (fun _ h => h.1))
    rw [←lintegral_indicator hm (fun ω => restrictedLayerCount G I W ω x)]
    exact htrunc n
  have hprob (n : ℕ) : law p (S n) ≤ B*ENNReal.ofReal (Real.exp (-s*n)) :=
    (measure_mono (fun _ h => h.2)).trans (hhit n)
  exact fractional_moment_of_height_slices (law p) S hS
    (ae_height_slices_cover G p D f s hs x hx hfin)
    (fun ω => restrictedLayerCount G I W ω x) (measurable_restrictedLayerCount G I W x)
    C B t s hfirst hprob ha ha1 hδ hδa

end Percolation.BenjaminiSchramm

end

end OAI
