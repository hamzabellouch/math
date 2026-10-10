import OAI.Geometry.HeilbronnTriangle.IntegerPointLaw
import OAI.Geometry.HeilbronnTriangle.IntegerSharedCollisions

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling

theorem ofMixture_pairProbability_le {Θ D : Type} [Fintype Θ] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (rho : Θ → ℝ) (p : D → ℝ)
    (a : Θ → D → Fin 3 → ZMod h)
    (V : Θ → Finset (Fin 3 → ZMod q))
    (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ θ, (V θ).card = s) :
    (ofMixture h q L s hc hL hs rho p a V hrho hsum hp hpsum hV).pairProbability ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  exact IntegerSamplingPairs.shared_mixture_columnLaw_pairMass_le
    h q L (NeZero.pos h) (NeZero.pos q) hL rho hrho hsum
    (fun _ => p) (fun _ => hp) (fun _ => hpsum) a (fun θ _ => V θ)
    (fun _ _ => s) (fun _ _ => hs)

theorem ofSpecialLinear_pairProbability_le {Ω D : Type}
    [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).pairProbability ≤
      8 * ((h * q : ℕ) : ℝ) ^ 6 / ((L * (h * q) : ℕ) : ℝ) ^ 3 := by
  unfold ofSpecialLinear ofIndependentEnvironments
  apply ofMixture_pairProbability_le

end Problem355.IntegerPointLaw

end

end OAI
