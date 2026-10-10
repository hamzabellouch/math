import OAI.Geometry.HeilbronnTriangle.ParameterSampling
import OAI.Geometry.HeilbronnTriangle.IntegerSampling
import OAI.Geometry.HeilbronnTriangle.FiniteMixtures

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling

def ofMixture {Θ D : Type} [Fintype Θ] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (rho : Θ → ℝ) (p : D → ℝ)
    (a : Θ → D → Fin 3 → ZMod h)
    (V : Θ → Finset (Fin 3 → ZMod q))
    (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ θ, (V θ).card = s) : PointLaw where
  Environment := Θ
  Column := Box (L * (h * q)) 3 (samplingShift (L * (h * q)))
  environmentFintype := inferInstance
  columnFintype := inferInstance
  rho := rho
  mu := fun θ => mixtureWeight p (fun d => columnLaw h q L
    (samplingShift (L * (h * q))) (a θ d) (V θ) s)
  point := fun _ x => project x
  rho_nonneg := hrho
  rho_sum := hsum
  mu_nonneg := fun θ x => mixtureWeight_nonneg p _ hp
    (fun d x => columnLaw_nonneg h q L _ (a θ d) (V θ) s x) x
  mu_sum := fun θ => sum_mixtureWeight p _ hpsum
    (fun d => sum_columnLaw h q L hc hL _ (a θ d) (V θ) s hs (hV θ))
  in_square := fun _ x => project_in_unitSquare
    (mul_pos hL (mul_pos (NeZero.pos h) (NeZero.pos q))) x

def ofIndependentEnvironments {Θ Ω D : Type}
    [Fintype Θ] [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (rho : Θ → ℝ) (w : Ω → ℝ) (p : D → ℝ)
    (a : Θ → D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hrho : ∀ θ, 0 ≤ rho θ) (hsum : ∑ θ, rho θ = 1)
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) : PointLaw :=
  ofMixture h q L s hc hL hs (fun z : Θ × Ω => rho z.1 * w z.2) p
    (fun z d => a z.1 d) (fun z => V z.2)
    (fun z => mul_nonneg (hrho z.1) (hw z.2))
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, hwsum, mul_one]
      exact hsum)
    hp hpsum (fun z => hV z.2)

def ofSpecialLinear {Ω D : Type} [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) : PointLaw := by
  classical
  let G := Matrix.SpecialLinearGroup (Fin 3) (ZMod h)
  apply ofIndependentEnvironments h q L s hc hL hs
    (fun _ : G => 1 / (Nat.card G : ℝ)) w p (fun g d => g • c d) V
  · intro g
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
    exact mul_one_div_cancel (by positivity)
  · exact hw
  · exact hwsum
  · exact hp
  · exact hpsum
  · exact hV

end Problem355.IntegerPointLaw

end

end OAI
