import OAI.MeasureTheory.Falconer.Estimates.ActualDistanceTerminal
import OAI.MeasureTheory.Falconer.Geometry.PositiveDistanceBins
import OAI.MeasureTheory.Falconer.Angular.ActualAngularTerminal
import OAI.MeasureTheory.Falconer.Angular.AngularStateData
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem PositiveDistanceData.terminal_power (d : PositiveDistanceData) {B : ℕ} {δ eps : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hN : 0 < d.N) (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (ht : d.t ≤ d.a+100*d.q) (heps : 0 ≤ eps) :
    d.coincidence ≠ ⊤ ∧
    d.coincidence.toReal ≤ ((2:ℝ)^d.N)^(200*(d.q:ℝ)/d.N+12*d.lam+eps) := by
  let := hd.probability
  refine ⟨d.coincidence_ne_top,(d.actual_distance_terminal hd ha hX hY ht).trans ?_⟩
  rw [two_rpow_as_scale d.N hN,← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N)]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

theorem AngularStateData.terminal_bound (d : AngularStateData) {B : ℕ} {δ W : ℝ}
    (hd : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass)
    (hQ : 0 < d.Q.side) (ha : d.a ≤ d.N) (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (ht : d.v ≤ d.a+100*d.q) (K : ℕ)
    (k : Fin 2 → PolicyDescriptor → ℕ) (hk : ∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (Ψ : ℝ → ℝ) (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    d.energy k h Ψ ≠ ⊤ ∧ (d.energy k h Ψ).toReal ≤
      (4*W*(symbolDerivativeConstant K^K)^4*(sourceArcLength.real univ)^2)*
        (2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) := by
  have htR : (d.v:ℝ) ≤ (d.a:ℝ)+100*d.q := by exact_mod_cast ht
  have hp : ∀ l : Fin 2, (![d.X,d.Y] l).length = d.a := by
    intro l
    fin_cases l <;> simp [hX,hY]
  exact actual_inherited_angular_terminal (fun _ => d.retainedList d.a) (fun _ => id) k K hk
    (fun _ => d.Q) (fun _ => hQ) (fun _ => d.ρ) (fun _ => d.mass) d.N B δ d.lam d.sig
    (fun _ => hd) d.J d.i h hh hhb d.a d.q ha ![d.X,d.Y] hp d.v (by linarith) Ψ hW hw hs

theorem uniform_angular_state_terminal (K : ℕ) {eps W : ℝ} (heps : 0 < eps) (hW : 0 ≤ W)
    (Ψ : ℝ → ℝ) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ d : AngularStateData, N₀ ≤ d.N →
      0 < d.Q.side → d.a ≤ d.N → d.X.length = d.a → d.Y.length = d.a →
      d.v ≤ d.a+100*d.q → ∀ B : ℕ, ∀ δ : ℝ,
      RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ e ∈ d.retainedList d.a, k l e ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      d.energy k h Ψ ≠ ⊤ ∧
      (d.energy k h Ψ).toReal ≤ ((2:ℝ)^d.N)^(200*(d.q:ℝ)/d.N+12*d.lam+eps) := by
  let C := 4*W*(symbolDerivativeConstant K^K)^4*(sourceArcLength.real univ)^2
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed heps C
  refine ⟨max 1 N₁,by omega,?_⟩
  intro d hN hQ ha hX hY ht B δ hd k hk h hh hhb
  have hb := d.terminal_bound hd hQ ha hX hY ht K k hk h hh hhb Ψ hW hw hs
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hc := h₁ d.N (by omega)
  change C*(2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) ≤ _
  calc
    _ ≤ ((2:ℝ)^d.N)^eps*(2:ℝ)^(200*(d.q:ℝ))*((2:ℝ)^d.N)^(12*d.lam) := by
      gcongr
    _ = _ := by
      rw [two_rpow_as_scale d.N (by omega),← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N),
        ← Real.rpow_add (by positivity : 0 < (2:ℝ)^d.N)]
      congr 1
      ring

end PlanarFalconer

end OAI
