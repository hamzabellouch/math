import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.FiniteInterpolation
import OAI.Probability.CriticalPercolation.Criticality.InterpolationUniform

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph

variable {V E : Type*} [Fintype V] [Fintype E]

theorem finite_interpolation_uniform (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (hd : 2≤d) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c ε : ℝ} (hc : 0<c) (hε : 0<ε) (hεp : ε≤p) (hεq : ε≤1-p)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) :
    ∃ j<d, 0 < prob w (endpointEvent G (x j) (x (j+1)) s) ∧
      -Real.log (prob w (endpointEvent G (x j) (x (j+1)) s)) ≤
        interpolationConstant c ε *
          (Real.log (1/prob w (endpointEvent G (x 0) (x d) s))+Nat.clog 2 d+1) := by
  have hw := homogeneous_normalized w p h0 h1
  have hn := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  have hc1 : c≤1 := (hconn 0 1 (by omega) (by omega) (by omega)).trans (prob_le_one w hw hn _)
  obtain ⟨j,hj,hpos,hbound⟩ := finite_interpolation_index G d x hd hp w h0 h1 hc hconn s hδ
  exact ⟨j,hj,hpos,hbound.trans
    (interpolation_uniform_algebra hp hc hc1 hε hεp hεq hδ (prob_le_one w hw hn _) _)⟩

theorem finite_interpolation_edge (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (hd : 2≤d) (path : Fin d → E)
    (hpath : ∀ j : Fin d, G.ends (path j) = s(x j,x (j+1)))
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c ε : ℝ} (hc : 0<c) (hε : 0<ε) (hεp : ε≤p) (hεq : ε≤1-p)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) :
    ∃ j : Fin d, G.ends (path j) = s(x j,x (j+1)) ∧
      0 < prob w (endpointEvent G (x j) (x (j+1)) s) ∧
      -Real.log (prob w (endpointEvent G (x j) (x (j+1)) s)) ≤
        interpolationConstant c ε *
          (Real.log (1/prob w (endpointEvent G (x 0) (x d) s))+Nat.clog 2 d+1) := by
  obtain ⟨j,hj,hpos,hbound⟩ := finite_interpolation_uniform G d x hd hp w h0 h1 hc hε hεp hεq hconn s hδ
  exact ⟨⟨j,hj⟩,hpath ⟨j,hj⟩,hpos,hbound⟩

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
