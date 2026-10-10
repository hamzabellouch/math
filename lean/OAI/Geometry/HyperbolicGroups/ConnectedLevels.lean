import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V C : Type*}

lemma preconnected_color_constant (G : SimpleGraph V) (U : Set V)
    (hc : (G.induce U).Preconnected) (color : V → C)
    (hcolor : ∀ v ∈ U, ∀ w ∈ U, G.Adj v w → color v = color w) :
    ∀ v ∈ U, ∀ w ∈ U, color v = color w := by
  have hp : ∀ {v w : U}, (G.induce U).Walk v w → color v.val = color w.val := by
    intro v w p
    induction p with
    | nil => rfl
    | @cons v w u h p ih => exact (hcolor _ v.property _ w.property h).trans ih
  intro v hv w hw
  obtain ⟨p⟩ := hc ⟨v,hv⟩ ⟨w,hw⟩
  exact hp p

/-- A connected set avoiding an integer level cannot pass from below to
above it when adjacent depths differ by at most one. Isolated/empty
induced graphs are covered by Preconnected, with no global connectedness
or positivity assumption. -/
theorem connected_avoids_level (G : SimpleGraph V) (depth : V → ℤ)
    (hd : ∀ v w, G.Adj v w → depth v ≤ depth w+1 ∧ depth w ≤ depth v+1)
    (U : Set V) (hc : (G.induce U).Preconnected) (z : ℤ)
    (hz : ∀ v ∈ U, depth v ≠ z) :
    ∀ v ∈ U, ∀ w ∈ U, (depth v < z ↔ depth w < z) := by
  have hh := preconnected_color_constant G U hc (fun v => depth v < z) (by
    intro v hv w hw hadj
    apply propext
    have hvz := hz v hv
    have hwz := hz w hw
    have hdist := hd v w hadj
    omega)
  intro v hv w hw
  exact Iff.of_eq (hh v hv w hw)

lemma graph_dist_int_adj (G : SimpleGraph V) (r : V) :
    ∀ v w, G.Adj v w → (G.dist r v : ℤ) ≤ (G.dist r w : ℤ)+1 ∧
      (G.dist r w : ℤ) ≤ (G.dist r v : ℤ)+1 := by
  intro v w h
  have hh := h.diff_dist_adj (u := r)
  omega

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
