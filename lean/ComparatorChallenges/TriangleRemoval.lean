import Mathlib

namespace OAI

section
section

open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

abbrev Graph (n : ℕ) := Finset (Finset (Fin n))

def completeGraph (n : ℕ) : Graph n := Finset.univ.powersetCard 2

def triangles {n : ℕ} (G : Graph n) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter (fun t => t.powersetCard 2 ⊆ G)

noncomputable def step {n : ℕ} (G : Graph n) : PMF (Graph n) :=
  if h : (triangles G).Nonempty then
    (PMF.uniformOfFinset (triangles G) h).map (fun t => G \ t.powersetCard 2)
  else PMF.pure G

noncomputable def evolve {n : ℕ} (G : Graph n) : ℕ → PMF (Graph n)
  | 0 => PMF.pure G
  | k + 1 => (evolve G k).bind step

noncomputable def terminalLaw (n : ℕ) : PMF (Graph n) :=
  evolve (completeGraph n) (n.choose 2)

noncomputable def expectation (n : ℕ) (f : Graph n → ℝ) : ℝ :=
  ∑ G, (terminalLaw n G).toReal * f G

noncomputable def probability (n : ℕ) (P : Graph n → Prop) : ℝ := by
  classical
  exact expectation n (fun G => if P G then 1 else 0)

noncomputable def normalization (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)

noncomputable def normalizedLeave (n : ℕ) (G : Graph n) : ℝ :=
  (G.card : ℝ) / normalization n

noncomputable def sharpConstant : ℝ := 1 / (2 * Real.sqrt 2)

end SharpTerminalLeave
end
end

open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem sharp_terminal_leave :
    Tendsto (fun n => expectation n (fun G =>
      (normalizedLeave n G - sharpConstant) ^ 2)) atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => probability n (fun G =>
        ε < |normalizedLeave n G - sharpConstant|)) atTop (𝓝 0)) ∧
    Tendsto (fun n => expectation n (fun G => (G.card : ℝ)) / normalization n)
      atTop (𝓝 sharpConstant) := by
  sorry

end SharpTerminalLeave

end OAI
