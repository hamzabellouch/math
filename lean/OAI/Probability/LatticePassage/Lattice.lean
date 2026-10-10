import OAI.Probability.LatticePassage.Environment
import Lean.Elab.Tactic.Omega

namespace OAI

namespace CompanionFPP

private theorem horizontal_nat (a b : ℤ) (n : ℕ) :
    Nonempty (lattice.Walk (a, b) (a + (n : ℤ), b)) := by
  induction n with
  | zero => simpa using (show Nonempty (lattice.Walk (a,b) (a,b)) from ⟨.nil⟩)
  | succ n ih =>
    obtain ⟨p⟩ := ih
    have h : lattice.Adj (a + (n : ℤ), b) (a + ((n+1 : ℕ) : ℤ), b) := by
      change |a + (n : ℤ) - (a + ((n+1 : ℕ) : ℤ))| + |b - b| = 1
      simp
    exact ⟨p.concat h⟩

private theorem vertical_nat (a b : ℤ) (n : ℕ) :
    Nonempty (lattice.Walk (a, b) (a, b + (n : ℤ))) := by
  induction n with
  | zero => simpa using (show Nonempty (lattice.Walk (a,b) (a,b)) from ⟨.nil⟩)
  | succ n ih =>
    obtain ⟨p⟩ := ih
    have h : lattice.Adj (a, b + (n : ℤ)) (a, b + ((n+1 : ℕ) : ℤ)) := by
      change |a - a| + |b + (n : ℤ) - (b + ((n+1 : ℕ) : ℤ))| = 1
      simp
    exact ⟨p.concat h⟩

theorem horizontal_walk (a c b : ℤ) : Nonempty (lattice.Walk (a,b) (c,b)) := by
  by_cases h : a ≤ c
  · have he : a + ((c-a).toNat : ℤ) = c := by omega
    simpa only [he] using horizontal_nat a b (c-a).toNat
  · have he : c + ((a-c).toNat : ℤ) = a := by omega
    have hp : Nonempty (lattice.Walk (c,b) (a,b)) := by
      simpa only [he] using horizontal_nat c b (a-c).toNat
    obtain ⟨p⟩ := hp
    exact ⟨p.reverse⟩

theorem vertical_walk (a b c : ℤ) : Nonempty (lattice.Walk (a,b) (a,c)) := by
  by_cases h : b ≤ c
  · have he : b + ((c-b).toNat : ℤ) = c := by omega
    simpa only [he] using vertical_nat a b (c-b).toNat
  · have he : c + ((b-c).toNat : ℤ) = b := by omega
    have hp : Nonempty (lattice.Walk (a,c) (a,b)) := by
      simpa only [he] using vertical_nat a c (b-c).toNat
    obtain ⟨p⟩ := hp
    exact ⟨p.reverse⟩

theorem lattice_walk (x y : Vertex) : Nonempty (lattice.Walk x y) := by
  obtain ⟨p⟩ := horizontal_walk x.1 y.1 x.2
  obtain ⟨q⟩ := vertical_walk y.1 x.2 y.2
  exact ⟨p.append q⟩

theorem passageTime_properties : ∀ᵐ ω ∂environmentLaw,
    (∀ x y, 0 ≤ passageTime ω x y) ∧
    (∀ x, passageTime ω x x = 0) ∧
    (∀ x y, passageTime ω x y = passageTime ω y x) ∧
    (∀ x y z, passageTime ω x z ≤ passageTime ω x y + passageTime ω y z) := by
  filter_upwards [all_edge_weights_positive] with ω hω
  have hn : ∀ e, 0 ≤ ω e := fun e => (hω e).le
  exact ⟨fun x y => passageTime_nonneg ω hn (lattice_walk x y),
    passageTime_self ω hn, passageTime_symm ω,
    fun x y z => passageTime_triangle ω hn (lattice_walk x y) (lattice_walk y z)⟩

end CompanionFPP

end OAI
