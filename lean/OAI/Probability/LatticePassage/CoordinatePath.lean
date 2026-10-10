import OAI.Probability.LatticePassage.Geodesic

namespace OAI

namespace CompanionFPP

private theorem horizontal_length (a b : ℤ) (n : ℕ) :
    ∃ p : lattice.Walk (a, b) (a + (n : ℤ), b), p.length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih
    have h : lattice.Adj (a + (n : ℤ), b) (a + ((n+1 : ℕ) : ℤ), b) := by
      change |a + (n : ℤ) - (a + ((n+1 : ℕ) : ℤ))| + |b - b| = 1
      simp
    exact ⟨p.concat h, by simp [hp]⟩

private theorem vertical_length (a b : ℤ) (n : ℕ) :
    ∃ p : lattice.Walk (a, b) (a, b + (n : ℤ)), p.length = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨p,hp⟩ := ih
    have h : lattice.Adj (a, b + (n : ℤ)) (a, b + ((n+1 : ℕ) : ℤ)) := by
      change |a - a| + |b + (n : ℤ) - (b + ((n+1 : ℕ) : ℤ))| = 1
      simp
    exact ⟨p.concat h, by simp [hp]⟩

theorem horizontal_coordinate_length (a c b : ℤ) :
    ∃ p : lattice.Walk (a,b) (c,b), p.length = (c-a).natAbs := by
  by_cases h : a ≤ c
  · have he : a + ((c-a).toNat : ℤ) = c := by omega
    have hn : (c-a).toNat = (c-a).natAbs := by omega
    have hh := horizontal_length a b (c-a).toNat
    rw [he] at hh
    simpa only [hn] using hh
  · have he : c + ((a-c).toNat : ℤ) = a := by omega
    obtain ⟨p,hp⟩ := horizontal_length c b (a-c).toNat
    have hn : (a-c).toNat = (c-a).natAbs := by omega
    have hq : ∃ p : lattice.Walk (c,b) (a,b), p.length = (c-a).natAbs := by
      have hh : ∃ p : lattice.Walk (c,b) (c + ((a-c).toNat : ℤ),b),
          p.length = (a-c).toNat := ⟨p,hp⟩
      rw [he] at hh
      simpa only [hn] using hh
    obtain ⟨q,hq⟩ := hq
    exact ⟨q.reverse, by simpa using hq⟩

theorem vertical_coordinate_length (a b c : ℤ) :
    ∃ p : lattice.Walk (a,b) (a,c), p.length = (c-b).natAbs := by
  by_cases h : b ≤ c
  · have he : b + ((c-b).toNat : ℤ) = c := by omega
    have hn : (c-b).toNat = (c-b).natAbs := by omega
    have hh := vertical_length a b (c-b).toNat
    rw [he] at hh
    simpa only [hn] using hh
  · have he : c + ((b-c).toNat : ℤ) = b := by omega
    have hn : (b-c).toNat = (c-b).natAbs := by omega
    have hq : ∃ p : lattice.Walk (a,c) (a,b), p.length = (c-b).natAbs := by
      have hh := vertical_length a c (b-c).toNat
      rw [he] at hh
      simpa only [hn] using hh
    obtain ⟨q,hq⟩ := hq
    exact ⟨q.reverse, by simpa using hq⟩

def latticeDistance (x y : Vertex) : ℕ := (y.1-x.1).natAbs + (y.2-x.2).natAbs

theorem coordinate_path (x y : Vertex) :
    ∃ p : lattice.Walk x y, p.IsPath ∧ p.length ≤ latticeDistance x y := by
  classical
  obtain ⟨p,hp⟩ := horizontal_coordinate_length x.1 y.1 x.2
  obtain ⟨q,hq⟩ := vertical_coordinate_length y.1 x.2 y.2
  refine ⟨(p.append q).bypass, (p.append q).bypass_isPath, ?_⟩
  exact (p.append q).length_bypass_le_length.trans (by simp [hp, hq, latticeDistance])

end CompanionFPP

end OAI
