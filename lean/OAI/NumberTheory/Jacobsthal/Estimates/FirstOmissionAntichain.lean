import OAI.NumberTheory.Jacobsthal.Primes.BoundaryPrimeMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
open FinitePathGeometry ReferenceAdmission

theorem admitted_prefix {w r : ℝ} {i : Side} {pre whole : List ℕ}
    (hpre : pre <+: whole) (hwhole : admitted w i r whole) : admitted w i r pre := by
  obtain ⟨suf,he⟩ := hpre
  rw [← he,admitted_append] at hwhole
  exact hwhole.1

theorem proper_prefix_admitted {w r : ℝ} {i : Side} {pre whole : List ℕ}
    (hfirst : FirstOmitted w i r whole) (hpre : pre <+: whole)
    (hlen : pre.length < whole.length) : admitted w i r pre := by
  obtain ⟨parent,p,he,hparent,_⟩ := hfirst
  have hpar : parent <+: whole := ⟨[p],he.symm⟩
  have hlen' : pre.length ≤ parent.length := by
    rw [he,List.length_append,List.length_singleton] at hlen
    omega
  exact admitted_prefix (List.prefix_of_prefix_length_le hpre hpar hlen') hparent

theorem first_omission_antichain {w r : ℝ} {i : Side} {pre whole : List ℕ}
    (hp : FirstOmitted w i r pre) (hq : FirstOmitted w i r whole)
    (hpre : pre <+: whole) : pre = whole := by
  by_contra hne
  have hlenle := hpre.length_le
  have hlenne : pre.length ≠ whole.length := fun h => hne (hpre.eq_of_length h)
  have hlen : pre.length < whole.length := by omega
  exact firstOmitted_not_admitted hp (proper_prefix_admitted hq hpre hlen)

theorem first_omission_prefix_unique {w r : ℝ} {i : Side} {p q whole : List ℕ}
    (hp : FirstOmitted w i r p) (hq : FirstOmitted w i r q)
    (hpref : p <+: whole) (hqref : q <+: whole) : p = q := by
  rcases List.prefix_or_prefix_of_prefix hpref hqref with h | h
  · exact first_omission_antichain hp hq h
  · exact (first_omission_antichain hq hp h).symm

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
