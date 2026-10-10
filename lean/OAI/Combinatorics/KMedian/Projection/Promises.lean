import Mathlib
import OAI.Combinatorics.KMedian.Projection.Repeat

namespace OAI

section Inline_PCPProjectionPromises

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B U' V' D' S' A' B' : Type}
variable (G : BiProjection U V D S A B) (H : BiProjection U' V' D' S' A' B')
lemma perfect_prod (hG : G.Perfect) (hH : H.Perfect) : (G.prod H).Perfect := by
  obtain ⟨a,b,hab⟩ := hG
  obtain ⟨a',b',hab'⟩ := hH
  refine ⟨fun p => (a p.1,a' p.2),fun p => (b p.1,b' p.2),?_⟩
  rintro ⟨u,u'⟩ ⟨d,d'⟩
  exact Prod.ext (hab u d) (hab' u' d')
lemma consistent_prod (hG : G.Consistent) (hH : H.Consistent) : (G.prod H).Consistent := by
  rintro ⟨u,u'⟩ ⟨d,d'⟩ ⟨e,e'⟩ he ⟨a,a'⟩
  have h0 : (G.edge (u,d)).1=(G.edge (u,e)).1 := congrArg (fun p : V × V' => p.1) he
  have h1 : (H.edge (u',d')).1=(H.edge (u',e')).1 := congrArg (fun p : V × V' => p.2) he
  exact Prod.ext (hG u d e h0 a) (hH u' d' e' h1 a')
lemma perfect_power (hG : G.Perfect) (n : ℕ) : (G.power n).Perfect := by
  induction n with
  | zero => exact ⟨fun _ => (),fun _ => (),fun _ _ => rfl⟩
  | succ n ih => exact G.perfect_prod (G.power n) hG ih
lemma consistent_power (hG : G.Consistent) (n : ℕ) : (G.power n).Consistent := by
  induction n with
  | zero => exact fun _ _ _ _ _ => rfl
  | succ n ih => exact G.consistent_prod (G.power n) hG ih
end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionPromises

end OAI
