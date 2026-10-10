import Mathlib
import OAI.Geometry.HyperbolicGroups.WordPicturePeel
import OAI.Geometry.HyperbolicGroups.PictureFillingAlgebra
import OAI.Geometry.HyperbolicGroups.OutsideComponentFilling
import OAI.Geometry.HyperbolicGroups.EdgeEraseCount

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)}

lemma cycles_positive {D : Type*} [DecidableEq D] [Fintype D] (p : Perm D) (a : D) :
    1 ≤ cycles p := by
  rw [cycles_eq_card_classes]
  let : Nonempty (Quotient (SameCycle.setoid p)) := ⟨Quotient.mk _ a⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')

/-- The distinguished outside is not paid for: a nonempty literal boundary
has a filling costing at most the number of INTERIOR face cycles. -/
theorem filling_interior {w : Word A} (P : WordPicture R w) (ho : P.outside ≠ []) :
    ∃ n, Homotopy R w [] n ∧ n ≤ Fintype.card P.Dart / 2 ∧
      (n : ℤ) + 1 ≤ cycles P.pairing.face := by
  by_cases hc : ∀ x ∈ P.outside, P.pairing.edge x ∈ P.outside
  · refine ⟨0,P.isolated_outside_filling hc,Nat.zero_le _,?_⟩
    obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil _ ho
    exact cycles_positive P.pairing.face a
  push Not at hc
  obtain ⟨a,hao,hai⟩ := hc
  obtain ⟨ol,orr,ho⟩ := List.mem_iff_append.mp hao
  let Q := P.rotate ol.length
  have hqo : Q.outside = a::(orr++ol) := by
    change P.outside.rotate ol.length = _
    rw [ho,List.rotate_append_length_eq,List.cons_append]
  have hqi : Q.pairing.edge a ∉ Q.outside := by
    change P.pairing.edge a ∉ P.outside.rotate ol.length
    simpa only [List.mem_rotate] using hai
  have hne : ¬ Q.pairing.face.SameCycle a (Q.pairing.edge a) := by
    intro hh
    have haQ : a ∈ Q.outside := hqo.symm ▸ List.mem_cons_self
    exact hqi (Q.boundary.mem_of_sameCycle haQ hh)
  obtain ⟨xs,hs,hm,hrel⟩ := Q.interior (Q.pairing.edge a) hqi
  obtain ⟨il,irr,hi⟩ := List.mem_iff_append.mp hm
  have hin : IsBoundary Q.pairing.face (Q.pairing.edge a::(irr++il)) := by
    simpa only [List.cons_append] using (hi ▸ hs).rotate_append
  have hface : Homotopy R ((Q.pairing.edge a::(irr++il)).map Q.label) [] 1 := by
    have hh := hrel.filling
    rw [hi,List.map_append] at hh
    simpa only [List.map_append,List.map_cons,List.cons_append] using hh.rotate_null
  let S := Q.peelAt hqo hin hne
  have hrem : ∃ n, Homotopy R (((irr++il) ++ (show List Q.Dart from orr++ol)).map Q.label) [] n ∧
      n ≤ Fintype.card S.Dart / 2 ∧ (n : ℤ) + 2 ≤ cycles P.pairing.face := by
    by_cases hz : S.outside = []
    · have hempty : (irr++il) ++ (show List Q.Dart from orr++ol) = [] := by
        have he := congrArg (List.map Subtype.val) hz
        simpa only [S,WordPicture.peelAt,List.map_attachWith,List.map_nil,List.attach_map_subtype_val] using he
      refine ⟨0,?_,Nat.zero_le _,?_⟩
      · rw [hempty,List.map_nil]; exact Homotopy.refl []
      · have hp := cycles_positive (Q.pairing.face * swap (show Q.Dart from a) (Q.pairing.edge a)) a
        have hm := cycles_merge_right Q.pairing.face hne
        change 0 + 2 ≤ cycles Q.pairing.face
        calc
          (0 : ℤ) + 2 = 1 + 1 := rfl
          _ ≤ cycles (Q.pairing.face * swap (show Q.Dart from a) (Q.pairing.edge a)) + 1 := by simpa only [add_comm] using add_le_add_right hp 1
          _ = cycles Q.pairing.face := hm
    · obtain ⟨n,hn,he,hf⟩ := filling_interior (w := _) S hz
      refine ⟨n,hn,he,?_⟩
      have hF := Q.pairing.eraseEdge_faces_le a hne
      change cycles S.pairing.face + 1 ≤ cycles P.pairing.face at hF
      omega
  obtain ⟨n,hn,he,hf⟩ := hrem
  refine ⟨1+n,?_,?_,?_⟩
  · have hword : w.rotate ol.length = Q.label a :: (orr ++ ol).map Q.label :=
      Q.word.symm.trans (congrArg (List.map Q.label) hqo)
    have hh : Homotopy R (w.rotate ol.length) [] (1+n) := by
      rw [hword]
      have hn' : Homotopy R ((irr++il).map Q.label ++ (orr++ol).map Q.label) [] n := by
        exact (List.map_append (f := Q.label) (l₁ := irr ++ il) (l₂ := orr ++ ol)) ▸ hn
      exact Homotopy.peel (Q.paired a) hface hn'
    apply Homotopy.unrotate_null ol.length _ hh
    have hl : P.outside.length = w.length := by simpa using congrArg List.length P.word
    simp only [ho,List.length_append,List.length_cons] at hl
    omega
  · have hD := card_offPair (Q.pairing.edge_ne a).symm
    simp only [← Nat.card_eq_fintype_card] at hD he ⊢
    change Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} + 2 =
      Nat.card P.Dart at hD
    change n ≤ Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} / 2 at he
    omega
  · omega
termination_by Fintype.card P.Dart
decreasing_by
  have hD := card_offPair (Q.pairing.edge_ne a).symm
  simp only [← Nat.card_eq_fintype_card] at hD ⊢
  change Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} < Nat.card P.Dart
  change Nat.card {x : Q.Dart // OffPair a (Q.pairing.edge a) x} + 2 =
    Nat.card P.Dart at hD
  omega

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
