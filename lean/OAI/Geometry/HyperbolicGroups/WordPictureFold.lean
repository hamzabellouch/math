import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryEraseList
import OAI.Geometry.HyperbolicGroups.WordPictureExist

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {A : Type*} {R : Set (Word A)} {w : Word A}
namespace WordPicture
variable (P : WordPicture R w)

/-- Free boundary cancellation lands in a new actual genus-zero diagram,
retaining every interior relator face, with all repeated side indices intact. -/
def foldAt {l r : List P.Dart} {a b : P.Dart} (he : P.outside = l++a::b::r)
    (hc : P.label a = invLetter (P.label b)) : WordPicture R ((l++r).map P.label) := by
  have hb : IsBoundary P.pairing.face (l++a::b::r) := he ▸ P.boundary
  have hab : a ≠ b := by
    have hn := (List.nodup_append.mp hb.nodup).2.1
    exact fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  let M := P.pairing.boundaryFold hab hb.middle_next
  have hp := IsBoundary.middle_offpair hb.nodup
  refine {
    Dart := {x // OffPair a b x}
    pairing := M
    genusZero := P.pairing.boundaryFold_genusZero hab hb.middle_next P.genusZero
    label := P.label ∘ Subtype.val
    paired := (P.pairing.boundaryFold_respects hab hb.middle_next P.respects hc).2
    outside := (l++r).attachWith (OffPair a b) hp
    boundary := P.pairing.boundaryFold_boundary hb hab
    word := List.attachWith_map_val hp
    interior := ?_ }
  intro x hx
  have hxo : x.val ∉ P.outside := by
    intro hm
    have he' : x.val ∈ l++r := by
      rw [he] at hm
      simp only [List.mem_append,List.mem_cons] at hm ⊢
      rcases hm with hm | hm
      · exact Or.inl hm
      · rcases hm with ha | hb | hr
        · exact False.elim (x.property.1 ha)
        · exact False.elim (x.property.2 hb)
        · exact Or.inr hr
    exact hx ((List.mem_attachWith hp x).mpr he')
  obtain ⟨xs,hxs,hxm,hr⟩ := P.interior x.val hxo
  have hdis : ∀ y ∈ xs, y ∉ P.outside := by
    intro y hy hyo
    exact hxo (P.boundary.mem_of_sameCycle hyo (hxs.sameCycle hy hxm))
  have ha : a ∈ P.outside := by rw [he]; simp
  have hb' : b ∈ P.outside := by rw [he]; simp
  have hp' : ∀ y ∈ xs, OffPair a b y := by
    intro y hy
    exact ⟨fun he => hdis y hy (he ▸ ha),fun he => hdis y hy (he ▸ hb')⟩
  refine ⟨xs.attachWith (OffPair a b) hp',?_,(List.mem_attachWith hp' x).mpr hxm,?_⟩
  · apply hxs.lift hp' M.face
    intro y hy
    apply P.pairing.boundaryFold_other_face hab hb.middle_next
    intro hf
    exact hdis y hy (P.boundary.mem_of_sameCycle ha hf)
  · simpa only [Function.comp_def,List.attachWith_map_val] using hr

include P

lemma of_step {v : Word A} (h : FreeGroup.Red.Step w v) : Nonempty (WordPicture R v) := by
  cases h with
  | @not l r x b =>
    obtain ⟨ls,rs,he,hl,hrs⟩ := List.map_eq_append_iff.mp P.word
    obtain ⟨a,rs',hr,ha,hrs'⟩ := List.map_eq_cons_iff.mp hrs
    obtain ⟨b',rs'',hr',hb,hrs''⟩ := List.map_eq_cons_iff.mp hrs'
    have hout : P.outside = ls++a::b'::rs'' := by rw [he,hr,hr']
    have hc : P.label a = invLetter (P.label b') := by rw [ha,hb]; simp [invLetter]
    have H := P.foldAt hout hc
    have hw : (ls++rs'').map P.label = l++r := by rw [List.map_append,hl,hrs'']
    exact ⟨hw ▸ H⟩

lemma of_red {v : Word A} (h : FreeGroup.Red w v) : Nonempty (WordPicture R v) := by
  induction h with
  | refl => exact ⟨P⟩
  | tail h h' ih => obtain ⟨Q⟩ := ih; exact Q.of_step h'

end WordPicture

/-- Source disk producer with a freely reduced exterior: a null word admits
an actual finite genus-zero relator diagram whose literal boundary is a
reduction of that word, hence has no greater boundary length. No diagram or
planarity hypothesis is assumed. -/
theorem reduced_picture_existence {R : Set (Word A)} (w : Word A)
    (h : PresentedGroup.mk (FreeGroup.mk '' R) (FreeGroup.mk w) = 1) :
    ∃ z, FreeGroup.Red w z ∧ Nonempty (WordPicture R z) := by
  obtain ⟨v,hv,⟨P⟩⟩ := picture_existence w h
  obtain ⟨z,hvz,hwz⟩ := FreeGroup.Red.exact.mp hv
  exact ⟨z,hwz,P.of_red hvz⟩

end HyperbolicObstruction.WordPictures
end
end

section

end
end

end OAI
