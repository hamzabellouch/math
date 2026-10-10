import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.PictureGenus
import OAI.Geometry.HyperbolicGroups.ColoredApex

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap

omit [DecidableEq D] [Fintype D] in
@[ext] lemma ext {M N : PictureMap D} (hf : M.face = N.face) (he : M.edge = N.edge) : M = N := by
  cases M
  cases N
  cases hf
  cases he
  rfl

instance : Finite (PictureMap D) :=
  Finite.of_injective (fun M : PictureMap D => (M.face,M.edge))
    (fun _ _ h => PictureMap.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

variable {L V : Type*}

/-- Literal oriented-edge and vertex labels into any target one-skeleton.
The vertex label of a dart is the initial vertex of its oriented edge label.
No filling or normal-form conclusion is included in this compatibility. -/
def Respects (M : PictureMap D) (label : D → L) (start : L → V) (rev : L → L) : Prop :=
  (∀ d, start (label (M.vertex d)) = start (label d)) ∧
    ∀ d, label (M.edge d) = rev (label d)

omit [Fintype D] in
lemma switch_respects {M : PictureMap D} {label : D → L} {start : L → V} {rev : L → L}
    (hM : M.Respects label start rev) {a b : D} (hab : label a = label b) :
    (M.switch a b).Respects label start rev := by
  constructor
  · intro x
    have hfar : start (label (M.edge a)) = start (label (M.edge b)) := by
      rw [hM.2 a,hM.2 b,hab]
    have hnear : start (label a) = start (label b) := congrArg start hab
    rw [M.vertex_switch]
    simp only [mul_apply,hM.1]
    change (start ∘ label) (swap (M.edge a) (M.edge b) (swap a b x)) = (start ∘ label) x
    rw [Equiv.apply_swap_eq_self (v := start ∘ label) hfar,
      Equiv.apply_swap_eq_self (v := start ∘ label) hnear]
  · intro x
    change label (swap a b (M.edge (swap a b x))) = rev (label x)
    rw [Equiv.apply_swap_eq_self hab,hM.2,Equiv.apply_swap_eq_self hab]

/-- A finite normalizing producer for radial labels on actual side-pairings.
The same darts, face cycles and mapped oriented edge labels are retained.
Thus all face maps/lifted face chains remain unchanged. Genus zero is retained
by the checked switch theorem, not assumed of the output.

`radial` is the target incidence fact: every edge starting at an apex ends at
an ordinary vertex. The conclusion says each outgoing radial label occurs
at most once in each actual apex vertex-link cycle. -/
theorem normalize_radial {M : PictureMap D} {label : D → L} {start : L → V} {rev : L → L}
    (isApex : V → Bool) (hM : M.Respects label start rev) (hG : M.GenusZero)
    (radial : ∀ d, isApex (start (label d)) = true →
      isApex (start (rev (label d))) = false) :
    ∃ N : PictureMap D, N.face = M.face ∧ N.Respects label start rev ∧ N.GenusZero ∧
      ∀ a b, isApex (start (label a)) = true → N.vertex.SameCycle a b →
        label a = label b → a = b := by
  classical
  let c : D → Bool := fun d => isApex (start (label d))
  let good : PictureMap D → Prop := fun N => N.face = M.face ∧ N.Respects label start rev ∧ N.GenusZero
  let := Fintype.ofFinite (PictureMap D)
  let s := Finset.univ.filter good
  have hm : M ∈ s := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨rfl,hM,hG⟩
  obtain ⟨N,hN,hmax⟩ := s.exists_max_image (fun N => N.apexCount c) ⟨M,hm⟩
  have hn : good N := (Finset.mem_filter.mp hN).2
  refine ⟨N,hn.1,hn.2.1,hn.2.2,?_⟩
  intro a b ha hv hl
  by_contra hne
  have hc : ∀ x, c (N.vertex x) = c x := fun x => congrArg isApex (hn.2.1.1 x)
  have hb : c b = true := by change isApex (start (label b)) = true; rw [← hl]; exact ha
  have hfa : c (N.edge a) = false := by
    change isApex (start (label (N.edge a))) = false
    rw [hn.2.1.2 a]
    exact radial a ha
  have hfb : c (N.edge b) = false := by
    change isApex (start (label (N.edge b))) = false
    rw [hn.2.1.2 b]
    exact radial b hb
  have hs : good (N.switch a b) := ⟨hn.1,switch_respects hn.2.1 hl,
    N.switch_genusZero hn.2.2 a b hne hv
      (N.radial_far c hc ha hfa) (N.radial_far c hc ha hfb)⟩
  have hmem : N.switch a b ∈ s := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]; exact hs
  have hbound := hmax (N.switch a b) hmem
  have hinc := N.switch_apexCount c hc hne hv ha hb hfa hfb
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
