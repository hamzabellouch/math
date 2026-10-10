import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.SourceExposure
import OAI.Combinatorics.SharpRamsey.Windows.WindowLayout
import OAI.Combinatorics.SharpRamsey.Windows.WindowDeletion

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {ι β C X : Type} [Fintype β]
namespace ExposureModel

def lift (M : ExposureModel ι β C) (z : M.History) (e : X↪ι)
    (h : ∀ x,∃ i,M.origin z i=e x) : X↪M.Index z where
  toFun x := (h x).choose
  inj' := by
    intro x y he
    apply e.injective
    rw [←(h x).choose_spec,←(h y).choose_spec]
    exact congrArg (M.origin z) he

lemma lift_origin (M : ExposureModel ι β C) (z : M.History) (e : X↪ι)
    (h : ∀ x,∃ i,M.origin z i=e x) (x : X) : M.origin z (M.lift z e h x)=e x :=
  (h x).choose_spec

lemma lift_restore (M : ExposureModel ι β C) (z : M.History) (e : X↪ι)
    (h : ∀ x,∃ i,M.origin z i=e x) (x : X) (y : M.Index z→β) :
    y (M.lift z e h x)=M.restore z y (e x) := by
  rw [←M.lift_origin z e h x,M.restore_origin]

def representative (M : ExposureModel ι β C) (x : M.FreshHistory) : C↪M.Index x.1 where
  toFun b := M.embedding x.1 (b,x.2 b)
  inj' := by
    intro b c h
    exact congrArg Prod.fst ((M.embedding x.1).injective h)

lemma representative_selected [Fintype C] (M : ExposureModel ι β C) (x : M.FreshHistory) :
    univ.map (M.representative x)=M.freshSelected x := by
  ext i
  simp only [mem_map,mem_univ,true_and,freshSelected,freshRepresentatives,mem_image]
  rfl

end ExposureModel

namespace Windows
variable [Fintype C]

lemma owner_early {w n : ℕ} (j : Slot w n) (i : Fin w)
    (h : owner w n j=some (i,false)) : j.1=i ∧ j.2.val<n := by
  unfold owner at h
  split_ifs at h with he hl
  · have hh:=Option.some.inj h
    exact ⟨congrArg Prod.fst hh,he⟩
  · have hh:=congrArg Prod.snd (Option.some.inj h)
    cases hh

lemma owner_late {w n : ℕ} (j : Slot w n) (i : Fin w)
    (h : owner w n j=some (i,true)) : j.1=i ∧ 3*n≤ j.2.val := by
  unfold owner at h
  split_ifs at h with he hl
  · have hh:=congrArg Prod.snd (Option.some.inj h)
    cases hh
  · have hh:=Option.some.inj h
    exact ⟨congrArg Prod.fst hh,hl⟩

lemma owner_between {w n : ℕ} (i : Fin w) (a b : Slot w n)
    (ha : owner w n a=some (i,false)) (hb : owner w n b=some (i,true))
    (x : Fin (2*n)) : position a<position (middle w n (i,x)) ∧
      position (middle w n (i,x))<position b := by
  obtain ⟨ha₁,ha₂⟩:=owner_early a i ha
  obtain ⟨hb₁,hb₂⟩:=owner_late b i hb
  change a.1.val*(4*n)+a.2.val< i.val*(4*n)+(n+x.val) ∧
    i.val*(4*n)+(n+x.val)< b.1.val*(4*n)+b.2.val
  rw [ha₁,hb₁]
  constructor <;> omega

lemma owner_before_next {w n : ℕ} (i j : Fin w) (hij : i<j)
    (a b : Slot w n) (ha : a.1=i) (hb : b.1=j) : position a<position b := by
  change a.1.val*(4*n)+a.2.val< b.1.val*(4*n)+b.2.val
  rw [ha,hb]
  have hi : i.val+1≤ j.val := hij
  have hA:=a.2.isLt
  nlinarith

end Windows
end
end SharpLogRamsey.Selection

end

end OAI
