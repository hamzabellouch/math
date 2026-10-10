import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.MemSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TestVacuous

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

abbrev FreeResidues (S : PrimeSystem) (w : ClosedLine h ℓ) :=
  ∀ p : S.FreeIndex w, ZMod (p.val:ℕ)

def binarySplit (S : PrimeSystem) (w : ClosedLine h ℓ) :
    S.Residues ≃ S.FixedResidues w × S.FreeResidues w :=
  Equiv.piEquivPiSubtypeProd (S.IsFixed w) (fun p : S.Index => ZMod (p:ℕ))

def mergeResidues (w : ClosedLine h ℓ) (a : S.FixedResidues w) (c : S.FreeResidues w) : S.Residues :=
  (S.binarySplit w).symm (a,c)

@[simp] lemma merge_fixed (w : ClosedLine h ℓ) (a : S.FixedResidues w) (c : S.FreeResidues w)
    (p : S.FixedIndex w) : mergeResidues w a c p.val = a p := by
  simp [mergeResidues,binarySplit,p.property]

@[simp] lemma merge_free (w : ClosedLine h ℓ) (a : S.FixedResidues w) (c : S.FreeResidues w)
    (p : S.FreeIndex w) : mergeResidues w a c p.val = c p := by
  simp [mergeResidues,binarySplit,p.property]

namespace AttachedSpec
variable {w : ClosedLine h ℓ}

def Compatible (s : AttachedSpec w D L) (a : S.FixedResidues w) : Prop :=
  ∀ p : S.FixedIndex w, s.spec.ResidueTest p.val s.vertex (a p)

noncomputable def residualCylinder (s : AttachedSpec w D L) :
    Cylinder (fun p : S.FreeIndex w => ZMod (p.val:ℕ)) :=
  ⟨fun p => s.fullCylinder.value p.val⟩

lemma residualCylinder_holds (s : AttachedSpec w D L) (c : S.FreeResidues w) :
    s.residualCylinder.Holds c ↔ ∀ p : S.FreeIndex w, s.spec.ResidueTest p.val s.vertex (c p) := by
  constructor
  · intro hc p
    by_cases hp : (p.val:ℕ) ∈ s.spec.primeSupport
    · have he := hc p (s.origin : ZMod (p.val:ℕ)) (by simp only [residualCylinder,fullCylinder,ite_eq_left hp])
      rw [he]
      exact s.origin_tests p.val
    · exact s.spec.test_vacuous p.val hp s.vertex (c p)
  · intro hc p b hb
    by_cases hp : (p.val:ℕ) ∈ s.spec.primeSupport
    · have he : (s.origin : ZMod (p.val:ℕ))=b := Option.some.inj (by
        simpa only [residualCylinder,fullCylinder,ite_eq_left hp] using hb)
      exact (s.spec.test_unique p.val hp s.vertex (c p) _ (hc p) (s.origin_tests p.val)).trans he
    · simp [residualCylinder,fullCylinder,hp] at hb

lemma fullCylinder_merge (s : AttachedSpec w D L) (a : S.FixedResidues w) (c : S.FreeResidues w) :
    s.fullCylinder.Holds (mergeResidues w a c) ↔ s.Compatible a ∧ s.residualCylinder.Holds c := by
  rw [s.fullCylinder_holds,s.residualCylinder_holds]
  constructor
  · intro ht
    exact ⟨fun p => by simpa only [merge_fixed] using ht p.val,
      fun p => by simpa only [merge_free] using ht p.val⟩
  · rintro ⟨hf,hc⟩ p
    by_cases hp : S.IsFixed w p
    · rw [show mergeResidues w a c p = a ⟨p,hp⟩ from merge_fixed w a c ⟨p,hp⟩]
      exact hf ⟨p,hp⟩
    · rw [show mergeResidues w a c p = c ⟨p,hp⟩ from merge_free w a c ⟨p,hp⟩]
      exact hc ⟨p,hp⟩

lemma residual_support_iff (s : AttachedSpec w D L) (p : S.FreeIndex w) :
    p ∈ s.residualCylinder.support ↔ (p.val:ℕ) ∈ s.spec.primeSupport := by
  by_cases hp : (p.val:ℕ) ∈ s.spec.primeSupport <;>
    simp [Cylinder.support,residualCylinder,fullCylinder,hp]

lemma residualCylinder_width (s : AttachedSpec w D L) :
    s.residualCylinder.support.card ≤ L*⌈C₀*Real.log B⌉₊+1 := by
  have hinj : Set.InjOn (fun p : S.FreeIndex w => p.val) (s.residualCylinder.support: Set _) :=
    fun _ _ _ _ he => Subtype.ext he
  have hsub : s.residualCylinder.support.image (fun p => p.val) ⊆ s.fullCylinder.support := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    exact (s.mem_fullCylinder_support q.val).mpr ((s.residual_support_iff q).mp hq)
  calc
    _ = (s.residualCylinder.support.image (fun p => p.val)).card := (card_image_of_injOn hinj).symm
    _ ≤ s.fullCylinder.support.card := card_le_card hsub
    _ ≤ _ := s.fullCylinder_width

lemma residual_eq_bot_iff_support_fixed (s : AttachedSpec w D L) :
    s.residualCylinder = ⊥ ↔ ∀ p : S.Index, (p:ℕ) ∈ s.spec.primeSupport → S.IsFixed w p := by
  rw [Cylinder.eq_bot_iff,eq_empty_iff_forall_notMem]
  simp only [s.residual_support_iff]
  constructor
  · intro ht p hp
    by_contra hn
    exact ht ⟨p,hn⟩ hp
  · intro ht p hp
    exact p.property (ht p.val hp)

end AttachedSpec

noncomputable def residualEvents (w : ClosedLine h ℓ) (D : S.DivisorFamily B τ C₀)
    (L : ℕ) (a : S.FixedResidues w) : Finset (Cylinder (fun p : S.FreeIndex w => ZMod (p.val:ℕ))) :=
  (univ.filter (fun s : AttachedSpec w D L => s.Compatible a)).image AttachedSpec.residualCylinder

def NoFixedForbidden (w : ClosedLine h ℓ) (D : S.DivisorFamily B τ C₀) (L : ℕ)
    (a : S.FixedResidues w) : Prop :=
  ∀ s : AttachedSpec w D L, s.Compatible a →
    ¬ ∀ p : S.Index, (p:ℕ) ∈ s.spec.primeSupport → S.IsFixed w p

lemma residualEvents_proper (w : ClosedLine h ℓ) (a : S.FixedResidues w)
    (ha : NoFixedForbidden w D L a) : ∀ e ∈ residualEvents w D L a, e ≠ ⊥ := by
  intro e he
  obtain ⟨s,hs,rfl⟩ := mem_image.mp he
  exact fun he => ha s (mem_filter.mp hs).2 (s.residual_eq_bot_iff_support_fixed.mp he)

lemma residualEvents_width (w : ClosedLine h ℓ) (a : S.FixedResidues w) :
    ∀ e ∈ residualEvents w D L a, e.support.card ≤ L*⌈C₀*Real.log B⌉₊+1 := by
  intro e he
  obtain ⟨s,_,rfl⟩ := mem_image.mp he
  exact s.residualCylinder_width

lemma residualEvents_avoidance (w : ClosedLine h ℓ) (a : S.FixedResidues w) (c : S.FreeResidues w) :
    (∀ e ∈ residualEvents w D L a, ¬e.Holds c) ↔
      ∀ s : AttachedSpec w D L, ¬s.fullCylinder.Holds (mergeResidues w a c) := by
  constructor
  · intro ha s hs
    have hh := s.fullCylinder_merge a c |>.mp hs
    exact ha s.residualCylinder (mem_image.mpr ⟨s,mem_filter.mpr ⟨mem_univ _,hh.1⟩,rfl⟩) hh.2
  · intro hs e he hc
    obtain ⟨s,hs',rfl⟩ := mem_image.mp he
    exact hs s (s.fullCylinder_merge a c |>.mpr ⟨(mem_filter.mp hs').2,hc⟩)

def VertexAllowed (D : S.DivisorFamily B τ C₀) (h L : ℕ) (x : ℤ) : Prop :=
  ∀ s : S.Specification D h L, s.Primitive → ¬s.QualifiesAt x

lemma all_attachments_integer_iff (w : ClosedLine h ℓ) (n : ℤ) :
    (∀ s : AttachedSpec w D L, ¬s.fullCylinder.Holds (S.integerResidues n)) ↔
      ∀ i : Fin (ℓ+1), VertexAllowed D h L (n+w.offset i) := by
  constructor
  · intro hs i t ht
    exact (show ¬(AttachedSpec.fullCylinder (⟨i,t,ht⟩ : AttachedSpec w D L)).Holds
      (S.integerResidues n) from hs ⟨i,t,ht⟩) ∘ (AttachedSpec.fullCylinder_integer ⟨i,t,ht⟩ n).mpr
  · intro hi s hs
    exact hi s.index s.spec s.primitive ((s.fullCylinder_integer n).mp hs)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
