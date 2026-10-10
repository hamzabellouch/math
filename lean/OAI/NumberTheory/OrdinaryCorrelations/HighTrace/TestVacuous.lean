import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecPrimeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AttachedMetadata
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Cylinder
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntegerResidues

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

instance (w : ClosedLine h ℓ) : Finite (AttachedSpec w D L) := by
  apply Finite.of_injective
    (fun s : AttachedSpec w D L => (attachedMetadata w s,specPrimeCode s.spec))
  intro s t ht
  exact attached_code_injective w s t (congrArg Prod.fst ht) (congrArg Prod.snd ht)

noncomputable instance (w : ClosedLine h ℓ) : Fintype (AttachedSpec w D L) := Fintype.ofFinite _

lemma Specification.test_vacuous (s : S.Specification D h L) (p : S.Index)
    (hp : (p:ℕ) ∉ s.primeSupport) (b : ℤ) (a : ZMod (p:ℕ)) : s.ResidueTest p b a := by
  constructor
  · intro he
    exact (hp (mem_insert.mpr (Or.inl he))).elim
  · intro i hd
    apply False.elim
    apply hp
    apply mem_insert_of_mem
    apply mem_biUnion.mpr
    refine ⟨i,mem_univ _,Nat.mem_primeFactors.mpr ⟨S.prime_mem p.val p.property,hd,?_⟩⟩
    have := D.greater_one _ (s.label_mem i)
    omega

lemma Specification.test_unique (s : S.Specification D h L) (p : S.Index)
    (hp : (p:ℕ) ∈ s.primeSupport) (b : ℤ) (a a' : ZMod (p:ℕ))
    (ha : s.ResidueTest p b a) (ha' : s.ResidueTest p b a') : a=a' := by
  rcases mem_insert.mp hp with he | he
  · exact add_right_cancel ((ha.1 he).trans (ha'.1 he).symm)
  · obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp he
    have hd := (Nat.mem_primeFactors.mp hpi).2.1
    exact add_right_cancel ((ha.2 i hd).trans (ha'.2 i hd).symm)

namespace AttachedSpec
variable {w : ClosedLine h ℓ}

noncomputable def origin (s : AttachedSpec w D L) : ℤ :=
  Classical.choose s.primitive.1 - s.vertex

lemma origin_tests (s : AttachedSpec w D L) (p : S.Index) :
    s.spec.ResidueTest p s.vertex (s.origin : ZMod (p:ℕ)) := by
  apply (s.spec.qualifies_iff_residueTests s.origin s.vertex).mp
  simpa only [origin,sub_add_cancel] using Classical.choose_spec s.primitive.1

noncomputable def fullCylinder (s : AttachedSpec w D L) :
    Cylinder (fun p : S.Index => ZMod (p:ℕ)) :=
  ⟨fun p => if (p:ℕ) ∈ s.spec.primeSupport then some (s.origin : ZMod (p:ℕ)) else none⟩

lemma fullCylinder_holds (s : AttachedSpec w D L) (r : S.Residues) :
    s.fullCylinder.Holds r ↔ ∀ p : S.Index, s.spec.ResidueTest p s.vertex (r p) := by
  constructor
  · intro hr p
    by_cases hp : (p:ℕ) ∈ s.spec.primeSupport
    · have he := hr p (s.origin : ZMod (p:ℕ)) (by simp only [fullCylinder,ite_eq_left hp])
      rw [he]
      exact s.origin_tests p
    · exact s.spec.test_vacuous p hp s.vertex (r p)
  · intro hr p a ha
    by_cases hp : (p:ℕ) ∈ s.spec.primeSupport
    · have he : (s.origin : ZMod (p:ℕ))=a := Option.some.inj (by
        simpa only [fullCylinder,ite_eq_left hp] using ha)
      exact (s.spec.test_unique p hp s.vertex (r p) _ (hr p) (s.origin_tests p)).trans he
    · simp [fullCylinder,hp] at ha

@[simp] lemma mem_fullCylinder_support (s : AttachedSpec w D L) (p : S.Index) :
    p ∈ s.fullCylinder.support ↔ (p:ℕ) ∈ s.spec.primeSupport := by
  by_cases hp : (p:ℕ) ∈ s.spec.primeSupport <;>
    simp [Cylinder.support,fullCylinder,hp]

lemma fullCylinder_width (s : AttachedSpec w D L) :
    s.fullCylinder.support.card ≤ L*⌈C₀*Real.log B⌉₊+1 := by
  have he : s.fullCylinder.support = univ.image (specSlotPrime s.spec) := by
    ext p
    simp only [mem_fullCylinder_support,mem_image,mem_univ,true_and]
    exact specSupport_iff_slot s.spec p
  rw [he]
  exact card_image_le.trans (by simpa using specPrimeSlot_card s.spec)

lemma fullCylinder_integer (s : AttachedSpec w D L) (n : ℤ) :
    s.fullCylinder.Holds (S.integerResidues n) ↔ s.spec.QualifiesAt (n+s.vertex) := by
  rw [s.fullCylinder_holds]
  exact (s.spec.qualifies_iff_residueTests n s.vertex).symm

end AttachedSpec

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
