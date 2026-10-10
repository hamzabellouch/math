import Mathlib
import OAI.Computability.DirectedFeedback.Games.BlockOrientations

namespace OAI

namespace DFVSGames.Quadratic

open Module
open scoped BigOperators

noncomputable section

section AlignmentEvents

variable {R F V ι n : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype V] [Fintype ι] [Fintype n]

def alignmentEvent (z : V → n → F) (g : V →ₗ[R] (n → F)) (c : V → F) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ (∑ i, z v i * g v i) = c v)

theorem all_lifts_bound_iff_subsets (b : Basis ι R V) (z : V → n → F)
    (c : V → F) (k : ℕ) :
    (∀ g : V →ₗ[R] (n → F), (alignmentEvent z g c).card ≤ k) ↔
      ∀ E : Finset V, 0 ∉ E → E.card = k + 1 →
        (fun e : E => c e) ∉
          LinearMap.range (alignmentMatrix b (fun e : E => (e : V)) z).mulVecLin := by
  classical
  constructor
  · intro h E hzero hcard hmem
    obtain ⟨g, hg⟩ := (exists_lift_alignment_iff_mem_range b
      (fun e : E => (e : V)) z (fun e : E => c e)).mpr hmem
    have hsubset : E ⊆ alignmentEvent z g c := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hg ⟨v, hv⟩⟩
      intro hvzero
      exact hzero (hvzero ▸ hv)
    have hle := (Finset.card_le_card hsubset).trans (h g)
    omega
  · intro h g
    by_contra hbad
    have hlarge : k + 1 ≤ (alignmentEvent z g c).card := by omega
    obtain ⟨E, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
    have hzero : (0 : V) ∉ E := by
      intro hz
      have hh := (Finset.mem_filter.mp (hsub hz)).2.1
      exact hh rfl
    apply h E hzero hcard
    apply (exists_lift_alignment_iff_mem_range b
      (fun e : E => (e : V)) z (fun e : E => c e)).mp
    refine ⟨g, ?_⟩
    intro e
    exact (Finset.mem_filter.mp (hsub e.property)).2.2

theorem all_lifts_bound_of_card_le (z : V → n → F) (c : V → F) (k : ℕ)
    (hcard : Fintype.card V - 1 ≤ k) (g : V →ₗ[R] (n → F)) :
    (alignmentEvent z g c).card ≤ k := by
  classical
  have hsub : alignmentEvent z g c ⊆ Finset.univ.erase (0 : V) := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hv).2.1, Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  simpa using hle.trans (by simpa using hcard)

end AlignmentEvents

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

def alignmentRightHandSide (z : Fin 3 → F) : F := squareRoot (z 0 * z 1 * z 2)

def IsGeneric (S : Submodule (ZMod 2) (Fin 3 → F)) : Prop := by
  classical
  exact
    (∀ z w : S, z ≠ 0 → w ≠ 0 →
      (∃ t : F, (z : Fin 3 → F) = t • (w : Fin 3 → F)) → z = w) ∧
    (∀ g : S →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent (R := ZMod 2) (fun z : S => (z : Fin 3 → F)) g
        (fun z : S => alignmentRightHandSide (z : Fin 3 → F))).card ≤
          3 * Module.finrank (ZMod 2) S)

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

theorem finrank_le_one_of_nonzero_unique
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → v = w) :
    Module.finrank R V ≤ 1 := by
  classical
  by_cases hex : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hex
    apply finrank_le_one v
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    · exact ⟨1, by simpa using h v w hv hw⟩
  · apply finrank_le_one (0 : V)
    intro w
    have hw : w = 0 := by
      by_contra hw
      exact hex ⟨w, hw⟩
    exact ⟨0, by simp [hw]⟩

theorem finrank_ker_le_one_of_nonzero_unique (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R f.ker ≤ 1 := by
  apply finrank_le_one_of_nonzero_unique
  intro v w hv hw
  apply Subtype.ext
  apply h v w
  · intro hv0
    apply hv
    exact Subtype.ext hv0
  · intro hw0
    apply hw
    exact Subtype.ext hw0
  · exact v.property
  · exact w.property

theorem finrank_source_le_range_add_one [FiniteDimensional R V]
    (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R V ≤ Module.finrank R f.range + 1 := by
  have hk := finrank_ker_le_one_of_nonzero_unique f h
  have hr := f.finrank_range_add_finrank_ker
  omega

variable [Fintype V] [Fintype I] [DecidableEq I]

def lossIndices (f : I → V →ₗ[R] W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ v : V, v ≠ 0 ∧ f i v = 0)

def alignedCharacters (aligned : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ aligned v)

theorem lossIndices_subset_image (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    lossIndices f ⊆ (alignedCharacters aligned).image lineOf := by
  classical
  intro i hi
  obtain ⟨v, hv, hfv⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨halign, hline⟩ := hkernel i v hv hfv
  apply Finset.mem_image.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, halign⟩, hline⟩

theorem card_lossIndices_le_card_aligned (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    (lossIndices f).card ≤ (alignedCharacters aligned).card := by
  classical
  exact (Finset.card_le_card (lossIndices_subset_image f aligned lineOf hkernel)).trans
    (Finset.card_image_le (s := alignedCharacters aligned) (f := lineOf))

theorem card_lossIndices_le (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I) (r : ℕ)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i)
    (hgeneric : (alignedCharacters aligned).card ≤ 3 * r) :
    (lossIndices f).card ≤ 3 * r :=
  (card_lossIndices_le_card_aligned f aligned lineOf hkernel).trans hgeneric

theorem card_lossIndices_le_nonzero (f : I → V →ₗ[R] W)
    (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → lineOf v = i) :
    (lossIndices f).card ≤ Fintype.card V - 1 := by
  classical
  have h := card_lossIndices_le_card_aligned f (fun _ => True) lineOf
    (fun i v hv hfv => ⟨trivial, hkernel i v hv hfv⟩)
  simpa [alignedCharacters, Finset.filter_ne'] using h

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem dot_add_first_inline_BlockRestriction (x y z : Vec F) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  ring

def blockCharacterLinear (g z : Vec F) :
    (Vec F × Vec F) →ₗ[ZMod 2] ZMod 2 where
  toFun := blockCharacter g z
  map_add' := by
    intro p q
    simp only [blockCharacter, Prod.fst_add, Prod.snd_add, dot_add_right, map_add]
    ring
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> simp [blockCharacter]

def blockRestriction (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) :
    S →ₗ[ZMod 2] ((U v) →ₗ[ZMod 2] ZMod 2) where
  toFun z := (blockCharacterLinear (g z) z).comp (U v).subtype
  map_add' := by
    intro z w
    ext p
    simp only [LinearMap.comp_apply, blockCharacterLinear, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply, map_add, Submodule.coe_add,
      blockCharacter, dot_add_first_inline_BlockRestriction, map_add]
    ring
  map_smul' := by
    intro c z
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> ext p <;>
      simp [blockCharacterLinear, blockCharacter]

omit [Fintype F] in
@[simp] theorem blockRestriction_apply (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) (p : U v) :
    blockRestriction S g v z p = blockCharacter (g z) z p := rfl

omit [Fintype F] in

theorem blockRestriction_eq_zero_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) :
    blockRestriction S g v z = 0 ↔ BlockAnnihilates (g z) z v := by
  constructor
  · intro h p hp
    exact LinearMap.congr_fun h ⟨p, hp⟩
  · intro h
    ext p
    exact h p p.property

theorem mem_ker_blockRestriction_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) {v : Vec F} (hv : v ≠ 0)
    {z : S} (hz : z ≠ 0) :
    z ∈ (blockRestriction S g v).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  have hz' : (z : Vec F) ≠ 0 := fun h => hz (Subtype.ext h)
  rw [LinearMap.mem_ker, blockRestriction_eq_zero_iff, blockAnnihilates_iff hv hz']

theorem blockRestriction_nonzero_kernel_unique
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S)
    (z w : S) (hz : z ≠ 0) (hw : w ≠ 0)
    (hgz : blockRestriction S g v z = 0)
    (hgw : blockRestriction S g v w = 0) : z = w := by
  have hzline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v z).mp hgz)
  have hwline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v w).mp hgw)
  obtain ⟨t, ht⟩ := (mem_line_iff v z).mp hzline
  obtain ⟨s, hs⟩ := (mem_line_iff v w).mp hwline
  have hsne : s ≠ 0 := by
    intro hzero
    apply hw
    apply Subtype.ext
    simpa [hzero] using hs.symm
  apply hS.1 z w hz hw
  refine ⟨t / s, ?_⟩
  rw [← ht, ← hs, smul_smul, div_mul_cancel₀ _ hsne]

theorem finrank_ker_blockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) :
    Module.finrank (ZMod 2) (blockRestriction S g v).ker ≤ 1 :=
  finrank_ker_le_one_of_nonzero_unique (blockRestriction S g v)
    (blockRestriction_nonzero_kernel_unique S g hv hS)

theorem finrank_blockRestriction_source_le_range_add_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) :
    Module.finrank (ZMod 2) S ≤
      Module.finrank (ZMod 2) (blockRestriction S g v).range + 1 :=
  finrank_source_le_range_add_one (blockRestriction S g v)
    (blockRestriction_nonzero_kernel_unique S g hv hS)

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F B : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [AddCommGroup B] [Module (ZMod 2) B]

def orientedBlockRestriction (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) :
    S →ₗ[ZMod 2] (B →ₗ[ZMod 2] ZMod 2) :=
  J.dualMap.toLinearMap.comp (blockRestriction S g v)

omit [Fintype F] in
@[simp] theorem orientedBlockRestriction_apply
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) (z : S) (b : B) :
    orientedBlockRestriction S g v J z b = blockCharacter (g z) z (J b) := rfl

omit [Fintype F] in
theorem orientedBlockRestriction_eq_zero_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) (z : S) :
    orientedBlockRestriction S g v J z = 0 ↔ blockRestriction S g v z = 0 := by
  change J.dualMap (blockRestriction S g v z) = 0 ↔ _
  constructor
  · intro h
    apply J.dualMap.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

omit [Fintype F] in
theorem ker_orientedBlockRestriction
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J : B ≃ₗ[ZMod 2] U v) :
    (orientedBlockRestriction S g v J).ker = (blockRestriction S g v).ker := by
  ext z
  simp only [LinearMap.mem_ker, orientedBlockRestriction_eq_zero_iff]

omit [Fintype F] in
theorem ker_orientedBlockRestriction_independent
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (v : Vec F) (J J' : B ≃ₗ[ZMod 2] U v) :
    (orientedBlockRestriction S g v J).ker =
      (orientedBlockRestriction S g v J').ker := by
  rw [ker_orientedBlockRestriction, ker_orientedBlockRestriction]

theorem mem_ker_orientedBlockRestriction_iff
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (J : B ≃ₗ[ZMod 2] U v)
    {z : S} (hz : z ≠ 0) :
    z ∈ (orientedBlockRestriction S g v J).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  rw [ker_orientedBlockRestriction]
  exact mem_ker_blockRestriction_iff S g hv hz

theorem finrank_ker_orientedBlockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) (J : B ≃ₗ[ZMod 2] U v) :
    Module.finrank (ZMod 2) (orientedBlockRestriction S g v J).ker ≤ 1 := by
  rw [ker_orientedBlockRestriction]
  exact finrank_ker_blockRestriction_le_one S g hv hS

end

end DFVSGames.Quadratic

namespace DFVSGames.Gadget.BlockDescent

open Quadratic OrientedBlockKernel

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev BinaryDual := Vec F →ₗ[ZMod 2] ZMod 2

def traceSpace (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    Submodule (ZMod 2) (Vec F) := S.map traceDualEquiv.symm.toLinearMap

def traceSpaceEquiv (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    S ≃ₗ[ZMod 2] traceSpace S :=
  Submodule.equivMapOfInjective traceDualEquiv.symm.toLinearMap
    traceDualEquiv.symm.injective S

omit [CharP F 2] in
theorem traceSpace_finrank (S : Submodule (ZMod 2) (BinaryDual (F := F))) :
    Module.finrank (ZMod 2) (traceSpace S) = Module.finrank (ZMod 2) S :=
  (traceSpaceEquiv S).finrank_eq.symm

omit [CharP F 2] in
@[simp] theorem traceSpaceEquiv_apply_val
    (S : Submodule (ZMod 2) (BinaryDual (F := F))) (z : S) :
    (traceSpaceEquiv S z).val = traceDualEquiv.symm z.val := rfl

omit [CharP F 2] in
theorem traceSpaceEquiv_symm_val
    (S : Submodule (ZMod 2) (BinaryDual (F := F))) (z : traceSpace S) :
    ((traceSpaceEquiv S).symm z).val = traceDualEquiv z.val := by
  apply traceDualEquiv.symm.injective
  have h := congrArg Subtype.val ((traceSpaceEquiv S).apply_symm_apply z)
  simpa only [traceSpaceEquiv_apply_val, LinearEquiv.symm_apply_apply] using h

def traceLift (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) : traceSpace S →ₗ[ZMod 2] Vec F :=
  representTraceFamily (γ.comp (traceSpaceEquiv S).symm.toLinearMap)

theorem childCharacter_comp_traceSpaceEquiv
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).comp (traceSpaceEquiv S).symm.toLinearMap =
      orientedBlockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1) i.2 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro b
  change γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 +
    ((traceSpaceEquiv S).symm z).val (i.2 b).val.2 =
      traceBinary (dot (traceLift S γ z) (i.2 b).val.1 + dot z.val (i.2 b).val.2)
  rw [map_add]
  rw [show traceBinary (dot (traceLift S γ z) (i.2 b).val.1) =
    γ ((traceSpaceEquiv S).symm z) (i.2 b).val.1 from
      representTraceFamily_spec (γ.comp (traceSpaceEquiv S).symm.toLinearMap) z _]
  rw [traceSpaceEquiv_symm_val, traceDualEquiv_apply]

theorem childCharacter_range_eq
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      (orientedBlockRestriction (traceSpace S) (traceLift S γ)
        (lineGenerator i.1) i.2).range := by
  rw [← childCharacter_comp_traceSpaceEquiv]
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)).symm

theorem childCharacter_range_eq_dual_pullback
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (i : BlockOrientationIndex F) :
    (childCharacter orientedBlockLinear γ i).range =
      ((blockRestriction (traceSpace S) (traceLift S γ) (lineGenerator i.1)).range).map
        i.2.dualMap.toLinearMap := by
  rw [childCharacter_range_eq]
  exact LinearMap.range_comp _ _

theorem childCharacter_rank_independent
    (S : Submodule (ZMod 2) (BinaryDual (F := F)))
    (γ : S →ₗ[ZMod 2] BinaryDual (F := F)) (A : FieldLine F)
    (J J' : BlockOrientation A) :
    Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J⟩).range =
      Module.finrank (ZMod 2) (childCharacter orientedBlockLinear γ ⟨A, J'⟩).range := by
  rw [childCharacter_range_eq_dual_pullback, childCharacter_range_eq_dual_pullback]
  rw [J.dualMap.finrank_map_eq, J'.dualMap.finrank_map_eq]

end

end DFVSGames.Gadget.BlockDescent

namespace DFVSGames.Gadget.Descent

universe u v

variable {k : Type u} {B I X : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B] [FiniteDimensional k B]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

variable (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B)

noncomputable def commonGamma (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) : S →ₗ[k] (X →ₗ[k] k) :=
  Classical.choose (exists_common_child_character J hJ Q s S L)

omit [FiniteDimensional k B] in
omit [Finite B] in
theorem commonGamma_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (z : S) (h : s.Shift) :
    L.family z (Pi.single i (s.embed h)) =
      childCharacter J (commonGamma J hJ Q s S L) i z (s.logical h) :=
  Classical.choose_spec (exists_common_child_character J hJ Q s S L) i z h

noncomputable def childDomain (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) : Submodule k (B →ₗ[k] k) :=
  LinearMap.range (childCharacter J (commonGamma J hJ Q s S L) i)

noncomputable def childLift (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Lift s (childDomain J hJ Q s S L i) :=
  Classical.choose (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i)

noncomputable def childSection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    childDomain J hJ Q s S L i →ₗ[k] S :=
  Classical.choose (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))

omit [FiniteDimensional k B] [Finite B] in
theorem childSection_rightInverse (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I)
    (z : childDomain J hJ Q s S L i) :
    childCharacter J (commonGamma J hJ Q s S L) i
      (childSection J hJ Q s S L i z) = z.val :=
  (Classical.choose_spec (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))).1 z

omit [FiniteDimensional k B] [Finite B] in
theorem childLift_spec (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I)
    (z : childDomain J hJ Q s S L i) (p : s.Input) :
    (childLift J hJ Q s S L i).family z p =
      L.family (childSection J hJ Q s S L i z) (Pi.single i p) :=
  (Classical.choose_spec (Classical.choose_spec (exists_descendant_lift J hJ Q s S L
    (commonGamma J hJ Q s S L) (commonGamma_spec J hJ Q s S L) i))).2 z p

omit [FiniteDimensional k B] [Finite B] in
theorem child_detection (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) (n : s.Noise)
    (hdetect : ∃ z, (childLift J hJ Q s S L i).family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 :=
  descendant_detection_implies_parent J hJ Q s S L _ _ i
    (childLift_spec J hJ Q s S L i) n hdetect

omit [Finite B] in
theorem child_rank_le (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) (i : I) :
    Module.finrank k (childDomain J hJ Q s S L i) ≤ Module.finrank k S :=
  LinearMap.finrank_range_le _

noncomputable def leafRank
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J)) (Q : X → B) :
    (n : ℕ) → (S : Submodule k (B →ₗ[k] k)) →
    Lift (Stage.iterate J hJ Q n) S → (Stage.iterate J hJ Q n).Noise → ℕ
  | 0, S, _, _ => Module.finrank k S
  | n + 1, S, L, t => leafRank J hJ Q n
      (childDomain J hJ Q (Stage.iterate J hJ Q n) S L t.1)
      (childLift J hJ Q (Stage.iterate J hJ Q n) S L t.1) t.2

theorem leafRank_le (n : ℕ) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.iterate J hJ Q n) S) (t : (Stage.iterate J hJ Q n).Noise) :
    leafRank J hJ Q n S L t ≤ Module.finrank k S := by
  induction n generalizing S with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih _ _ _).trans (child_rank_le J hJ Q _ S L t.1)

end DFVSGames.Gadget.Descent

namespace DFVSGames.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance : Fintype (FieldLine F) := Fintype.ofFinite _
local instance (S : Submodule (ZMod 2) (Vec F)) : Fintype S := by
  classical
  exact Subtype.fintype (Membership.mem S)

def characterFieldLine (A₀ : FieldLine F) (z : Vec F) : FieldLine F := by
  classical
  exact if hz : z = 0 then A₀ else Projectivization.mk F z hz

omit [Fintype F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem characterFieldLine_eq_of_mem {A₀ A : FieldLine F} {z : Vec F}
    (hz : z ≠ 0) (hm : z ∈ line (lineGenerator A)) :
    characterFieldLine A₀ z = A := by
  classical
  rw [characterFieldLine, dite_eq_right hz, ← Projectivization.mk_rep A]
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact (mem_line_iff (lineGenerator A) z).mp hm

def fieldLineRestrictions (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (J : ∀ A : FieldLine F, BlockOrientation A) :
    FieldLine F → S →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  fun A => orientedBlockRestriction S g (lineGenerator A) (J A)

theorem alignedCharacters_eq_alignmentEvent
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F) :
    alignedCharacters (fun z : S =>
      dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2)) =
      alignmentEvent (fun z : S => (z : Vec F)) g
        (fun z : S => alignmentRightHandSide (z : Vec F)) := by
  classical
  ext z
  simp [alignedCharacters, alignmentEvent, alignmentRightHandSide,
    Fin.sum_univ_three, dot, mul_comm]

theorem card_loss_fieldLineRestrictions_le
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S)
    (A₀ : FieldLine F) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  classical
  apply card_lossIndices_le (fieldLineRestrictions S g J)
    (fun z : S => dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2))
    (fun z : S => characterFieldLine A₀ (z : Vec F)) (Module.finrank (ZMod 2) S)
  · intro A z hz hzero
    have hk := (mem_ker_orientedBlockRestriction_iff S g
      (lineGenerator_ne_zero A) (J A) hz).mp hzero
    refine ⟨hk.2, characterFieldLine_eq_of_mem ?_ hk.1⟩
    exact fun h => hz (Subtype.ext h)
  · rw [alignedCharacters_eq_alignmentEvent]
    exact hS.2 g

theorem card_loss_fieldLineRestrictions_le_three_rank
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    (J : ∀ A : FieldLine F, BlockOrientation A) (hS : IsGeneric S) :
    (lossIndices (fieldLineRestrictions S g J)).card ≤
      3 * Module.finrank (ZMod 2) S := by
  let A₀ : FieldLine F := Projectivization.mk F (fun _ : Fin 3 => (1 : F)) (by
    intro h
    have h0 := congrFun h 0
    exact one_ne_zero h0)
  exact card_loss_fieldLineRestrictions_le S g J hS A₀

end

end DFVSGames.Quadratic

end OAI
