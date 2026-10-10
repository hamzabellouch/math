import OAI.GroupTheory.PolycyclicRecognition.Algebra.MaximalAbelianNormal
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Abelian
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Extensions
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicFiniteGeneration

namespace OAI

/-! # Finite generation detected on abelian subgroups of nilpotent groups

In class two, commutators with finitely many generators of a maximal abelian
normal subgroup embed the quotient into a finite power of the center. Induction
through the center quotient reduces the general nilpotent case to this one.
-/

namespace PolycyclicRecognition

open scoped commutatorElement
open Subgroup

variable {G : Type*} [Group G]

/-- The class-two case uses only abelian subgroups, their finite generating
sets, and the central commutator pairing. -/
theorem isPolycyclic_of_central_commutators
    (hc : ∀ x y : G, ⁅x, y⁆ ∈ Subgroup.center G)
    (hfg : ∀ A : Subgroup G, IsMulCommutative A → Group.FG A) : IsPolycyclic G := by
  classical
  have hnil : Group.IsNilpotent G := by
    apply Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    refine ⟨2, ?_⟩
    apply le_antisymm _ bot_le
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ]
    apply (Subgroup.commutator_mono ?_ le_rfl).trans
      (le_of_eq (Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr le_rfl))
    change _root_.commutator G ≤ Subgroup.center G
    exact Subgroup.commutator_le.mpr (fun x _ y _ => hc x y)
  let := hnil
  obtain ⟨A, hAn, hAa, hmax⟩ := exists_maximal_abelian_normal_subgroup G
  let := hAn
  let : CommGroup A := { (inferInstance : Group A) with
    mul_comm := hAa.is_comm.comm }
  let : Group.FG A := hfg A hAa
  let Z := Subgroup.center G
  let : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp x.property y).symm }
  let : Group.FG Z := hfg Z inferInstance
  obtain ⟨S, hS⟩ := Group.fg_def.mp (inferInstance : Group.FG A)
  let F : G →* (S → Z) :=
    { toFun := fun g a => ⟨⁅g, (a.val : G)⁆, hc g a.val⟩
      map_one' := by ext a; simp
      map_mul' := by
        intro g h
        ext a
        change ⁅g * h, (a.val : G)⁆ = ⁅g, (a.val : G)⁆ * ⁅h, (a.val : G)⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hz := Subgroup.mem_center_iff.mp (hc h (a.val : G)) g
        rw [hz, mul_inv_cancel_right]
        exact (Subgroup.mem_center_iff.mp (hc h (a.val : G)) _).symm }
  have hker : F.ker = A := by
    apply Eq.trans ?_ (centralizer_eq_of_maximal_abelian_normal G A hmax)
    ext g
    constructor
    · intro hg
      apply Subgroup.mem_centralizer_iff_commutator_eq_one'.mpr
      intro a ha
      let C := Subgroup.centralizer ({g} : Set G)
      have hS' : (S : Set A) ⊆ C.comap A.subtype := by
        intro a haS
        apply Subgroup.mem_centralizer_iff.mpr
        intro x hx
        obtain rfl : x = g := Set.mem_singleton_iff.mp hx
        have he := congrArg (fun z : S → Z => (z ⟨a, haS⟩ : G)) hg
        exact (commutatorElement_eq_one_iff_mul_comm.mp he)
      have hAC : (⊤ : Subgroup A) ≤ C.comap A.subtype := by
        rw [← hS]
        exact (Subgroup.closure_le _).mpr hS'
      have he : g * a = a * g := hAC (show (⟨a, ha⟩ : A) ∈ ⊤ from trivial) g (by simp)
      exact commutatorElement_eq_one_iff_mul_comm.mpr he
    · intro hg
      change F g = 1
      ext a
      exact Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hg _ a.val.property
  have hQ : IsPolycyclic (G ⧸ F.ker) := by
    have hR : IsPolycyclic F.range :=
      (isPolycyclic_of_finitelyGenerated_commGroup (S → Z)).of_injective
        F.range.subtype Subtype.val_injective
    exact (isPolycyclic_equiv (QuotientGroup.quotientKerEquivRange F)).mpr hR
  have hQA : IsPolycyclic (G ⧸ A) :=
    (isPolycyclic_equiv (QuotientGroup.quotientMulEquivOfEq hker)).mp hQ
  exact isPolycyclic_of_normal_subgroup A (isPolycyclic_of_finitelyGenerated_commGroup A) hQA

/-- The hypothesis that abelian subgroups are finitely generated passes to
an injectively represented subgroup. -/
theorem abelian_subgroups_fg_of_injective
    (hfg : ∀ A : Subgroup G, IsMulCommutative A → Group.FG A)
    {H : Type*} [Group H] (f : H →* G) (hf : Function.Injective f) :
    ∀ A : Subgroup H, IsMulCommutative A → Group.FG A := by
  intro A hA
  let := hA
  let : Group.FG (A.map f) := hfg (A.map f) inferInstance
  let e := A.equivMapOfInjective f hf
  exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- In a nilpotent group, finite generation of every abelian subgroup
suffices for polycyclicity of the whole group. -/
theorem isPolycyclic_of_nilpotent_abelian_subgroups_fg [Group.IsNilpotent G]
    (hfg : ∀ A : Subgroup G, IsMulCommutative A → Group.FG A) : IsPolycyclic G := by
  apply Group.nilpotent_center_quotient_ind G
    (P := fun K _ _ => (∀ A : Subgroup K, IsMulCommutative A → Group.FG A) →
      IsPolycyclic K) ?_ ?_ hfg
  · intro K _ _ _
    exact isPolycyclic_of_subsingleton
  · intro K _ _ ih hK
    let q := QuotientGroup.mk' (Subgroup.center K)
    have hQ : ∀ B : Subgroup (K ⧸ Subgroup.center K),
        IsMulCommutative B → Group.FG B := by
      intro B hB
      let P := B.comap q
      have hPc (x y : P) : ⁅x, y⁆ ∈ Subgroup.center P := by
        have hxy : q ⁅(x : K), (y : K)⁆ = 1 := by
          rw [map_commutatorElement]
          apply commutatorElement_eq_one_iff_mul_comm.mpr
          exact congrArg Subtype.val
            (hB.is_comm.comm (⟨q x, x.property⟩ : B) (⟨q y, y.property⟩ : B))
        have hc : ⁅(x : K), (y : K)⁆ ∈ Subgroup.center K :=
          (QuotientGroup.eq_one_iff _).mp hxy
        apply Subgroup.mem_center_iff.mpr
        intro z
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp hc z
      have hP := isPolycyclic_of_central_commutators hPc
        (abelian_subgroups_fg_of_injective hK P.subtype Subtype.val_injective)
      let f : P →* B := (q.comp P.subtype).codRestrict B (fun x => x.property)
      have hf : Function.Surjective f := by
        intro b
        obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) b.val
        exact ⟨⟨x, by change q x ∈ B; rw [hx]; exact b.property⟩, Subtype.ext hx⟩
      exact (hP.of_surjective f hf).finitelyGenerated
    let Z := Subgroup.center K
    let : CommGroup Z := { (inferInstance : Group Z) with
      mul_comm := fun x y => Subtype.ext (Subgroup.mem_center_iff.mp x.property y).symm }
    let : Group.FG Z := hK Z inferInstance
    exact isPolycyclic_of_normal_subgroup Z
      (isPolycyclic_of_finitelyGenerated_commGroup Z) (ih hQ)

end PolycyclicRecognition

end OAI
