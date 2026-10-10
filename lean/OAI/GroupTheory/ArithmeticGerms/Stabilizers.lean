import Mathlib
import OAI.GroupTheory.ArithmeticGerms.Basic

namespace OAI

/-! Full arithmetic germ stabilizers and finite orbits. -/



namespace ArithmeticGerms

open scoped Pointwise

class ICC (G : Type*) [Group G] : Prop where
  infinite_conjugacyClass : ∀ g : G, g ≠ 1 → (ConjClasses.mk g).carrier.Infinite

section FiniteIndex
variable {K L : Type*} [Group K] [Group L]

lemma finiteIndex_comap (A : Subgroup L) [A.FiniteIndex] (f : K →* L) :
    (A.comap f).FiniteIndex := by
  refine ⟨?_⟩
  rw [Subgroup.index_comap]
  exact (Subgroup.isFiniteRelIndex_of_finiteIndex (H := A) (K := f.range)).relIndex_ne_zero

lemma finiteIndex_map (A : Subgroup K) [A.FiniteIndex] (f : K →* L)
    [f.range.FiniteIndex] : (A.map f).FiniteIndex := by
  refine ⟨?_⟩
  rw [Subgroup.index_map]
  exact mul_ne_zero (Subgroup.finiteIndex_of_le (H := A) le_sup_left).index_ne_zero
    Subgroup.FiniteIndex.index_ne_zero

lemma finiteIndex_image_of_relIndex (S T : Subgroup K) (hST : S ≤ T)
    [S.IsFiniteRelIndex T] (f : K →* L) [(T.map f).FiniteIndex] :
    (S.map f).FiniteIndex := by
  let φ := f.comp T.subtype
  have hr : φ.range = T.map f := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have : φ.range.FiniteIndex := hr ▸ (inferInstance : (T.map f).FiniteIndex)
  have h := finiteIndex_map (S.subgroupOf T) φ
  have he : (S.subgroupOf T).map φ = S.map f := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hST]
  exact he ▸ h

end FiniteIndex

section ICC
variable {G : Type*} [Group G] [ICC G]

theorem eq_one_of_centralizes_finiteIndex (A : Subgroup G) [A.FiniteIndex]
    (g : G) (hg : ∀ a ∈ A, g * a = a * g) : g = 1 := by
  by_contra hne
  have hle : A ≤ Subgroup.centralizer ({g} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    exact hg a ha
  have : (Subgroup.centralizer ({g} : Set G)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  have hi : (MulAction.stabilizer (ConjAct G) g).FiniteIndex := by
    refine ⟨?_⟩
    have h := (Subgroup.FiniteIndex.index_ne_zero
      (H := Subgroup.centralizer ({g} : Set G)))
    have he : (Subgroup.centralizer ({g} : Set G)).index =
        (MulAction.stabilizer (ConjAct G) g).index := calc
      _ = ((MulAction.stabilizer (ConjAct G) g).comap
          (ConjAct.toConjAct (G := G)).toMonoidHom).index :=
        congrArg Subgroup.index (Subgroup.centralizer_eq_comap_stabilizer g)
      _ = _ := Subgroup.index_comap_of_surjective _
        (ConjAct.toConjAct (G := G)).surjective
    exact fun hz => h (he.trans hz)
  have : Finite (MulAction.orbit (ConjAct G) g) :=
    (MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).finite_iff.mpr inferInstance
  have hf : (MulAction.orbit (ConjAct G) g).Finite := Set.toFinite _
  rw [ConjAct.orbit_eq_carrier_conjClasses] at hf
  exact (ICC.infinite_conjugacyClass g hne).not_finite hf

end ICC

namespace VirtualGraph
variable {G H : Type*} [Group G] [Group H]

noncomputable def toDomain (C : VirtualGraph G H) : C.graph ≃* C.domain :=
  MulEquiv.ofBijective ((MonoidHom.fst G H).subgroupMap C.graph)
    ⟨fun _ _ h => C.fst_injective (congrArg Subtype.val h),
      (MonoidHom.fst G H).subgroupMap_surjective C.graph⟩

noncomputable def toCodomain (C : VirtualGraph G H) : C.graph ≃* C.codomain :=
  MulEquiv.ofBijective ((MonoidHom.snd G H).subgroupMap C.graph)
    ⟨fun _ _ h => C.snd_injective (congrArg Subtype.val h),
      (MonoidHom.snd G H).subgroupMap_surjective C.graph⟩

noncomputable def iso (C : VirtualGraph G H) : C.domain ≃* C.codomain :=
  C.toDomain.symm.trans C.toCodomain

lemma pair_mem_graph (C : VirtualGraph G H) (a : C.domain) :
    ((a : G), (C.iso a : H)) ∈ C.graph := by
  have h := (C.toDomain.symm a).property
  have he := congrArg (fun x : C.domain => (x : G)) (C.toDomain.apply_symm_apply a)
  change ((C.toDomain.symm a).val.1, (C.toDomain.symm a).val.2) ∈ C.graph at h
  change ((a : G), (C.toDomain.symm a).val.2) ∈ C.graph
  change (C.toDomain.symm a).val.1 = (a : G) at he
  rwa [he] at h

lemma finiteRelIndex_of_fst (C : VirtualGraph G H) (S : Subgroup (G × H))
    (hS : S ≤ C.graph) [(S.map (MonoidHom.fst G H)).FiniteIndex] :
    S.IsFiniteRelIndex C.graph := by
  let φ := (MonoidHom.fst G H).comp C.graph.subtype
  have he : (S.map (MonoidHom.fst G H)).comap φ = S.subgroupOf C.graph := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      have hxy : (⟨y, hS hy⟩ : C.graph) = x := C.fst_injective he
      have hv : y = x.val := congrArg Subtype.val hxy
      change x.val ∈ S
      exact hv ▸ hy
    · intro hx
      exact ⟨x.val, hx, rfl⟩
  have hi := finiteIndex_comap (S.map (MonoidHom.fst G H)) φ
  rw [he] at hi
  exact Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr hi

lemma commensurable_of_le (C D : VirtualGraph G H) (hle : C.graph ≤ D.graph) :
    C.graph.Commensurable D.graph := by
  exact ⟨D.finiteRelIndex_of_fst C.graph hle,
    ⟨(Subgroup.relIndex_eq_one.mpr hle).trans_ne one_ne_zero⟩⟩

def restriction (C : VirtualGraph G H) (S : Subgroup (G × H)) (hS : S ≤ C.graph)
    [S.IsFiniteRelIndex C.graph] : VirtualGraph G H where
  graph := S
  fst_injective := by
    intro x y h
    exact Subtype.ext (congrArg (fun t : C.graph => t.val)
      (C.fst_injective (a₁ := ⟨x.val, hS x.property⟩)
        (a₂ := ⟨y.val, hS y.property⟩) h))
  snd_injective := by
    intro x y h
    exact Subtype.ext (congrArg (fun t : C.graph => t.val)
      (C.snd_injective (a₁ := ⟨x.val, hS x.property⟩)
        (a₂ := ⟨y.val, hS y.property⟩) h))
  fst_finite := finiteIndex_image_of_relIndex S C.graph hS (MonoidHom.fst G H)
  snd_finite := finiteIndex_image_of_relIndex S C.graph hS (MonoidHom.snd G H)

theorem commensurable_iff_common_restriction (C D : VirtualGraph G H) :
    C.graph.Commensurable D.graph ↔
      ∃ R : VirtualGraph G H, R.graph ≤ C.graph ∧ R.graph ≤ D.graph := by
  constructor
  · intro h
    have : (C.graph ⊓ D.graph).IsFiniteRelIndex C.graph :=
      ⟨by rw [Subgroup.inf_relIndex_left]; exact h.2.relIndex_ne_zero⟩
    exact ⟨C.restriction (C.graph ⊓ D.graph) inf_le_left, inf_le_left, inf_le_right⟩
  · rintro ⟨R, hRC, hRD⟩
    exact (R.commensurable_of_le C hRC).symm.trans (R.commensurable_of_le D hRD)

lemma iso_extends (C D : VirtualGraph G H) (hle : C.graph ≤ D.graph) (a : C.domain) :
    (C.iso a : H) = D.iso ⟨a.val, (Subgroup.map_mono hle) a.property⟩ := by
  have he := D.fst_injective
    (a₁ := ⟨(a.val, (C.iso a : H)), hle (C.pair_mem_graph a)⟩)
    (a₂ := ⟨(a.val, (D.iso ⟨a.val, (Subgroup.map_mono hle) a.property⟩ : H)),
      D.pair_mem_graph ⟨a.val, (Subgroup.map_mono hle) a.property⟩⟩) rfl
  exact congrArg (fun x : D.graph => x.val.2) he

def ofEquiv (e : G ≃* H) : VirtualGraph G H where
  graph := e.toMonoidHom.graph
  fst_injective := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext h (x.property.symm.trans ((congrArg e h).trans y.property))
  snd_injective := by
    intro x y h
    apply Subtype.ext
    exact Prod.ext (e.injective (x.property.trans (h.trans y.property.symm))) h
  fst_finite := by
    have he : e.toMonoidHom.graph.map (MonoidHom.fst G H) = ⊤ := by
      ext g
      exact ⟨fun _ => Subgroup.mem_top _, fun _ => ⟨(g, e g), rfl, rfl⟩⟩
    rw [he]
    infer_instance
  snd_finite := by
    have he : e.toMonoidHom.graph.map (MonoidHom.snd G H) = ⊤ := by
      ext h
      refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
      exact ⟨(e.symm h, h), e.apply_symm_apply h, rfl⟩
    rw [he]
    infer_instance

def conjugate (C : VirtualGraph G H) (k : G × H) : VirtualGraph G H where
  graph := C.graph.map (MulAut.conj k).toMonoidHom
  fst_injective := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩ he
    have hab : (⟨a, ha⟩ : C.graph) = ⟨b, hb⟩ :=
      C.fst_injective ((MulAut.conj k.1).injective he)
    exact Subtype.ext (congrArg (MulAut.conj k) (congrArg Subtype.val hab))
  snd_injective := by
    rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩ he
    have hab : (⟨a, ha⟩ : C.graph) = ⟨b, hb⟩ :=
      C.snd_injective ((MulAut.conj k.2).injective he)
    exact Subtype.ext (congrArg (MulAut.conj k) (congrArg Subtype.val hab))
  fst_finite := by
    have he : (C.graph.map (MulAut.conj k).toMonoidHom).map (MonoidHom.fst G H) =
        C.domain.map (MulAut.conj k.1).toMonoidHom := by
      simp only [domain, Subgroup.map_map]
      rfl
    refine ⟨?_⟩
    rw [he, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact Subgroup.FiniteIndex.index_ne_zero
  snd_finite := by
    have he : (C.graph.map (MulAut.conj k).toMonoidHom).map (MonoidHom.snd G H) =
        C.codomain.map (MulAut.conj k.2).toMonoidHom := by
      simp only [codomain, Subgroup.map_map]
      rfl
    refine ⟨?_⟩
    rw [he, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact Subgroup.FiniteIndex.index_ne_zero

lemma conjugate_graph (C : VirtualGraph G H) (k : G × H) :
    (C.conjugate k).graph = ConjAct.toConjAct k • C.graph := rfl

instance : MulAction (G × H) (VirtualGraph G H) where
  smul k C := C.conjugate k
  one_smul C := by
    apply VirtualGraph.ext
    change (C.conjugate 1).graph = C.graph
    rw [conjugate_graph, map_one, one_smul]
  mul_smul k l C := by
    apply VirtualGraph.ext
    change (C.conjugate (k * l)).graph = ((C.conjugate l).conjugate k).graph
    simp only [conjugate_graph, map_mul, mul_smul]

lemma smul_graph (C : VirtualGraph G H) (k : G × H) :
    (k • C).graph = ConjAct.toConjAct k • C.graph := rfl

def fullSubgroup (C : VirtualGraph G H) : Subgroup (G × H) :=
  Subgroup.Commensurable.commensurator C.graph

lemma graph_le_fullSubgroup (C : VirtualGraph G H) : C.graph ≤ C.fullSubgroup := by
  intro k hk
  change (ConjAct.toConjAct k • C.graph).Commensurable C.graph
  rw [Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hk)]

lemma snd_eq_one_of_mem_fullSubgroup [ICC H] (C : VirtualGraph G H)
    (k : G × H) (hk : k ∈ C.fullSubgroup) (hfst : k.1 = 1) : k.2 = 1 := by
  let S := C.graph ⊓ ConjAct.toConjAct k • C.graph
  have hcomm : (ConjAct.toConjAct k • C.graph).Commensurable C.graph := hk
  have : S.IsFiniteRelIndex C.graph :=
    ⟨by change (C.graph ⊓ _).relIndex C.graph ≠ 0
        rw [Subgroup.inf_relIndex_left]; exact hcomm.1.relIndex_ne_zero⟩
  have : (S.map (MonoidHom.snd G H)).FiniteIndex :=
    finiteIndex_image_of_relIndex S C.graph inf_le_left _
  apply eq_one_of_centralizes_finiteIndex (S.map (MonoidHom.snd G H)) k.2
  rintro a ⟨x, hx, rfl⟩
  have hy : k⁻¹ * x * k ∈ C.graph := by
    have h := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx.2
    simpa only [← map_inv, ConjAct.toConjAct_inv_smul] using h
  have he : (⟨k⁻¹ * x * k, hy⟩ : C.graph) = ⟨x, hx.1⟩ := by
    apply C.fst_injective
    change k.1⁻¹ * x.1 * k.1 = x.1
    simp [hfst]
  have he' := congrArg (fun y : C.graph => y.val.2) he
  change k.2⁻¹ * x.2 * k.2 = x.2 at he'
  calc
    k.2 * x.2 = k.2 * (k.2⁻¹ * x.2 * k.2) := congrArg (k.2 * ·) he'.symm
    _ = x.2 * k.2 := by group

lemma fst_eq_one_of_mem_fullSubgroup [ICC G] (C : VirtualGraph G H)
    (k : G × H) (hk : k ∈ C.fullSubgroup) (hsnd : k.2 = 1) : k.1 = 1 := by
  let S := C.graph ⊓ ConjAct.toConjAct k • C.graph
  have hcomm : (ConjAct.toConjAct k • C.graph).Commensurable C.graph := hk
  have : S.IsFiniteRelIndex C.graph :=
    ⟨by change (C.graph ⊓ _).relIndex C.graph ≠ 0
        rw [Subgroup.inf_relIndex_left]; exact hcomm.1.relIndex_ne_zero⟩
  have : (S.map (MonoidHom.fst G H)).FiniteIndex :=
    finiteIndex_image_of_relIndex S C.graph inf_le_left _
  apply eq_one_of_centralizes_finiteIndex (S.map (MonoidHom.fst G H)) k.1
  rintro a ⟨x, hx, rfl⟩
  have hy : k⁻¹ * x * k ∈ C.graph := by
    have h := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx.2
    simpa only [← map_inv, ConjAct.toConjAct_inv_smul] using h
  have he : (⟨k⁻¹ * x * k, hy⟩ : C.graph) = ⟨x, hx.1⟩ := by
    apply C.snd_injective
    change k.2⁻¹ * x.2 * k.2 = x.2
    simp [hsnd]
  have he' := congrArg (fun y : C.graph => y.val.1) he
  change k.1⁻¹ * x.1 * k.1 = x.1 at he'
  calc
    k.1 * x.1 = k.1 * (k.1⁻¹ * x.1 * k.1) := congrArg (k.1 * ·) he'.symm
    _ = x.1 * k.1 := by group

def full [ICC G] [ICC H] (C : VirtualGraph G H) : VirtualGraph G H where
  graph := C.fullSubgroup
  fst_injective := by
    apply (injective_iff_map_eq_one _).mpr
    intro k hk
    apply Subtype.ext
    exact Prod.ext hk (C.snd_eq_one_of_mem_fullSubgroup k.val k.property hk)
  snd_injective := by
    apply (injective_iff_map_eq_one _).mpr
    intro k hk
    apply Subtype.ext
    exact Prod.ext (C.fst_eq_one_of_mem_fullSubgroup k.val k.property hk) hk
  fst_finite := Subgroup.finiteIndex_of_le (Subgroup.map_mono C.graph_le_fullSubgroup)
  snd_finite := Subgroup.finiteIndex_of_le (Subgroup.map_mono C.graph_le_fullSubgroup)

lemma commensurable_full [ICC G] [ICC H] (C : VirtualGraph G H) :
    C.graph.Commensurable C.full.graph :=
  C.commensurable_of_le C.full C.graph_le_fullSubgroup

lemma finiteIndex_in_full [ICC G] [ICC H] (C : VirtualGraph G H) :
    C.graph.IsFiniteRelIndex C.full.graph :=
  C.commensurable_full.1

end VirtualGraph

def germSetoid (G H : Type*) [Group G] [Group H] : Setoid (VirtualGraph G H) where
  r C D := C.graph.Commensurable D.graph
  iseqv := ⟨fun C => .refl C.graph, fun h => h.symm, fun h h' => h.trans h'⟩

def Germ (G H : Type*) [Group G] [Group H] := Quotient (germSetoid G H)

namespace Germ
variable {G H : Type*} [Group G] [Group H]

def mk (C : VirtualGraph G H) : Germ G H := Quotient.mk (germSetoid G H) C

@[elab_as_elim]
lemma induction_on {P : Germ G H → Prop} (d : Germ G H)
    (h : ∀ C, P (mk C)) : P d := Quotient.inductionOn d h

lemma mk_eq_mk_iff (C D : VirtualGraph G H) :
    mk C = mk D ↔ C.graph.Commensurable D.graph := Quotient.eq

instance : MulAction (G × H) (Germ G H) where
  smul k d := Quotient.map (k • ·)
    (fun C D (h : C.graph.Commensurable D.graph) =>
      Subgroup.Commensurable.smul (ConjAct.toConjAct k) h) d
  one_smul d := by
    induction d using induction_on with | h C =>
      exact congrArg mk (one_smul (G × H) C)
  mul_smul k l d := by
    induction d using induction_on with | h C =>
      exact congrArg mk (mul_smul k l C)

@[simp]
lemma smul_mk (k : G × H) (C : VirtualGraph G H) : k • mk C = mk (k • C) := rfl

section ICC
variable [ICC G] [ICC H]

def full (d : Germ G H) : VirtualGraph G H :=
  Quotient.lift VirtualGraph.full
    (fun _ _ h => VirtualGraph.ext (Subgroup.Commensurable.eq h)) d

@[simp]
lemma full_mk (C : VirtualGraph G H) : (mk C).full = C.full := rfl

theorem full_graph_eq_stabilizer (d : Germ G H) :
    d.full.graph = MulAction.stabilizer (G × H) d := by
  induction d using induction_on with | h C =>
    ext k
    change (ConjAct.toConjAct k • C.graph).Commensurable C.graph ↔ k • mk C = mk C
    exact (mk_eq_mk_iff (k • C) C).symm

lemma mk_full (d : Germ G H) : mk d.full = d := by
  induction d using induction_on with | h C =>
    exact (mk_eq_mk_iff _ _).mpr C.commensurable_full.symm

lemma mem_full_iff (d : Germ G H) (k : G × H) :
    k ∈ d.full.graph ↔ k • d = d := by
  rw [full_graph_eq_stabilizer, MulAction.mem_stabilizer_iff]

theorem representative_in_full (C : VirtualGraph G H) :
    C.graph ≤ (mk C).full.graph ∧ C.graph.IsFiniteRelIndex (mk C).full.graph :=
  ⟨C.graph_le_fullSubgroup, C.finiteIndex_in_full⟩

theorem eq_mk_of_fixed_by_finiteIndex (C : VirtualGraph G H)
    (S : Subgroup (G × H)) (hS : S ≤ C.graph) [S.IsFiniteRelIndex C.graph]
    (d : Germ G H) (hfix : ∀ k ∈ S, k • d = d) : d = mk C := by
  let R := C.restriction S hS
  have hRC : R.graph ≤ C.graph := hS
  have hRD : R.graph ≤ d.full.graph := fun k hk => (mem_full_iff d k).mpr (hfix k hk)
  calc
    d = mk d.full := (mk_full d).symm
    _ = mk C := (mk_eq_mk_iff _ _).mpr
      ((R.commensurable_of_le d.full hRD).symm.trans (R.commensurable_of_le C hRC))

theorem eq_of_fixed_by_finiteIndex (d x : Germ G H) (S : Subgroup (G × H))
    (hS : S ≤ MulAction.stabilizer (G × H) d)
    [S.IsFiniteRelIndex (MulAction.stabilizer (G × H) d)]
    (hfix : ∀ k ∈ S, k • x = x) : x = d := by
  have h' : S ≤ d.full.graph := by rwa [full_graph_eq_stabilizer]
  have : S.IsFiniteRelIndex d.full.graph := by
    rw [full_graph_eq_stabilizer]
    infer_instance
  exact (eq_mk_of_fixed_by_finiteIndex d.full S h' x hfix).trans (mk_full d)

theorem finite_orbit_iff_eq_mk (C : VirtualGraph G H) (d : Germ G H) :
    (MulAction.orbit C.graph d).Finite ↔ d = mk C := by
  constructor
  · intro hf
    have : Finite (MulAction.orbit C.graph d) := Set.finite_coe_iff.mpr hf
    have : Finite (C.graph ⧸ MulAction.stabilizer C.graph d) :=
      (MulAction.orbitEquivQuotientStabilizer C.graph d).finite_iff.mp inferInstance
    let A := MulAction.stabilizer C.graph d
    have : A.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    let S := A.map C.graph.subtype
    have he : S.subgroupOf C.graph = A := by
      change (A.map C.graph.subtype).comap C.graph.subtype = A
      exact Subgroup.comap_map_eq_self (by simp)
    have : S.IsFiniteRelIndex C.graph := by
      apply Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
      rw [he]
      infer_instance
    apply eq_mk_of_fixed_by_finiteIndex C S (Subgroup.map_subtype_le A) d
    rintro k ⟨a, ha, rfl⟩
    exact ha
  · rintro rfl
    apply (Set.finite_singleton (mk C)).subset
    rintro d ⟨k, rfl⟩
    exact (mem_full_iff (mk C) k.val).mp (C.graph_le_fullSubgroup k.property)

theorem finite_orbit_iff (d x : Germ G H) :
    (MulAction.orbit (MulAction.stabilizer (G × H) d) x).Finite ↔ x = d := by
  rw [← full_graph_eq_stabilizer]
  simpa only [mk_full] using finite_orbit_iff_eq_mk d.full x

end ICC

def inner (g : G) : Germ G G := mk (VirtualGraph.ofEquiv (MulAut.conj g))

theorem inner_injective [ICC G] : Function.Injective (inner : G → Germ G G) := by
  intro g h hgh
  obtain ⟨R, hg, hh⟩ := (VirtualGraph.commensurable_iff_common_restriction _ _).mp
    ((mk_eq_mk_iff _ _).mp hgh)
  have he : h⁻¹ * g = 1 := by
    apply eq_one_of_centralizes_finiteIndex R.domain (h⁻¹ * g)
    intro a ha
    have hc := (MonoidHom.mem_graph.mp (hg (R.pair_mem_graph ⟨a, ha⟩))).trans
      (MonoidHom.mem_graph.mp (hh (R.pair_mem_graph ⟨a, ha⟩))).symm
    change g * a * g⁻¹ = h * a * h⁻¹ at hc
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (h⁻¹ * g) * a * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * a * g⁻¹) * h := by group
      _ = h⁻¹ * (h * a * h⁻¹) * h := by rw [hc]
      _ = a := by group
  exact (inv_mul_eq_one.mp he).symm

end Germ

theorem full_stabilizers_and_finite_orbit_test
    {G H : Type*} [Group G] [Group H] [ICC G] [ICC H] (C : VirtualGraph G H) :
    Function.Injective (Germ.inner : G → Germ G G) ∧
    Function.Injective (Germ.inner : H → Germ H H) ∧
    ∃ (F : VirtualGraph G H) (hle : C.graph ≤ F.graph),
      F.graph = MulAction.stabilizer (G × H) (Germ.mk C) ∧
      C.graph.IsFiniteRelIndex F.graph ∧
      (∀ a : C.domain,
        (C.iso a : H) = F.iso ⟨a.val, (Subgroup.map_mono hle) a.property⟩) ∧
      (∀ x : Germ G H, (MulAction.orbit F.graph x).Finite ↔ x = Germ.mk C) ∧
      (∀ x : Germ G H, (MulAction.orbit C.graph x).Finite ↔ x = Germ.mk C) := by
  refine ⟨Germ.inner_injective, Germ.inner_injective, C.full, C.graph_le_fullSubgroup,
    Germ.full_graph_eq_stabilizer (Germ.mk C), C.finiteIndex_in_full,
    C.iso_extends C.full C.graph_le_fullSubgroup, ?_, Germ.finite_orbit_iff_eq_mk C⟩
  intro x
  have hfull : Germ.mk C.full = Germ.mk C := Germ.mk_full (Germ.mk C)
  simpa only [hfull] using Germ.finite_orbit_iff_eq_mk C.full x

end ArithmeticGerms

end OAI
