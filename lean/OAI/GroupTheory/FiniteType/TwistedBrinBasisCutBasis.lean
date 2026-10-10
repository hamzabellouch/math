import Mathlib
import OAI.GroupTheory.FiniteType.ActionTransport

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
noncomputable instance : MulAction (localGroup ρ) (CutBasis ρ) where
  smul g B := ⟨translate ρ g B.val⟩
  one_smul B := ext (translate_one ρ B.val)
  mul_smul g h B := ext (translate_mul ρ g h B.val)
@[simp] lemma smul_val (g : localGroup ρ) (B : CutBasis ρ) : (g • B).val = translate ρ g B.val := rfl
instance : IsMonotoneAction (localGroup ρ) (CutBasis ρ) where
  mono g _ _ h := translate_cutRefines ρ g h
abbrev Sublevel (h : ℕ) := rankBelow (fun B : CutBasis ρ => rank ρ B.val) h
noncomputable instance (h : ℕ) : MulAction (localGroup ρ) (Sublevel (ρ := ρ) h) where
  smul g B := ⟨g • B.val,by
    change rank ρ (translate ρ g B.val.val) ≤ h
    rw [rank_translate]
    exact B.property⟩
  one_smul B := Subtype.ext (one_smul _ B.val)
  mul_smul g k B := Subtype.ext (mul_smul g k B.val)
instance (h : ℕ) : IsMonotoneAction (localGroup ρ) (Sublevel (ρ := ρ) h) where
  mono g _ _ h := translate_cutRefines ρ g h
lemma sublevel_val_injective (h : ℕ) : Function.Injective (fun B : Sublevel (ρ := ρ) h => B.val.val) := by
  intro B C he
  exact Subtype.ext (ext he)
lemma vertex_finite_orbits (h : ℕ) :
    Finite (MulAction.orbitRel.Quotient (localGroup ρ) (Sublevel (ρ := ρ) h)) := by
  classical
  obtain ⟨R,hR⟩ := rank_finite_orbit_representatives ρ h
  let T : Set (Sublevel (ρ := ρ) h) := (fun B => B.val.val) ⁻¹' (R : Set (Basis ρ))
  have hT : T.Finite := R.finite_toSet.preimage (sublevel_val_injective h).injOn
  apply finite_orbits_of_cover T hT
  intro B
  exact hR B.val.val B.property
lemma edge_finite_orbits (ho : Oligomorphic ρ) (h : ℕ) :
    Finite (MulAction.orbitRel.Quotient (localGroup ρ) (Edge (Sublevel (ρ := ρ) h))) := by
  classical
  obtain ⟨R,hR⟩ := pair_finite_orbit_representatives ρ ho h
  let f : Edge (Sublevel (ρ := ρ) h) → Basis ρ × Basis ρ := fun e => (e.val.1.val.val,e.val.2.val.val)
  have hi : Function.Injective f := by
    intro e d he
    apply Subtype.ext
    exact Prod.ext (sublevel_val_injective h (congrArg Prod.fst he))
      (sublevel_val_injective h (congrArg Prod.snd he))
  apply finite_orbits_of_cover (f ⁻¹' (R : Set (Basis ρ × Basis ρ))) (R.finite_toSet.preimage hi.injOn)
  intro e
  exact hR _ _ e.property e.val.2.property
lemma triangle_finite_orbits (ho : Oligomorphic ρ) (h : ℕ) :
    Finite (MulAction.orbitRel.Quotient (localGroup ρ) (Triangle (Sublevel (ρ := ρ) h))) := by
  let := edge_finite_orbits ho h
  apply finite_orbits_of_map (Triangle.e02 (P := Sublevel (ρ := ρ) h)) (fun _ _ => rfl)
  intro e
  let B := e.val.1.val.val
  let C := e.val.2.val.val
  let := finite_interval ρ B C
  let f : {t : Triangle (Sublevel (ρ := ρ) h) // t.e02 = e} →
      {D : Basis ρ // B ≤ D ∧ D ≤ C} := fun t => ⟨t.val.val.2.1.val.val,by
    have hb := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.1.val.val) t.property
    have hc := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.2.val.val) t.property
    change t.val.val.1.val.val = B at hb
    change t.val.val.2.2.val.val = C at hc
    exact ⟨hb ▸ le_of_cutRefines ρ t.val.property.1,hc ▸ le_of_cutRefines ρ t.val.property.2⟩⟩
  apply Finite.of_injective f
  intro s t he
  apply Subtype.ext
  apply Subtype.ext
  have hp : s.val.e02 = t.val.e02 := s.property.trans t.property.symm
  have ha := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.1) hp
  have hb := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.2) hp
  exact Prod.ext ha (Prod.ext (sublevel_val_injective h (congrArg Subtype.val he)) hb)

lemma sublevel_connected [Nonempty S] (h : ℕ) (hh : 18 ≤ h) : Connected (Sublevel (ρ := ρ) h) := by
  apply connected_of_constant
  intro f hf x y
  let U := rankBelow (fun B : CutBasis ρ => rank ρ B.val) h
  have he := OrderChains.constant_of_exact_zero (CutBasis ρ) (sublevel_exact 0 h (by simpa using hh))
    (fun B => f (OrderChains.project (CutBasis ρ) U x B)) (fun B hB C hC hBC => by
      apply hf
      change (OrderChains.project (CutBasis ρ) U x B).val ≤ (OrderChains.project (CutBasis ρ) U x C).val
      rw [OrderChains.project_val (CutBasis ρ) x hB,OrderChains.project_val (CutBasis ρ) x hC]
      exact hBC)
    x.property y.property
  simpa only [OrderChains.project_include] using he
end TwistedBrin.Basis.CutBasis

namespace FiniteExtension
variable {L : Type*} [Group L] (K : Subgroup L) [K.Normal]
lemma finitelyGenerated [Finite (L ⧸ K)] [Group.FG K] : Group.FG L := by
  classical
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG K)
  let T : Set L := K.subtype '' S ∪ Set.range (sectionMap K)
  have ht : T.Finite := (hfin.image _).union (Set.finite_range _)
  have hK (k : K) : (k : L) ∈ Subgroup.closure T := by
    have hk : k ∈ Subgroup.closure S := by rw [hS]; trivial
    induction hk using Subgroup.closure_induction with
    | mem k hk => exact Subgroup.subset_closure (Or.inl ⟨k,hk,rfl⟩)
    | one => exact (Subgroup.closure T).one_mem
    | mul k l hk hl ik il => exact (Subgroup.closure T).mul_mem ik il
    | inv k hk ik => exact (Subgroup.closure T).inv_mem ik
  have htop : Subgroup.closure T = ⊤ := by
    apply top_le_iff.mp
    intro x hx
    have ht := (Subgroup.closure T).mul_mem (hK (factor K x))
      (Subgroup.subset_closure (Or.inr ⟨pi K x,rfl⟩))
    simpa only [factor,mul_assoc,inv_mul_cancel,mul_one] using ht
  exact Group.fg_iff.mpr ⟨T,htop,ht⟩
end FiniteExtension

namespace TwistedBrin.Basis
open ActionPresentation
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
lemma vertex_finitelyPresented (hρ : Function.Injective ρ) [Group.IsFinitelyPresented A] (B : Basis ρ) :
    Group.IsFinitelyPresented (vertexStabilizer ρ B) := by
  let := finite_pi_finitelyPresented (fun _ : B => A)
  let := Group.IsFinitelyPresented.equiv (vertexKernelEquiv ρ hρ B)
  let := (vertexPermutationHom ρ B).ker.fintypeQuotientOfFiniteIndex
  exact FiniteExtension.finitelyPresented (vertexPermutationHom ρ B).ker
lemma pair_finitelyGenerated (hρ : Function.Injective ρ)
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F)) {B C : Basis ρ}
    (hBC : CutRefines ρ B C) : Group.FG (pairStabilizer ρ B C) := by
  let F := hBC.some
  let (b : B) : Group.FG (pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) := hS _
  let e := F.pairKernelEquiv ρ hρ
  let : Group.FG (pairPermutationHom ρ B C).ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  let := (pairPermutationHom ρ B C).ker.fintypeQuotientOfFiniteIndex
  exact FiniteExtension.finitelyGenerated (pairPermutationHom ρ B C).ker
end TwistedBrin.Basis

namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
lemma sublevel_vertex_stabilizer (h : ℕ) (B : Sublevel (ρ := ρ) h) :
    MulAction.stabilizer (localGroup ρ) B = vertexStabilizer ρ B.val.val := by
  ext g
  change (g • B = B) ↔ translate ρ g B.val.val = B.val.val
  exact ⟨fun he => congrArg (fun C : Sublevel (ρ := ρ) h => C.val.val) he,
    fun he => sublevel_val_injective h he⟩
lemma sublevel_edge_stabilizer (h : ℕ) (e : Edge (Sublevel (ρ := ρ) h)) :
    MulAction.stabilizer (localGroup ρ) e = pairStabilizer ρ e.val.1.val.val e.val.2.val.val := by
  ext g
  change (g • e = e) ↔ g ∈ vertexStabilizer ρ e.val.1.val.val ∧ g ∈ vertexStabilizer ρ e.val.2.val.val
  rw [← sublevel_vertex_stabilizer h e.val.1,← sublevel_vertex_stabilizer h e.val.2]
  change (g • e = e) ↔ (g • e.val.1 = e.val.1) ∧ (g • e.val.2 = e.val.2)
  exact ⟨fun he => ⟨congrArg (fun d : Edge (Sublevel (ρ := ρ) h) => d.val.1) he,
    congrArg (fun d : Edge (Sublevel (ρ := ρ) h) => d.val.2) he⟩,
    fun he => Subtype.ext (Prod.ext he.1 he.2)⟩

theorem localGroup_finitelyPresented [Nonempty S] (hρ : Function.Injective ρ)
    (ho : Oligomorphic ρ) [Group.IsFinitelyPresented A]
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F)) :
    Group.IsFinitelyPresented (localGroup ρ) := by
  let P := Sublevel (ρ := ρ) 18
  let : Nonempty P := ⟨⟨⟨trivial ρ⟩,by
    change rank ρ (trivial ρ) ≤ 18
    simp [rank,trivial]⟩⟩
  let F := orbitFrames (localGroup ρ) P
  let E := orbitFrames (localGroup ρ) (Edge P)
  let T := orbitFrames (localGroup ρ) (Triangle P)
  let : Finite F.Index := vertex_finite_orbits 18
  let : Finite E.Index := edge_finite_orbits ho 18
  let : Finite T.Index := triangle_finite_orbits ho 18
  apply finitelyPresented_of_frames (sublevel_connected 18 le_rfl)
    (fun R _ c => sublevel_cocycle_trivial 18 le_rfl c) F E T
  · intro i
    change Group.IsFinitelyPresented (MulAction.stabilizer (localGroup ρ) (F.rep i))
    rw [sublevel_vertex_stabilizer]
    exact vertex_finitelyPresented ρ hρ _
  · intro i
    change Group.FG (MulAction.stabilizer (localGroup ρ) (E.rep i))
    rw [sublevel_edge_stabilizer]
    exact pair_finitelyGenerated ρ hρ hS (E.rep i).property
end TwistedBrin.Basis.CutBasis

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrderChainComplex
open OrderListChains
variable (P : Type) [Preorder P]
def simplexSet (n : ℕ) : Set (Simplex P) := {s | OrderChains.Descending P s ∧ degree P s = n}
def chains (n : ℕ) := Finsupp.supported ℤ ℤ (simplexSet P n)

lemma mem_chains {n : ℕ} {c : Chain P} : c ∈ chains P n ↔
    c ∈ OrderChains.module P ∧ Homogeneous P n c := by
  constructor
  · intro h
    exact ⟨fun s hs => (h hs).1,fun s hs => (h hs).2⟩
  · rintro ⟨h,h'⟩ s hs
    exact ⟨h hs,h' s hs⟩

def basisIso (n : ℕ) : chains P n ≃ₗ[ℤ] (simplexSet P n →₀ ℤ) :=
  Finsupp.supportedEquivFinsupp _

instance (n : ℕ) : Module.Free ℤ (chains P n) := Module.Free.of_equiv (basisIso P n).symm

lemma boundary_internal (n : ℕ) (c : chains P (n+1)) : boundary P c ∈ chains P n := by
  exact (mem_chains P).mpr ⟨OrderChains.boundary_mem P ((mem_chains P).mp c.property).1,
    boundary_mem_degreeModule P ((mem_chains P).mp c.property).2⟩

def d (n : ℕ) : chains P (n+1) →ₗ[ℤ] chains P n :=
  LinearMap.codRestrict _ ((boundary P).comp (chains P (n+1)).subtype) (boundary_internal P n)
def aug : chains P 0 →ₗ[ℤ] ℤ := (augmentation P).comp (chains P 0).subtype
lemma d_val (n : ℕ) (c : chains P (n+1)) : (d P n c).val = boundary P c := rfl
lemma d_d (n : ℕ) : (d P n).comp (d P (n+1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  exact boundary_boundary P c.val
lemma d_aug : (aug P).comp (d P 0) = 0 := by
  ext c
  exact augmentation_boundary P c.val

lemma augmentation_degree {n : ℕ} (hn : n ≠ 0) (c : chains P n) : augmentation P c = 0 := by
  classical
  have hh := ((mem_chains P).mp c.property).2
  rw [← Finsupp.sum_single c.val,map_finsuppSum]
  apply Finset.sum_eq_zero
  intro s hs
  change augmentation P (Finsupp.single s (c.val s)) = 0
  rw [augmentation_single]
  have hd := hh s hs
  have hl : s.2 ≠ [] := by intro h; apply hn; simpa [degree,h] using hd.symm
  simp [hl]

lemma aug_surjective [Nonempty P] : Function.Surjective (aug P) := by
  intro r
  let v := Classical.arbitrary P
  refine ⟨⟨Finsupp.single (simplexVertex P v) r, ?_⟩,?_⟩
  · change Supported P (fun s => OrderChains.Descending P s ∧ degree P s = 0) _
    exact supported_single P ⟨by simp [OrderChains.Descending,list,simplexVertex],rfl⟩ r
  · exact augmentation_single P (simplexVertex P v) r

lemma exact_aug (he : OrderChains.ExactIn P 0) : Function.Exact (d P 0) (aug P) := by
  intro c
  constructor
  · intro hc
    obtain ⟨b,hb,hn,hd⟩ := he c ((mem_chains P).mp c.property).1
      ((mem_chains P).mp c.property).2 (by
        classical
        rw [← Finsupp.sum_single c.val,map_finsuppSum]
        apply Finset.sum_eq_zero
        intro s hs
        have hd := ((mem_chains P).mp c.property).2 s hs
        change boundary P (Finsupp.single s (c.val s)) = 0
        rw [show Finsupp.single s (c.val s) = c.val s • Finsupp.single s 1 by simp,map_smul]
        have hz : boundary P (Finsupp.single s 1) = 0 := OrderBasedComplex.d_vertex (based P) hd
        rw [hz,smul_zero]) hc
    exact ⟨⟨b,(mem_chains P).mpr ⟨hb,hn⟩⟩,Subtype.ext hd⟩
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (d_aug P) b

lemma exact_succ (n : ℕ) (he : OrderChains.ExactIn P (n+1)) :
    Function.Exact (d P (n+1)) (d P n) := by
  intro c
  constructor
  · intro hc
    obtain ⟨b,hb,hn,hd⟩ := he c ((mem_chains P).mp c.property).1
      ((mem_chains P).mp c.property).2 (congrArg Subtype.val hc)
      (augmentation_degree P (Nat.succ_ne_zero n) c)
    exact ⟨⟨b,(mem_chains P).mpr ⟨hb,hn⟩⟩,Subtype.ext hd⟩
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (d_d P n) b
end OrderChainComplex

end

end OAI
