import Mathlib
import OAI.GroupTheory.FiniteType.EquivariantOrderChains

namespace OAI

noncomputable section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace FiniteIndexProducts
variable {G : Type} [Group G] (K : Subgroup G) [K.Normal] [K.FiniteIndex]
variable (I : Type) (n : ℕ)
def homologyIso : groupHomology (RegularProductR.rep ℤ K I) n ≅
    groupHomology (RegularProductR.rep ℤ G I) n := by
  classical
  letI := K.fintypeQuotientOfFiniteIndex
  exact (groupHomology.indIso K (RegularProductR.rep ℤ K I) n).symm ≪≫
    (groupHomology.functor ℤ G n).mapIso (FiniteIndexRegular.indIso K I)

lemma downNormal (hz : IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
    IsZero (groupHomology (RegularProductR.rep ℤ K I) n) := hz.of_iso (homologyIso K I n)
lemma upNormal (hz : IsZero (groupHomology (RegularProductR.rep ℤ K I) n)) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) n) := hz.of_iso (homologyIso K I n).symm

variable (H : Subgroup G) [H.FiniteIndex]
include H in

theorem down (hz : IsZero (groupHomology (RegularProductR.rep ℤ G I) n)) :
    IsZero (groupHomology (RegularProductR.rep ℤ H I) n) := by
  let C := H.normalCore
  have hC := downNormal C I n hz
  let e : C.subgroupOf H ≃* C := Subgroup.subgroupOfEquivOfLe H.normalCore_le
  have hcH := hC.of_iso (RegularProductR.homologyRelabel e I n)
  exact upNormal (C.subgroupOf H) I n hcH

include H in
                                                                         
theorem up (hz : IsZero (groupHomology (RegularProductR.rep ℤ H I) n)) :
    IsZero (groupHomology (RegularProductR.rep ℤ G I) n) := by
  let C := H.normalCore
  have hC := downNormal (C.subgroupOf H) I n hz
  let e : C.subgroupOf H ≃* C := Subgroup.subgroupOfEquivOfLe H.normalCore_le
  have hcG := hC.of_iso (RegularProductR.homologyRelabel e I n).symm
  exact upNormal C I n hcG
end FiniteIndexProducts

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace EquivariantOrderChains
open OrderListChains OrderChainComplex
variable {G P : Type} [Group G] [Preorder P] [MulAction G P]
  [CovariantClass G P HSMul.hSMul LE.le] {n : ℕ}

def tuple (s : simplexSet P n) (i : Fin (n+1)) : P :=
  (s.val.1 :: s.val.2).get ⟨i.val,by
    have hn : s.val.2.length = n := s.property.2
    simp only [List.length_cons]
    omega⟩

lemma tuple_injective : Function.Injective (tuple (P := P) (n := n)) := by
  intro s t he
  have hl : s.val.1 :: s.val.2 = t.val.1 :: t.val.2 := by
    apply List.ext_get
    · simp only [List.length_cons,show s.val.2.length = n from s.property.2,
        show t.val.2.length = n from t.property.2]
    · intro i hi hj
      have hi' : i < n+1 := by
        have hs : s.val.2.length = n := s.property.2
        simpa only [List.length_cons,hs] using hi
      exact congrFun he ⟨i,hi'⟩
  exact Subtype.ext (Prod.ext (List.cons.inj hl).1 (List.cons.inj hl).2)

lemma tuple_antitone (s : simplexSet P n) : Antitone (tuple s) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (List.pairwise_iff_get.mp s.property.1) _ _ hlt
  · exact le_rfl

lemma tuple_smul (g : G) (s : simplexSet P n) (i : Fin (n+1)) :
    tuple (g • s) i = g • tuple s i := by
  have hi : i.val < (s.val.1 :: s.val.2).length := by
    have hs : s.val.2.length = n := s.property.2
    simpa only [List.length_cons,hs] using i.isLt
  have hi' : i.val < ((s.val.1 :: s.val.2).map (fun x : P => g • x)).length := by simpa using hi
  change ((s.val.1 :: s.val.2).map (fun x : P => g • x))[i.val] = g • (s.val.1 :: s.val.2)[i.val]
  exact List.getElem_map (fun x : P => g • x)

instance covariantPosetAction : ActionTransport.IsMonotoneAction G P where
  mono g _ _ h := smul_le_smul_left g h

def endpoints (s : simplexSet P n) : ActionTransport.Edge P :=
  ⟨(tuple s (Fin.last n),tuple s 0),tuple_antitone s (Fin.zero_le _)⟩

lemma endpoints_smul (g : G) (s : simplexSet P n) :
    endpoints (g • s) = g • endpoints s := by
  apply Subtype.ext
  exact Prod.ext (tuple_smul g s _) (tuple_smul g s _)
end EquivariantOrderChains

namespace TwistedBrin.Basis.CutBasis
open OrderChainComplex EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

instance sublevel_covariant (h : ℕ) :
    CovariantClass (localGroup ρ) (Sublevel (ρ := ρ) h) HSMul.hSMul LE.le where
  elim g _ _ hBC := translate_cutRefines ρ g hBC

lemma simplex_endpoint_fiber_finite (h n : ℕ) (e : Edge (Sublevel (ρ := ρ) h)) :
    Finite {s : simplexSet (Sublevel (ρ := ρ) h) n // endpoints s = e} := by
  classical
  let B := e.val.1.val.val
  let C := e.val.2.val.val
  let := finite_interval ρ B C
  let j : {s : simplexSet (Sublevel (ρ := ρ) h) n // endpoints s = e} →
      (Fin (n+1) → {D : Basis ρ // B ≤ D ∧ D ≤ C}) := fun s i =>
    ⟨(tuple s.val i).val.val,by
      have hb := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.1.val.val) s.property
      have hc := congrArg (fun e : Edge (Sublevel (ρ := ρ) h) => e.val.2.val.val) s.property
      change (tuple s.val (Fin.last n)).val.val = B at hb
      change (tuple s.val 0).val.val = C at hc
      rw [← hb,← hc]
      exact ⟨le_of_cutRefines ρ (tuple_antitone s.val (Fin.le_last i)),
        le_of_cutRefines ρ (tuple_antitone s.val (Fin.zero_le i))⟩⟩
  apply Finite.of_injective j
  intro s t he
  apply Subtype.ext
  apply tuple_injective
  funext i
  apply sublevel_val_injective h
  exact congrArg Subtype.val (congrFun he i)

lemma simplex_finite_orbits (ho : Oligomorphic ρ) (h n : ℕ) :
    Finite (OrbitCoefficients.Orbits (G := localGroup ρ) (simplexSet (Sublevel (ρ := ρ) h) n)) := by
  let := edge_finite_orbits ho h
  exact finite_orbits_of_map endpoints endpoints_smul (simplex_endpoint_fiber_finite h n)
end TwistedBrin.Basis.CutBasis

namespace FiniteFiberStabilizers
universe u v w
variable {G : Type u} [Group G] {X : Type v} {Y : Type w}
  [MulAction G X] [MulAction G Y]
variable (f : X → Y) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)

include heq
lemma stabilizer_le (x : X) : MulAction.stabilizer G x ≤ MulAction.stabilizer G (f x) := by
  intro g hg
  change g • f x = f x
  rw [← heq, show g • x = x from hg]

lemma finiteIndex (x : X) [Finite {z : X // f z = f x}] :
    ((MulAction.stabilizer G x).subgroupOf (MulAction.stabilizer G (f x))).FiniteIndex := by
  classical
  let H := MulAction.stabilizer G (f x)
  let K := MulAction.stabilizer H x
  have hfin : Finite (MulAction.orbit H x) := by
    let j : MulAction.orbit H x → {z : X // f z = f x} := fun z => ⟨z.val,by
      obtain ⟨g,hg⟩ := z.property
      rw [← hg]
      change f (g.val • x) = f x
      rw [heq]
      exact g.property⟩
    exact Finite.of_injective j (fun a b h => Subtype.ext (congrArg (fun z : {z : X // f z = f x} => z.val) h))
  let := hfin
  let : Finite (H ⧸ K) := Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer H x)
  have hK : K = (MulAction.stabilizer G x).subgroupOf H := by
    ext g
    rfl
  rw [← hK]
  exact Subgroup.finiteIndex_iff.mpr Subgroup.index_ne_zero_of_finite
end FiniteFiberStabilizers

namespace TwistedBrin.Basis
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

lemma pair_regular_products (hρ : Function.Injective ρ)
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1)))
    {B C : Basis ρ} (hBC : CutRefines ρ B C) (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (pairStabilizer ρ B C) I) (n+1)) := by
  let F := hBC.some
  let (b : B) : Group.IsFinitelyPresented (pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b))) := hFP _
  have hv := ProductGroupHomology.finitePiProducts
    (fun b : B => pointwiseStabilizer ρ (Pattern.coordinates (F.pattern b)))
    (fun b => hz _) I n
  let e := F.pairKernelEquiv ρ hρ
  have hk := hv.of_iso (RegularProductR.homologyRelabel e I (n+1)).symm
  exact FiniteIndexProducts.up I (n+1) (pairPermutationHom ρ B C).ker hk
end TwistedBrin.Basis

namespace TwistedBrin.Basis.CutBasis
open OrderChainComplex EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

lemma simplex_stabilizer_fg (hρ : Function.Injective ρ)
    (hS : ∀ F : Finset S, Group.FG (pointwiseStabilizer ρ F))
    (h n : ℕ) (s : simplexSet (Sublevel (ρ := ρ) h) n) :
    Group.FG (MulAction.stabilizer (localGroup ρ) s) := by
  let f : simplexSet (Sublevel (ρ := ρ) h) n → Edge (Sublevel (ρ := ρ) h) := endpoints
  let H := MulAction.stabilizer (localGroup ρ) (f s)
  let K := MulAction.stabilizer (localGroup ρ) s
  let := simplex_endpoint_fiber_finite h n (f s)
  let : (K.subgroupOf H).FiniteIndex := FiniteFiberStabilizers.finiteIndex f endpoints_smul s
  let eH := MulEquiv.subgroupCongr (sublevel_edge_stabilizer (ρ := ρ) h (f s))
  let := pair_finitelyGenerated ρ hρ hS (f s).property
  let : Group.FG H := Group.fg_of_surjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  let : Group.FG (K.subgroupOf H) := Subgroup.fg_of_index_ne_zero _
  let e := Subgroup.subgroupOfEquivOfLe (FiniteFiberStabilizers.stabilizer_le (G := localGroup ρ) f endpoints_smul s)
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

lemma simplex_stabilizer_products (hρ : Function.Injective ρ)
    (hFP : ∀ F : Finset S, Group.IsFinitelyPresented (pointwiseStabilizer ρ F))
    (hz : ∀ F : Finset S, ∀ (I : Type) (n : ℕ),
      IsZero (groupHomology (RegularProductR.rep ℤ (pointwiseStabilizer ρ F) I) (n+1)))
    (h n : ℕ) (s : simplexSet (Sublevel (ρ := ρ) h) n) (I : Type) (j : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (MulAction.stabilizer (localGroup ρ) s) I) (j+1)) := by
  let f : simplexSet (Sublevel (ρ := ρ) h) n → Edge (Sublevel (ρ := ρ) h) := endpoints
  let H := MulAction.stabilizer (localGroup ρ) (f s)
  let K := MulAction.stabilizer (localGroup ρ) s
  let := simplex_endpoint_fiber_finite h n (f s)
  let : (K.subgroupOf H).FiniteIndex := FiniteFiberStabilizers.finiteIndex f endpoints_smul s
  let eH := MulEquiv.subgroupCongr (sublevel_edge_stabilizer (ρ := ρ) h (f s))
  have hh : IsZero (groupHomology (RegularProductR.rep ℤ H I) (j+1)) :=
    CategoryTheory.Limits.IsZero.of_iso (pair_regular_products hρ hFP hz (f s).property I j)
      (RegularProductR.homologyRelabel eH I (j+1))
  have hk := FiniteIndexProducts.down I (j+1) (K.subgroupOf H) hh
  let e := Subgroup.subgroupOfEquivOfLe (FiniteFiberStabilizers.stabilizer_le (G := localGroup ρ) f endpoints_smul s)
  exact hk.of_iso (RegularProductR.homologyRelabel e I (j+1)).symm
end TwistedBrin.Basis.CutBasis

end

end OAI
