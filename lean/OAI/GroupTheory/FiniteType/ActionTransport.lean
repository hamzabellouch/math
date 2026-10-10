import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrinBasisMatching

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
namespace ActionTransport
section
open PosetTransport ActionPresentation
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q]
omit [Preorder P] in
lemma exists_liftedFrames [Preorder P] (F : Frames G P) [Finite F.Index]
    (hFP : ∀ i, Group.IsFinitelyPresented (F.stab i))
    (p : Q →* G) (hp : Function.Surjective p) :
    ∃ (S : Set Q) (_ : S.Finite) (hS : S ⊆ p.ker),
      Nonempty (LiftedFrames F (killProjection p S hS)) := by
  classical
  let M (i : F.Index) : LiftModel p (F.stab i).subtype := by
    letI := hFP i
    exact liftModel p hp (F.stab i).subtype
  let S : Set Q := ⋃ i, (M i).obstruction
  have hS : S ⊆ p.ker := by
    intro q hq
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
    exact (M i).obstruction_ker hi
  let q := QuotientGroup.mk' (Subgroup.normalClosure S)
  have hq : ∀ i r, r ∈ (M i).obstruction → q r = 1 := by
    intro i r hr
    apply (QuotientGroup.eq_one_iff r).mpr
    exact Subgroup.subset_normalClosure (Set.mem_iUnion.mpr ⟨i,hr⟩)
  refine ⟨S,Set.finite_iUnion (fun i => (M i).obstruction_finite),hS,?_⟩
  refine ⟨⟨fun i => (M i).hom q (hq i),?_⟩⟩
  intro i h
  exact DFunLike.congr_fun ((M i).hom_commutes q (hq i) (killProjection p S hS) rfl) h
end

section
open PosetTransport ActionPresentation
universe u v w
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable {Q : Type w} [Group Q] [IsMonotoneAction G P]
variable {p : Q →* G} {t : P → G}

def edgeLeftHom (d : Gauge p t) (e : Edge P) : MulAction.stabilizer G e →* Q where
  toFun g := d.value g.val e.val.1
  map_one' := d.one _
  map_mul' g h := by
    have hh := congrArg (fun e : Edge P => e.val.1) h.property
    change h.val • e.val.1 = e.val.1 at hh
    change d.value (g.val * h.val) e.val.1 = _
    rw [d.mul,hh]

def edgeRightHom (d : Gauge p t) (e : Edge P) (L : Q) : MulAction.stabilizer G e →* Q where
  toFun g := L * d.value g.val e.val.2 * L⁻¹
  map_one' := by
    change L * d.value 1 e.val.2 * L⁻¹ = 1
    rw [d.one]
    group
  map_mul' g h := by
    have hh := congrArg (fun e : Edge P => e.val.2) h.property
    change h.val • e.val.2 = e.val.2 at hh
    change L * d.value (g.val * h.val) e.val.2 * L⁻¹ = _
    rw [d.mul,hh]
    group

lemma coherent_of_generators (d : Gauge p t) (e : Edge P) (L : Q)
    (S : Set (MulAction.stabilizer G e)) (hS : Subgroup.closure S = ⊤)
    (hrel : ∀ h ∈ S, d.value h.val e.val.1 * L = L * d.value h.val e.val.2) :
    ∀ h : MulAction.stabilizer G e, d.value h.val e.val.1 * L = L * d.value h.val e.val.2 := by
  have he : edgeLeftHom d e = edgeRightHom d e L := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro h hh
    change d.value h.val e.val.1 = L * d.value h.val e.val.2 * L⁻¹
    rw [← hrel h hh]
    group
  intro h
  have hh := DFunLike.congr_fun he h
  change d.value h.val e.val.1 = L * d.value h.val e.val.2 * L⁻¹ at hh
  rw [hh]
  group

lemma edge_defect_projects (F : Frames G P) (E : Frames G (Edge P))
    (d : Gauge p F.element) (L : E.Index → Q)
    (hL : ∀ i, p (L i) = (F.element (E.rep i).val.1)⁻¹ * F.element (E.rep i).val.2)
    (i : E.Index) (h : E.stab i) :
    p (d.value h.val (E.rep i).val.1 * L i * (d.value h.val (E.rep i).val.2)⁻¹ * (L i)⁻¹) = 1 := by
  have h1 := congrArg (fun e : Edge P => e.val.1) h.property
  have h2 := congrArg (fun e : Edge P => e.val.2) h.property
  change h.val • (E.rep i).val.1 = (E.rep i).val.1 at h1
  change h.val • (E.rep i).val.2 = (E.rep i).val.2 at h2
  simp only [map_mul,map_inv,d.projects,hL,h1,h2]
  group

theorem finite_flat_quotient (F : Frames G P) (E : Frames G (Edge P))
    (T : Frames G (Triangle P)) [Finite F.Index] [Finite E.Index] [Finite T.Index]
    (hEFG : ∀ i, Group.FG (E.stab i)) (p : Q →* G) (hp : Function.Surjective p)
    (d : Gauge p F.element) :
    ∃ (S : Set Q) (_ : S.Finite) (hS : S ⊆ p.ker),
      ∃ c : Cocycle P (Q ⧸ Subgroup.normalClosure S),
        (∀ {x y} (h : x ≤ y), killProjection p S hS (c.edge h) = (F.element x)⁻¹ * F.element y) ∧
        (∀ g {x y} (h : x ≤ y), c.edge (act_mono g h) =
          (d.map (QuotientGroup.mk' _) (killProjection p S hS) rfl).value g x * c.edge h *
          ((d.map (QuotientGroup.mk' _) (killProjection p S hS) rfl).value g y)⁻¹) := by
  classical
  choose L hL using fun i : E.Index => hp ((F.element (E.rep i).val.1)⁻¹ * F.element (E.rep i).val.2)
  choose A hA using fun i => (hEFG i).out
  let c₀ := rawEdge F E d L
  let defect (i : E.Index) (h : E.stab i) :=
    d.value h.val (E.rep i).val.1 * L i * (d.value h.val (E.rep i).val.2)⁻¹ * (L i)⁻¹
  let D₁ : Set Q := ⋃ i, defect i '' (A i : Set (E.stab i))
  let D₂ : Set Q := Set.range (fun i => c₀ (Edge.diag (F.rep i)))
  let D₃ : Set Q := Set.range (fun i => c₀ (T.rep i).e01 * c₀ (T.rep i).e12 * (c₀ (T.rep i).e02)⁻¹)
  let S := D₁ ∪ D₂ ∪ D₃
  have hfin : S.Finite := ((Set.finite_iUnion fun i => (A i).finite_toSet.image (defect i)).union
    (Set.finite_range _)).union (Set.finite_range _)
  have hproj (e : Edge P) : p (c₀ e) = (F.element e.val.1)⁻¹ * F.element e.val.2 :=
    rawEdge_projects F E p d L hL e
  have hS : S ⊆ p.ker := by
    rintro r ((hr | hr) | hr)
    · obtain ⟨i,h,hh,rfl⟩ := Set.mem_iUnion.mp hr
      exact edge_defect_projects F E d L hL i h
    · obtain ⟨i,rfl⟩ := hr
      change p (c₀ (Edge.diag (F.rep i))) = 1
      rw [hproj]
      exact inv_mul_cancel _
    · obtain ⟨i,rfl⟩ := hr
      change p (c₀ (T.rep i).e01 * c₀ (T.rep i).e12 * (c₀ (T.rep i).e02)⁻¹) = 1
      simp only [map_mul,map_inv]
      rw [hproj (T.rep i).e01,hproj (T.rep i).e12,hproj (T.rep i).e02]
      dsimp only [Triangle.e01,Triangle.e12,Triangle.e02]
      group
  let q := QuotientGroup.mk' (Subgroup.normalClosure S)
  let p' := killProjection p S hS
  let d' := d.map q p' rfl
  let c' : Edge P → Q ⧸ Subgroup.normalClosure S := fun e => q (c₀ e)
  have hkill (r : Q) (hr : r ∈ S) : q r = 1 :=
    (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure hr)
  have hcoh : ∀ i k, k ∈ E.stab i →
      d'.value k (E.rep i).val.1 * q (L i) = q (L i) * d'.value k (E.rep i).val.2 := by
    intro i k hk
    apply coherent_of_generators d' (E.rep i) (q (L i)) (A i : Set (E.stab i)) (hA i) ?_ ⟨k,hk⟩
    intro h hh
    have hd := hkill (defect i h) (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i,h,hh,rfl⟩)))
    change q (d.value h.val (E.rep i).val.1 * L i * (d.value h.val (E.rep i).val.2)⁻¹ * (L i)⁻¹) = 1 at hd
    apply mul_inv_eq_one.mp
    simpa only [d',Gauge.map,map_mul,map_inv,mul_inv_rev,mul_assoc] using hd
  have heq (g : G) (e : Edge P) : c' (g • e) = d'.value g e.val.1 * c' e * (d'.value g e.val.2)⁻¹ := by
    have hh := rawEdge_equivariant F E d' (fun i => q (L i)) hcoh g e
    change q (rawEdge F E d L (g • e)) =
      d'.value g e.val.1 * q (rawEdge F E d L e) * (d'.value g e.val.2)⁻¹
    rw [← rawEdge_map F E d L q p' rfl (g • e),← rawEdge_map F E d L q p' rfl e]
    exact hh
  have hdiag (i : F.Index) : c' (Edge.diag (F.rep i)) = 1 :=
    hkill _ (Or.inl (Or.inr ⟨i,rfl⟩))
  have htri (i : T.Index) : c' (T.rep i).e01 * c' (T.rep i).e12 = c' (T.rep i).e02 := by
    apply mul_inv_eq_one.mp
    have hh := hkill _ (Or.inr ⟨i,rfl⟩)
    simpa only [map_mul,map_inv] using hh
  refine ⟨S,hfin,hS,cocycleOfFlat F T d' c' heq hdiag htri,?_,?_⟩
  · intro x y h
    exact hproj ⟨(x,y),h⟩
  · intro g x y h
    exact heq g ⟨(x,y),h⟩
end

section
open PosetTransport ActionPresentation
universe u v
variable {G : Type u} [Group G] {P : Type v} [Preorder P] [MulAction G P]
variable [IsMonotoneAction G P]

theorem finitelyPresented_of_frames [Nonempty P] (hconn : Connected P)
    (hsc : ∀ (R : Type) (_ : Group R) (c : Cocycle P R), c.Trivial)
    (F : Frames G P) (E : Frames G (Edge P)) (T : Frames G (Triangle P))
    [Finite F.Index] [Finite E.Index] [Finite T.Index]
    (hV : ∀ i, Group.IsFinitelyPresented (F.stab i))
    (hE : ∀ i, Group.FG (E.stab i)) : Group.IsFinitelyPresented G := by
  classical
  have hVG (i : F.Index) : (F.stab i).FG := by
    obtain ⟨n,f,hf,_⟩ := (hV i).out
    exact (Group.fg_iff_subgroup_fg _).mp (Group.fg_of_surjective hf)
  let : Group.FG G := fg_of_frames hconn F E hVG
  obtain ⟨α,hα,p₀,hp₀⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp
    (inferInstance : Group.FG G)
  let : Finite α := hα
  obtain ⟨S₁,hs₁,hker₁,⟨J⟩⟩ := exists_liftedFrames F hV p₀ hp₀
  let Q₁ := FreeGroup α ⧸ Subgroup.normalClosure S₁
  let : Group.IsFinitelyPresented Q₁ := kill_finitelyPresented S₁ hs₁
  let p₁ : Q₁ →* G := killProjection p₀ S₁ hker₁
  have hp₁ : Function.Surjective p₁ := killProjection_surj p₀ hp₀ S₁ hker₁
  obtain ⟨S₂,hs₂,hker₂,c,hproj,heq⟩ := finite_flat_quotient F E T hE p₁ hp₁ J.gauge
  let Q₂ := Q₁ ⧸ Subgroup.normalClosure S₂
  let : Group.IsFinitelyPresented Q₂ := kill_finitelyPresented S₂ hs₂
  let p₂ : Q₂ →* G := killProjection p₁ S₂ hker₂
  let d₂ := J.gauge.map (QuotientGroup.mk' (Subgroup.normalClosure S₂)) p₂ rfl
  obtain ⟨s,hs⟩ := section_of_cocycle hconn act_mono p₂ F.element d₂ c
    (hsc Q₂ inferInstance c) hproj heq
  exact finitelyPresented_retract p₂ s hs
end

universe u v w
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
noncomputable def orbitFrames (G : Type u) [Group G] (X : Type v) [MulAction G X] : Frames G X where
  Index := MulAction.orbitRel.Quotient G X
  rep := Quotient.out
  index := Quotient.mk _
  index_rep := Quotient.out_eq
  index_smul _ _ := MulAction.orbitRel.Quotient.quotient_smul_eq
  element x := Classical.choose (show ∃ g : G, g • (Quotient.mk (MulAction.orbitRel G X) x).out = x from
    Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)).symm)
  frame x := Classical.choose_spec (show ∃ g : G, g • (Quotient.mk (MulAction.orbitRel G X) x).out = x from
    Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) x)).symm)

lemma finite_orbits_of_cover (T : Set X) (hT : T.Finite)
    (hcov : ∀ x : X, ∃ g : G, g • x ∈ T) : Finite (MulAction.orbitRel.Quotient G X) := by
  classical
  let : Finite T := hT.to_subtype
  apply Finite.of_surjective (fun x : T => (⟦x.val⟧ : MulAction.orbitRel.Quotient G X))
  intro q
  obtain ⟨g,hg⟩ := hcov q.out
  exact ⟨⟨g • q.out,hg⟩,by simp only [MulAction.orbitRel.Quotient.quotient_smul_eq,Quotient.out_eq]⟩

lemma finite_orbits_of_map {Y : Type w} [MulAction G Y]
    [Finite (MulAction.orbitRel.Quotient G Y)] (f : X → Y)
    (heq : ∀ (g : G) x, f (g • x) = g • f x) (hfin : ∀ y, Finite {x // f x = y}) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  classical
  let F := orbitFrames G Y
  let : Finite F.Index := inferInstanceAs (Finite (MulAction.orbitRel.Quotient G Y))
  let (i : F.Index) : Finite {x // f x = F.rep i} := hfin _
  have hs : Function.Surjective (fun z : Σ i : F.Index, {x // f x = F.rep i} =>
      (⟦z.2.val⟧ : MulAction.orbitRel.Quotient G X)) := by
    intro q
    let x := q.out
    let g := F.element (f x)
    have hf : f (g⁻¹ • x) = F.rep (F.index (f x)) := by
      rw [heq,inv_smul_eq_iff]
      exact (F.frame (f x)).symm
    refine ⟨⟨F.index (f x),⟨g⁻¹ • x,hf⟩⟩,?_⟩
    simp only [MulAction.orbitRel.Quotient.quotient_smul_eq]
    exact Quotient.out_eq q
  exact Finite.of_surjective _ hs
end ActionTransport

end

end OAI
