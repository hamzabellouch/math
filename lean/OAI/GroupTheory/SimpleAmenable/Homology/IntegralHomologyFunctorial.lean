import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.IntegralTransgressionFinite

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntegralHomologyFunctorial
open Classical CategoryTheory Finsupp groupHomology
namespace IntegralHomology
variable {E F G : Type} [Group E] [Group F] [Group G]

lemma chainsMap2_eq (f : E →* F) :
    (chainsMap₂ f (coefficientMap f)).hom=mapC2 f := by
  apply Finsupp.lhom_ext
  intro xy n
  simp [chainsMap₂,coefficientMap,mapC2]

lemma cyclesMap2_val (f : E →* F) (x : cycles₂ (coefficients E)) :
    (mapCycles₂ f (coefficientMap f) x).val=mapC2 f x.val := by
  rw [coe_mapCycles₂]
  exact LinearMap.congr_fun (chainsMap2_eq f) x.val

theorem mapH2_inner (c : E) : mapH2 (MulAut.conj c).toMonoidHom=LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using H2_induction_on with
  | h x =>
    change groupHomology.map (MulAut.conj c).toMonoidHom _ 2 (H2π (coefficients E) x)=
      H2π (coefficients E) x
    rw [H2π_comp_map_apply]
    apply (H2π_eq_iff _ _).mpr
    change ∃y, d₃₂ (coefficients E) y=
      (mapCycles₂ (MulAut.conj c).toMonoidHom (coefficientMap _) x).val-x.val
    rw [cyclesMap2_val]
    refine ⟨-prism2 c x.val,?_⟩
    have ht := LinearMap.congr_fun (prism_identity c) x.val
    change d₃₂ (coefficients E) (prism2 c x.val) + prism1 c (d₂₁ (coefficients E) x.val) =
      x.val-mapC2 (MulAut.conj c).toMonoidHom x.val at ht
    have hx : d₂₁ (coefficients E) x.val=0 := x.property
    rw [hx,map_zero,add_zero] at ht
    rw [map_neg,ht]
    abel

@[simp] theorem mapH2_id : mapH2 (MonoidHom.id E)=LinearMap.id := by
  have he : coefficientMap (MonoidHom.id E)=𝟙 (coefficients E) := rfl
  unfold mapH2
  rw [he,groupHomology.map_id]
  rfl

theorem mapH2_comp (f : E →* F) (g : F →* G) :
    mapH2 (g.comp f)=(mapH2 g).comp (mapH2 f) := by
  have he : coefficientMap (g.comp f)=coefficientMap f ≫ (Rep.resFunctor f).map (coefficientMap g) := by
    apply Rep.hom_ext
    ext
    rfl
  unfold mapH2
  rw [he,groupHomology.map_comp]
  rfl

theorem mapH2_conjugate (c : F) (f : E →* F) :
    mapH2 ((MulAut.conj c).toMonoidHom.comp f)=mapH2 f := by
  rw [mapH2_comp,mapH2_inner,LinearMap.id_comp]

end IntegralHomology
end IntegralHomologyFunctorial

section ConfigurationChains
open Classical Finsupp
namespace ConfigurationChains
variable {V : Type*}
abbrev Chain (V : Type*) := List V →₀ ℤ

noncomputable def cone (v : V) : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.lmapDomain ℤ ℤ (List.cons v)

@[simp] theorem cone_single (v : V) (l : List V) (n : ℤ) :
    cone v (single l n)=single (v::l) n := by
  simp [cone]

noncomputable def faceSum : List V → Chain V
  | [] => 0
  | v::l => single l 1-cone v (faceSum l)

noncomputable def boundary : Chain V →ₗ[ℤ] Chain V :=
  Finsupp.linearCombination ℤ faceSum

@[simp] theorem boundary_single (l : List V) (n : ℤ) :
    boundary (single l n)=n • faceSum l := by
  simp [boundary]

theorem boundary_cone (v : V) (c : Chain V) :
    boundary (cone v c)=c-cone v (boundary c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih =>
    simp only [map_add,cone_single,boundary_single,faceSum,smul_sub,map_smul,ih]
    rw [Finsupp.smul_single,smul_eq_mul,mul_one]
    abel

@[simp] theorem boundary_faceSum (l : List V) : boundary (faceSum l)=0 := by
  induction l with
  | nil => simp [faceSum]
  | cons v l ih => simp [faceSum,boundary_cone,ih]

@[simp] theorem boundary_boundary (c : Chain V) : boundary (boundary c)=0 := by
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l n c hl hn ih => simp [ih]

noncomputable def vertices (c : Chain V) : Finset V := c.support.biUnion List.toFinset

@[simp] theorem vertices_zero : vertices (0 : Chain V)=∅ := by simp [vertices]

theorem mem_vertices {c : Chain V} {v : V} : v∈vertices c ↔ ∃l∈c.support,v∈l := by
  simp [vertices]

theorem vertices_single_subset (l : List V) (n : ℤ) :
    vertices (single l n)⊆l.toFinset := by
  intro v hv
  obtain ⟨s,hs,hv⟩ := mem_vertices.mp hv
  have he : s=l := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  simpa [he] using hv

theorem vertices_add_subset (c d : Chain V) : vertices (c+d)⊆vertices c∪vertices d := by
  intro v hv
  obtain ⟨l,hl,hv⟩ := mem_vertices.mp hv
  rcases Finset.mem_union.mp (Finsupp.support_add hl) with hl|hl
  · exact Finset.mem_union.mpr (Or.inl (mem_vertices.mpr ⟨l,hl,hv⟩))
  · exact Finset.mem_union.mpr (Or.inr (mem_vertices.mpr ⟨l,hl,hv⟩))

@[simp] theorem vertices_neg (c : Chain V) : vertices (-c)=vertices c := by
  simp [vertices]

theorem vertices_sub_subset (c d : Chain V) : vertices (c-d)⊆vertices c∪vertices d := by
  simpa [sub_eq_add_neg] using vertices_add_subset c (-d)

theorem cone_support_subset (v : V) (c : Chain V) :
    (cone v c).support⊆c.support.image (List.cons v) := by
  exact Finsupp.mapDomain_support

theorem vertices_cone_subset (v : V) (c : Chain V) :
    vertices (cone v c)⊆insert v (vertices c) := by
  intro x hx
  obtain ⟨l,hl,hx⟩ := mem_vertices.mp hx
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (cone_support_subset v c hl)
  rcases List.mem_cons.mp hx with rfl|hx
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (mem_vertices.mpr ⟨s,hs,hx⟩)

theorem faceSum_support {l s : List V} (hs : s∈(faceSum l).support) :
    s.Sublist l ∧ s.length+1=l.length := by
  induction l generalizing s with
  | nil => simp [faceSum] at hs
  | cons v l ih =>
    have hu := Finsupp.support_sub hs
    rcases Finset.mem_union.mp hu with hs|hs
    · have he : s=l := Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
      subst s
      exact ⟨List.sublist_cons_self _ _,by simp⟩
    · obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (cone_support_subset v _ hs)
      obtain ⟨hts,htl⟩ := ih ht
      exact ⟨hts.cons_cons _,by simp; omega⟩

theorem faceSum_support_card (l : List V) : (faceSum l).support.card≤l.length := by
  induction l with
  | nil => simp [faceSum]
  | cons v l ih =>
    calc
      (faceSum (v::l)).support.card ≤
          ((single l (1:ℤ)).support∪(cone v (faceSum l)).support).card :=
        Finset.card_le_card Finsupp.support_sub
      _ ≤ (single l (1:ℤ)).support.card+(cone v (faceSum l)).support.card := Finset.card_union_le _ _
      _ ≤ 1+(faceSum l).support.card := by
        have hc := Finset.card_le_card (cone_support_subset v (faceSum l))
        have hi := Finset.card_image_le (s:=(faceSum l).support) (f:=List.cons v)
        simp only [Finsupp.support_single _ (by decide : (1:ℤ)≠0),Finset.card_singleton]
        omega
      _ ≤ (v::l).length := by simp; omega

end ConfigurationChains
end ConfigurationChains

end SimpleAmenable
end
end

end OAI
