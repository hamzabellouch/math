import Mathlib
import OAI.GroupTheory.FiniteType.CategoryTheoryShortComplex

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
namespace InducedFree
variable {k G H : Type} [CommRing k] [Group G] [Group H]
variable (φ : G →* H) (α : Type)

def unit (j : α) : Rep.free k G α := Finsupp.single j (.single 1 1)
def seed : Rep.free k G α ⟶ Rep.res φ (Rep.free k H α) :=
  Rep.freeLift k G _ (fun j => unit (k := k) (G := H) α j)
def forward : Rep.ind φ (Rep.free k G α) ⟶ Rep.free k H α :=
  (Rep.indResHomEquiv φ _ _).symm (seed φ α)
def backward : Rep.free k H α ⟶ Rep.ind φ (Rep.free k G α) :=
  Rep.freeLift k H _ (fun j => IndV.mk φ (Rep.free k G α).ρ 1 (unit α j))

lemma forward_mk (h : H) (a : Rep.free k G α) :
    forward φ α (IndV.mk φ (Rep.free k G α).ρ h a) =
      (Rep.free k H α).ρ h⁻¹ (seed φ α a) := by
  simp [forward,Rep.indResHomEquiv]

lemma seed_unit (j : α) : seed (k := k) φ α (unit α j) = unit α j := by
  simp [seed,unit,Rep.freeLift,Representation.freeLift]
lemma backward_unit (j : α) : backward (k := k) φ α (unit α j) =
    IndV.mk φ (Rep.free k G α).ρ 1 (unit α j) := by
  simp [backward,unit,Rep.freeLift,Representation.freeLift]

lemma backward_forward : backward (k := k) φ α ≫ forward φ α = 𝟙 _ := by
  apply Rep.free_ext
  intro j
  change forward φ α (backward φ α (unit α j)) = unit α j
  rw [backward_unit,forward_mk,seed_unit]
  simp

lemma forward_backward : forward (k := k) φ α ≫ backward φ α = 𝟙 _ := by
  apply (Rep.indResHomEquiv φ _ _).injective
  apply Rep.free_ext
  intro j
  change backward φ α (forward φ α (IndV.mk φ (Rep.free k G α).ρ 1 (unit α j))) =
    IndV.mk φ (Rep.free k G α).ρ 1 (unit α j)
  rw [forward_mk,seed_unit]
  simpa only [inv_one,map_one,Module.End.one_apply] using backward_unit (k := k) φ α j

def iso : Rep.ind φ (Rep.free k G α) ≅ Rep.free k H α where
  hom := forward φ α
  inv := backward φ α
  hom_inv_id := forward_backward φ α
  inv_hom_id := backward_forward φ α
end InducedFree

namespace OrbitModule
open scoped MonoidalCategory
variable {k G : Type} [CommRing k] [Group G]
structure Presentation (C : Rep k G) where
  α : Type
  β : Type
  [finiteα : Finite α]
  [finiteβ : Finite β]
  d : Rep.free k G β ⟶ Rep.free k G α
  ε : Rep.free k G α ⟶ C
  w : d ≫ ε = 0
  exact : (ShortComplex.mk d ε w).Exact
  [epi : Epi ε]
attribute [instance] Presentation.finiteα Presentation.finiteβ Presentation.epi

def Presentation.ofIso {C D : Rep k G} (P : Presentation C) (e : C ≅ D) : Presentation D where
  α := P.α
  β := P.β
  d := P.d
  ε := P.ε ≫ e.hom
  w := by rw [← Category.assoc,P.w,zero_comp]
  exact := by
    let E := ShortComplex.mk P.d P.ε P.w
    let F := ShortComplex.mk P.d (P.ε ≫ e.hom) (by rw [← Category.assoc,P.w,zero_comp])
    let iso : E ≅ F := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e
      (by dsimp [E,F]; simp) (by dsimp [E,F]; simp)
    exact (ShortComplex.exact_iff_of_iso iso).mp P.exact

def Presentation.induced {H : Type} [Group H] (φ : G →* H) {C : Rep k G}
    (P : Presentation C) : Presentation (Rep.ind φ C) := by
  let F := Rep.indFunctor k φ
  let e0 := InducedFree.iso (k := k) φ P.α
  let e1 := InducedFree.iso (k := k) φ P.β
  have hS := P.exact.map_of_epi_of_preservesCokernel F P.epi inferInstance
  exact {
    α := P.α
    β := P.β
    d := e1.inv ≫ F.map P.d ≫ e0.hom
    ε := e0.inv ≫ F.map P.ε
    w := by simp only [Category.assoc,Iso.hom_inv_id_assoc,← Functor.map_comp,P.w,Functor.map_zero,comp_zero]
    exact := by
      let E := (ShortComplex.mk P.d P.ε P.w).map F
      let D := ShortComplex.mk (e1.inv ≫ F.map P.d ≫ e0.hom) (e0.inv ≫ F.map P.ε)
        (by simp only [Category.assoc,Iso.hom_inv_id_assoc,← Functor.map_comp,P.w,Functor.map_zero,comp_zero])
      let iso : E ≅ D := ShortComplex.isoMk e1 e0 (Iso.refl _)
        (by change e1.hom ≫ e1.inv ≫ F.map P.d ≫ e0.hom = F.map P.d ≫ e0.hom
            simp only [Iso.hom_inv_id_assoc])
        (by change e0.hom ≫ e0.inv ≫ F.map P.ε = F.map P.ε ≫ 𝟙 _
            simp only [Iso.hom_inv_id_assoc,Category.comp_id])
      exact (ShortComplex.exact_iff_of_iso iso).mp hS }

variable (G) in
def Presentation.ofBeginning (B : ProductFiniteResolution.Beginning (Rep.trivial k G k)) :
    Presentation (Rep.trivial k G k) where
  α := B.α₀
  β := B.α₁
  d := B.d₁
  ε := B.ε
  w := B.d₁_ε
  exact := B.exact₀
end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace ProductCoefficient
variable (G I : Type) [Group G]
def unitEquiv : Module G I PUnit.{1} ≃ₗ[ℤ] RegularProductR.Module ℤ G I :=
  LinearEquiv.piCongrRight (fun _ => Finsupp.domLCongr (Equiv.punitProd G))
lemma unitEquiv_comm (g : G) :
    (unitEquiv G I).toLinearMap.comp ((rep G I PUnit.{1}).ρ g) =
      ((RegularProductR.rep ℤ G I).ρ g).comp (unitEquiv G I).toLinearMap := by
  apply LinearMap.ext
  intro a
  funext i
  have h : (Finsupp.domLCongr (R := ℤ) (M := ℤ) (Equiv.punitProd G)).toLinearMap.comp
      (rightShift G PUnit.{1} g) = (RegularProductR.rightShift ℤ G g).comp
        (Finsupp.domLCongr (Equiv.punitProd G)).toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨c,x⟩ z
    simp
  exact LinearMap.congr_fun h (a i)
def unitIso : rep G I PUnit.{1} ≅ RegularProductR.rep ℤ G I :=
  Rep.mkIso (Representation.Equiv.mk (unitEquiv G I) (unitEquiv_comm G I))
end ProductCoefficient

namespace ListChains
variable (G I C : Type) [groupG : Group G]
def flattenProduct (z : ProductAmbient G I C) : ProductAmbient G (I×C) PUnit.{1} :=
  fun ic => Finsupp.single PUnit.unit (z ic.1 ic.2)
lemma flatten_bounded {z : ProductAmbient G I C} (hz : z ∈ boundedProducts G I C) :
    flattenProduct G I C z ∈ boundedProducts G (I×C) PUnit.{1} := by
  obtain ⟨A,hA,hz⟩ := hz
  exact ⟨A,hA,fun ic => single_mem_cosetModule G _ PUnit.unit (hz ic.1 ic.2)⟩
omit groupG in
lemma flatten_degree [Group G] {n : ℕ} {z : ProductAmbient G I C} (hz : z ∈ degreeProducts G I C n) :
    flattenProduct G I C z ∈ degreeProducts G (I×C) PUnit.{1} n :=
  fun ic => single_mem_cosetModule G _ PUnit.unit (hz ic.1 ic.2)
omit groupG in
lemma flatten_boundary [Group G] (z : ProductAmbient G I C) :
    productBoundary G (I×C) PUnit.{1} (flattenProduct G I C z) =
      flattenProduct G I C (productBoundary G I C z) := by
  funext ic
  exact cosetBoundary_single G _ _

def gatherProduct (T : I → Finset C) (z : ProductAmbient G (I×C) PUnit.{1}) :
    ProductAmbient G I C := fun i => ∑ c ∈ T i, Finsupp.single c (z (i,c) PUnit.unit)
omit groupG in
lemma gather_apply [Group G] [DecidableEq C] (T : I → Finset C) (z : ProductAmbient G (I×C) PUnit.{1}) (i : I) (c : C) :
    gatherProduct G I C T z i c = if c ∈ T i then z (i,c) PUnit.unit else 0 := by
  classical
  simp [gatherProduct,Finsupp.single_apply]
lemma gather_bounded (T : I → Finset C) {z : ProductAmbient G (I×C) PUnit.{1}}
    (hz : z ∈ boundedProducts G (I×C) PUnit.{1}) :
    gatherProduct G I C T z ∈ boundedProducts G I C := by
  classical
  obtain ⟨A,hA,hz⟩ := hz
  refine ⟨A,hA,fun i c => ?_⟩
  rw [gather_apply]
  split_ifs
  · exact hz (i,c) PUnit.unit
  · exact Submodule.zero_mem _
lemma gather_degree (T : I → Finset C) {n : ℕ} {z : ProductAmbient G (I×C) PUnit.{1}}
    (hz : z ∈ degreeProducts G (I×C) PUnit.{1} n) :
    gatherProduct G I C T z ∈ degreeProducts G I C n := by
  classical
  intro i c
  rw [gather_apply]
  split_ifs
  · exact hz (i,c) PUnit.unit
  · exact Submodule.zero_mem _
lemma gather_boundary (T : I → Finset C) (z : ProductAmbient G (I×C) PUnit.{1}) :
    productBoundary G I C (gatherProduct G I C T z) =
      gatherProduct G I C T (productBoundary G (I×C) PUnit.{1} z) := by
  classical
  funext i
  apply Finsupp.ext
  intro c
  simp only [productBoundary_apply,cosetBoundary_apply,gather_apply]
  split_ifs <;> simp
lemma gather_flatten (z : ProductAmbient G I C) :
    gatherProduct G I C (fun i => (z i).support) (flattenProduct G I C z) = z := by
  classical
  funext i
  apply Finsupp.ext
  intro c
  rw [gather_apply]
  split_ifs with h
  · simp [flattenProduct]
  · exact (Finsupp.notMem_support_iff.mp h).symm

lemma bounded_filling_unit (n : ℕ)
    (hz : IsZero (groupHomology (RegularProductR.rep ℤ G (I×C)) (n+1)))
    (z : productCycles G (I×C) PUnit.{1} (n+1)) :
    ∃ w : productChains G (I×C) PUnit.{1} (n+2), productDifferential G (I×C) PUnit.{1} (n+1) w = z := by
  have h0 : IsZero (groupHomology (ProductCoefficient.rep G (I×C) PUnit.{1}) (n+1)) :=
    hz.of_iso ((groupHomology.functor ℤ G (n+1)).mapIso
      (ProductCoefficient.unitIso G (I×C)))
  have hb := h0.of_iso (groupHomologyProductQuotientIso G (I×C) PUnit.{1} n).symm
  have hs : Subsingleton (BoundedProductHomology G (I×C) PUnit.{1} (n+1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hb
  have he : (Submodule.Quotient.mk z : BoundedProductHomology G (I×C) PUnit.{1} (n+1)) = 0 :=
    @Subsingleton.elim _ hs _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp he

theorem productCoefficient_vanishing (n : ℕ)
    (hz : ∀ J : Type, IsZero (groupHomology (RegularProductR.rep ℤ G J) (n+1))) :
    IsZero (groupHomology (ProductCoefficient.rep G I C) (n+1)) := by
  let : Subsingleton (BoundedProductHomology G I C (n+1)) := by
    apply Submodule.Quotient.subsingleton_iff.mpr
    apply top_unique
    intro z _
    let zf : productCycles G (I×C) PUnit.{1} (n+1) := ⟨flattenProduct G I C z.val,
      ⟨flatten_bounded G I C z.property.1.1,flatten_degree G I C z.property.1.2⟩, by
        change productBoundary G (I×C) PUnit.{1} (flattenProduct G I C z.val) = 0
        rw [flatten_boundary,show productBoundary G I C z.val = 0 from z.property.2]
        funext ic
        simp [flattenProduct]⟩
    obtain ⟨w,hw⟩ := bounded_filling_unit G I C n (hz (I×C)) zf
    refine ⟨⟨gatherProduct G I C (fun i => (z.val i).support) w.val,
      gather_bounded G I C _ w.property.1,gather_degree G I C _ w.property.2⟩,?_⟩
    apply Subtype.ext
    change productBoundary G I C (gatherProduct G I C _ w.val) = z.val
    rw [gather_boundary,show productBoundary G (I×C) PUnit.{1} w.val = zf.val from
      congrArg Subtype.val hw]
    exact gather_flatten G I C z.val
  exact (ModuleCat.isZero_of_subsingleton _).of_iso
    (groupHomologyProductQuotientIso G I C n)
end ListChains

end

end OAI
