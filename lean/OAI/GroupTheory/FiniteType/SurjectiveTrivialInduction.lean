import Mathlib
import OAI.GroupTheory.FiniteType.ProductFiniteResolutionBeginningOfComplex

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation
attribute [-instance] AddCommGroup.toIntModule
variable {G H : Type} [Group G] [Group H] (φ : G →* H) (hs : Function.Surjective φ)

include hs in
lemma mk_eq (h : H) (a : ℤ) :
    IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a = IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1 a := by
  obtain ⟨g,rfl⟩ := hs h
  have he := Coinvariants.mk_tmul_inv ((Representation.leftRegular ℤ H).comp φ)
    (Rep.trivial ℤ G ℤ).ρ (MonoidAlgebra.single (1 : H) (1 : ℤ)) a g
  simpa using he.symm

def forward : Rep.ind φ (Rep.trivial ℤ G ℤ) ⟶ Rep.trivial ℤ H ℤ :=
  (Rep.indResHomEquiv φ _ _).symm (Rep.ofHom ⟨LinearMap.id,fun _ => rfl⟩)
lemma forward_mk (h : H) (a : ℤ) :
    forward φ (IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a) = a := by
  simp [forward,Rep.indResHomEquiv]

def backward : Rep.trivial ℤ H ℤ ⟶ Rep.ind φ (Rep.trivial ℤ G ℤ) :=
  Rep.ofHom ⟨IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1, by
    intro h
    apply DFunLike.ext
    intro a
    change IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1 a =
      (Representation.ind φ (Rep.trivial ℤ G ℤ).ρ) h (IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1 a)
    rw [Representation.ind_mk]
    exact (mk_eq φ hs _ _).symm⟩

def iso : Rep.ind φ (Rep.trivial ℤ G ℤ) ≅ Rep.trivial ℤ H ℤ where
  hom := forward φ
  inv := backward φ hs
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply IndV.hom_ext
    intro h
    apply DFunLike.ext
    intro a
    change IndV.mk φ (Rep.trivial ℤ G ℤ).ρ 1
      (forward φ (IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a)) = IndV.mk φ (Rep.trivial ℤ G ℤ).ρ h a
    rw [forward_mk]
    exact (mk_eq φ hs h a).symm
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply DFunLike.ext
    intro a
    exact forward_mk φ 1 a
end SurjectiveTrivialInduction

namespace OrbitModule
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable (G : Type) [Group G]
theorem trivial_presentation_of_fg [Group.FG G] :
    Nonempty (Presentation (Rep.trivial ℤ G ℤ)) := by
  classical
  obtain ⟨α,hα,φ,hφ⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp (inferInstance : Group.FG G)
  let := hα
  obtain ⟨B⟩ := ProductFiniteResolution.beginning_exists (FreeGroup α)
  let P := (Presentation.ofBeginning (FreeGroup α) B).induced φ
  exact ⟨P.ofIso (SurjectiveTrivialInduction.iso φ hφ)⟩
end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule
variable {G H α : Type} [Group G] [Group H]
instance action : MulAction (G × H) (α × G) where
  smul g x := (x.1,g.1*x.2)
  one_smul x := by
    change (x.1,(1:G)*x.2) = x
    exact Prod.ext rfl (one_mul _)
  mul_smul g h x := by
    change (x.1,(g.1*h.1)*x.2) = (x.1,g.1*(h.1*x.2))
    rw [mul_assoc]

lemma action_def (g : G × H) (x : α × G) : g • x = (x.1,g.1*x.2) := rfl

instance [Finite α] : Finite (OrbitCoefficients.Orbits (G := G × H) (α × G)) := by
  apply Finite.of_surjective (fun a : α => (Quotient.mk'' (a,(1:G)) : OrbitCoefficients.Orbits (G := G × H) (α × G)))
  intro x
  obtain ⟨⟨a,g⟩,rfl⟩ := Quotient.exists_rep x
  refine ⟨a,Quotient.sound ?_⟩
  exact ⟨(g⁻¹,(1:H)),by simp [action_def]⟩

def stabilizerEquiv (v : α × G) : MulAction.stabilizer (G × H) v ≃* H where
  toFun g := g.val.2
  invFun h := ⟨(1,h),by change (v.1,1*v.2) = v; simp⟩
  left_inv g := by
    apply Subtype.ext
    have hg := congrArg Prod.snd (MulAction.mem_stabilizer_iff.mp g.property)
    change g.val.1*v.2 = v.2 at hg
    exact Prod.ext (mul_right_cancel (hg.trans (one_mul v.2).symm)).symm rfl
  right_inv h := rfl
  map_mul' _ _ := rfl

variable (G H α) in
def freePermIso : Rep.res (MonoidHom.fst G H) (Rep.free ℤ G α) ≅ OrbitBrown.perm (G × H) (α × G) := by
  classical
  let e : (α →₀ MonoidAlgebra ℤ G) ≃ₗ[ℤ] ((α × G) →₀ ℤ) :=
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ)).trans (Finsupp.curryLinearEquiv ℤ).symm
  apply Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply Finsupp.lhom_ext
  intro a b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp only [Finsupp.single_zero,map_zero]
  | add x y hx hy => simp only [Finsupp.single_add,map_add,hx,hy]
  | single h r =>
    change e ((Rep.free ℤ G α).ρ g.1 (Finsupp.single a (.single h r))) =
      (OrbitBrown.perm (G × H) (α × G)).ρ g (e (Finsupp.single a (.single h r)))
    rw [Representation.free_single_single]
    have hs (h : G) : e (Finsupp.single a (.single h r)) = Finsupp.single (a,h) r := by
      ext x
      simp [e,Finsupp.single_apply]
    rw [hs,hs,OrbitBrown.perm_single]
    rfl

variable (G H) in
lemma free_coordinates [Finite α] [Group.FG H] (I : Type) :
    Function.Bijective (ProductCriterion.coordinates (I := I) (Rep.res (MonoidHom.fst G H) (Rep.free ℤ G α))) := by
  apply OrbitBrown.coordinates_iso (freePermIso G H α).symm
  apply OrbitBrown.coordinates_perm (G × H) (α × G)
  intro v
  let := Group.fg_of_surjective (f := (stabilizerEquiv (H := H) v).symm.toMonoidHom) (stabilizerEquiv (H := H) v).symm.surjective
  exact OrbitModule.trivial_presentation_of_fg _

open scoped MonoidalCategory
variable (G H) in
lemma free_acyclic [Finite α] (I : Type)
    (hz : ∀ (J : Type) (j : ℕ), IsZero (groupHomology (RegularProductR.rep ℤ H J) (j+1))) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (G × H) I ⊗ Rep.res (MonoidHom.fst G H) (Rep.free ℤ G α)) (n+1)) := by
  apply IsZero.of_iso _ ((groupHomology.functor ℤ (G × H) (n+1)).mapIso
    ((tensorLeft (RegularProductR.rep ℤ (G × H) I)).mapIso (freePermIso G H α)))
  apply OrbitBrown.acyclic_perm (G × H) (α × G)
  intro v J j
  exact (hz J j).of_iso (RegularProductR.homologyRelabel (stabilizerEquiv (H := H) v) J (j+1))
end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
variable {G H : Type} [Group G] [Group H]
variable (P : ProjectiveResolution (Rep.trivial ℤ G ℤ))
abbrev R : Rep ℤ G ⥤ Rep ℤ (G × H) := Rep.resFunctor (MonoidHom.fst G H)
def C : ℕ → Rep ℤ (G × H)
  | 0 => Rep.trivial ℤ (G × H) ℤ
  | n+1 => (R (G := G) (H := H)).obj (P.complex.X n)
def d : (n : ℕ) → C (H := H) P (n+1) ⟶ C (H := H) P n
  | 0 => (R (H := H)).map (P.π.f 0)
  | n+1 => (R (H := H)).map (P.complex.d (n+1) n)
lemma w (n : ℕ) : d (H := H) P (n+1) ≫ d P n = 0 := by
  cases n with
  | zero =>
    change (R (G := G) (H := H)).map (P.complex.d 1 0) ≫ (R (G := G) (H := H)).map (P.π.f 0) = 0
    rw [← Functor.map_comp,P.complex_d_comp_π_f_zero,Functor.map_zero]
  | succ n =>
    change (R (H := H)).map _ ≫ (R (H := H)).map _ = 0
    rw [← Functor.map_comp,P.complex.d_comp_d,Functor.map_zero]
instance : Epi (d (H := H) P 0) :=
  (Rep.epi_iff_surjective _).mpr ((Rep.epi_iff_surjective (P.π.f 0)).mp inferInstance)
lemma exact (n : ℕ) : (ShortComplex.mk (d (H := H) P (n+1)) (d P n) (w P n)).Exact := by
  cases n with
  | zero => exact P.exact₀.map (R (H := H))
  | succ n => exact (P.exact_succ n).map (R (H := H))

theorem products [Group.FG G] [Group.FG H]
    (hf : ∀ n, ∃ α : Type, Finite α ∧ Nonempty (P.complex.X n ≅ Rep.free ℤ G α))
    (hz : ∀ (J : Type) (j : ℕ), IsZero (groupHomology (RegularProductR.rep ℤ H J) (j+1)))
    (I : Type) (n : ℕ) :
    IsZero (groupHomology (RegularProductR.rep ℤ (G × H) I) (n+1)) := by
  apply ProductBrown.regularProductsOfComplex (C (H := H) P) (d P) (w P) (Iso.refl _) n
  · intro i hi
    exact exact P i
  · intro i hi hlo
    cases i with
    | zero =>
      obtain ⟨Q⟩ := OrbitModule.trivial_presentation_of_fg (G × H)
      exact @ProductCriterion.coordinates_of_presentation ℤ (G × H) I _ _ _ Q.α Q.β
        Q.finiteα Q.finiteβ Q.d Q.ε Q.epi Q.w Q.exact
    | succ i =>
      obtain ⟨α,hα,⟨e⟩⟩ := hf i
      let := hα
      apply OrbitBrown.coordinates_iso ((R (H := H)).mapIso e).symm
      exact free_coordinates G H I
  · intro i hi j
    obtain ⟨α,hα,⟨e⟩⟩ := hf i
    let := hα
    apply IsZero.of_iso _ ((groupHomology.functor ℤ (G × H) (j+1)).mapIso
      ((tensorLeft (RegularProductR.rep ℤ (G × H) I)).mapIso ((R (H := H)).mapIso e)))
    exact free_acyclic G H I hz j
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

namespace ActionPresentation
section
universe u v w
variable {Q : Type u} {G : Type v} [Group Q] [Group G]

lemma ker_retraction_fg [Group.FG Q] (p : Q →* G) (s : G →* Q)
    (hs : p.comp s = MonoidHom.id G) : p.ker.IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  let D : Set Q := (fun q => q * (s (p q))⁻¹) '' S
  let N := Subgroup.normalClosure D
  have hN : N ≤ p.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨q,hq,rfl⟩
    have hsq : p (s (p q)) = p q := DFunLike.congr_fun hs _
    simp [MonoidHom.mem_ker,hsq]
  refine ⟨D,hfin.image _, le_antisymm ?_ ?_⟩
  · exact hN
  · let f := QuotientGroup.mk' N
    have hf : ∀ q ∈ S, f q = f (s (p q)) := by
      intro q hq
      have hd : q * (s (p q))⁻¹ ∈ N := Subgroup.subset_normalClosure ⟨q,hq,rfl⟩
      exact mul_inv_eq_one.mp (by simpa [f] using (QuotientGroup.eq_one_iff _).mpr hd)
    have he : f = f.comp (s.comp p) := by
      apply MonoidHom.ext
      intro q
      have hq : q ∈ Subgroup.closure S := by rw [hS]; trivial
      induction hq using Subgroup.closure_induction with
      | mem q hq => exact hf q hq
      | one => simp
      | mul a b ha hb ia ib => simpa using congrArg₂ (· * ·) ia ib
      | inv a ha ia => simpa using congrArg Inv.inv ia
    intro q hq
    apply (QuotientGroup.eq_one_iff q).mp
    have hp : p q = 1 := hq
    simpa [f,hp] using DFunLike.congr_fun he q

lemma finitelyPresented_retract [Group.IsFinitelyPresented Q]
    (p : Q →* G) (s : G →* Q) (hs : p.comp s = MonoidHom.id G) :
    Group.IsFinitelyPresented G := by
  obtain ⟨n,f,hf,hker⟩ := (inferInstance : Group.IsFinitelyPresented Q).out
  let : Group.FG Q := Group.fg_of_surjective hf
  exact Group.IsFinitelyPresented.of_surjective p
    (fun g => ⟨s g,DFunLike.congr_fun hs g⟩) (ker_retraction_fg p s hs)

variable {F : Type*} {H : Type*} {R : Type*} [Group F] [Group H] [Group R]

noncomputable def descend (f : F →* H) (hf : Function.Surjective f)
    (g : F →* R) (hg : f.ker ≤ g.ker) : H →* R :=
  (QuotientGroup.lift f.ker g hg).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom

lemma descend_comp (f : F →* H) (hf : Function.Surjective f)
    (g : F →* R) (hg : f.ker ≤ g.ker) : (descend f hf g hg).comp f = g := by
  ext x
  have he : (QuotientGroup.quotientKerEquivOfSurjective f hf) (QuotientGroup.mk x) = f x := rfl
  have hi := congrArg (QuotientGroup.quotientKerEquivOfSurjective f hf).symm he
  simp only [MulEquiv.symm_apply_apply] at hi
  change (QuotientGroup.lift f.ker g hg)
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x)) = g x
  rw [← hi]
  rfl

structure LiftModel (p : Q →* G) (f : H →* G) where
  n : ℕ
  present : FreeGroup (Fin n) →* H
  surjective : Function.Surjective present
  lift : FreeGroup (Fin n) →* Q
  commutes : p.comp lift = f.comp present
  rels : Set (FreeGroup (Fin n))
  finite : rels.Finite
  kernel : Subgroup.normalClosure rels = present.ker

noncomputable def liftModel [Group.IsFinitelyPresented H] (p : Q →* G)
    (hp : Function.Surjective p) (f : H →* G) : LiftModel p f := Classical.choice (by
  classical
  obtain ⟨n,a,ha,T,hT,he⟩ := (inferInstance : Group.IsFinitelyPresented H).out
  choose b hb using fun i : Fin n => hp (f (a (FreeGroup.of i)))
  refine ⟨⟨n,a,ha,FreeGroup.lift b,?_,T,hT,he⟩⟩
  ext i
  simpa using hb i)

namespace LiftModel
variable {p : Q →* G} {f : H →* G} (M : LiftModel p f)
def obstruction : Set Q := M.lift '' M.rels
lemma obstruction_finite : M.obstruction.Finite := M.finite.image _
lemma obstruction_ker : M.obstruction ⊆ p.ker := by
  rintro q ⟨r,hr,rfl⟩
  have hk : M.present r = 1 := by
    apply (MonoidHom.mem_ker).mp
    rw [← M.kernel]
    exact Subgroup.subset_normalClosure hr
  change p (M.lift r) = 1
  simpa [hk] using DFunLike.congr_fun M.commutes r
lemma ker_le (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1) :
    M.present.ker ≤ (q.comp M.lift).ker := by
  rw [← M.kernel]
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact hq _ ⟨r,hr,rfl⟩
noncomputable def hom (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1) : H →* R :=
  descend M.present M.surjective (q.comp M.lift) (M.ker_le q hq)
lemma hom_comp (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1) :
    (M.hom q hq).comp M.present = q.comp M.lift := descend_comp _ _ _ _
lemma hom_commutes (q : Q →* R) (hq : ∀ r ∈ M.obstruction, q r = 1)
    (p' : R →* G) (hp' : p'.comp q = p) : p'.comp (M.hom q hq) = f := by
  ext h
  obtain ⟨r,rfl⟩ := M.surjective h
  change p' (M.hom q hq (M.present r)) = f (M.present r)
  have hh := DFunLike.congr_fun (M.hom_comp q hq) r
  change M.hom q hq (M.present r) = q (M.lift r) at hh
  rw [hh]
  exact (DFunLike.congr_fun hp' (M.lift r)).trans (DFunLike.congr_fun M.commutes r)
end LiftModel

def killProjection (p : Q →* G) (S : Set Q) (hS : S ⊆ p.ker) :
    Q ⧸ Subgroup.normalClosure S →* G :=
  QuotientGroup.lift _ p (Subgroup.normalClosure_le_normal hS)
lemma killProjection_comp (p : Q →* G) (S : Set Q) (hS : S ⊆ p.ker) :
    (killProjection p S hS).comp (QuotientGroup.mk' _) = p := rfl
lemma killProjection_surj (p : Q →* G) (hp : Function.Surjective p)
    (S : Set Q) (hS : S ⊆ p.ker) : Function.Surjective (killProjection p S hS) := by
  intro g
  obtain ⟨q,rfl⟩ := hp g
  exact ⟨QuotientGroup.mk q,rfl⟩
lemma kill_finitelyPresented [Group.IsFinitelyPresented Q] (S : Set Q) (hS : S.Finite) :
    Group.IsFinitelyPresented (Q ⧸ Subgroup.normalClosure S) :=
  Group.IsFinitelyPresented.quotient (Subgroup.normalClosure S) ⟨S,hS,rfl⟩

end

universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
lemma fg_of_fp [Group.IsFinitelyPresented G] : Group.FG G := by
  obtain ⟨n,f,hf,_⟩ := (inferInstance : Group.IsFinitelyPresented G).out
  exact Group.fg_of_surjective hf

lemma commute_of_generators {Q : Type w} [Group Q] (f : G →* Q) (g : H →* Q)
    (S : Set G) (T : Set H) (hS : Subgroup.closure S = ⊤) (hT : Subgroup.closure T = ⊤)
    (h : ∀ x ∈ S, ∀ y ∈ T, Commute (f x) (g y)) : ∀ x y, Commute (f x) (g y) := by
  intro x
  have hx : x ∈ Subgroup.closure S := by rw [hS]; trivial
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    intro y
    have hy : y ∈ Subgroup.closure T := by rw [hT]; trivial
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => simp
    | mul y z hy hz iy iz => simpa only [map_mul] using iy.mul_right iz
    | inv y hy iy => simpa only [map_inv] using iy.inv_right
  | one => intro y; simp
  | mul x z hx hz ix iz => intro y; simpa only [map_mul] using (ix y).mul_left (iz y)
  | inv x hx ix => intro y; simpa only [map_inv] using (ix y).inv_left

lemma product_finitelyPresented [Group.IsFinitelyPresented G] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (G × H) := by
  classical
  let : Group.FG G := fg_of_fp
  let : Group.FG H := fg_of_fp
  obtain ⟨S,hS,hs⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  obtain ⟨T,hT,ht⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let P := Monoid.Coprod G H
  let i : G →* P := Monoid.Coprod.inl
  let j : H →* P := Monoid.Coprod.inr
  let p : P →* G × H := Monoid.Coprod.lift (MonoidHom.inl G H) (MonoidHom.inr G H)
  have pi (g : G) : p (i g) = (g,1) := rfl
  have pj (h : H) : p (j h) = (1,h) := rfl
  let R : Set P := (fun z : G × H => i z.1 * j z.2 * (j z.2 * i z.1)⁻¹) '' (S ×ˢ T)
  have hR : R.Finite := (hs.prod ht).image _
  have hk : R ⊆ p.ker := by
    rintro _ ⟨⟨g,h⟩,⟨hg,hh⟩,rfl⟩
    change p (i g * j h * (j h * i g)⁻¹) = 1
    rw [map_mul,map_mul,map_inv,map_mul,pi,pj]
    ext <;> simp
  let Q := P ⧸ Subgroup.normalClosure R
  let q : P →* Q := QuotientGroup.mk' _
  let a := q.comp i
  let b := q.comp j
  have hc : ∀ g h, Commute (a g) (b h) := by
    apply commute_of_generators a b S T hS hT
    intro g hg h hh
    have hr : i g * j h * (j h * i g)⁻¹ ∈ Subgroup.normalClosure R :=
      Subgroup.subset_normalClosure ⟨(g,h),⟨hg,hh⟩,rfl⟩
    have he := (QuotientGroup.eq_one_iff (N := Subgroup.normalClosure R) _).mpr hr
    change a g * b h = b h * a g
    change q (i g * j h * (j h * i g)⁻¹) = 1 at he
    rw [map_mul,map_mul,map_inv,map_mul] at he
    exact mul_inv_eq_one.mp he
  let s : G × H →* Q := a.noncommCoprod b hc
  let π := killProjection p R hk
  have hsec : π.comp s = MonoidHom.id (G × H) := by
    apply MonoidHom.ext
    intro z
    change p (i z.1 * j z.2) = z
    rw [map_mul,pi,pj]
    exact Prod.ext (mul_one _) (one_mul _)
  let : Group.IsFinitelyPresented Q := kill_finitelyPresented R hR
  exact finitelyPresented_retract π s hsec

lemma finite_pi_finitelyPresented {I : Type u} [Finite I] (K : I → Type v)
    [∀ i, Group (K i)] [∀ i, Group.IsFinitelyPresented (K i)] :
    Group.IsFinitelyPresented (∀ i, K i) := by
  classical
  let := Fintype.ofFinite I
  suffices h : ∀ n (K : Fin n → Type v) [∀ i, Group (K i)]
      [∀ i, Group.IsFinitelyPresented (K i)], Group.IsFinitelyPresented (∀ i, K i) by
    let e := Fintype.equivFin I
    let e' : (∀ i, K i) ≃* (∀ i, K (e.symm i)) :=
      { (Equiv.piCongrLeft K e.symm).symm with map_mul' := fun _ _ => rfl }
    let := h (Fintype.card I) (fun i => K (e.symm i))
    exact Group.IsFinitelyPresented.equiv e'.symm
  intro n
  induction n with
  | zero => intro K _ _; infer_instance
  | succ n ih =>
    intro K _ _
    let e : (∀ i, K i) ≃* K 0 × (∀ i : Fin n, K i.succ) :=
      { toFun f := (f 0,fun i => f i.succ)
        invFun p := Fin.cases p.1 p.2
        left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
        right_inv p := rfl
        map_mul' _ _ := rfl }
    let := ih (fun i => K i.succ)
    let := product_finitelyPresented (G := K 0) (H := ∀ i : Fin n, K i.succ)
    exact Group.IsFinitelyPresented.equiv e.symm
end ActionPresentation

end

end OAI
