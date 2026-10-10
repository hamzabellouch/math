import Mathlib
import OAI.GroupTheory.PeriodicGroups.Presentation.SmallFaithful

namespace OAI

section
namespace SourceBurnside.Stability.SteinbergAction
noncomputable section
open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R]

def scaleHom (u : Fin n → Rˣ) : Steinberg n R →* Steinberg n R :=
  Steinberg.lift (fun p a => x p ((u p.row).val*a*(u p.col).inv))
    (by intro p a b; simp only [mul_add,add_mul,x_add])
    (by intro p q h₁ h₂ a b; exact x_commute p q h₁ h₂ _ _)
    (by
      intro i j k hij hjk hik a b
      rw [x_mul i j k hij hjk hik]
      congr 1
      calc (u i).val*a*(u j).inv*((u j).val*b*(u k).inv) =
          (u i).val*a*((u j).inv*(u j).val)*b*(u k).inv := by noncomm_ring
           _ = (u i).val*(a*b)*(u k).inv := by rw [(u j).inv_val]; noncomm_ring)

@[simp] lemma scaleHom_x (u : Fin n → Rˣ) (p : Root n) (a : R) :
    scaleHom u (x p a) = x p ((u p.row).val*a*(u p.col).inv) :=
  Steinberg.lift_x _ _ _ _ _ _

lemma scaleHom_one : scaleHom (fun _ : Fin n => (1 : Rˣ)) = MonoidHom.id _ := by
  apply Steinberg.hom_ext
  intro p a
  simp

lemma scaleHom_mul (u v : Fin n → Rˣ) :
    scaleHom (fun i => u i*v i) = (scaleHom u).comp (scaleHom v) := by
  apply Steinberg.hom_ext
  intro p a
  simp only [MonoidHom.comp_apply,scaleHom_x,Units.val_mul]
  congr 1
  noncomm_ring

def scale (u : Fin n → Rˣ) : MulAut (Steinberg n R) where
  toFun := scaleHom u
  invFun := scaleHom (fun i => (u i)⁻¹)
  left_inv g := by
    have hh := DFunLike.congr_fun (scaleHom_mul (fun i => (u i)⁻¹) u) g
    simpa only [inv_mul_cancel,scaleHom_one,MonoidHom.id_apply,MonoidHom.comp_apply] using hh.symm
  right_inv g := by
    have hh := DFunLike.congr_fun (scaleHom_mul u (fun i => (u i)⁻¹)) g
    simpa only [mul_inv_cancel,scaleHom_one,MonoidHom.id_apply,MonoidHom.comp_apply] using hh.symm
  map_mul' := (scaleHom u).map_mul

@[simp] lemma scale_apply (u : Fin n → Rˣ) (g : Steinberg n R) : scale u g = scaleHom u g := rfl
@[simp] lemma scale_x (u : Fin n → Rˣ) (p : Root n) (a : R) :
    scale u (x p a) = x p ((u p.row).val*a*(u p.col).inv) := scaleHom_x u p a

lemma scale_inv (u : Fin n → Rˣ) : (scale u)⁻¹ = scale (fun i => (u i)⁻¹) := by
  ext g
  rfl

lemma elementary_eq_e (p : Root n) (a : R) : elementary p.row p.col p.ne a = Elementary.e p a := by
  apply Units.ext
  rfl

lemma diagonal_conjugate_e (u : Fin n → Rˣ) (p : Root n) (a : R) :
    diagonal u * Elementary.e p a * (diagonal u)⁻¹ =
      Elementary.e p ((u p.row).val*a*(u p.col).inv) := by
  apply Units.ext
  change Matrix.diagonal (fun i => (u i).val) * (1+Matrix.single p.row p.col a) *
    Matrix.diagonal (fun i => (u i).inv) = 1+Matrix.single p.row p.col _
  rw [mul_add,add_mul,Matrix.mul_one,Matrix.diagonal_mul_diagonal]
  have hd : Matrix.diagonal (fun i => (u i).val*(u i).inv) = (1 : Matrix (Fin n) (Fin n) R) := by
    simp
  rw [hd]
  congr 1
  ext i j
  simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.single_apply]
  split_ifs with h
  · rw [h.1,h.2]
  · simp

lemma representation_scale (u : Fin n → Rˣ) (g : Steinberg n R) :
    Elementary.representation (scale u g) = diagonal u * Elementary.representation g * (diagonal u)⁻¹ := by
  have hh : Elementary.representation.comp (scale u).toMonoidHom =
      (MulAut.conj (diagonal u)).toMonoidHom.comp Elementary.representation := by
    apply Steinberg.hom_ext
    intro p a
    simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
      scale_x,Elementary.representation_x]
    exact (diagonal_conjugate_e u p a).symm
  exact DFunLike.congr_fun hh g

end
end SourceBurnside.Stability.SteinbergAction

end
section
namespace SourceBurnside.Stability.SteinbergAction
noncomputable section
open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R]

abbrev GLGenerator := SmallPresentation.Generator (Fin n) R

def generatorAction : GLGenerator (n := n) (R := R) → MulAut (Steinberg n R)
  | .root i j h a => MulAut.conj (x ⟨i,j,h⟩ a)
  | .diag i u => scale (fun j => if j=i then u else 1)

def wordAction : FreeGroup (GLGenerator (n := n) (R := R)) →* MulAut (Steinberg n R) :=
  FreeGroup.lift generatorAction

@[simp] lemma wordAction_of (s : GLGenerator (n := n) (R := R)) :
    wordAction (FreeGroup.of s) = generatorAction s := FreeGroup.lift_apply_of

lemma generator_equivariant (s : GLGenerator (n := n) (R := R)) (g : Steinberg n R) :
    Elementary.representation (generatorAction s g) = s.matrix * Elementary.representation g * s.matrix⁻¹ := by
  cases s with
  | root i j h a =>
    change Elementary.representation (x ⟨i,j,h⟩ a * g * (x ⟨i,j,h⟩ a)⁻¹) = _
    simp only [map_mul,map_inv,Elementary.representation_x,SmallPresentation.Generator.matrix]
    rfl
  | diag i u => exact representation_scale (fun j => if j=i then u else 1) g

lemma word_equivariant (w : FreeGroup (GLGenerator (n := n) (R := R))) (g : Steinberg n R) :
    Elementary.representation (wordAction w g) =
      SmallPresentation.matrixWord w * Elementary.representation g * (SmallPresentation.matrixWord w)⁻¹ := by
  induction w using FreeGroup.induction_on generalizing g with
  | one => simp
  | of s =>
    simp only [wordAction_of,SmallPresentation.matrixWord,FreeGroup.lift_apply_of]
    exact generator_equivariant s g
  | inv_of s ih =>
    rw [map_inv,map_inv,inv_inv]
    have hh := ih ((wordAction (FreeGroup.of s))⁻¹ g)
    have hh' := congrArg (fun h => (SmallPresentation.matrixWord (FreeGroup.of s))⁻¹ * h *
      SmallPresentation.matrixWord (FreeGroup.of s)) hh
    simpa only [MulAut.apply_inv_self,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,
      inv_mul_cancel,mul_one] using hh'.symm
  | mul w z hw hz =>
    rw [map_mul,map_mul,mul_inv_rev]
    change Elementary.representation (wordAction w (wordAction z g)) = _
    rw [hw,hz]
    group

end
end SourceBurnside.Stability.SteinbergAction

end
section
namespace SourceBurnside.Stability.MatrixK1
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def E : Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure {g | ∃i j h a, g = elementary i j h a}

lemma elementary_mem (i j : ι) (h : i≠j) (a : R) : elementary i j h a ∈ E :=
  Subgroup.subset_closure ⟨i,j,h,a,rfl⟩

lemma evaluate_elementary : SmallPresentation.elementaryGroup.map
    (SmallPresentation.evaluate (ι := ι) (R := R)) = E := by
  rw [SmallPresentation.elementaryGroup,MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x,⟨i,j,h,a,rfl⟩,rfl⟩
    exact ⟨i,j,h,a,SmallPresentation.evaluate_root _ _ _ _⟩
  · rintro ⟨i,j,h,a,rfl⟩
    exact ⟨SmallPresentation.root i j h a,⟨i,j,h,a,rfl⟩,
      SmallPresentation.evaluate_root _ _ _ _⟩

variable [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include ε hI

lemma normal : (E (ι := ι) (R := R)).Normal := by
  rw [←evaluate_elementary]
  exact Subgroup.Normal.map inferInstance _ (SmallPresentation.evaluate_surjective ε hI)

lemma evaluate_mem_iff (g : SmallPresentation.Group (ι := ι) (R := R)) :
    SmallPresentation.evaluate g ∈ E ↔ g ∈ SmallPresentation.elementaryGroup := by
  rw [←evaluate_elementary]
  constructor
  · rintro ⟨x,hx,he⟩
    exact SmallPresentation.evaluate_injective ε hI ι he ▸ hx
  · intro hg; exact ⟨g,hg,rfl⟩

variable [Fintype κ] [DecidableEq κ]

omit [Algebra (ZMod 2) R] ε hI in
lemma embed_mem (e : ι ↪ κ) {g : (Matrix ι ι R)ˣ} (hg : g∈E) : embed e g ∈ E := by
  have he : E (R := R) ≤ (E (R := R)).comap (embed e) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i,j,h,a,rfl⟩
    change embed e (elementary i j h a) ∈ E
    rw [embed_elementary]
    exact elementary_mem _ _ _ _
  exact he hg

lemma embed_mem_iff (e : ι ↪ κ) (hι : 5≤Fintype.card ι) (g : (Matrix ι ι R)ˣ) :
    embed e g ∈ E ↔ g∈E := by
  obtain ⟨x,rfl⟩ := SmallPresentation.evaluate_surjective ε hI g
  rw [←SmallPresentation.evaluate_inclusion_apply,evaluate_mem_iff ε hI,evaluate_mem_iff ε hI]
  constructor
  · intro hx
    have hh : SmallPresentation.K1map e (SmallPresentation.toK1 x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    have hinj := (SmallPresentation.K1equivalence (R := R) e hι).injective
    have hq : SmallPresentation.toK1 x = 1 := hinj (hh.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff _).mp hq
  · intro hx
    exact SmallPresentation.elementary_inclusion (R := R) e hx

lemma coset_representative (e : ι ↪ κ) (hι : 5≤Fintype.card ι) (g : (Matrix κ κ R)ˣ) :
    ∃h : (Matrix ι ι R)ˣ, g * embed e h ∈ E := by
  obtain ⟨x,rfl⟩ := SmallPresentation.evaluate_surjective ε hI g
  obtain ⟨y,hy⟩ := (SmallPresentation.K1equivalence (R := R) e hι).surjective
    (SmallPresentation.toK1 x)⁻¹
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective SmallPresentation.elementaryGroup y
  refine ⟨SmallPresentation.evaluate z,?_⟩
  rw [←SmallPresentation.evaluate_inclusion_apply,←map_mul,evaluate_mem_iff ε hI]
  apply (QuotientGroup.eq_one_iff _).mp
  change SmallPresentation.toK1 (x * SmallPresentation.inclusion e z) = 1
  rw [map_mul]
  change SmallPresentation.toK1 x * SmallPresentation.K1map e (SmallPresentation.toK1 z) = 1
  change SmallPresentation.toK1 x * (SmallPresentation.K1equivalence (R := R) e hι)
    (SmallPresentation.toK1 z) = 1
  change (SmallPresentation.K1equivalence (R := R) e hι) (SmallPresentation.toK1 z) = _ at hy
  rw [hy,mul_inv_cancel]

end
end SourceBurnside.Stability.MatrixK1

end

end OAI
