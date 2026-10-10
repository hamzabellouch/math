import OAI.GroupTheory.Congruence.Parabolic
import OAI.Geometry.Coboundary.Frames
import OAI.Combinatorics.Coboundary.Mixing

namespace OAI

noncomputable section

/-!
Row-parabolic groups, row-frame actions, finite images, and congruence stabilizers.
-/

section
open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowParabolic
variable (A : Type*) [CommRing A] (a b : ℕ)
abbrev Idx := Fin a ⊕ Fin b

def fixed : Subgroup (Matrix.SpecialLinearGroup (Idx a b) A) where
  carrier := {g | ∀ i : Fin b, ∀ j, g (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j}
  one_mem' := by intro i j; rfl
  mul_mem' := by
    intro g h hg hh i j
    change ∀ i j, g.val (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j at hg
    change ∀ i j, h.val (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j at hh
    change (g.val * h.val) (Sum.inr i) j = _
    simpa [Matrix.mul_apply, hg, Matrix.one_apply] using hh i j
  inv_mem' := by
    intro g hg i j
    change ∀ i j, g.val (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j at hg
    have he : (g.val * (g⁻¹).val) (Sum.inr i) j = (1 : Matrix (Idx a b) (Idx a b) A) (Sum.inr i) j := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    simpa [Matrix.mul_apply, hg, Matrix.one_apply] using he

lemma block_form (g : fixed A a b) : g.val.val =
    Matrix.fromBlocks (Matrix.toBlocks₁₁ g.val.val) (Matrix.toBlocks₁₂ g.val.val) 0 1 := by
  funext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    have h := g.property i j
    cases j <;> simpa [Matrix.one_apply] using h

def project : fixed A a b →* Matrix.SpecialLinearGroup (Fin a) A where
  toFun g := ⟨Matrix.toBlocks₁₁ g.val.val, by
    have h := g.val.property
    rw [block_form A a b g, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one] at h
    exact h⟩
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change (1 : Matrix (Idx a b) (Idx a b) A) _ _ = (1 : Matrix (Fin a) (Fin a) A) _ _
    simp [Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    change Matrix.toBlocks₁₁ (g.val.val * h.val.val) = Matrix.toBlocks₁₁ g.val.val * Matrix.toBlocks₁₁ h.val.val
    rw [block_form A a b g, block_form A a b h, Matrix.fromBlocks_multiply]
    simp

def ofBlocks (g : Matrix.SpecialLinearGroup (Fin a) A) (v : Matrix (Fin a) (Fin b) A) : fixed A a b :=
  ⟨⟨Matrix.fromBlocks g.val v 0 1, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact g.property⟩,
    by intro i j; cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]⟩

@[simp] lemma project_ofBlocks (g : Matrix.SpecialLinearGroup (Fin a) A) (v : Matrix (Fin a) (Fin b) A) :
    project A a b (ofBlocks A a b g v) = g := rfl

def sectionHom : Matrix.SpecialLinearGroup (Fin a) A →* fixed A a b where
  toFun g := ofBlocks A a b g 0
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact Matrix.fromBlocks_one
  map_mul' g h := by
    apply Subtype.ext; apply Subtype.ext
    change Matrix.fromBlocks (g.val*h.val) 0 0 (1 : Matrix (Fin b) (Fin b) A) =
      Matrix.fromBlocks g.val 0 0 1 * Matrix.fromBlocks h.val 0 0 1
    simp [Matrix.fromBlocks_multiply]

variable {A} {B : Type*} [CommRing B]
def map (f : A →+* B) : fixed A a b →* fixed B a b where
  toFun g := ⟨Matrix.SpecialLinearGroup.map f g.val, by
    intro i j
    change f (g.val.val (Sum.inr i) j) = _
    rw [g.property i j]
    simp [Matrix.one_apply]⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

lemma map_surjective (f : A →+* B) (hf : Function.Surjective f)
    (hSL : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a) f)) :
    Function.Surjective (map a b f) := by
  intro g
  obtain ⟨h,hh⟩ := hSL (project B a b g)
  choose v hv using fun i j => hf (g.val.val (Sum.inl i) (Sum.inr j))
  refine ⟨ofBlocks A a b h v, ?_⟩
  apply Subtype.ext; apply Matrix.SpecialLinearGroup.ext
  intro i j
  change f (Matrix.fromBlocks h.val v 0 (1 : Matrix (Fin b) (Fin b) A) i j) = g.val.val i j
  cases i with
  | inl i => cases j with
    | inl j => exact congrArg (fun z : Matrix.SpecialLinearGroup (Fin a) B => z i j) hh
    | inr j => exact hv i j
  | inr i =>
    rw [g.property i j]
    cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

end CoboundaryExpanders.RowParabolic

namespace CoboundaryExpanders.Unimodular
variable {R : Type*} [CommRing R] {a b : ℕ}

lemma normalize_rows (ha : 0 < a) (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R)
    (hM : IsUnit M.det) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) R,
      ∀ i : Fin b, ∀ j, g (Sum.inr i) j = M (Sum.inr i) j := by
  obtain ⟨u,hu⟩ := hM
  let z : Fin a ⊕ Fin b := Sum.inl ⟨0,ha⟩
  let D : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R :=
    Matrix.diagonal (fun i => if i = z then (↑u⁻¹ : R) else 1)
  have hD : D.det = ↑u⁻¹ := by simp [D, Matrix.det_diagonal]
  refine ⟨⟨D * M, ?_⟩, ?_⟩
  · rw [Matrix.det_mul, hD, ← hu]
    exact Units.inv_mul u
  · intro i j
    simp [D, Matrix.diagonal_mul, z]

theorem row_completion [IsDomain R] [IsPrincipalIdealRing R]
    (ha : 0 < a) (f : Fin b → (Fin a ⊕ Fin b → R)) (hf : IsFrame R f) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) R,
      ∀ i j, g (Sum.inr i) j = f i j := by
  obtain ⟨r,hr⟩ := hf
  have hk : Module.finrank R r.ker = a := by
    have h := frame_rank_split f r hr
    simp only [Fintype.card_fin, Module.finrank_pi, Fintype.card_sum] at h
    omega
  let eK : r.ker ≃ₗ[R] (Fin a → R) :=
    ((Module.finBasis R r.ker).reindex (finCongr hk)).equivFun
  let e : (Fin a ⊕ Fin b → R) ≃ₗ[R] (Fin a ⊕ Fin b → R) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) R R).trans
      ((LinearEquiv.prodComm R (Fin a → R) (Fin b → R)).trans
        ((LinearEquiv.prodCongr (LinearEquiv.refl R (Fin b → R)) eK.symm).trans
          (splitEquiv f r hr).symm))
  have hei (i : Fin b) : e (Pi.single (Sum.inr i) 1) = f i := by
    change combine f (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inr j)) +
      (eK.symm (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inl j)) : r.ker) = f i
    have h1 : (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inr j)) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply]
    have h0 : (fun j => (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → R) (Sum.inl j)) = 0 := by
      ext j; simp
    rw [h1,h0,map_zero]
    change combine f (Pi.single i 1) + 0 = f i
    rw [add_zero]
    simp [combine_apply, Pi.single_apply]
  let M := (LinearMap.toMatrix' e.toLinearMap).transpose
  have hu : IsUnit M.det := by
    rw [Matrix.det_transpose]
    apply (isUnit_iff_exists_inv).mpr
    refine ⟨(LinearMap.toMatrix' e.symm.toLinearMap).det, ?_⟩
    rw [← Matrix.det_mul, ← LinearMap.toMatrix'_comp]
    simp
  obtain ⟨g,hg⟩ := normalize_rows ha M hu
  refine ⟨g,fun i j => (hg i j).trans ?_⟩
  change (e (Pi.single (Sum.inr i) 1)) j = f i j
  rw [hei]

end CoboundaryExpanders.Unimodular

end

section
open scoped Matrix BigOperators
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.Unimodular
variable {R A ι S M N : Type*} [CommRing R] [CommRing A]
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma frame_linearEquiv (f : S → M) (e : M ≃ₗ[R] N) :
    IsFrame R (fun i => e (f i)) ↔ IsFrame R f := by
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r.comp e.toLinearMap, hr⟩
  · rintro ⟨r,hr⟩
    exact ⟨r.comp e.symm.toLinearMap, fun i => by simpa using hr i⟩

lemma frame_map (φ : R →+* A) (f : S → (ι → R)) (hf : IsFrame R f) :
    IsFrame A (fun i j => φ (f i j)) := by
  obtain ⟨r,hr⟩ := hf
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' r).map φ), ?_⟩
  intro i
  ext j
  have hh := congrArg φ (congrFun (hr i) j)
  rw [← LinearMap.toMatrix'_mulVec r (f i)] at hh
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.single_apply] at hh
  change ∑ x, φ (LinearMap.toMatrix' r j x) * φ (f i x) = _
  simpa only [apply_ite φ, map_one, map_zero, Pi.single_apply] using hh

lemma frame_injective [Nontrivial R] (f : S → M) (hf : IsFrame R f) :
    Function.Injective f := by
  obtain ⟨r,hr⟩ := hf
  intro i j hij
  by_contra h
  have hh := congrFun ((hr i).symm.trans ((congrArg r hij).trans (hr j))) i
  simp [h] at hh

end CoboundaryExpanders.Unimodular

namespace CoboundaryExpanders.RowFrames
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

scoped instance (priority := high) rowSMul : SMul (Matrix.SpecialLinearGroup ι A) (ι → A) :=
  ⟨fun g v => Matrix.vecMul v (g⁻¹).val⟩

scoped instance (priority := high) action : MulAction (Matrix.SpecialLinearGroup ι A) (ι → A) where
  smul g v := Matrix.vecMul v (g⁻¹).val
  one_smul v := by
    change Matrix.vecMul v ((1 : Matrix.SpecialLinearGroup ι A)⁻¹).val = v
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  mul_smul g h v := by
    change Matrix.vecMul v ((g*h)⁻¹).val = Matrix.vecMul (Matrix.vecMul v (h⁻¹).val) (g⁻¹).val
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.vecMul_vecMul]

open scoped RowFrames
@[simp] lemma smul_eq (g : Matrix.SpecialLinearGroup ι A) (v : ι → A) :
    g • v = Matrix.vecMul v (g⁻¹).val := rfl

def linearAction (g : Matrix.SpecialLinearGroup ι A) : (ι → A) ≃ₗ[A] (ι → A) where
  toFun v := g • v
  invFun v := g⁻¹ • v
  left_inv v := inv_smul_smul g v
  right_inv v := smul_inv_smul g v
  map_add' first second := Matrix.add_vecMul _ first second
  map_smul' a v := Matrix.smul_vecMul a v _

lemma frame_smul {S : Type*} (f : S → (ι → A))
    (g : Matrix.SpecialLinearGroup ι A) :
    Unimodular.IsFrame A (fun i => g • f i) ↔ Unimodular.IsFrame A f :=
  Unimodular.frame_linearEquiv f (linearAction g)

lemma standard_fixed_iff {a b : ℕ} (g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
    (∀ i : Fin b, g • (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → A) = Pi.single (Sum.inr i) 1) ↔
      g ∈ RowParabolic.fixed A a b := by
  have he (h : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
      (∀ i : Fin b, h • (Pi.single (Sum.inr i) 1 : Fin a ⊕ Fin b → A) = Pi.single (Sum.inr i) 1) ↔
        h⁻¹ ∈ RowParabolic.fixed A a b := by
    constructor
    · intro hh i j
      have hx := congrFun (hh i) j
      simpa [smul_eq, Matrix.single_vecMul, Pi.single_apply, Matrix.one_apply,eq_comm] using hx
    · intro hh i
      ext j
      have hx := hh i j
      simpa [smul_eq, Matrix.single_vecMul, Pi.single_apply, Matrix.one_apply,eq_comm] using hx
  rw [he, Subgroup.inv_mem_iff]

end CoboundaryExpanders.RowFrames

end

namespace CoboundaryExpanders.Construction
variable (p m : ℕ) [Fact p.Prime]

lemma residue_isUnit (hm : 1 ≤ m) (a : Trunc p m)
    (ha : residue p m hm a ≠ 0) : IsUnit a := by
  let c : Trunc p m := Ideal.Quotient.mk (powerIdeal p m) (Polynomial.C (residue p m hm a)⁻¹)
  have hc : residue p m hm c = (residue p m hm a)⁻¹ := by simp [c]
  have hu := residue_one_isUnit p m hm (a*c) (by rw [map_mul,hc,mul_inv_cancel₀ ha])
  exact isUnit_of_mul_isUnit_left hu

theorem trunc_SL_surjective (hm : 1 ≤ m) (a : ℕ) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a)
      (Ideal.Quotient.mk (powerIdeal p m))) :=
  Elementary.SL_map_surjective _ (Ideal.Quotient.mk_surjective)
    (residue p m hm) (residue_isUnit p m hm)

end CoboundaryExpanders.Construction

section
open scoped BigOperators Matrix
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.Unimodular
variable {A F : Type*} [CommRing A] [Field F] {a b : ℕ}

theorem row_completion_of_residue_frame (π : A →+* F) (hp : Function.Surjective π)
    (hu : ∀ x, π x ≠ 0 → IsUnit x) (ha : 0 < a)
    (f : Fin b → (Fin a ⊕ Fin b → A))
    (hf : IsFrame F (fun i j => π (f i j))) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A,
      ∀ i j, g (Sum.inr i) j = f i j := by
  obtain ⟨g,hg⟩ := row_completion ha _ hf
  choose v hv using fun i : Fin a => fun j => hp (g (Sum.inl i) j)
  let M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) A := Sum.elim v f
  have hM : M.map π = g.val := by
    ext i j
    cases i with
    | inl i => exact hv i j
    | inr i => exact (hg i j).symm
  have hdet : π M.det = 1 := by
    rw [RingHom.map_det]
    change (M.map π).det = 1
    rw [hM]; exact g.property
  obtain ⟨G,hG⟩ := normalize_rows ha M (hu M.det (by rw [hdet]; exact one_ne_zero))
  exact ⟨G,hG⟩

theorem row_completion_residue (π : A →+* F) (hp : Function.Surjective π)
    (hu : ∀ x, π x ≠ 0 → IsUnit x) (ha : 0 < a)
    (f : Fin b → (Fin a ⊕ Fin b → A)) (hf : IsFrame A f) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A,
      ∀ i j, g (Sum.inr i) j = f i j :=
  row_completion_of_residue_frame π hp hu ha f (frame_map π f hf)

end CoboundaryExpanders.Unimodular

namespace CoboundaryExpanders.Construction
variable (p m : ℕ) [Fact p.Prime]
lemma residue_surjective (hm : 1 ≤ m) : Function.Surjective (residue p m hm) := by
  intro a
  refine ⟨Ideal.Quotient.mk (powerIdeal p m) (Polynomial.C a), ?_⟩
  simp

theorem trunc_SL_surjective_any (hm : 1 ≤ m) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := ι)
      (Ideal.Quotient.mk (powerIdeal p m))) :=
  Elementary.SL_map_surjective_reindex _ (trunc_SL_surjective p m hm _)

theorem trunc_frame_lift (hm : 1 ≤ m) {a b : ℕ} (ha : 0 < a)
    (f : Fin b → (Fin a ⊕ Fin b → Trunc p m))
    (hf : Unimodular.IsFrame (Trunc p m) f) :
    ∃ g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) (R p),
      ∀ i j, Ideal.Quotient.mk (powerIdeal p m) (g (Sum.inr i) j) = f i j := by
  obtain ⟨g,hg⟩ := Unimodular.row_completion_residue (residue p m hm)
    (residue_surjective p m hm) (residue_isUnit p m hm) ha f hf
  obtain ⟨G,hG⟩ := trunc_SL_surjective_any p m hm (Fin a ⊕ Fin b) g
  refine ⟨G,fun i j => ?_⟩
  exact (congrArg (fun z : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) (Trunc p m) =>
    z (Sum.inr i) j) hG).trans (hg i j)
end CoboundaryExpanders.Construction

end

section
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A B : Type*} [CommRing A] [CommRing B] {a b : ℕ}
abbrev standard (i : Fin b) : Fin a ⊕ Fin b → A := Pi.single (Sum.inr i) 1
lemma standard_frame : Unimodular.IsFrame A (standard (A := A) (a := a) (b := b)) := by
  refine ⟨LinearMap.pi (fun i : Fin b => LinearMap.proj (Sum.inr i)), ?_⟩
  intro i
  ext j
  simp [standard, Pi.single_apply]
@[simp] lemma inverse_smul_standard (g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A)
    (i : Fin b) : g⁻¹ • standard (a := a) i = g (Sum.inr i) := by
  ext j
  simp [smul_eq, standard, Matrix.single_vecMul]
lemma row_frame (g : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) A) :
    Unimodular.IsFrame A (fun i : Fin b => g (Sum.inr i)) := by
  simpa only [inverse_smul_standard] using
    (frame_smul (standard (A := A) (a := a) (b := b)) g⁻¹).mpr standard_frame

theorem same_reduction_orbit [IsDomain A] [IsPrincipalIdealRing A]
    (φ : A →+* B) (hφ : Function.Surjective φ)
    (hSL : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a) φ))
    (ha : 0 < a) (f g : Fin b → (Fin a ⊕ Fin b → A))
    (hf : Unimodular.IsFrame A f) (hg : Unimodular.IsFrame A g)
    (he : ∀ i j, φ (f i j) = φ (g i j)) :
    ∃ k : (Matrix.SpecialLinearGroup.map (n := Fin a ⊕ Fin b) φ).ker,
      ∀ i, k.val • f i = g i := by
  obtain ⟨P,hP⟩ := Unimodular.row_completion ha f hf
  obtain ⟨Q,hQ⟩ := Unimodular.row_completion ha g hg
  let bar := Matrix.SpecialLinearGroup.map (n := Fin a ⊕ Fin b) φ
  have hfix : bar P * (bar Q)⁻¹ ∈ RowParabolic.fixed B a b := by
    intro i j
    change ((bar P).val * ((bar Q)⁻¹).val) (Sum.inr i) j = _
    have hrow (x) : (bar P) (Sum.inr i) x = (bar Q) (Sum.inr i) x := by
      change φ (P (Sum.inr i) x) = φ (Q (Sum.inr i) x)
      rw [hP,hQ]; exact he i x
    have hx := congrArg (fun z : Matrix.SpecialLinearGroup (Fin a ⊕ Fin b) B => z (Sum.inr i) j)
      (mul_inv_cancel (bar Q))
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply, hrow] using hx
  obtain ⟨r,hr⟩ := RowParabolic.map_surjective a b φ hφ hSL
    ⟨bar P * (bar Q)⁻¹,hfix⟩
  have hr' : bar r.val = bar P * (bar Q)⁻¹ := congrArg Subtype.val hr
  let k := Q⁻¹ * r.val⁻¹ * P
  have hk : k ∈ bar.ker := by
    change bar k = 1
    simp only [k,map_mul,map_inv,hr']
    group
  refine ⟨⟨k,hk⟩, fun i => ?_⟩
  have hf' : f i = P⁻¹ • standard (a := a) i := by
    rw [inverse_smul_standard]; exact funext (hP i) |>.symm
  have hg' : g i = Q⁻¹ • standard (a := a) i := by
    rw [inverse_smul_standard]; exact funext (hQ i) |>.symm
  rw [hf',hg']
  have hrf : r.val⁻¹ • standard (a := a) i = standard i :=
    (standard_fixed_iff r.val⁻¹).mpr ((RowParabolic.fixed A a b).inv_mem r.property) i
  change (Q⁻¹ * r.val⁻¹ * P) • (P⁻¹ • standard (a := a) i) = _
  rw [mul_smul,mul_smul,smul_inv_smul,hrf]
end CoboundaryExpanders.RowFrames

end

namespace CoboundaryExpanders.MultiParabolic
open scoped Matrix BigOperators

open Construction RowParabolic CategoryTheory
variable (p a b m : ℕ)
abbrev group : Subgroup (Matrix.SpecialLinearGroup (Idx a b) (R p)) :=
  fixed (R p) a b ⊓ (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))).ker

def toFixed : group p a b m →* fixed (R p) a b :=
  Subgroup.inclusion inf_le_left

def project : group p a b m →* Gamma p a m :=
  ((RowParabolic.project (R p) a b).comp (toFixed p a b m)).codRestrict _ (by
    intro A
    have h := A.property.2
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have he := congrArg (fun B : Matrix.SpecialLinearGroup (Idx a b) (R p ⧸ powerIdeal p m) =>
      B (Sum.inl i) (Sum.inl j)) h
    change Ideal.Quotient.mk (powerIdeal p m) (A.val.val (Sum.inl i) (Sum.inl j)) =
      (1 : Matrix (Fin a) (Fin a) (R p ⧸ powerIdeal p m)) i j
    simpa [Matrix.one_apply] using he)

def sectionValue (A : Gamma p a m) : group p a b m :=
  ⟨(RowParabolic.sectionHom (R p) a b A.val).val, by
    constructor
    · exact (RowParabolic.sectionHom (R p) a b A.val).property
    · apply Matrix.SpecialLinearGroup.ext
      intro i j
      have h := A.property
      change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) A.val = 1 at h
      have hh (i j : Fin a) := congrArg (fun B : Matrix.SpecialLinearGroup (Fin a)
        (R p ⧸ powerIdeal p m) => B i j) h
      change Ideal.Quotient.mk (powerIdeal p m)
        (Matrix.fromBlocks A.val.val (0 : Matrix (Fin a) (Fin b) (R p)) 0 1 i j) =
          (1 : Matrix (Idx a b) (Idx a b) (R p ⧸ powerIdeal p m)) i j
      cases i with
      | inl i => cases j with
        | inl j => simpa [Matrix.one_apply, Matrix.SpecialLinearGroup.map_apply_coe] using hh i j
        | inr j => simp
      | inr i => cases j with
        | inl j => simp
        | inr j => simp [Matrix.one_apply]⟩

lemma project_surjective : Function.Surjective (project p a b m) := by
  intro A
  exact ⟨sectionValue p a b m A, by apply Subtype.ext; rfl⟩

lemma kernel_form (A : (project p a b m).ker) : A.val.val.val =
    Matrix.fromBlocks (1 : Matrix (Fin a) (Fin a) (R p))
      (Matrix.toBlocks₁₂ A.val.val.val) 0 1 := by
  have he := congrArg (fun x : Gamma p a m => x.val.val) A.property
  change Matrix.toBlocks₁₁ A.val.val.val = 1 at he
  have hh := RowParabolic.block_form (R p) a b (toFixed p a b m A.val)
  change A.val.val.val = Matrix.fromBlocks (Matrix.toBlocks₁₁ A.val.val.val)
    (Matrix.toBlocks₁₂ A.val.val.val) 0 1 at hh
  rw [he] at hh
  exact hh

def kernelBlock : (project p a b m).ker →* Multiplicative (Matrix (Fin a) (Fin b) (R p)) where
  toFun A := Multiplicative.ofAdd (Matrix.toBlocks₁₂ A.val.val.val)
  map_one' := by
    change Matrix.toBlocks₁₂ (1 : Matrix (Idx a b) (Idx a b) (R p)) = 0
    funext i j
    change (1 : Matrix (Idx a b) (Idx a b) (R p)) (Sum.inl i) (Sum.inr j) = 0
    simp
  map_mul' A B := by
    change Matrix.toBlocks₁₂ (A.val.val.val * B.val.val.val) =
      Matrix.toBlocks₁₂ A.val.val.val + Matrix.toBlocks₁₂ B.val.val.val
    rw [kernel_form p a b m A, kernel_form p a b m B, Matrix.fromBlocks_multiply]
    simp [add_comm]

lemma kernelBlock_injective : Function.Injective (kernelBlock p a b m) := by
  intro A B h
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [kernel_form p a b m A, kernel_form p a b m B]
  exact congrArg (fun v : Matrix (Fin a) (Fin b) (R p) => Matrix.fromBlocks 1 v 0 1)
    (congrArg Multiplicative.toAdd h)

theorem project_homology_isIso [Fact p.Prime] (hp : Odd p) (j : ℕ) :
    IsIso (groupHomology.map (project p a b m)
      (QuotientCoinvariants.trivialMap _) j) := by
  apply QuotientCoinvariants.surjection_map_isIso _ (project_surjective p a b m)
  exact QuotientCoinvariants.localOdd_of_injective (kernelBlock p a b m)
    (kernelBlock_injective p a b m)
    (LocallyFiniteOdd.vector_group_local_odd p hp (Matrix (Fin a) (Fin b) (R p)))

lemma homology_isZero [Fact p.Prime] (hp : Odd p) (j : ℕ)
    (hz : CategoryTheory.Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j)) :
    CategoryTheory.Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (group p a b m) (ZMod 2)) j) := by
  have := project_homology_isIso p a b m hp j
  exact CategoryTheory.Limits.IsZero.of_mono
    (groupHomology.map (project p a b m) (QuotientCoinvariants.trivialMap _) j) hz
end CoboundaryExpanders.MultiParabolic


section
open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A B ι κ : Type} [CommRing A] [CommRing B] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma reindex_smul (e : ι ≃ κ) (g : Matrix.SpecialLinearGroup ι A) (v : κ → A) :
    (fun i => ((Blocks.reindexSL e g) • v) (e i)) = g • (fun i => v (e i)) := by
  have hi : (Blocks.reindexSL e g)⁻¹ = Blocks.reindexSL e g⁻¹ := (map_inv _ g).symm
  ext j
  simp only [smul_eq,hi,Matrix.vecMul,dotProduct]
  rw [← e.sum_comp (fun x => v x * (Blocks.reindexSL e g⁻¹) x (e j))]
  simp only [Blocks.reindexSL_apply]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma frame_coordinates {S : Type} [Fintype S] (e : ι ≃ κ) (f : S → (κ → A)) :
    Unimodular.IsFrame A (fun s i => f s (e i)) ↔ Unimodular.IsFrame A f :=
  Unimodular.frame_linearEquiv f (LinearEquiv.funCongrLeft A A e)

def kernelReindex (φ : A →+* B) (e : ι ≃ κ) :
    (Matrix.SpecialLinearGroup.map (n := ι) φ).ker ≃*
      (Matrix.SpecialLinearGroup.map (n := κ) φ).ker where
  toFun g := ⟨Blocks.reindexSL e g.val, by
    change Matrix.SpecialLinearGroup.map φ (Blocks.reindexSL e g.val) = 1
    rw [Blocks.reindexSL_map, g.property, map_one]⟩
  invFun g := ⟨Blocks.reindexSL e.symm g.val, by
    change Matrix.SpecialLinearGroup.map φ (Blocks.reindexSL e.symm g.val) = 1
    rw [Blocks.reindexSL_map, g.property, map_one]⟩
  left_inv g := by
    apply Subtype.ext
    exact (Blocks.reindexSL e).left_inv g.val
  right_inv g := by
    apply Subtype.ext
    exact (Blocks.reindexSL e).right_inv g.val
  map_mul' g h := by apply Subtype.ext; exact map_mul _ _ _

lemma same_reduction_orbit_coordinates [IsDomain A] [IsPrincipalIdealRing A]
    {a b : ℕ} (φ : A →+* B) (hφ : Function.Surjective φ)
    (hSL : Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin a) φ))
    (ha : 0 < a) (e : Fin a ⊕ Fin b ≃ ι) (f g : Fin b → (ι → A))
    (hf : Unimodular.IsFrame A f) (hg : Unimodular.IsFrame A g)
    (he : ∀ i j, φ (f i j) = φ (g i j)) :
    ∃ k : (Matrix.SpecialLinearGroup.map (n := ι) φ).ker,
      ∀ i, k.val • f i = g i := by
  obtain ⟨k,hk⟩ := same_reduction_orbit φ hφ hSL ha
    (fun i j => f i (e j)) (fun i j => g i (e j))
    ((frame_coordinates e f).mpr hf) ((frame_coordinates e g).mpr hg)
    (fun i j => he i (e j))
  refine ⟨kernelReindex φ e k, fun i => ?_⟩
  ext j
  obtain ⟨j,rfl⟩ := e.surjective j
  exact (congrFun (reindex_smul e k.val (f i)) j).trans (congrFun (hk i) j)

def splitCoordinates (n b : ℕ) (h : b ≤ n) : Fin (n-b) ⊕ Fin b ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel h))

end CoboundaryExpanders.RowFrames

end

namespace CoboundaryExpanders.FiniteImage

section
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def equiv (f : V → W) (s : Finset V) (h : Set.InjOn f (s : Set V)) : s ≃ s.image f :=
  Equiv.ofBijective (fun v => ⟨f v,Finset.mem_image.mpr ⟨v,v.property,rfl⟩⟩) (by
    constructor
    · intro x y he
      exact Subtype.ext (h x.property y.property (congrArg Subtype.val he))
    · rintro ⟨w,hw⟩
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact ⟨⟨v,hv⟩,rfl⟩)
omit [DecidableEq V] in
@[simp] lemma equiv_val (f : V → W) (s : Finset V) (h : Set.InjOn f (s : Set V)) (v : s) :
    (equiv f s h v).val = f v := rfl
omit [DecidableEq V] in
lemma equiv_symm_val (f : V → W) (s : Finset V) (h : Set.InjOn f (s : Set V)) (w : s.image f) :
    f (equiv f s h |>.symm w) = w.val := by
  exact congrArg Subtype.val ((equiv f s h).apply_symm_apply w)

def matching (f : V → W) (s t : Finset V)
    (hs : Set.InjOn f (s : Set V)) (ht : Set.InjOn f (t : Set V))
    (he : s.image f = t.image f) : s ≃ t :=
  (equiv f s hs).trans ((Finset.equivOfEq he).trans (equiv f t ht).symm)
omit [DecidableEq V] in
lemma matching_val (f : V → W) (s t : Finset V)
    (hs : Set.InjOn f (s : Set V)) (ht : Set.InjOn f (t : Set V))
    (he : s.image f = t.image f) (v : s) :
    f (matching f s t hs ht he v) = f v := by
  simp only [matching, Equiv.trans_apply, equiv_symm_val]
  rfl

omit [DecidableEq V] in
lemma image_eq_of_matching {G : Type} [Group G] [MulAction G V]
    (s t : Finset V) (e : s ≃ t) (g : G) (h : ∀ v : s, g • v.val = (e v).val) :
    s.map (MulAction.toPerm g).toEmbedding = t := by
  ext v
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, MulAction.toPerm_apply]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact h ⟨w,hw⟩ ▸ (e ⟨w,hw⟩).property
  · intro hv
    obtain ⟨w,hw⟩ := e.surjective ⟨v,hv⟩
    exact ⟨w.val,w.property,(h w).trans (congrArg Subtype.val hw)⟩
end

variable {V : Type} [DecidableEq V]
def enumeration {b : ℕ} (s : Finset V) (hs : s.card = b) : Fin b ≃ s :=
  (finCongr hs.symm).trans (Finset.equivFin s).symm

def familyEquiv {b : ℕ} (f : Fin b → V) (hf : Function.Injective f) :
    Fin b ≃ Finset.univ.image f :=
  Equiv.ofBijective (fun i => ⟨f i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h; exact hf (congrArg Subtype.val h)
    · rintro ⟨v,hv⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨i,rfl⟩)
@[simp] lemma familyEquiv_val {b : ℕ} (f : Fin b → V) (hf : Function.Injective f) (i : Fin b) :
    (familyEquiv f hf i).val = f i := rfl
end CoboundaryExpanders.FiniteImage

section
open scoped Matrix BigOperators CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.RowFrames
variable {A B ι : Type} [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
lemma map_smul (φ : A →+* B) (g : Matrix.SpecialLinearGroup ι A) (v : ι → A) :
    (fun j => φ ((g • v) j)) = (Matrix.SpecialLinearGroup.map φ g) • (fun j => φ (v j)) := by
  ext j
  simp only [smul_eq, Matrix.vecMul, dotProduct, map_sum, map_mul, ← map_inv,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

lemma kernel_smul (φ : A →+* B) (g : (Matrix.SpecialLinearGroup.map (n := ι) φ).ker)
    (v : ι → A) : (fun j => φ ((g.val • v) j)) = (fun j => φ (v j)) := by
  rw [map_smul,g.property,one_smul]

scoped instance (priority := high) subgroupRowSMul (H : Subgroup (Matrix.SpecialLinearGroup ι A)) :
    SMul H (ι → A) := ⟨fun g v => g.val • v⟩
scoped instance (priority := high) subgroupAction (H : Subgroup (Matrix.SpecialLinearGroup ι A)) :
    MulAction H (ι → A) where
  smul g v := g.val • v
  one_smul v := one_smul (Matrix.SpecialLinearGroup ι A) v
  mul_smul g h v := mul_smul g.val h.val v

lemma complex_invariant (H : Subgroup (Matrix.SpecialLinearGroup ι A)) :
    (Unimodular.complex A (id : (ι → A) → (ι → A))).Invariant (G := H) := by
  intro g s hs
  change Unimodular.IsFrame A (fun v : s.map (MulAction.toPerm g).toEmbedding => v.val)
  apply (Unimodular.frame_equiv (R := A)
    (f := fun v : s.map (MulAction.toPerm g).toEmbedding => v.val)
    (Finset.equivMap (MulAction.toPerm g).toEmbedding s)).mp
  exact (frame_smul (fun v : s => v.val) g.val).mpr hs
end CoboundaryExpanders.RowFrames

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains
variable (p n m : ℕ) [Fact p.Prime]
abbrev source : CoboundaryExpanders.InfiniteChains.Complex (Fin n → R p) := complex (R p) id
abbrev reduce (v : Fin n → R p) : Fin n → Trunc p m :=
  fun j => Ideal.Quotient.mk (powerIdeal p m) (v j)
abbrev residueVector (hm : 1 ≤ m) (v : Fin n → Trunc p m) : Fin n → ZMod p :=
  fun j => residue p m hm (v j)
abbrev target (hm : 1 ≤ m) : CoboundaryExpanders.InfiniteChains.Complex (Fin n → Trunc p m) :=
  complex (ZMod p) (residueVector p n m hm)

instance invariant : Fact ((source p n).Invariant (G := Gamma p n m)) :=
  ⟨RowFrames.complex_invariant (Gamma p n m)⟩

lemma reduce_injOn (hm : 1 ≤ m) (s : Finset (Fin n → R p))
    (hs : s ∈ (source p n).faces) :
    Set.InjOn (reduce p n m) (s : Set (Fin n → R p)) := by
  intro v hv w hw he
  have hframe := frame_map (Polynomial.evalRingHom (R := ZMod p) 0) (fun v : s => v.val) hs
  apply congrArg Subtype.val (frame_injective _ hframe (a₁ := ⟨v,hv⟩) (a₂ := ⟨w,hw⟩) ?_)
  ext j
  exact congrArg (residue p m hm) (congrFun he j)

def reduction (hm : 1 ≤ m) : (source p n).Reduction (target p n m hm) where
  f := reduce p n m
  injOn := reduce_injOn p n m hm
  faces s hs := by
    change IsFrame (ZMod p) (fun v : s.image (reduce p n m) => residueVector p n m hm v.val)
    apply (frame_equiv (R := ZMod p)
      (f := fun v : s.image (reduce p n m) => residueVector p n m hm v.val)
      (FiniteImage.equiv (reduce p n m) s (reduce_injOn p n m hm s hs))).mp
    exact frame_map (Polynomial.evalRingHom (R := ZMod p) 0) (fun v : s => v.val) hs

lemma reduce_smul (g : Gamma p n m) (v : Fin n → R p) :
    reduce p n m (g • v) = reduce p n m v :=
  RowFrames.kernel_smul (Ideal.Quotient.mk (powerIdeal p m)) g v

lemma face_invariant (hm : 1 ≤ m) (b : ℕ) (g : Gamma p n m) (s : (source p n).Face b) :
    (reduction p n m hm).face b (g • s) = (reduction p n m hm).face b s := by
  apply Subtype.ext
  change (s.val.map (MulAction.toPerm g).toEmbedding).image (reduce p n m) = s.val.image (reduce p n m)
  rw [Finset.map_eq_image,Finset.image_image]
  congr 1
  funext v
  exact reduce_smul p n m g v

lemma target_exact (hm : 1 ≤ m) (b : ℕ) (hb : b < n) :
    Attachment.ExactIn (target p n m hm).faces b := by
  apply field_exact (ZMod p) (Fin n → Trunc p m) n (residueVector p n m hm) _ b hb
  intro v
  exact ⟨fun j => Ideal.Quotient.mk (powerIdeal p m) (Polynomial.C (v j)), by ext j; simp⟩

lemma source_exact (b : ℕ) (hb : b < n) : Attachment.ExactIn (source p n).faces b :=
  polynomial_exact (ZMod p) (Fin n → R p) n id Function.surjective_id b hb

end CoboundaryExpanders.CongruenceFrames

end

open scoped BigOperators Matrix CoboundaryExpanders.RowFrames
attribute [local instance] Classical.decEq

namespace CoboundaryExpanders.CongruenceFrames
open Construction Unimodular InfiniteChains RowFrames
variable (p n m : ℕ) [Fact p.Prime]

lemma ordered_lift (hm : 1 ≤ m) {b : ℕ} (hb : b < n)
    (f : Fin b → (Fin n → Trunc p m))
    (hf : IsFrame (ZMod p) (fun i => residueVector p n m hm (f i))) :
    ∃ g : Fin b → (Fin n → R p), IsFrame (R p) g ∧ ∀ i, reduce p n m (g i) = f i := by
  let e := splitCoordinates n b hb.le
  have hff : IsFrame (ZMod p) (fun i j => residue p m hm (f i (e j))) :=
    (frame_coordinates e _).mpr hf
  obtain ⟨P,hP⟩ := row_completion_of_residue_frame (residue p m hm)
    (residue_surjective p m hm) (residue_isUnit p m hm)
    (show 0 < n-b by omega) (fun i j => f i (e j)) hff
  obtain ⟨G,hG⟩ := trunc_SL_surjective_any p m hm (Fin (n-b) ⊕ Fin b) P
  let g : Fin b → (Fin n → R p) := fun i j => G (Sum.inr i) (e.symm j)
  refine ⟨g,?_,?_⟩
  · apply (frame_coordinates e g).mp
    simpa only [g,Equiv.symm_apply_apply] using row_frame G
  · intro i
    ext j
    have hx := congrArg (fun z : Matrix.SpecialLinearGroup (Fin (n-b) ⊕ Fin b) (Trunc p m) =>
      z (Sum.inr i) (e.symm j)) hG
    exact hx.trans ((hP i (e.symm j)).trans (congrArg (f i) (e.apply_symm_apply j)))

lemma face_surjective (hm : 1 ≤ m) (b : ℕ) (hb : b < n) :
    Function.Surjective ((reduction p n m hm).face b) := by
  intro s
  let e := FiniteImage.enumeration s.val s.property.2
  let f : Fin b → (Fin n → Trunc p m) := fun i => (e i).val
  have hf : IsFrame (ZMod p) (fun i => residueVector p n m hm (f i)) :=
    (frame_equiv (R := ZMod p) (f := fun v : s.val => residueVector p n m hm v.val) e).mpr s.property.1
  obtain ⟨g,hg,hred⟩ := ordered_lift p n m hm hb f hf
  have hgi := frame_injective g hg
  let t := Finset.univ.image g
  have ht : t ∈ (source p n).faces := by
    apply (frame_equiv (R := R p) (f := fun v : t => v.val)
      (FiniteImage.familyEquiv g hgi)).mp
    exact hg
  have htcard : t.card = b := by
    rw [Finset.card_image_of_injective _ hgi, Finset.card_univ,Fintype.card_fin]
  refine ⟨⟨t,ht,htcard⟩,?_⟩
  apply Subtype.ext
  change t.image (reduce p n m) = s.val
  ext v
  simp only [t,Finset.image_image,Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply,hred]
  constructor
  · rintro ⟨i,rfl⟩
    exact (e i).property
  · intro hv
    obtain ⟨i,hi⟩ := e.surjective ⟨v,hv⟩
    exact ⟨i,congrArg Subtype.val hi⟩

lemma face_fiber (hm : 1 ≤ m) (b : ℕ) (hb : b < n)
    (s t : (source p n).Face b)
    (he : (reduction p n m hm).face b s = (reduction p n m hm).face b t) :
    ∃ g : Gamma p n m, g • s = t := by
  have hs := reduce_injOn p n m hm s.val s.property.1
  have ht := reduce_injOn p n m hm t.val t.property.1
  have himg : s.val.image (reduce p n m) = t.val.image (reduce p n m) := congrArg Subtype.val he
  let e := FiniteImage.matching (reduce p n m) s.val t.val hs ht himg
  let eS := FiniteImage.enumeration s.val s.property.2
  let f : Fin b → (Fin n → R p) := fun i => (eS i).val
  let h : Fin b → (Fin n → R p) := fun i => (e (eS i)).val
  have hf : IsFrame (R p) f := (frame_equiv (R := R p) (f := fun v : s.val => v.val) eS).mpr s.property.1
  have hh : IsFrame (R p) h :=
    (frame_equiv (R := R p) (f := fun v : t.val => v.val) (eS.trans e)).mpr t.property.1
  obtain ⟨g,hg⟩ := same_reduction_orbit_coordinates
    (Ideal.Quotient.mk (powerIdeal p m)) Ideal.Quotient.mk_surjective
    (trunc_SL_surjective p m hm (n-b)) (show 0 < n-b by omega)
    (splitCoordinates n b hb.le) f h hf hh (by
      intro i j
      exact (congrFun (FiniteImage.matching_val (reduce p n m) s.val t.val hs ht himg (eS i)) j).symm)
  refine ⟨g,?_⟩
  apply Subtype.ext
  apply FiniteImage.image_eq_of_matching s.val t.val e g
  intro v
  obtain ⟨i,rfl⟩ := eS.surjective v
  exact hg i

def orbitParam (hm : 1 ≤ m) (b : ℕ) (hb : b < n) :
    FinsuppPermutation.OrbitParam (Gamma p n m) ((source p n).Face b) ((target p n m hm).Face b) where
  f := (reduction p n m hm).face b
  invariant := face_invariant p n m hm b
  surjective := face_surjective p n m hm b hb
  fiber := face_fiber p n m hm b hb
end CoboundaryExpanders.CongruenceFrames

end

end OAI
