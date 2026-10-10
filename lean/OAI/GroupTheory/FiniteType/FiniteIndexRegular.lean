import Mathlib
import OAI.GroupTheory.FiniteType.ClassifyingSpaces

namespace OAI

noncomputable section
namespace FiniteIndexRegular
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation FiniteExtension
variable {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
open scoped Classical TensorProduct MonoidAlgebra

noncomputable def coords : L ≃ Q K × K where
  toFun x := (pi K x, factor K x)
  invFun p := (p.2 : L) * sectionMap K p.1
  left_inv x := by simp [factor]
  right_inv p := by
    rcases p with ⟨c,k⟩
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp [factor]

@[simp] lemma coords_mul_section (k : K) (c : Q K) :
    coords K ((k : L)*sectionMap K c) = (c,k) := (coords K).apply_symm_apply (c,k)

noncomputable def embedLM : RegularProductR.Module ℤ K I →ₗ[ℤ]
    RegularProductR.Module ℤ L I :=
  LinearMap.pi (fun i => (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)).comp (LinearMap.proj i))

noncomputable def embed : RegularProductR.rep ℤ K I ⟶
    Rep.res K.subtype (RegularProductR.rep ℤ L I) := Rep.ofHom ⟨embedLM K I, by
  intro k
  apply LinearMap.ext
  intro a
  funext i
  change Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)
    (RegularProductR.rightShift ℤ K k (a i)) =
    RegularProductR.rightShift ℤ L (k : L)
      (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L) (a i))
  have h : (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)).comp
      (RegularProductR.rightShift ℤ K k) =
      (RegularProductR.rightShift ℤ L (k : L)).comp
        (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L)) := by
    apply Finsupp.lhom_ext
    intro x r
    simp
  exact LinearMap.congr_fun h (a i)⟩

noncomputable def eval : Rep.ind K.subtype (RegularProductR.rep ℤ K I) ⟶
    RegularProductR.rep ℤ L I :=
  (Rep.indResHomEquiv K.subtype (RegularProductR.rep ℤ K I)
    (RegularProductR.rep ℤ L I)).symm (embed K I)

lemma eval_mk {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
    (h : L) (a : RegularProductR.Module ℤ K I) (i : I) :
    eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a) i =
      Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*h) (a i) := by
  simp [eval, Rep.indResHomEquiv]
  change RegularProductR.rightShift ℤ L h⁻¹
    (Finsupp.lmapDomain ℤ ℤ ((↑) : K → L) (a i)) = _
  rw [RegularProductR.rightShift, ← LinearMap.comp_apply, ← Finsupp.lmapDomain_comp]
  simp

noncomputable def slice (c : Q K) : (L →₀ ℤ) →ₗ[ℤ] (K →₀ ℤ) :=
  (Finsupp.lapply c).comp ((Finsupp.curryLinearEquiv ℤ).toLinearMap.comp
    (Finsupp.domLCongr (coords K)).toLinearMap)

@[simp] lemma slice_single (c : Q K) (x : L) (z : ℤ) :
    slice K c (Finsupp.single x z) =
      Finsupp.single (pi K x) (Finsupp.single (factor K x) z) c := by
  simp [slice, coords, Finsupp.curry_single]

noncomputable def slices (c : Q K) : RegularProductR.Module ℤ L I →ₗ[ℤ]
    RegularProductR.Module ℤ K I :=
  LinearMap.pi (fun i => (slice K c).comp (LinearMap.proj i))

@[simp] lemma factor_coemul (k : K) (h : L) :
    factor K ((k : L)*h) = k*factor K h := by
  apply Subtype.ext
  simp [factor, mul_assoc]

lemma slice_map (c : Q K) (h : L) :
    (slice K c).comp (Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*h)) =
      if c = pi K h then RegularProductR.rightShift ℤ K (factor K h)⁻¹ else 0 := by
  classical
  apply Finsupp.lhom_ext
  intro k z
  by_cases hc : c = pi K h
  · subst c
    simp [slice_single]
  · simp [slice_single, hc]

lemma slices_eval_mk (c : Q K) (h : L) (a : RegularProductR.Module ℤ K I) :
    slices K I c (eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a)) =
      if c = pi K h then (RegularProductR.rep ℤ K I).ρ (factor K h)⁻¹ a else 0 := by
  classical
  funext i
  change slice K c (eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a) i) = _
  rw [eval_mk, ← LinearMap.comp_apply, slice_map]
  split_ifs <;> rfl

lemma ind_mk_left {L : Type} [Group L] (K : Subgroup L) [K.Normal] (I : Type)
    (k : K) (h : L) (a : RegularProductR.Module ℤ K I) :
    IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ ((k : L)*h) a =
      IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h
        ((RegularProductR.rep ℤ K I).ρ k⁻¹ a) := by
  simp

variable [Fintype (Q K)]
noncomputable def invLM : RegularProductR.Module ℤ L I →ₗ[ℤ]
    Representation.IndV K.subtype (RegularProductR.rep ℤ K I).ρ :=
  ∑ c, (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ (sectionMap K c)).comp (slices K I c)

lemma inv_eval_mk (h : L) (a : RegularProductR.Module ℤ K I) :
    invLM K I (eval K I (IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a)) =
      IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ h a := by
  let A := RegularProductR.rep ℤ K I
  calc
    _ = ∑ c : Q K, IndV.mk K.subtype A.ρ (sectionMap K c)
        (slices K I c (eval K I (IndV.mk K.subtype A.ρ h a))) := by
      exact LinearMap.sum_apply _ _ _
    _ = ∑ c : Q K, if c = pi K h then
        IndV.mk K.subtype A.ρ (sectionMap K c) (A.ρ (factor K h)⁻¹ a) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [slices_eval_mk]
      split_ifs
      · rfl
      · exact map_zero _
    _ = IndV.mk K.subtype A.ρ (sectionMap K (pi K h)) (A.ρ (factor K h)⁻¹ a) := by
      simp
    _ = IndV.mk K.subtype A.ρ h a := by
      rw [← ind_mk_left]
      congr 1
      simp [factor]
      rfl

lemma sum_slices (a : L →₀ ℤ) :
    (∑ c : Q K, Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*sectionMap K c)
      (slice K c a)) = a := by
  have heq : (∑ c : Q K, (Finsupp.lmapDomain ℤ ℤ
        (fun k : K => (k : L)*sectionMap K c)).comp (slice K c)) =
      (LinearMap.id : (L →₀ ℤ) →ₗ[ℤ] (L →₀ ℤ)) := by
    apply Finsupp.lhom_ext
    intro x z
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, slice_single,
      Finsupp.single_apply, apply_ite, map_zero]
    rw [Finset.sum_ite_eq]
    simp [factor]
  simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
    using LinearMap.congr_fun heq a

lemma eval_inv (a : RegularProductR.Module ℤ L I) : eval K I (invLM K I a) = a := by
  funext i
  have he : invLM K I a = ∑ c : Q K,
      IndV.mk K.subtype (RegularProductR.rep ℤ K I).ρ (sectionMap K c) (slices K I c a) :=
    LinearMap.sum_apply _ _ _
  rw [he, map_sum, Finset.sum_apply]
  calc
    _ = ∑ c : Q K, Finsupp.lmapDomain ℤ ℤ (fun k : K => (k : L)*sectionMap K c)
        (slice K c (a i)) := by
      apply Finset.sum_congr rfl
      intro c _
      exact eval_mk K I (sectionMap K c) (slices K I c a) i
    _ = a i := sum_slices K (a i)

lemma inv_eval (a : Rep.ind K.subtype (RegularProductR.rep ℤ K I)) :
    invLM K I (eval K I a) = a := by
  have h : (invLM K I).comp (eval K I).hom.toLinearMap = LinearMap.id := by
    apply IndV.hom_ext
    intro h
    ext a
    exact inv_eval_mk K I h a
  exact LinearMap.congr_fun h a

noncomputable def indIso : Rep.ind K.subtype (RegularProductR.rep ℤ K I) ≅
    RegularProductR.rep ℤ L I :=
  Rep.mkIso (Representation.Equiv.mk
    { (eval K I).hom.toLinearMap with
      invFun := invLM K I
      left_inv := inv_eval K I
      right_inv := eval_inv K I }
    (eval K I).hom.2)

theorem product_vanishing
    (hn : ∀ (J : Type) (n : ℕ), 2 ≤ n → CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ K J) n))
    (n : ℕ) (h : 2 ≤ n) : CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ L I) n) := by
  classical
  exact (hn I n h).of_iso
    (((groupHomology.functor ℤ L n).mapIso (indIso K I).symm) ≪≫
      groupHomology.indIso K (RegularProductR.rep ℤ K I) n)

end FiniteIndexRegular

namespace RegularProductR
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {G H : Type} [Group G] [Group H] (e : G ≃* H) (I : Type)
noncomputable def relabel : Module ℤ G I ≃ₗ[ℤ] Module ℤ H I :=
  LinearEquiv.piCongrRight (fun _ => Finsupp.domLCongr (R := ℤ) e.toEquiv)

lemma relabel_comm (g : G) :
    (relabel e I).toLinearMap.comp ((rep ℤ G I).ρ g) =
      ((rep ℤ H I).ρ (e g)).comp (relabel e I).toLinearMap := by
  apply LinearMap.ext
  intro a
  funext i
  have h : (Finsupp.domLCongr (R := ℤ) (M := ℤ) e.toEquiv).toLinearMap.comp
      (rightShift ℤ G g) = (rightShift ℤ H (e g)).comp
        (Finsupp.domLCongr (R := ℤ) e.toEquiv).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x z
    simp
  exact LinearMap.congr_fun h (a i)

noncomputable def homologyRelabel (n : ℕ) :
    groupHomology (rep ℤ G I) n ≅ groupHomology (rep ℤ H I) n :=
  groupHomology.mapIso e (relabel e I) (relabel_comm e I) n

include e in
lemma vanishing_relabel
    (h : ∀ (J : Type) (n : ℕ), 2 ≤ n → CategoryTheory.Limits.IsZero
      (groupHomology (rep ℤ G J) n)) (n : ℕ) (hn : 2 ≤ n) :
    CategoryTheory.Limits.IsZero (groupHomology (rep ℤ H I) n) :=
  (h I n hn).of_iso (homologyRelabel e I n).symm
end RegularProductR

end

end OAI
