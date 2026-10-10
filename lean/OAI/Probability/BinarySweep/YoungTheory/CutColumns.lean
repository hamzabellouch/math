import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.HookCut

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

section
open Equiv Equiv.Perm

variable (μ : YoungDiagram) (p : ℕ)

lemma cutPerm_mem_column_iff (g : G (hookPart μ p) × G (southeast μ p)) :
    cutPerm μ p g ∈ C μ ↔ g.1 ∈ C (hookPart μ p) ∧ g.2 ∈ C (southeast μ p) := by
  constructor
  · intro h
    constructor
    · intro x
      simpa only [cutPerm_apply_hook,col_hookIn] using h (hookIn μ p x)
    · intro x
      simpa only [cutPerm_apply_southeast,col_southeastIn,Nat.add_right_cancel_iff] using
        h (southeastIn μ p x)
  · rintro ⟨h1,h2⟩ x
    obtain ⟨y,rfl⟩ := (cutEquiv μ p).surjective x
    cases y with
    | inl y => simpa only [cutEquiv_inl,cutPerm_apply_hook,col_hookIn] using h1 y
    | inr y => simpa only [cutEquiv_inr,cutPerm_apply_southeast,col_southeastIn] using
        congrArg (fun k : ℕ => k+p) (h2 y)

def cutColumns : C (hookPart μ p) × C (southeast μ p) ↪ C μ where
  toFun g := ⟨cutPerm μ p (g.1.val,g.2.val), (cutPerm_mem_column_iff μ p _).mpr ⟨g.1.property,g.2.property⟩⟩
  inj' a b h := by
    have hh := cutPerm_injective μ p (congrArg (fun c : C μ => c.val) h)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))

lemma column_glue_in_range (c : C μ)
    (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p))
    (he : tabloidOfPerm μ c.val = glueTabloid μ p t) : c ∈ Set.range (cutColumns μ p) := by
  let q := (cutEquiv μ p).symm.permCongr c.val⁻¹
  have hinr : Set.MapsTo q (Set.range Sum.inr) (Set.range Sum.inr) := by
    rintro x ⟨y,rfl⟩
    have hh := congrArg (fun v : Tabloid μ => v.val (southeastIn μ p y)) he
    change row (c.val⁻¹ (southeastIn μ p y)) = glueLabels μ p t (southeastIn μ p y) at hh
    rw [glueLabels_southeast] at hh
    have hc := (C μ).inv_mem c.property (southeastIn μ p y)
    rcases hq : q (Sum.inr y) with a | b
    · have hcell : c.val⁻¹ (southeastIn μ p y) = hookIn μ p a := by
        have h := congrArg (cutEquiv μ p) hq
        simpa only [q,Equiv.permCongr_apply,Equiv.symm_symm,
          Equiv.apply_symm_apply,cutEquiv_inr,cutEquiv_inl] using h
      rw [hcell,row_hookIn] at hh
      rw [hcell,col_hookIn,col_southeastIn] at hc
      have ha := hookPart_inHook μ p a
      omega
    · exact ⟨b,rfl⟩
  have hq := mem_sumCongrHom_range_of_perm_mapsTo_inl
    ((perm_mapsTo_inl_iff_mapsTo_inr q).mpr hinr)
  obtain ⟨g,hg⟩ := hq
  have hinv : cutPerm μ p g = c.val⁻¹ := by
    change (cutEquiv μ p).permCongr (sumCongrHom _ _ g) = _
    rw [hg]
    exact (cutEquiv μ p).permCongr.apply_symm_apply _
  have hg' : cutPerm μ p g⁻¹ = c.val := by rw [map_inv,hinv,inv_inv]
  have hgcol := (cutPerm_mem_column_iff μ p g⁻¹).mp (hg' ▸ c.property)
  refine ⟨(⟨g⁻¹.1,hgcol.1⟩,⟨g⁻¹.2,hgcol.2⟩),?_⟩
  apply Subtype.ext
  exact hg'

end

variable (μ : YoungDiagram) (p : ℕ)

lemma polytabloid_coefficient (t : Tabloid μ) :
    polytabloid μ t = ∑ c : C μ, if t = tabloidOfPerm μ c.val then signC μ c.val else 0 := by
  rw [polytabloid,columnAnti_apply]
  simp_rw [rep_basis,smul_tabloidOfPerm,mul_one]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,tabloidBasis,Pi.single_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

lemma cut_column_coefficient (a : C (hookPart μ p) × C (southeast μ p))
    (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    (if glueTabloid μ p t = tabloidOfPerm μ (cutColumns μ p a).val
      then signC μ (cutColumns μ p a).val else 0) =
    (if t.1 = tabloidOfPerm (hookPart μ p) a.1.val then signC (hookPart μ p) a.1.val else 0) *
    (if t.2 = tabloidOfPerm (southeast μ p) a.2.val then signC (southeast μ p) a.2.val else 0) := by
  change (if glueTabloid μ p t = tabloidOfPerm μ (cutPerm μ p (a.1.val,a.2.val))
    then signC μ (cutPerm μ p (a.1.val,a.2.val)) else 0) = _
  simp only [← glueTabloid_perm, (glueTabloid_injective μ p).eq_iff,Prod.ext_iff,signC_cutPerm]
  split_ifs <;> simp_all

theorem polytabloid_glue (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    polytabloid μ (glueTabloid μ p t) =
      polytabloid (hookPart μ p) t.1 * polytabloid (southeast μ p) t.2 := by
  rw [polytabloid_coefficient]
  let e := cutColumns μ p
  let f : C μ → ℂ := fun c =>
    if glueTabloid μ p t = tabloidOfPerm μ c.val then signC μ c.val else 0
  change ∑ c, f c = _
  have hs : ∑ c ∈ Finset.univ.image e, f c = ∑ c, f c := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    have hn : glueTabloid μ p t ≠ tabloidOfPerm μ c.val := by
      intro he
      obtain ⟨a,ha⟩ := column_glue_in_range μ p c t he.symm
      apply hc
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩
    exact ite_eq_right hn
  rw [← hs,Finset.sum_image e.injective.injOn]
  change (∑ a, if glueTabloid μ p t = tabloidOfPerm μ (cutColumns μ p a).val
    then signC μ (cutColumns μ p a).val else 0) = _
  simp_rw [cut_column_coefficient]
  rw [Fintype.sum_prod_type,polytabloid_coefficient,polytabloid_coefficient,Finset.sum_mul_sum]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) [ρ.IsIrreducible]

lemma span_orbit_eq_top (v : V) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun g : G => ρ g v)) = ⊤ := by
  let U : Subrepresentation ρ := {
    toSubmodule := Submodule.span ℂ (Set.range (fun g : G => ρ g v))
    apply_mem_toSubmodule := by
      intro g w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h,rfl⟩ := hx
        rw [← Module.End.mul_apply,← map_mul]
        exact Submodule.subset_span ⟨g*h,rfl⟩
      | zero => simpa only [map_zero] using Submodule.zero_mem _
      | add x y hx hy hx' hy' => simpa only [map_add] using Submodule.add_mem _ hx' hy'
      | smul c x hx hx' => simpa only [map_smul] using Submodule.smul_mem _ c hx' }
  have hvm : v ∈ U := by
    change v ∈ Submodule.span ℂ (Set.range (fun g : G => ρ g v))
    apply Submodule.subset_span
    exact ⟨1,by simp⟩
  rcases eq_bot_or_eq_top U with h | h
  · have hem : v ∈ (⊥ : Subrepresentation ρ) := h ▸ hvm
    have hv0 : v = 0 := hem
    exact (hv hv0).elim
  · exact congrArg Subrepresentation.toSubmodule h

end BinaryCoordinateSweeps.Irrep

end

end OAI
