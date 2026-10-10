import OAI.Probability.SignedSweeps.Irreducibility

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {G E : Type*} [Group G] [Fintype G] [AddCommGroup E] [Module ℝ E]

def realGroupAverage (ρ : Representation ℝ G E) : E →ₗ[ℝ] E :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g, ρ g

lemma realGroupAverage_invariant (ρ : Representation ℝ G E) (g : G) (x : E) :
    ρ g (realGroupAverage ρ x) = realGroupAverage ρ x := by
  classical
  simp only [realGroupAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

lemma realGroupAverage_fixed (ρ : Representation ℝ G E) (x : E)
    (hx : ∀ g, ρ g x = x) : realGroupAverage ρ x = x := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [realGroupAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx, Finset.sum_const,
    Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma realGroupAverage_apply_action (ρ : Representation ℝ G E) (g : G) (x : E) :
    realGroupAverage ρ (ρ g x) = realGroupAverage ρ x := by
  classical
  simp only [realGroupAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    ← Module.End.mul_apply, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {G E : Type*} [Group G] [AddCommGroup E] [Module ℝ E]

def fairAction (ρ : Representation ℝ G E) (g : G) : E →ₗ[ℝ] E :=
  (1 / 2 : ℝ) • (1 + ρ g)

lemma fairAction_apply (ρ : Representation ℝ G E) (g : G) (x : E) :
    fairAction ρ g x = (1 / 2 : ℝ) • (x + ρ g x) := rfl

lemma action_absorbs_fairAction (ρ : Representation ℝ G E) (g : G) (hg : g * g = 1) :
    ρ g * fairAction ρ g = fairAction ρ g := by
  ext x
  have hh : ρ g (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, hg, map_one, Module.End.one_apply]
  simp only [Module.End.mul_apply, fairAction_apply, map_smul, map_add, hh, add_comm]

lemma fairAction_idempotent (ρ : Representation ℝ G E) (g : G) (hg : g * g = 1) :
    IsIdempotentElem (fairAction ρ g) := by
  have he := action_absorbs_fairAction ρ g hg
  change fairAction ρ g * fairAction ρ g = fairAction ρ g
  conv_lhs => lhs; unfold fairAction
  rw [smul_mul_assoc, add_mul, one_mul, he]
  ext x
  simp only [LinearMap.smul_apply, LinearMap.add_apply]
  module

lemma fairActions_commute (ρ : Representation ℝ G E) {g h : G} (hgh : Commute g h) :
    Commute (fairAction ρ g) (fairAction ρ h) := by
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (Commute.one_left _)
  apply Commute.add_right (Commute.one_right _)
  exact hgh.map ρ

def realVectorStabilizer (ρ : Representation ℝ G E) (x : E) : Subgroup G where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) x = x
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g⁻¹ x = x
    have hh := congrArg (fun y => ρ g⁻¹ y) hg
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact hh.symm

lemma fairAction_prod_fixed (ρ : Representation ℝ G E) (L : List G)
    (hL : ∀ g ∈ L, g * g = 1) (hcomm : ∀ g ∈ L, ∀ h ∈ L, Commute g h)
    {g : G} (hg : g ∈ L) :
    ρ g * (L.map (fairAction ρ)).prod = (L.map (fairAction ρ)).prod := by
  have hf : fairAction ρ g * (L.map (fairAction ρ)).prod = (L.map (fairAction ρ)).prod := by
    apply prod_absorbs_commuting_idempotent
    · exact List.mem_map.mpr ⟨g, hg, rfl⟩
    · intro A hA
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hA
      exact fairActions_commute ρ (hcomm g hg h hh)
    · exact fairAction_idempotent ρ g (hL g hg)
  rw [← hf, ← mul_assoc, action_absorbs_fairAction ρ g (hL g hg)]

lemma realGroupAverage_fairAction [Fintype G] (ρ : Representation ℝ G E) (g : G) (x : E) :
    realGroupAverage ρ (fairAction ρ g x) = realGroupAverage ρ x := by
  rw [fairAction_apply, map_smul, map_add, realGroupAverage_apply_action]
  module

lemma realGroupAverage_eq_fairAction_prod [Fintype G] (ρ : Representation ℝ G E) (L : List G)
    (hL : ∀ g ∈ L, g * g = 1) (hcomm : ∀ g ∈ L, ∀ h ∈ L, Commute g h)
    (hgen : ∀ H : Subgroup G, (∀ g ∈ L, g ∈ H) → H = ⊤) :
    realGroupAverage ρ = (L.map (fairAction ρ)).prod := by
  have ha (L : List G) (x : E) :
      realGroupAverage ρ ((L.map (fairAction ρ)).prod x) = realGroupAverage ρ x := by
    induction L with
    | nil => simp
    | cons g L ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [realGroupAverage_fairAction, ih]
  ext x
  rw [← ha L x]
  apply realGroupAverage_fixed
  have hg := hgen (realVectorStabilizer ρ ((L.map (fairAction ρ)).prod x)) (by
    intro g hg
    exact congrArg (fun f : E →ₗ[ℝ] E => f x) (fairAction_prod_fixed ρ L hL hcomm hg))
  intro g
  exact (show g ∈ realVectorStabilizer ρ ((L.map (fairAction ρ)).prod x) from hg ▸ Subgroup.mem_top _)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A C : Type*} [Fintype A] [DecidableEq A]

lemma fiberSubgroup_le_of_swaps (f : A → C) (H : Subgroup (Equiv.Perm A))
    (hH : ∀ a b, f a = f b → Equiv.swap a b ∈ H) : fiberSubgroup f ≤ H := by
  intro g hg
  have haux : ∀ n : ℕ, ∀ g : Equiv.Perm A, g.support.card = n → g ∈ fiberSubgroup f → g ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hn hg
      by_cases he : g = 1
      · subst g; exact H.one_mem
      obtain ⟨a, ha⟩ : ∃ a, g a ≠ a := by
        by_contra hf
        push Not at hf
        exact he (Equiv.ext hf)
      let t := Equiv.swap a (g a) * g
      have hs : Equiv.swap a (g a) ∈ fiberSubgroup f := swap_mem_fiberSubgroup f (hg a).symm
      have ht : t ∈ fiberSubgroup f := (fiberSubgroup f).mul_mem hs hg
      have hsub : t.support ⊂ g.support := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨fun y hy => (Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne hy).1, ?_⟩
        intro heq
        have ha' : a ∈ t.support := heq ▸ Equiv.Perm.mem_support.mpr ha
        exact (Equiv.Perm.mem_support_swap_mul_imp_mem_support_ne ha').2 rfl
      have hlt : t.support.card < n := (Finset.card_lt_card hsub).trans_eq hn
      have htH := ih t.support.card hlt t rfl ht
      have hsH := hH a (g a) (hg a).symm
      have hx := H.mul_mem hsH htH
      simpa only [t, ← mul_assoc, Equiv.swap_mul_self, one_mul] using hx
  exact haux _ g rfl hg

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma flipPermutation_ne (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    flipPermutation d i x ≠ x := by
  intro h
  have hi := congrFun (congrArg (positionsEquiv d).symm h) i
  simp only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply, binaryFlip_apply,
    Function.update_self] at hi
  generalize (positionsEquiv d).symm x i = a at hi
  fin_cases a <;> simp at hi

lemma coordinate_edge_swap_mem (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    Equiv.swap x (flipPermutation d i x) ∈ coordinateSubgroup d i := by
  apply swap_mem_fiberSubgroup
  exact (flipPermutation_mem d i x).symm

lemma coordinateSubgroup_le_of_edge_swaps (d : ℕ) (i : Fin d)
    (H : Subgroup (SymmetricGroup (2 ^ d)))
    (hH : ∀ x, Equiv.swap x (flipPermutation d i x) ∈ H) : coordinateSubgroup d i ≤ H := by
  apply fiberSubgroup_le_of_swaps
  intro x y hxy
  rcases binary_eq_or_flip i ((positionsEquiv d).symm x) ((positionsEquiv d).symm y)
      (fun j hj => (congrFun hxy ⟨j, hj⟩).symm) with he | he
  · have hy : y = x := (positionsEquiv d).symm.injective he
    rw [hy, Equiv.swap_self]
    exact H.one_mem
  · have hy : y = flipPermutation d i x := by
      apply (positionsEquiv d).symm.injective
      simpa only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply] using he
    rw [hy]; exact hH x

lemma coordinate_edge_swaps_commute (d : ℕ) (i : Fin d) (x y : Fin (2 ^ d)) :
    Commute (Equiv.swap x (flipPermutation d i x)) (Equiv.swap y (flipPermutation d i y)) := by
  by_cases hy : y = x
  · subst y; exact Commute.refl _
  by_cases hf : y = flipPermutation d i x
  · subst y
    rw [flipPermutation_twice, Equiv.swap_comm (flipPermutation d i x) x]
  have hxy' : x ≠ flipPermutation d i y := by
    intro he
    have he' := congrArg (flipPermutation d i) he
    rw [flipPermutation_twice] at he'
    exact hf he'.symm
  apply Equiv.Perm.Disjoint.commute
  apply Equiv.Perm.disjoint_swap_swap
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_false_eq_true,
    not_or, List.nodup_nil, and_true]
  exact ⟨⟨(flipPermutation_ne d i x).symm, Ne.symm hy, hxy'⟩,
    ⟨⟨Ne.symm hf, fun h => hy ((flipPermutation d i).injective h).symm⟩,
      (flipPermutation_ne d i y).symm⟩⟩

lemma coordinate_real_average_as_switches {E : Type*} [AddCommGroup E] [Module ℝ E]
    (d : ℕ) (i : Fin d) (ρ : Representation ℝ (SymmetricGroup (2 ^ d)) E) :
    realGroupAverage (ρ.comp (coordinateSubgroup d i).subtype) =
      ((List.ofFn fun x : Fin (2 ^ d) => fairAction ρ
        (Equiv.swap x (flipPermutation d i x)))).prod := by
  let L : List (coordinateSubgroup d i) := List.ofFn (fun x =>
    ⟨Equiv.swap x (flipPermutation d i x), coordinate_edge_swap_mem d i x⟩)
  have hl := realGroupAverage_eq_fairAction_prod (ρ.comp (coordinateSubgroup d i).subtype) L
  suffices he : realGroupAverage (ρ.comp (coordinateSubgroup d i).subtype) =
      (L.map (fairAction (ρ.comp (coordinateSubgroup d i).subtype))).prod by
    simpa only [L, List.map_ofFn, Function.comp_def, fairAction, MonoidHom.comp_apply, Subgroup.subtype_apply] using he
  apply hl
  · intro g hg
    obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hg
    apply Subtype.ext
    exact Equiv.swap_mul_self _ _
  · intro g hg h hh
    obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hg
    obtain ⟨y, rfl⟩ := List.mem_ofFn.mp hh
    apply Subtype.ext
    exact coordinate_edge_swaps_commute d i x y
  · intro H hH
    have hr : coordinateSubgroup d i ≤ H.map (coordinateSubgroup d i).subtype := by
      apply coordinateSubgroup_le_of_edge_swaps
      intro x
      exact ⟨⟨_, coordinate_edge_swap_mem d i x⟩, hH _ (List.mem_ofFn.mpr ⟨x, rfl⟩), rfl⟩
    apply top_unique
    intro g hg
    obtain ⟨q, hq, he⟩ := hr g.property
    exact (Subtype.ext he : q = g) ▸ hq

end SignedSweeps
end

end OAI
