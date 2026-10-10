import Mathlib
import OAI.Geometry.Borsuk.Simplicial.Maps

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V : Type*} [DecidableEq V]
section Equivariance
variable (K : PreAbstractSimplicialComplex V) (e : V ≃ V)
    (he : ∀ s, s ∈ K ↔ s.image e ∈ K)

noncomputable def faceEquiv : {s : Finset V // s ∈ K} ≃ {s : Finset V // s ∈ K} where
  toFun s := ⟨s.val.image e, (he s.val).mp s.property⟩
  invFun s := ⟨s.val.image e.symm, (he _).mpr (by simp [Finset.image_image, s.property])⟩
  left_inv s := Subtype.ext (by simp [Finset.image_image])
  right_inv s := Subtype.ext (by simp [Finset.image_image])

lemma faceEquiv_involutive (hi : Function.Involutive e) :
    Function.Involutive (faceEquiv K e he) := by
  intro s
  apply Subtype.ext
  change (s.val.image e).image e = s.val
  rw [Finset.image_image]
  have h : e ∘ e = id := funext hi
  rw [h, Finset.image_id]

lemma faceEquiv_free (hf : ∀ s ∈ K, s.image e ≠ s) :
    ∀ s, faceEquiv K e he s ≠ s := by
  intro s hh
  exact hf s.val s.property (congrArg Subtype.val hh)

lemma mapChains_equiv :
    mapChains K K e = (Finsupp.domLCongr (faceEquiv K e he)).toLinearMap := by
  apply Finsupp.lhom_ext
  intro s r
  have hc : (s.val.image e).card = s.val.card := Finset.card_image_iff.mpr e.injective.injOn
  simp only [mapChains, Finsupp.linearCombination_single, mapSimplex, ite_eq_left hc,
    simplex_of_mem K ((he s.val).mp s.property), LinearEquiv.coe_toLinearMap,
    Finsupp.domLCongr_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

end Equivariance

section Cone

noncomputable def cone (K : PreAbstractSimplicialComplex V) (a : V) : Chain K →ₗ[F₂] Chain K :=
  Finsupp.linearCombination F₂ (fun s => if a ∈ s.val then 0 else simplex K (insert a s.val))

lemma cone_simplex (K : PreAbstractSimplicialComplex V) (a : V) {s : Finset V} (hs : s ∈ K) :
    cone K a (simplex K s) = if a ∈ s then 0 else simplex K (insert a s) := by
  simp [simplex_of_mem K hs, cone, Finsupp.linearCombination_single]

lemma cone_boundary_simplex (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) (ha : a ∉ s) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases hc : s.card = 1
  · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
    have hab : a ≠ b := by simpa using ha
    have hs' : ({a} : Finset V) ∈ K :=
      (K.isRelLowerSet_faces hinsert).2 (by simp) (Finset.singleton_nonempty a)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      boundary_simplex K hs, augmentation_simplex K hs]
    simp [ha, Finset.erase_insert_of_ne hab]
  · have hn : s.Nonempty := (K.isRelLowerSet_faces hs).1
    have hc' : 2 ≤ s.card := by have := hn.card_pos; omega
    have he (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
      omega
    have heK (b : V) (hb : b ∈ s) : s.erase b ∈ K :=
      (K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (he b hb)
    rw [cone_simplex K a hs, ite_eq_right ha, boundary_simplex K hinsert,
      augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero,
      boundary_simplex K hs, map_sum, Finset.sum_insert ha, Finset.erase_insert ha]
    apply congrArg (fun z => simplex K s + z)
    apply Finset.sum_congr rfl
    intro b hb
    have hab : a ≠ b := by intro hh; subst b; exact ha hb
    have hn : a ∉ s.erase b := fun hh => ha (Finset.mem_of_mem_erase hh)
    rw [cone_simplex K a (heK b hb), ite_eq_right hn, Finset.erase_insert_of_ne hab]

lemma cone_boundary_simplex_all (K : PreAbstractSimplicialComplex V) (a : V)
    {s : Finset V} (hs : s ∈ K) (hinsert : insert a s ∈ K) :
    boundary K (cone K a (simplex K s)) = simplex K s + cone K a (boundary K (simplex K s)) +
      augmentation K (simplex K s) • simplex K {a} := by
  classical
  by_cases ha : a ∈ s
  · by_cases hc : s.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hc
      have hab : a = b := Finset.mem_singleton.mp ha
      subst b
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, boundary_simplex K hs,
        augmentation_simplex K hs]
      simp [chain_add_self]
    · have hcn (b : V) (hb : b ∈ s) : (s.erase b).Nonempty := by
        have hn := (K.isRelLowerSet_faces hs).1.card_pos
        rw [← Finset.card_pos, Finset.card_erase_of_mem hb]
        omega
      have hcon : cone K a (boundary K (simplex K s)) = simplex K s := by
        rw [boundary_simplex K hs, map_sum]
        rw [Finset.sum_eq_single a]
        · rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset a s) (hcn a ha))]
          simp [Finset.insert_erase ha]
        · intro b hb hba
          rw [cone_simplex K a ((K.isRelLowerSet_faces hs).2 (Finset.erase_subset b s) (hcn b hb))]
          simp [Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩]
        · exact fun hn => False.elim (hn ha)
      rw [cone_simplex K a hs, ite_eq_left ha, map_zero, hcon,
        augmentation_simplex K hs, ite_eq_right hc, zero_smul, add_zero, chain_add_self]
  · exact cone_boundary_simplex K a hs hinsert ha

omit [DecidableEq V] in
lemma chain_eq_sum (K : PreAbstractSimplicialComplex V) (c : Chain K) :
    c = ∑ s ∈ c.support, c s • simplex K s.val := by
  conv_lhs => rw [← c.sum_single]
  simp [Finsupp.sum, simplex_of_mem K, Finsupp.smul_single]

lemma cone_boundary (K : PreAbstractSimplicialComplex V) (a : V) (c : Chain K)
    (hc : ∀ s ∈ c.support, insert a s.val ∈ K) :
    boundary K (cone K a c) = c + cone K a (boundary K c) +
      augmentation K c • simplex K {a} := by
  classical
  conv_lhs => rw [chain_eq_sum K c]
  rw [map_sum, map_sum]
  have he (s : { s : Finset V // s ∈ K }) (hs : s ∈ c.support) :
      boundary K (cone K a (c s • simplex K s.val)) =
        c s • simplex K s.val + cone K a (boundary K (c s • simplex K s.val)) +
        augmentation K (c s • simplex K s.val) • simplex K {a} := by
    rw [map_smul, map_smul, cone_boundary_simplex_all K a s.property (hc s hs)]
    simp only [smul_add, map_smul, smul_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← map_sum, ← map_sum, ← Finset.sum_smul, ← map_sum, ← chain_eq_sum K c]

end Cone

end BorsukNine.SimplicialChains

end OAI
