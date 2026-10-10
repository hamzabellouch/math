import Mathlib

namespace OAI

/-! Vector lattices, lifted bases and unit triangular linear maps. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLattice
lemma span_eq_top_of_compact_quotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : AddSubgroup E)
    [CompactSpace (E ⧸ L)] : Submodule.span ℝ (L : Set E) = ⊤ := by
  let W := Submodule.span ℝ (L : Set E)
  let : IsClosed (W : Set E) := W.closed_of_finiteDimensional
  let q : E ⧸ L → E ⧸ W := Quotient.lift (fun x => W.mkQ x) (by
    intro x y h
    apply QuotientAddGroup.eq.mpr
    exact Submodule.subset_span (QuotientAddGroup.leftRel_apply.mp h))
  have hq : Continuous q := by
    apply (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr
    exact W.mkQ.continuous_of_finiteDimensional
  have hsurj : Surjective q := by
    intro x
    obtain ⟨y, rfl⟩ := W.mkQ_surjective x
    exact ⟨QuotientAddGroup.mk y, rfl⟩
  let : CompactSpace (E ⧸ W) := hsurj.compactSpace hq
  by_contra hW
  let : Nontrivial (E ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hW
  have hc : IsCompact (Set.univ : Set (E ⧸ W)) := isCompact_univ
  exact NoncompactSpace.noncompact_univ hc

theorem exists_vector_lattice_basis {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : AddSubgroup E)
    [DiscreteTopology L] [CompactSpace (E ⧸ L)] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ E),
      ∀ x, x ∈ L ↔ ∀ i, ∃ z : ℤ, b.equivFun x i = z := by
  let M := L.toIntSubmodule
  let : DiscreteTopology M := inferInstanceAs (DiscreteTopology L)
  let : IsZLattice ℝ M := ⟨span_eq_top_of_compact_quotient L⟩
  let : Module.Finite ℤ M := ZLattice.module_finite ℝ M
  let : Module.Free ℤ M := ZLattice.module_free ℝ M
  let b := (Module.finBasis ℤ M).ofZLatticeBasis ℝ
  refine ⟨Module.finrank ℤ M,b,?_⟩
  intro x
  change x ∈ M ↔ ∀ i, ∃ z : ℤ, b.equivFun x i = z
  conv_lhs => rw [← (Module.finBasis ℤ M).ofZLatticeBasis_span ℝ]
  convert b.mem_span_iff_repr_mem ℤ x using 1
  simp [Module.Basis.equivFun_apply,Set.mem_range,eq_comm]
end RawLattice

namespace RawLinearBasis
variable {E F : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
lemma basis_append_lifts {n k : ℕ} (C : Submodule ℝ E) (D : E →ₗ[ℝ] F)
    (hker : D.ker = C) (hDs : Surjective D)
    (bq : Module.Basis (Fin n) ℝ F) (bc : Module.Basis (Fin k) ℝ C)
    (w : Fin n → E) (hw : ∀ i, D (w i) = bq i) :
    ∃ b : Module.Basis (Fin (n+k)) ℝ E,
      (b : Fin (n+k) → E) = Fin.append w (fun i => (bc i).val) := by
  classical
  let v := Fin.append w (fun i => (bc i).val)
  have hDc (z : C) : D z.val = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact z.property
  have hli : LinearIndependent ℝ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    have hq := congrArg D ha
    simp only [v,Fin.sum_univ_add,Fin.append_left,Fin.append_right,map_add,map_sum,
      map_smul,hw,hDc,smul_zero,Finset.sum_const_zero,add_zero,map_zero] at hq
    have hqa := Fintype.linearIndependent_iff.mp bq.linearIndependent _ hq
    have hc : ∑ i : Fin k, a (Fin.natAdd n i) • bc i = 0 := by
      apply Subtype.val_injective
      have hvg := ha
      simp only [v,Fin.sum_univ_add,Fin.append_left,Fin.append_right,hqa,zero_smul,
        Finset.sum_const_zero,zero_add] at hvg
      simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero] using hvg
    have hca := Fintype.linearIndependent_iff.mp bc.linearIndependent _ hc
    intro i
    exact Fin.addCases hqa hca i
  have hdim : Fintype.card (Fin (n+k)) = Module.finrank ℝ E := by
    have h := D.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hDs,finrank_top,hker] at h
    have hq := (Module.finrank_eq_card_basis bq).symm
    have hc := (Module.finrank_eq_card_basis bc).symm
    simp only [Fintype.card_fin] at hq hc ⊢
    omega
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' v hli hdim,
    coe_basisOfLinearIndependentOfCardEqFinrank' v hli hdim⟩
end RawLinearBasis

namespace RawLinearBasis
variable {E F : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma basis_append_projection {n k : ℕ} (C : Submodule ℝ E) (D : E →ₗ[ℝ] F)
    (hker : D.ker = C) (bq : Module.Basis (Fin n) ℝ F) (bc : Module.Basis (Fin k) ℝ C)
    (w : Fin n → E) (hw : ∀ i, D (w i) = bq i)
    (b : Module.Basis (Fin (n+k)) ℝ E)
    (hb : (b : Fin (n+k) → E) = Fin.append w (fun i => (bc i).val))
    (x : E) (i : Fin n) : bq.equivFun (D x) i = b.equivFun x (Fin.castAdd k i) := by
  have hDc (z : C) : D z.val = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact z.property
  have he : bq.equivFun.toLinearMap.comp D =
      (LinearMap.funLeft ℝ ℝ (Fin.castAdd k)).comp b.equivFun.toLinearMap := by
    apply b.ext
    intro j
    refine Fin.addCases (fun l => ?_) (fun l => ?_) j
    · simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
      rw [show D (b (Fin.castAdd k l)) = bq l by rw [hb,Fin.append_left,hw]]
      ext r
      simp [LinearMap.funLeft_apply,Module.Basis.equivFun_apply,Module.Basis.repr_self,
        Finsupp.single_apply,Fin.castAdd_inj]
    · simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
      rw [show D (b (Fin.natAdd n l)) = 0 by rw [hb,Fin.append_right,hDc],map_zero]
      ext r
      simp [LinearMap.funLeft_apply,Module.Basis.equivFun_apply,Module.Basis.repr_self,
        Finsupp.single_apply]
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
  exact congrFun (LinearMap.congr_fun he x) i

end RawLinearBasis

namespace RawLinearBasis
variable {E F : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

def Triangular {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (A : E →ₗ[ℝ] E) : Prop :=
  ∀ i j : Fin n, j ≤ i → b.equivFun (A (b i) - b i) j = 0

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma triangular_append {n k : ℕ} (C : Submodule ℝ E) (D : E →ₗ[ℝ] F)
    (hker : D.ker = C) (bq : Module.Basis (Fin n) ℝ F) (bc : Module.Basis (Fin k) ℝ C)
    (w : Fin n → E) (hw : ∀ i, D (w i) = bq i)
    (b : Module.Basis (Fin (n+k)) ℝ E)
    (hb : (b : Fin (n+k) → E) = Fin.append w (fun i => (bc i).val))
    (A : E →ₗ[ℝ] E) (Aq : F →ₗ[ℝ] F)
    (hA : ∀ x, D (A x) = Aq (D x)) (hAc : ∀ z : C, A z.val = z.val)
    (htri : Triangular bq Aq) : Triangular b A := by
  intro i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i
  · intro j
    refine Fin.addCases (fun r => ?_) (fun r => ?_) j
    · intro hri
      rw [← basis_append_projection C D hker bq bc w hw b hb]
      have hDb : D (b (Fin.castAdd k l)) = bq l := by rw [hb,Fin.append_left,hw]
      rw [map_sub,hA,hDb]
      apply htri l r
      exact hri
    · intro hri
      have hv : (Fin.natAdd n r).val ≤ (Fin.castAdd k l).val := hri
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
  · intro j hji
    have he : A (b (Fin.natAdd n l)) = b (Fin.natAdd n l) := by
      rw [hb,Fin.append_right,hAc]
    rw [he,sub_self,map_zero]
    rfl

end RawLinearBasis

namespace RawTriangular
lemma injective_of_unit_triangular {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hL : ∀ i j, j ≤ i → L (Pi.single i 1) j = if i = j then 1 else 0) :
    Function.Injective L := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hex : x = ∑ i : Fin n, (x i) • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  have hz : ∀ j : Fin n, x j = 0 := by
    intro j
    have H : ∀ k : ℕ, ∀ j : Fin n, j.val = k → x j = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro j hj
        have hh := congrFun hx j
        rw [hex,map_sum] at hh
        have he : (∑ i : Fin n, L ((x i) • Pi.single i 1) j) = x j := by
          rw [Finset.sum_eq_single j]
          · simp [hL j j le_rfl]
          · intro i _ hij
            by_cases hil : i < j
            · rw [ih i.val (by simpa [← hj] using hil) i rfl]
              simp
            · simp [map_smul,Pi.smul_apply,hL i j (le_of_not_gt hil),hij]
          · simp
        simp only [Finset.sum_apply,Pi.zero_apply] at hh
        rwa [he] at hh
    exact H j.val j rfl
  exact funext hz
lemma bijective_of_unit_triangular {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hL : ∀ i j, j ≤ i → L (Pi.single i 1) j = if i = j then 1 else 0) :
    Function.Bijective L := by
  have h := injective_of_unit_triangular L hL
  exact ⟨h, (LinearMap.injective_iff_surjective).mp h⟩
end RawTriangular

namespace RawTriangular
lemma row_of_unit_triangular {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hL : ∀ i j, j ≤ i → L (Pi.single i 1) j = if i = j then 1 else 0)
    (x : Fin n → ℝ) (j : Fin n) :
    L x j = x j + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j), x i * L (Pi.single i 1) j := by
  classical
  have hex : x = ∑ i : Fin n, (x i) • Pi.single i (1 : ℝ) := by
    ext k; simp [Finset.sum_apply,Pi.single_apply]
  calc
    L x j = ∑ i : Fin n, x i * L (Pi.single i 1) j := by
      conv_lhs => rw [hex,map_sum]
      simp [map_smul,Finset.sum_apply,Pi.smul_apply]
    _ = (∑ i : Fin n, if i = j then x j else 0) +
        ∑ i : Fin n, if i < j then x i * L (Pi.single i 1) j else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases he : i = j
      · subst i; simp [hL j j le_rfl]
      · by_cases hi : i < j
        · simp [he,hi]
        · simp [he,hi,hL i j (le_of_not_gt hi)]
    _ = _ := by simp [Finset.sum_filter]
end RawTriangular

namespace RawTriangular
lemma sum_lower {n : ℕ} (j : Fin n) (f : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j), f i =
      ∑ k : Fin j.val, f ⟨k.val,lt_trans k.isLt j.isLt⟩ := by
  classical
  apply Finset.sum_bij (fun i hi => (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin j.val))
  · intro i hi; exact Finset.mem_univ _
  · intro i hi k hk he
    exact Fin.ext (congrArg (fun z : Fin j.val => z.val) he)
  · intro k hk
    refine ⟨⟨k.val,lt_trans k.isLt j.isLt⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,k.isLt⟩,rfl⟩
  · intro i hi; rfl
end RawTriangular

namespace RawLattice
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
lemma span_subtype_eq_top (K : Submodule ℝ E) (A : Set E) (hA : A ⊆ K)
    (hspan : Submodule.span ℝ A = K) :
    Submodule.span ℝ ((Subtype.val : K → E) ⁻¹' A) = ⊤ := by
  apply Submodule.map_injective_of_injective K.injective_subtype
  rw [Submodule.map_span,Submodule.map_top,Submodule.range_subtype]
  have he : (K.subtype : K → E) '' ((Subtype.val : K → E) ⁻¹' A) = A := by
    apply Set.image_preimage_eq_iff.mpr
    intro x hx
    exact ⟨⟨x,hA hx⟩,rfl⟩
  rw [he,hspan]

lemma compact_quotient_of_span (L : AddSubgroup E) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set E) = ⊤) : CompactSpace (E ⧸ L) := by
  let M := L.toIntSubmodule
  let : DiscreteTopology M := inferInstanceAs (DiscreteTopology L)
  let : IsZLattice ℝ M := ⟨hspan⟩
  have H := IsZLattice.isCompact_range_of_periodic M
    (QuotientAddGroup.mk : E → E ⧸ L) QuotientAddGroup.continuous_mk (by
      intro z w hw
      apply QuotientAddGroup.eq.mpr
      change -(z+w)+z ∈ L
      convert L.neg_mem hw using 1; abel)
  rw [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at H
  exact ⟨H⟩

lemma exists_vector_lattice_basis_of_span (L : AddSubgroup E) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set E) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ E),
      ∀ x, x ∈ L ↔ ∀ i, ∃ z : ℤ, b.equivFun x i = z := by
  let M := L.toIntSubmodule
  let : DiscreteTopology M := inferInstanceAs (DiscreteTopology L)
  let : IsZLattice ℝ M := ⟨hspan⟩
  let : Module.Finite ℤ M := ZLattice.module_finite ℝ M
  let : Module.Free ℤ M := ZLattice.module_free ℝ M
  let b := (Module.finBasis ℤ M).ofZLatticeBasis ℝ
  refine ⟨Module.finrank ℤ M,b,?_⟩
  intro x
  change x ∈ M ↔ ∀ i, ∃ z : ℤ, b.equivFun x i = z
  conv_lhs => rw [← (Module.finBasis ℤ M).ofZLatticeBasis_span ℝ]
  convert b.mem_span_iff_repr_mem ℤ x using 1
  simp [Module.Basis.equivFun_apply,Set.mem_range,eq_comm]
end RawLattice
end

end OAI
