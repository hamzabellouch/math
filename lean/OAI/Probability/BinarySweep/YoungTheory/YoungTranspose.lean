import Mathlib
import OAI.Probability.BinarySweep.Representations.IrrepTransport
import OAI.Probability.BinarySweep.YoungTheory.YoungInducedMap

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]

def signTwist (ρ : Representation ℂ (G μ) V) : Representation ℂ (G μ) V where
  toFun g := signC μ g • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    rw [mul_comm]

def signTwistSubrep (ρ : Representation ℂ (G μ) V) :
    Subrepresentation ρ ≃o Subrepresentation (signTwist μ ρ) where
  toFun U := ⟨U.toSubmodule, fun g v hv => U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hv)⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.toSubmodule.smul_mem (signC μ g) (U.apply_mem_toSubmodule g hv)
    change signC μ g • (signC μ g • ρ g v) ∈ U.toSubmodule at h
    rwa [smul_smul, signC_sq, one_smul] at h⟩
  left_inv U := rfl
  right_inv U := rfl
  map_rel_iff' := Iff.rfl

instance signTwist_irreducible {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G μ) V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (k := ℂ) (G := G μ) (V := V) (signTwist μ ρ) :=
  (signTwistSubrep μ ρ).isSimpleOrder_iff.mp inferInstance

def transposeCells : Cell μ ≃ Cell μ.transpose where
  toFun x := ⟨x.val.swap, YoungDiagram.mem_transpose.mpr (by simp)⟩
  invFun x := ⟨x.val.swap, YoungDiagram.mem_transpose.mp x.property⟩
  left_inv x := by apply Subtype.ext; exact Prod.swap_swap _
  right_inv x := by apply Subtype.ext; exact Prod.swap_swap _

lemma transpose_sign (g : G μ) : signC μ.transpose ((transposeCells μ).permCongr g) =
    signC μ g := by rw [signC_eq, signC_eq, Equiv.Perm.sign_permCongr]

lemma transpose_row_to_col (r : rowStabilizer μ) :
    (transposeCells μ).permCongr r.val ∈ colStabilizer μ.transpose := by
  intro x
  exact r.property ((transposeCells μ).symm x)

lemma transpose_col_to_row (c : C μ) :
    (transposeCells μ).permCongr c.val ∈ rowStabilizer μ.transpose := by
  intro x
  exact c.property ((transposeCells μ).symm x)

def transposeRep : Representation ℂ (G μ) (SpechtSpace μ.transpose) :=
  (spechtRep μ.transpose).comp (transposeCells μ).permCongrHom.toMonoidHom

instance : Representation.IsIrreducible (k := ℂ) (G := G μ)
    (V := SpechtSpace μ.transpose) (transposeRep μ) :=
  Irrep.irreducible_comp_equiv _ _

lemma transposePoly_row_fixed (r : rowStabilizer μ) :
    signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) r.val (spechtPoly μ.transpose) = spechtPoly μ.transpose := by
  change signC μ r.val • spechtRep μ.transpose ((transposeCells μ).permCongr r.val)
    (spechtPoly μ.transpose) = _
  rw [spechtPoly_column μ.transpose ⟨_,transpose_row_to_col μ r⟩,
    transpose_sign, smul_smul, signC_sq, one_smul]

def transposeMap : SpechtSpace μ →ₗ[ℂ] SpechtSpace μ.transpose :=
  (fromTabloid μ (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (spechtPoly μ.transpose)).comp (spechtInclude μ)

lemma transposeMap_intertwines (g : G μ) (v : SpechtSpace μ) :
    transposeMap μ (spechtRep μ g v) =
      signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) g (transposeMap μ v) := by
  simp only [transposeMap, LinearMap.comp_apply, spechtInclude_rep]
  exact fromTabloid_intertwines μ _ _ (transposePoly_row_fixed μ) g _

lemma row_fixes_base_evaluation (r : rowStabilizer μ) (v : Tabloid μ → ℂ) :
    tabloidRepresentation μ r.val v (tabloidOfPerm μ 1) = v (tabloidOfPerm μ 1) := by
  change v (r.val⁻¹ • tabloidOfPerm μ 1) = _
  rw [smul_tabloidOfPerm, mul_one]
  congr 1
  exact (tabloidOfPerm_eq_iff μ _ _).mpr (by simp [r.property])

lemma transposeMap_poly_evaluation : spechtInclude μ.transpose
    (transposeMap μ (spechtPoly μ)) (tabloidOfPerm μ.transpose 1) = Fintype.card (C μ) := by
  change spechtInclude μ.transpose
    (fromTabloid μ (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (spechtPoly μ.transpose)
      (spechtInclude μ (spechtPoly μ))) _ = _
  rw [spechtInclude_poly, polytabloid, columnAnti_apply, map_sum]
  simp only [map_smul, rep_basis, smul_tabloidOfPerm, mul_one, fromTabloid_basis]
  simp_rw [tabloidVector_eq μ _ _ (transposePoly_row_fixed μ)]
  have ht (c : C μ) : signC μ c.val • signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ) c.val
      (spechtPoly μ.transpose) = spechtRep μ.transpose ((transposeCells μ).permCongr c.val)
        (spechtPoly μ.transpose) := by
    change signC μ c.val • (signC μ c.val •
      spechtRep μ.transpose ((transposeCells μ).permCongr c.val) (spechtPoly μ.transpose)) = _
    rw [smul_smul, signC_sq, one_smul]
  simp_rw [ht]
  rw [map_sum]
  simp only [Finset.sum_apply, spechtInclude_rep, spechtInclude_poly]
  have he (c : C μ) : tabloidRepresentation μ.transpose ((transposeCells μ).permCongr c.val)
      (polytabloid μ.transpose) (tabloidOfPerm μ.transpose 1) = 1 := by
    rw [row_fixes_base_evaluation μ.transpose ⟨_,transpose_col_to_row μ c⟩,
      polytabloid_base]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem specht_transpose_sign : Nonempty (Representation.Equiv (spechtRep μ)
    (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ))) := by
  let f := (transposeMap μ).intertwiningMap_of_isIntertwiningMap
    (spechtRep μ) (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) (transposeMap_intertwines μ)
  have hn : f ≠ 0 := by
    intro h
    have hz : transposeMap μ (spechtPoly μ) = 0 := by
      exact congrArg (fun g : Representation.IntertwiningMap (spechtRep μ)
        (signTwist (V := SpechtSpace μ.transpose) μ (transposeRep μ)) => g (spechtPoly μ)) h
    have he := transposeMap_poly_evaluation μ
    rw [hz, map_zero, Pi.zero_apply] at he
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card (C μ) : ℂ) ≠ 0) he.symm
  have : (signTwist μ (transposeRep μ)).IsIrreducible :=
    signTwist_irreducible μ (transposeRep μ)
  have hf := (Representation.IsIrreducible.bijective_or_eq_zero (k := ℂ) (G := G μ)
    (V := SpechtSpace μ) (W := SpechtSpace μ.transpose) f).resolve_right hn
  exact ⟨f.ofBijective hf⟩

lemma specht_finrank_transpose : Module.finrank ℂ (SpechtSpace μ) =
    Module.finrank ℂ (SpechtSpace μ.transpose) := by
  obtain ⟨e⟩ := specht_transpose_sign μ
  exact e.toLinearEquiv.finrank_eq

end BinaryCoordinateSweeps.Young

end

end OAI
