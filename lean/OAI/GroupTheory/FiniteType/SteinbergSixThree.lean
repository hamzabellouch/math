import Mathlib
import OAI.GroupTheory.FiniteType.CompressedSplittings

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace Steinberg
section
variable {R : Type*} [Ring R]

lemma six_three (i j : SixIndices) (_hij : i≠j) : ∃ k, i≠k ∧ j≠k := by
  let a : SixIndices := Sum.inl (Sum.inl 0)
  let b : SixIndices := Sum.inl (Sum.inl 1)
  let c : SixIndices := Sum.inr 0
  have hab : a≠b := by decide
  have hac : a≠c := by decide
  have hbc : b≠c := by decide
  by_cases hia : i=a
  · by_cases hjb : j=b
    · exact ⟨c,by rw [hia]; exact hac,by rw [hjb]; exact hbc⟩
    · exact ⟨b,by rw [hia]; exact hab,hjb⟩
  · by_cases hja : j=a
    · by_cases hib : i=b
      · exact ⟨c,by rw [hib]; exact hbc,by rw [hja]; exact hac⟩
      · exact ⟨b,hib,by rw [hja]; exact hab⟩
    · exact ⟨a,hia,hja⟩

lemma exchange_coefficient_kernel_central {φ : R →ₙ+* R}
    (E : CompressedSplittings.Idempotent φ) (D : RingExchange.Data R) (hD : D.E=E.val)
    (w : Group SixIndices R) (hw : pi w=1) (v : Group SixIndices R) :
    Commute (map E.coefficient w) v :=
  flip_kernel_central D E.coefficient (by simpa [hD] using E.coefficient_left)
    (by simpa [hD] using E.coefficient_right) w hw v

lemma exchange_coefficient_kernel_equal {φ : R →ₙ+* R}
    (E F : CompressedSplittings.Idempotent φ) (D : RingExchange.Data R)
    (hE : D.E=E.val) (hF : D.F=F.val)
    (hc : ∀ a, Commute D.unit.val (φ a))
    (w : Group SixIndices R) (hw : pi w=1) : map E.coefficient w=map F.coefficient w := by
  apply Eq.symm
  apply central_conjugated_coefficients D.unit (by rfl) E.coefficient F.coefficient
  · exact E.coefficient_conjugate F D.unit hc (by simpa [hE,hF] using D.conjugates)
  · exact exchange_coefficient_kernel_central E D hE w hw

theorem binary_kernel_annihilation_six (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (w : Group SixIndices R) (hw : pi w=1) : map φ w=1 := by
  have h₀ := exchange_coefficient_kernel_equal (D.projection 0) (D.projection 1)
    D.firstExchange rfl rfl D.firstExchange_commutes w hw
  have h₀₀ := exchange_coefficient_kernel_equal (D.doubleProjection 0 0) (D.projection 1)
    (D.secondExchange 0) rfl rfl (D.secondExchange_commutes 0) w hw
  have h₀₁ := exchange_coefficient_kernel_equal (D.doubleProjection 0 1) (D.projection 1)
    (D.secondExchange 1) rfl rfl (D.secondExchange_commutes 1) w hw
  have hsubrev : (D.doubleProjection 0 1).val*(D.doubleProjection 0 0).val=0 := by
    have hd : (D.d 1*D.d 0)*(D.s 0*D.s 0)=0 := by
      calc (D.d 1*D.d 0)*(D.s 0*D.s 0)=D.d 1*(D.d 0*D.s 0)*D.s 0 := by simp only [mul_assoc]
           _ = 0 := by rw [D.ds_same,D.d_right,D.ds_cross 1 0 (by decide)]
    change ((D.s 0*D.s 1)*(D.d 1*D.d 0))*((D.s 0*D.s 0)*(D.d 0*D.d 0))=0
    rw [mul_assoc,← mul_assoc (D.d 1*D.d 0),hd,zero_mul,mul_zero]
  have hsub := CompressedSplittings.Idempotent.steinberg_split six_three
    (D.projection 0) (D.doubleProjection 0 0) (D.doubleProjection 0 1)
    D.subsplit D.subcross hsubrev w
  rw [h₀,h₀₀,h₀₁] at hsub
  have h₁ : map (D.projection 1).coefficient w=1 :=
    mul_left_cancel (hsub.symm.trans (mul_one _).symm)
  have hsplit := CompressedSplittings.Idempotent.steinberg_split six_three
    (CompressedSplittings.full φ) (D.projection 0) (D.projection 1)
    D.split D.cross D.firstExchange.FE w
  have hfull : (CompressedSplittings.full φ).coefficient=φ := by
    ext a
    change φ a*φ 1=φ a
    rw [← map_mul,mul_one]
  rw [hfull,h₀,h₁,one_mul] at hsplit
  exact hsplit

end

variable {R S n m : Type*} [Ring R] [Ring S]

lemma map_reindex (φ : R →ₙ+* S) (f : n ↪ m) (z : Group n R) :
    map φ (reindex f z)=reindex f (map φ z) := by
  have h : (map φ).comp (reindex f) = (reindex f).comp (map (n:=n) φ) := by
    apply hom_ext
    intro i j hij a
    simp
  exact DFunLike.congr_fun h z

lemma reindex_equiv_symm (e : n ≃ m) (z : Group m R) :
    reindex e.toEmbedding (reindex e.symm.toEmbedding z)=z := by
  rw [← reindex_trans]
  have he : e.symm.toEmbedding.trans e.toEmbedding=Function.Embedding.refl m := by
    ext i
    exact e.apply_symm_apply i
  rw [he,reindex_id]

def sixEquiv : SixIndices ≃ Fin 6 :=
  (Fintype.equivFin SixIndices).trans (finCongr (by decide))

theorem binary_kernel_annihilation (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (w : Group (Fin 6) R) (hw : pi w=1) : map φ w=1 := by
  have hm : matrix w=1 := congrArg Subtype.val hw
  have hc : pi (reindex sixEquiv.symm.toEmbedding w)=1 := by
    apply Subtype.ext
    change matrix (reindex sixEquiv.symm.toEmbedding w)=1
    rw [matrix_reindex_equiv,hm,map_one]
  have h := binary_kernel_annihilation_six φ D (reindex sixEquiv.symm.toEmbedding w) hc
  have h' := congrArg (reindex (R:=R) sixEquiv.toEmbedding) h
  rw [map_reindex,reindex_equiv_symm,map_one] at h'
  exact h'

theorem kernelAnnihilationObligation : KernelAnnihilationObligation (R:=R) :=
  binary_kernel_annihilation

end Steinberg

namespace NoncommElementary
section
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma positions_commute (i j : n) (h : i≠j) (u v : Rˣ) :
    Commute (position i u) (position j v) := by
  apply Commute.map _ diagonal
  change (fun k => if k=i then u else 1)*(fun k => if k=j then v else 1)=
    (fun k => if k=j then v else 1)*(fun k => if k=i then u else 1)
  funext k
  by_cases hki : k=i
  · subst k; simp [h]
  · by_cases hkj : k=j
    · subst k; simp [Ne.symm h]
    · simp [hki,hkj]

lemma position_normalizes (i : n) (u : Rˣ) :
    position i u∈Subgroup.normalizer (elementary (R:=R) (n:=n) : Set (Matrix n n R)ˣ) :=
  diagonal_normalizes _

lemma position_commutator_mem (i j : n) (h : i≠j) (u v : Rˣ) :
    position i u*position i v*(position i u)⁻¹*(position i v)⁻¹∈elementary := by
  let a := position i u
  let b := position j u
  let c := position i v
  let r := a*b⁻¹
  have hr : r∈elementary := by simpa only [r,a,b,map_inv] using balanced_mem i j h u
  have hbc : Commute b c := positions_commute j i h.symm u v
  have hmove : b⁻¹*c*b=c := by rw [hbc.inv_left.eq]; group
  have heq : r*(c*r⁻¹*c⁻¹)=a*c*a⁻¹*c⁻¹ := by
    calc r*(c*r⁻¹*c⁻¹)=a*(b⁻¹*c*b)*a⁻¹*c⁻¹ := by dsimp [r]; group
         _ = a*c*a⁻¹*c⁻¹ := by rw [hmove]
  rw [← heq]
  apply (elementary (R:=R)).mul_mem hr
  exact (Subgroup.mem_normalizer_iff.mp (position_normalizes i v) r⁻¹).mp
    ((elementary (R:=R)).inv_mem hr)

def diagonalKernel (i : n) : Subgroup Rˣ := elementary.comap (position i)

instance diagonalKernel_normal (i : n) : (diagonalKernel (R:=R) i).Normal where
  conj_mem u hu v := by
    change position i (v*u*v⁻¹)∈elementary
    simp only [map_mul,map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (position_normalizes i v) (position i u)).mp hu

lemma quotient_commute (i j : n) (h : i≠j) (u v : Rˣ) :
    Commute (QuotientGroup.mk' (diagonalKernel i) u) (QuotientGroup.mk' (diagonalKernel i) v) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement,QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff]
  change position i (u*v*u⁻¹*v⁻¹)∈elementary
  simp only [map_mul,map_inv]
  exact position_commutator_mem i j h u v

lemma quotient_conjugate (i j : n) (h : i≠j) (u v : Rˣ) :
    QuotientGroup.mk' (diagonalKernel i) (u*v*u⁻¹)=QuotientGroup.mk' (diagonalKernel i) v := by
  simp only [map_mul,map_inv]
  rw [quotient_commute i j h u v |>.eq]
  simp [mul_assoc]

end

variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

theorem compressed_diagonal (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (i j : n) (h : i≠j) (u : Rˣ) :
    position i (NonunitalCompression.units φ u) ∈ elementary := by
  have hz := D.annihilates (QuotientGroup.mk' (diagonalKernel (R:=R) i))
    (quotient_conjugate i j h) u
  rw [QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff] at hz
  exact hz

def compressed (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (i j : n) (h : i≠j) : Rˣ →* elementary (R:=R) (n:=n) where
  toFun u := ⟨position i (NonunitalCompression.units φ u),compressed_diagonal φ D i j h u⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' u v := by apply Subtype.ext; simp

@[simp] lemma compressed_coe (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (i j : n) (h : i≠j) (u : Rˣ) :
    (compressed φ D i j h u : (Matrix n n R)ˣ)=position i (NonunitalCompression.units φ u) := rfl

end NoncommElementary

namespace Steinberg
variable {R : Type*} [Ring R]

noncomputable def descended (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ) :
    NoncommElementary.elementary (R:=R) (n:=Fin 6) →* Group (Fin 6) R :=
  (pi (R:=R) (n:=Fin 6)).liftOfSurjective pi_surjective
    ⟨map φ, fun w hw => binary_kernel_annihilation φ D w hw⟩

@[simp] lemma descended_pi (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (w : Group (Fin 6) R) : descended φ D (pi w)=map φ w := by
  simp [descended]

lemma matrix_descended (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (g : NoncommElementary.elementary (R:=R) (n:=Fin 6)) :
    matrix (descended φ D g)=NonunitalCompression.units (matrixCoefficient φ) g.val := by
  obtain ⟨w,rfl⟩ := pi_surjective g
  rw [descended_pi,matrix_map,pi_coe]

noncomputable def unitLift (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ) :
    Rˣ →* Group (Fin 6) R :=
  (descended φ D).comp (NoncommElementary.compressed φ D 0 1 (by decide))

lemma matrixCoefficient_position {n : Type*} [Fintype n] [DecidableEq n]
    (φ : R →ₙ+* R) (i : n) (v : Rˣ) :
    NonunitalCompression.units (matrixCoefficient φ) (NoncommElementary.position i v) =
      NoncommElementary.position i (NonunitalCompression.units φ v) := by
  apply Units.ext
  simp only [NonunitalCompression.units_val,NoncommElementary.position_val,
    add_sub_cancel_left]
  change 1+(Matrix.single i i (v.val-1)).map φ = 1+Matrix.single i i (φ (v.val-1))
  rw [Matrix.map_single _ _ _ φ]

lemma units_comp {S T : Type*} [Ring S] [Ring T]
    (ψ : S →ₙ+* T) (φ : R →ₙ+* S) (v : Rˣ) :
    NonunitalCompression.units ψ (NonunitalCompression.units φ v)=
      NonunitalCompression.units (ψ.comp φ) v := by
  apply Units.ext
  simp

theorem matrix_unitLift (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (v : Rˣ) : matrix (unitLift φ D v)=
    NoncommElementary.position (0:Fin 6) (NonunitalCompression.units (φ.comp φ) v) := by
  rw [unitLift,MonoidHom.comp_apply,matrix_descended,NoncommElementary.compressed_coe,
    matrixCoefficient_position,units_comp]

end Steinberg

end

end OAI
