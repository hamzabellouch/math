import OAI.GroupTheory.Kervaire.CurrentExistence

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace KervaireIncidenceCurrent

section
open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]

lemma contDiff_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Mat K} {g : E → Mat L} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x ↦ diag (f x) (g x)) := by
  simp only [diag_eq_corner]
  exact ((in11 (K := K) (R := L)).contDiff.comp hf).add
    ((in22 (K := K) (R := L)).contDiff.comp hg)

def swapBlocks : unitary (Mat (L ⊕ L)) :=
  ⟨Matrix.fromBlocks 0 1 1 0,by
    constructor <;>
      simp [star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one]⟩

lemma pair_cancel (Y : unitary (Mat L)) :
    diag (Y : Mat L) 1 * (swapBlocks (L := L) : Mat (L ⊕ L)) * diag 1 (star (Y : Mat L)) *
      star (swapBlocks (L := L) : Mat (L ⊕ L)) = 1 := by
  have hY : (Y : Mat L) * (Y : Mat L).conjTranspose = 1 := Y.property.2
  simp [swapBlocks,diag,star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply,← Matrix.fromBlocks_one,hY]

def pairedMap (Y : UMap (Mat K) (Mat L)) : UMap (Mat K) (Mat (K ⊕ (L ⊕ L))) where
  toFun X := diag X (diag (Y X) (star (Y X)))
  smooth := contDiff_diag contDiff_id (contDiff_diag Y.smooth ((starL ℝ).contDiff.comp Y.smooth))
  unitary X := diag_unitary X.property (diag_unitary (Y.unitary X) (by
    simpa only [Unitary.star_mem_iff] using Y.unitary X))

def coreMap : UMap (Mat K) (Mat (K ⊕ (L ⊕ L))) where
  toFun X := diag X 1
  smooth := contDiff_diag contDiff_id contDiff_const
  unitary X := diag_unitary X.property (by simp)

lemma paired_elementary_core (Y : UMap (Mat K) (Mat L)) :
    Elementary (pairedMap Y) (coreMap (K := K) (L := L)) := by
  obtain ⟨p,hp,hp0,hp1,hpu⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path
    (swapBlocks (L := L))
  refine ⟨fun q ↦ diag q.2 (diag (Y q.2) 1 * p q.1 * diag 1 (star (Y q.2)) * star (p q.1)),?_,?_,?_,?_⟩
  · exact contDiff_diag contDiff_snd (((contDiff_diag (Y.smooth.comp contDiff_snd) contDiff_const).mul
      (hp.comp contDiff_fst) |>.mul (contDiff_diag contDiff_const ((starL ℝ).contDiff.comp (Y.smooth.comp contDiff_snd)))).mul
      ((starL ℝ).contDiff.comp (hp.comp contDiff_fst)))
  · intro t X
    apply diag_unitary X.property
    apply (unitary _).mul_mem
    · apply (unitary _).mul_mem
      · exact (unitary _).mul_mem (diag_unitary (Y.unitary X) (by simp)) (hpu t)
      · exact diag_unitary (by simp) (by simpa only [Unitary.star_mem_iff] using Y.unitary X)
    · simpa only [Unitary.star_mem_iff] using hpu t
  · intro X
    simp only [hp0,mul_one,star_one,diag_mul,mul_one,one_mul]
    rfl
  · intro X
    dsimp only
    rw [hp1,pair_cancel ⟨Y X,Y.unitary X⟩]
    rfl

lemma core_elementary_model :
    Elementary (coreMap (K := K) (L := L)) (modelMap (K := K) (R := L ⊕ L)) := by
  obtain ⟨p,hp,hp0,hp1,hpu⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path
    (-1 : unitary (Mat (L ⊕ L)))
  refine ⟨fun q ↦ diag q.2 (p q.1),contDiff_diag contDiff_snd (hp.comp contDiff_fst),?_,?_,?_⟩
  · intro t X
    exact diag_unitary X.property (hpu t)
  · intro X
    dsimp only
    rw [hp0]
    rfl
  · intro X
    dsimp only
    rw [hp1]
    rfl

def rightMulMap {I : Type*} [Fintype I] [DecidableEq I]
    (F : UMap (Mat K) (Mat I)) (P : unitary (Mat I)) : UMap (Mat K) (Mat I) where
  toFun X := F X * P
  smooth := F.smooth.mul contDiff_const
  unitary X := (unitary _).mul_mem (F.unitary X) P.property

lemma elementary_rightMul {I : Type*} [Fintype I] [DecidableEq I]
    (F : UMap (Mat K) (Mat I)) (P : unitary (Mat I)) : Elementary F (rightMulMap F P) := by
  obtain ⟨p,hp,hp0,hp1,hpu⟩ := KervaireUnitaryExponential.matrix_exists_smooth_path P
  refine ⟨fun q ↦ F q.2 * p q.1,(F.smooth.comp contDiff_snd).mul (hp.comp contDiff_fst),?_,?_,?_⟩
  · intro t X
    exact (unitary _).mul_mem (F.unitary X) (hpu t)
  · intro X
    simp [hp0]
  · intro X
    dsimp only
    rw [hp1]
    rfl

lemma model_homotopic_paired_mul (Y : UMap (Mat K) (Mat L))
    (P : unitary (Mat (K ⊕ (L ⊕ L)))) :
    Homotopic (modelMap (K := K) (R := L ⊕ L)) (rightMulMap (pairedMap Y) P) :=
  homotopic_trans (homotopic_symm (homotopic_of_elementary core_elementary_model))
    (homotopic_trans (homotopic_symm (homotopic_of_elementary (paired_elementary_core Y)))
      (homotopic_of_elementary (elementary_rightMul (pairedMap Y) P)))

end

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

def includeFirst : (K → ℂ) →ₗ[ℂ] ((K ⊕ R) → ℂ) where
  toFun v := Sum.elim v (fun _ ↦ 0)
  map_add' v w := by ext i; cases i <;> simp
  map_smul' c v := by ext i; cases i <;> simp

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma includeFirst_injective : Function.Injective (includeFirst (K := K) (R := R)) := by
  intro v w h
  exact funext fun k ↦ congrFun h (Sum.inl k)

omit [DecidableEq R] in
lemma diag_mulVec_includeFirst (T : Mat R) (v : K → ℂ) :
    diag 1 T *ᵥ includeFirst v = includeFirst (R := R) v := by
  simp only [diag,includeFirst,LinearMap.coe_mk,AddHom.coe_mk,Matrix.fromBlocks_mulVec,
    Function.comp_def,Matrix.one_mulVec,Matrix.zero_mulVec,add_zero,zero_add]
  congr 1
  exact Matrix.mulVec_zero _

lemma rank_of_incidence {f : ℝ × Mat K → Mat (K ⊕ R)} (t : ℝ)
    (p : unitary (Alg K R)) (hp : incidence f (t,(p : Alg K R)) = 1) :
    Fintype.card K ≤ Module.finrank ℂ
      (LinearMap.ker ((f (t,p.val.1)).mulVecLin - LinearMap.id)) := by
  let Q : unitary (Mat (K ⊕ R)) := ⟨p.val.2.1,(unitary_alg_parts p).2.1⟩
  let T : unitary (Mat R) := ⟨p.val.2.2,(unitary_alg_parts p).2.2⟩
  have hQ (D : Mat (K ⊕ R)) : star (Q : Mat (K ⊕ R))*((Q : Mat (K ⊕ R))*D) = D := by
    rw [← mul_assoc,Q.property.1,one_mul]
  have hdiag : diag (1 : Mat K) (star (T : Mat R))*diag 1 (T : Mat R) = 1 := by
    rw [diag_mul,one_mul,T.property.1,diag_one]
  have heq : f (t,p.val.1)*(Q : Mat (K ⊕ R)) = (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) := by
    have hh := congrArg (fun M : Mat (K ⊕ R) ↦ M*(Q : Mat (K ⊕ R))*diag 1 (T : Mat R)) hp
    change f (t,p.val.1)*(Q : Mat (K ⊕ R))*diag 1 (star (T : Mat R))*star (Q : Mat (K ⊕ R)) *
      (Q : Mat (K ⊕ R))*diag 1 (T : Mat R) = _ at hh
    simpa only [mul_assoc,hQ,hdiag,mul_one,one_mul] using hh
  have hiQ : Function.Injective (Q.val.mulVecLin) := by
    intro v w h
    have hh := congrArg (fun v ↦ star Q.val *ᵥ v) h
    simpa only [Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,Q.property.1,Matrix.one_mulVec] using hh
  let L : (K → ℂ) →ₗ[ℂ] LinearMap.ker ((f (t,p.val.1)).mulVecLin - LinearMap.id) :=
    LinearMap.codRestrict _ (Q.val.mulVecLin.comp includeFirst) (by
      intro v
      change f (t,p.val.1) *ᵥ (Q.val *ᵥ includeFirst v) - Q.val *ᵥ includeFirst v = 0
      rw [Matrix.mulVec_mulVec,heq,← Matrix.mulVec_mulVec,diag_mulVec_includeFirst,sub_self])
  have hL : Function.Injective L := by
    intro v w h
    apply includeFirst_injective (R := R)
    apply hiQ
    exact congrArg Subtype.val h
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    smul_eq_mul,mul_one] using LinearMap.finrank_le_finrank_of_injective hL

end

open KervaireUnitaryHomotopy
variable {K L : Type*} [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
lemma exists_paired_fixed [Nonempty K] (Y : UMap (Mat K) (Mat L))
    (P : unitary (Mat (K ⊕ (L ⊕ L)))) :
    ∃ X : unitary (Mat K), Fintype.card K ≤ Module.finrank ℂ
      (LinearMap.ker ((((pairedMap Y) X * P)).mulVecLin - LinearMap.id)) := by
  obtain ⟨p,hp⟩ := exists_incidence_of_homotopic (rightMulMap (pairedMap Y) P)
    (model_homotopic_paired_mul Y P)
  refine ⟨⟨p.val.1,(unitary_alg_parts p).1⟩,?_⟩
  exact rank_of_incidence (f := timeless (rightMulMap (pairedMap Y) P)) 0 p hp
end KervaireIncidenceCurrent

namespace KervaireSignPairing

section
open Matrix
variable {I K : Type*} [Fintype I]

abbrev positive (s : I → ℤ) := {i // s i = 1}
abbrev negative (s : I → ℤ) := {i // s i ≠ 1}

lemma sign_count (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (h : ∑ i, s i = 1) : Fintype.card (positive s) = Fintype.card (negative s) + 1 := by
  classical
  have hp : (∑ i : positive s, s i) = (Fintype.card (positive s) : ℤ) := by
    simp only [show (fun i : positive s ↦ s i) = fun _ ↦ (1 : ℤ) from
      funext (fun i ↦ i.property),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have hn : (∑ i : negative s, s i) = -(Fintype.card (negative s) : ℤ) := by
    simp only [show (fun i : negative s ↦ s i) = fun _ ↦ (-1 : ℤ) from
      funext (fun i ↦ (hs i).resolve_left i.property),Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_neg,mul_one]
  have hc := Fintype.sum_subtype_add_sum_subtype (fun i ↦ s i = 1) s
  rw [hp,hn,h] at hc
  omega

noncomputable def positiveEquiv (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    Unit ⊕ negative s ≃ positive s := Fintype.equivOfCardEq (by
  simpa only [Fintype.card_sum,Fintype.card_unit] using (Nat.add_comm _ _).trans hc.symm)

noncomputable def signsEquiv (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    (Unit ⊕ negative s) ⊕ negative s ≃ I :=
  (Equiv.sumCongr (positiveEquiv s hc) (Equiv.refl _)).trans (Equiv.sumCompl (fun i ↦ s i = 1))

lemma signsEquiv_pos (s : I → ℤ) (hc) (j : Unit ⊕ negative s) :
    s (signsEquiv s hc (.inl j)) = 1 := by
  change s ((positiveEquiv s hc) j) = 1
  exact ((positiveEquiv s hc) j).property
lemma signsEquiv_neg (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hc) (j : negative s) : s (signsEquiv s hc (.inr j)) = -1 := by
  exact (hs j).resolve_left j.property

noncomputable def coordinates (s : I → ℤ)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) :
    K ⊕ ((K × negative s) ⊕ (K × negative s)) ≃ K × I :=
  (Equiv.sumAssoc K (K × negative s) (K × negative s)).symm.trans
    ((Equiv.sumCongr ((Equiv.sumCongr (Equiv.prodUnique K Unit).symm (Equiv.refl _)).trans
      (Equiv.prodSumDistrib K Unit (negative s)).symm) (Equiv.refl _)).trans
        ((Equiv.prodSumDistrib K (Unit ⊕ negative s) (negative s)).symm.trans
          (Equiv.prodCongr (Equiv.refl K) (signsEquiv s hc))))

end

open Matrix KervaireIncidenceCurrent KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K D : Type*} [Fintype I] [Fintype K] [Fintype D]
  [DecidableEq I] [DecidableEq K] [DecidableEq D]

def repeatMatrix (X : Mat K) : Mat (K × D) := blockDiagonal (fun _ ↦ X)

def repeatMap : UMap (Mat K) (Mat (K × D)) where
  toFun := repeatMatrix
  smooth := by
    let L : Mat K →ₗ[ℝ] Mat (K × D) :=
      { toFun := repeatMatrix
        map_add' := by intro X Y; exact blockDiagonal_add _ _
        map_smul' := by intro c X; exact blockDiagonal_smul c _ }
    exact L.toContinuousLinearMap.contDiff
  unitary X := by
    have h1 : (X : Mat K).conjTranspose * X = 1 := X.property.1
    have h2 : (X : Mat K) * (X : Mat K).conjTranspose = 1 := X.property.2
    constructor <;>
      simp only [repeatMatrix,star_eq_conjTranspose,blockDiagonal_conjTranspose,
        ← blockDiagonal_mul,h1,h2]
    all_goals exact blockDiagonal_one

def signedMatrix (s : I → ℤ) (X : Mat K) : Mat (K × I) :=
  blockDiagonal (fun i ↦ if s i = 1 then X else star X)

omit [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq K] [DecidableEq D] in
lemma coordinates_inl (s : I → ℤ) (hc) (k : K) :
    coordinates s hc (.inl k) = (k,signsEquiv s hc (.inl (.inl ()))) := rfl
omit [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq K] [DecidableEq D] in
lemma coordinates_middle (s : I → ℤ) (hc) (k : K) (j : negative s) :
    coordinates s hc (.inr (.inl (k,j))) = (k,signsEquiv s hc (.inl (.inr j))) := rfl
omit [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq K] [DecidableEq D] in
lemma coordinates_last (s : I → ℤ) (hc) (k : K) (j : negative s) :
    coordinates s hc (.inr (.inr (k,j))) = (k,signsEquiv s hc (.inr j)) := rfl

omit [Fintype K] [DecidableEq K] in
lemma signedMatrix_coordinates (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hc : Fintype.card (positive s) = Fintype.card (negative s) + 1) (X : Mat K) :
    (signedMatrix s X).submatrix (coordinates s hc) (coordinates s hc) =
      diag X (diag (repeatMatrix (D := negative s) X) (star (repeatMatrix (D := negative s) X))) := by
  classical
  ext i j
  rcases i with i | ⟨i,i'⟩ | ⟨i,i'⟩ <;> rcases j with j | ⟨j,j'⟩ | ⟨j,j'⟩ <;>
    simp [Matrix.submatrix_apply,signedMatrix,coordinates_inl,coordinates_middle,coordinates_last,
      signsEquiv_pos,signsEquiv_neg s hs,KervaireIncidenceCurrent.diag,Matrix.fromBlocks,repeatMatrix,
      blockDiagonal_apply,star_eq_conjTranspose]

end KervaireSignPairing

end

end OAI
