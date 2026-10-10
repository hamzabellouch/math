import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.PackingRounds
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixUnitsHom

namespace OAI

noncomputable section
namespace ConcreteMatrixUnits
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unit_projection (i : ι) : IsStarProjection (unit i i) :=
  ⟨by change unit i i*unit i i=unit i i; rw [unit_mul,ite_eq_left rfl], unit_star i i⟩

def pairProjection (i j : ι) (z : ℂ) : CStarMatrix ι ι ℂ :=
  (1/2:ℂ) • (unit i i+unit j j+z • unit i j+star z • unit j i)

lemma pairProjection_star (i j : ι) (z : ℂ) : star (pairProjection i j z)=pairProjection i j z := by
  simp only [pairProjection,star_smul,star_add,unit_star,star_star]
  norm_num
  module

lemma pairProjection_sq {i j : ι} (hij : i≠j) {z : ℂ} (hz : star z*z=1) :
    pairProjection i j z*pairProjection i j z=pairProjection i j z := by
  have hzi : z*star z=1 := by rw [mul_comm,hz]
  simp only [pairProjection,smul_mul_assoc,mul_smul_comm,mul_add,add_mul,
    unit_mul,ite_true,ite_eq_right hij,ite_eq_right hij.symm,smul_zero,zero_add,add_zero,
    smul_smul]
  match_scalars <;> ring_nf <;> simp only [hz,hzi] <;> norm_num

lemma pairProjection_projection {i j : ι} (hij : i≠j) {z : ℂ} (hz : star z*z=1) :
    IsStarProjection (pairProjection i j z) :=
  ⟨pairProjection_sq hij hz,pairProjection_star i j z⟩

lemma unit_trace (i j : ι) : Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm (unit i j))=if i=j then 1 else 0 := by
  change Matrix.trace (Matrix.single i j (1:ℂ))=_
  by_cases h : i=j
  · subst j; simp [Matrix.trace_single_eq_same]
  · simp [Matrix.trace_single_eq_of_ne _ _ _ h,h]

lemma pairProjection_trace {i j : ι} (hij : i≠j) (z : ℂ) :
    Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm (pairProjection i j z))=1 := by
  simp only [pairProjection,map_smul,map_add,Matrix.trace_smul,Matrix.trace_add,unit_trace,
    ite_true,ite_eq_right hij,ite_eq_right hij.symm,smul_eq_mul,mul_zero,add_zero]
  norm_num

lemma pairProjection_recovers {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    unit i j = (1/2:ℂ) • (pairProjection i j 1-pairProjection i j (-1)) +
      (-Complex.I/2:ℂ) • (pairProjection i j Complex.I-pairProjection i j (-Complex.I)) := by
  simp only [pairProjection,star_neg]
  simp only [star_one,Complex.star_def,Complex.conj_I]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]; norm_num

end ConcreteMatrixUnits

namespace CurrentMain.ProjectionRow
open Pureness
open scoped ComplexOrder

variable {D I : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable [Fintype I] [DecidableEq I] {p q e : D} {m : ℕ}
variable (V : ProjectionRow (Fin m) p) (U : ProjectionRow I q)

lemma matrixHom_projection {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {p : D} {m : ℕ} (V : ProjectionRow (Fin m) p)
    {P : CStarMatrix (Fin m) (Fin m) ℂ} (hP : IsStarProjection P) :
    IsStarProjection (V.matrixHom P) where
  isIdempotentElem := by change V.matrixHom P*V.matrixHom P=V.matrixHom P; rw [←map_mul,hP.isIdempotentElem.eq]
  isSelfAdjoint := by change star (V.matrixHom P)=V.matrixHom P; rw [←map_star,hP.isSelfAdjoint.star_eq]

lemma matrixHom_le {P : CStarMatrix (Fin m) (Fin m) ℂ} (hP : IsStarProjection P) :
    V.matrixHom P ≤ V.sample p :=
  ((V.matrixHom_projection hP).le_iff_mul_eq_left V.range_projection).mpr (V.matrixHom_right P)

lemma amplified_trace_rankone {D I : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    [Fintype I] [DecidableEq I] {p q e : D} {m : ℕ}
    (V : ProjectionRow (Fin m) p) (U : ProjectionRow I q) (he : V.sample p=e) (heq : e≤q)
    {P : CStarMatrix (Fin m) (Fin m) ℂ}
    (htrace : Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1) (τ : TracialState D) :
    (m:ℂ)*τ.functional (V.amplifiedMatrixHom U he heq P)=τ.functional (U.sample e) := by
  change (m:ℂ)*τ.functional (U.sample (V.matrixHom P))=τ.functional (U.sample e)
  rw [U.trace_sample τ _ (V.matrixHom_supported U.projection he heq P).2]
  change (m:ℂ)*((Fintype.card I:ℂ)*τ.functional (V.matrix p (CStarMatrix.ofMatrixStarAlgEquiv.symm P)))=_
  rw [V.trace_matrix τ p V.projection.isIdempotentElem.eq,htrace,one_mul,
    U.trace_sample τ e ((show IsStarProjection e from he ▸ V.range_projection).le_iff_mul_eq_left U.projection |>.mp heq),
    ←he,V.trace_sample τ p V.projection.isIdempotentElem.eq,Fintype.card_fin]
  ring

lemma amplified_rankone_trace_real (hm : 0 < m) (he : V.sample p=e) (heq : e≤q)
    {P : CStarMatrix (Fin m) (Fin m) ℂ}
    (htrace : Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1) (τ : TracialState D) :
    (τ.functional (V.amplifiedMatrixHom U he heq P)).re=(1/(m:ℝ))*(τ.functional (U.sample e)).re := by
  have h := congrArg Complex.re (V.amplified_trace_rankone U he heq htrace τ)
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at h
  have hm0 : (m:ℝ)≠0 := by positivity
  apply (mul_left_cancel₀ hm0)
  calc
    (m:ℝ)*(τ.functional (V.amplifiedMatrixHom U he heq P)).re=(τ.functional (U.sample e)).re := h
    _ = (m:ℝ)*((1/(m:ℝ))*(τ.functional (U.sample e)).re) := by field_simp

lemma amplified_rankone_sampling (hm : 0 < m) (he : V.sample p=e) (heq : e≤q)
    {P : CStarMatrix (Fin m) (Fin m) ℂ} (hP : IsStarProjection P)
    (htrace : Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1)
    (x : unitary D) {η c δ : ℝ} (hη0 : 0≤η) (hη : η<1) (hc : 0≤c)
    (happrox : ∃ H : Matrix I I ℂ, ‖U.sample q*(x:D)*U.sample q-U.matrix q H‖<η)
    (τ : TracialState D) (hmass : |(τ.functional (U.sample e)).re-c*(τ.functional (U.sample q)).re|≤δ) :
    traceTwoNorm τ ((x:D)*V.amplifiedMatrixHom U he heq P-V.amplifiedMatrixHom U he heq P*(x:D))^2 ≤
      c*traceTwoNorm τ ((x:D)*U.sample q-U.sample q*(x:D))^2+
      6*η*((τ.functional (U.sample e)).re+c*(τ.functional (U.sample q)).re)+10*δ := by
  have hPe : V.matrixHom P≤e := he ▸ V.matrixHom_le hP
  have hPq := hPe.trans heq
  have ht := V.amplified_rankone_trace_real U hm he heq htrace τ
  have hi : 0≤1/(m:ℝ) := by positivity
  have hi1 : 1/(m:ℝ)≤1 := by apply (div_le_one (by positivity : (0:ℝ) < m)).mpr; exact_mod_cast hm
  have hcr : 0≤c/(m:ℝ) := by positivity
  have hb := (U.matrix_block_sampling (V.matrixHom_projection hP) hPq x hη hcr happrox τ).2
  have hy : 0≤(τ.functional (U.sample e)).re :=
    (τ.functional.map_nonneg (U.sample_projection (he ▸ V.range_projection)
      ((he ▸ V.range_projection).le_iff_mul_eq_right U.projection |>.mp heq)).nonneg).1
  have hp : 0≤(τ.functional (U.sample q)).re := (τ.functional.map_nonneg U.range_projection.nonneg).1
  change |traceTwoNorm τ ((x:D)*V.amplifiedMatrixHom U he heq P-V.amplifiedMatrixHom U he heq P*(x:D))^2-
    (c/(m:ℝ))*traceTwoNorm τ ((x:D)*U.sample q-U.sample q*(x:D))^2|≤_ at hb
  have herr : |(τ.functional (V.amplifiedMatrixHom U he heq P)).re-(c/(m:ℝ))*(τ.functional (U.sample q)).re|≤δ := by
    rw [ht,show c/(m:ℝ)=(1/(m:ℝ))*c by ring,mul_assoc,←mul_sub,abs_mul,abs_of_nonneg hi]
    exact (mul_le_mul_of_nonneg_left hmass hi).trans ((mul_le_mul_of_nonneg_right hi1 (le_trans (abs_nonneg _) hmass)).trans_eq (one_mul δ))
  have hc1 : c/(m:ℝ)≤c := by simpa only [one_div,div_eq_mul_inv,mul_one,one_mul] using mul_le_mul_of_nonneg_left hi1 hc
  have ht1 : (τ.functional (V.amplifiedMatrixHom U he heq P)).re≤(τ.functional (U.sample e)).re := by
    rw [ht]; exact (mul_le_mul_of_nonneg_right hi1 hy).trans_eq (one_mul _)
  have ht2 := mul_le_mul_of_nonneg_right hc1 hp
  have he2 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg (traceTwoNorm τ ((x:D)*U.sample q-U.sample q*(x:D))))
  have hlarge := mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity : 0≤6*η)
  change |traceTwoNorm τ ((x:D)*V.amplifiedMatrixHom U he heq P-V.amplifiedMatrixHom U he heq P*(x:D))^2-
    (c/(m:ℝ))*traceTwoNorm τ ((x:D)*U.sample q-U.sample q*(x:D))^2|≤
    6*η*((τ.functional (V.amplifiedMatrixHom U he heq P)).re+(c/(m:ℝ))*(τ.functional (U.sample q)).re)+
    10*|(τ.functional (V.amplifiedMatrixHom U he heq P)).re-(c/(m:ℝ))*(τ.functional (U.sample q)).re| at hb
  linarith [(abs_le.mp hb).2]

end CurrentMain.ProjectionRow

namespace DirectPacking
open CurrentMain Pureness
open scoped ComplexOrder

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

lemma exists_round_matrix_maps {m : ℕ} (hm : 0 < m)
    (hmat : ∀ e : D, IsStarProjection e → ∃ p : D, ∃ V : ProjectionRow (Fin m) p,V.sample p=e)
    {z₀ r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η σ δ : ℝ}
    (R : SampledPackingRound F z₀ K η δ) (hη : 0<η) (hσ : 0≤σ) (hσ1 : σ<1)
    (hR : ∀ a, PackingStepBounds (F.range a.1) (R.occupied a) (R.sampled a) (R.inserted a)
      (η*F.weight a.1/2) σ δ K ∧
      ∃ e : D, IsStarProjection e ∧ e≤F.base a.1 ∧ R.sampled a=(F.row a.1).sample e)
    (happrox : ∀ j, ∀ x∈K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
      ‖F.range j*(x:D)*F.range j-(F.row j).matrix (F.base j) H‖<σ) :
    ∃ φ : F.Index × Bool → (CStarMatrix (Fin m) (Fin m) ℂ →⋆ₙₐ[ℂ] D),
      (∀ a,φ a 1=R.sampled a) ∧
      ∀ P : CStarMatrix (Fin m) (Fin m) ℂ, IsStarProjection P →
        Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1 →
        ∀ x∈K, ∀ τ : RestrictedTracialState D,
        (∑ a,traceTwoNorm τ ((x:D)*φ a P-φ a P*(x:D))^2)≤
          η*(∑ j,F.weight j*traceTwoNorm τ ((x:D)*F.range j-F.range j*(x:D))^2)+
          6*σ*(R.sampledMass τ+R.targetMass τ)+10*R.totalError := by
  classical
  choose e he heq hy using fun a => (hR a).2
  choose p V hV using fun a => hmat (e a) (he a)
  let φ := fun a : F.Index × Bool => (V a).amplifiedMatrixHom (F.row a.1) (hV a) (heq a)
  refine ⟨φ,?_,?_⟩
  · intro a
    exact ((V a).amplifiedMatrixHom_one (F.row a.1) (hV a) (heq a)).trans (hy a).symm
  · intro P hP htr x hx τ
    have hb (a : F.Index × Bool) := (V a).amplified_rankone_sampling (F.row a.1) hm
      (hV a) (heq a) hP htr x hσ hσ1
      (show 0≤η*F.weight a.1/2 by have hw := F.weight_pos a.1; positivity) (happrox a.1 x hx) τ
      (show |(τ.functional ((F.row a.1).sample (e a))).re-(η*F.weight a.1/2)*(τ.functional (F.range a.1)).re|≤δ by
        rw [←hy a]; exact (hR a).1.mass τ)
    have h := Finset.sum_le_sum fun a (_ : a∈Finset.univ) => hb a
    apply h.trans_eq
    simp only [←hy,Finset.sum_add_distrib,←Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      SampledPackingRound.sampledMass,SampledPackingRound.targetMass,SampledPackingRound.totalError]
    change (∑ a : F.Index × Bool, η*F.weight a.1/2*traceTwoNorm τ ((x:D)*F.range a.1-F.range a.1*(x:D))^2)+
      6*σ*((∑ a,(τ.functional (R.sampled a)).re)+(∑ a : F.Index × Bool,η*F.weight a.1/2*(τ.functional (F.range a.1)).re))+
      10*((Fintype.card (F.Index × Bool):ℝ)*δ)=_
    rw [signed_weighted_sum F η (fun j => traceTwoNorm τ ((x:D)*F.range j-F.range j*(x:D))^2),
      signed_weighted_sum F η (fun j => (τ.functional (F.range j)).re)]

end DirectPacking

end

end OAI
