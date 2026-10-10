import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicDescent

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set MeasureTheory
namespace PrimeDegreePackets.Adelic

def absoluteNormalizedMatrix {n : ℕ} (h : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  |h.val.det| ^ (-(1 : ℝ) / n) • h.val

lemma absoluteNormalizedMatrix_det {n : ℕ} (hn : 0 < n) (h : GL (Fin n) ℝ) :
    |(absoluteNormalizedMatrix h).det| = 1 :=
  normalizedMatrix_abs_det h.val hn (Units.ne_zero (GeneralLinearGroup.det h))

lemma absoluteNormalizedMatrix_det_pos_iff {n : ℕ} (h : GL (Fin n) ℝ) :
    0 < (absoluteNormalizedMatrix h).det ↔ 0 < h.val.det := by
  rw [absoluteNormalizedMatrix,Matrix.det_smul,Fintype.card_fin]
  exact mul_pos_iff_of_pos_left (pow_pos (Real.rpow_pos_of_pos
    (abs_pos.mpr (Units.ne_zero (GeneralLinearGroup.det h))) _) _)

 

def realSLNormalize {n : ℕ} (hodd : Odd n) (h : GL (Fin n) ℝ) : G n :=
  ⟨if 0 < h.val.det then absoluteNormalizedMatrix h else -absoluteNormalizedMatrix h,by
    have hd := absoluteNormalizedMatrix_det hodd.pos h
    split_ifs with hp
    · rw [abs_of_pos ((absoluteNormalizedMatrix_det_pos_iff h).mpr hp)] at hd
      exact hd
    · have hn : (absoluteNormalizedMatrix h).det < 0 := by
        have hn0 : (absoluteNormalizedMatrix h).det ≠ 0 := by intro he; simp [he] at hd
        exact lt_of_le_of_ne (not_lt.mp ((absoluteNormalizedMatrix_det_pos_iff h).not.mpr hp)) hn0
      rw [Matrix.det_neg,Fintype.card_fin,hodd.neg_one_pow]
      rwa [abs_of_neg hn,neg_eq_neg_one_mul] at hd⟩

lemma realSLNormalize_projective {n : ℕ} (hodd : Odd n) (h : GL (Fin n) ℝ) :
    SpecialLinearGroup.toPGL (realSLNormalize hodd h) = ProjGenLinGroup.mk h := by
  have hr : |h.val.det| ^ (-(1 : ℝ) / n) ≠ 0 :=
    (Real.rpow_pos_of_pos (abs_pos.mpr (Units.ne_zero (GeneralLinearGroup.det h))) _).ne'
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  by_cases hp : 0 < h.val.det
  · refine ⟨Units.mk0 (|h.val.det| ^ (-(1 : ℝ) / n))⁻¹ (inv_ne_zero hr),?_⟩
    apply Units.ext
    change (if 0 < h.val.det then absoluteNormalizedMatrix h else -absoluteNormalizedMatrix h) *
      Matrix.scalar (Fin n) _ = h.val
    rw [ite_eq_left hp]
    change (|h.val.det| ^ (-(1 : ℝ) / n) • h.val) *
      Matrix.diagonal (fun _ => (|h.val.det| ^ (-(1 : ℝ) / n))⁻¹) = h.val
    rw [← Matrix.smul_one_eq_diagonal,Matrix.mul_smul,Matrix.mul_one,smul_smul]
    simp [hr]
  · refine ⟨Units.mk0 (- (|h.val.det| ^ (-(1 : ℝ) / n)))⁻¹ (inv_ne_zero (neg_ne_zero.mpr hr)),?_⟩
    apply Units.ext
    change (if 0 < h.val.det then absoluteNormalizedMatrix h else -absoluteNormalizedMatrix h) *
      Matrix.scalar (Fin n) _ = h.val
    rw [ite_eq_right hp]
    change (-(|h.val.det| ^ (-(1 : ℝ) / n) • h.val)) *
      Matrix.diagonal (fun _ => (-(|h.val.det| ^ (-(1 : ℝ) / n)))⁻¹) = h.val
    rw [← neg_smul,← Matrix.smul_one_eq_diagonal,Matrix.mul_smul,Matrix.mul_one,smul_smul]
    simp [hr]

lemma continuous_absoluteNormalizedMatrix (n : ℕ) :
    Continuous (@absoluteNormalizedMatrix n) := by
  exact ((Units.continuous_val.matrix_det.abs).rpow_const (fun h => Or.inl
    (abs_ne_zero.mpr (Units.ne_zero (GeneralLinearGroup.det h))))).smul Units.continuous_val

lemma continuous_realSLNormalize {n : ℕ} (hodd : Odd n) : Continuous (realSLNormalize hodd) := by
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  intro h
  have hc := continuous_absoluteNormalizedMatrix n
  by_cases hp : 0 < h.val.det
  · apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Units.continuous_val.matrix_det).mem_nhds hp] with k hk
    exact ite_eq_left hk
  · have hn : h.val.det < 0 := lt_of_le_of_ne (not_lt.mp hp) (Units.ne_zero (GeneralLinearGroup.det h))
    apply hc.neg.continuousAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt Units.continuous_val.matrix_det continuous_const).mem_nhds hn] with k hk
    exact ite_eq_right (not_lt.mpr (le_of_lt hk))

lemma ambientEquiv_realSLNormalize {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (h : GL (Fin n) ℝ) :
    ambientEquiv hodd hn b (Quotient.mk _ (realSLNormalize hodd h)) = realMatrixPoint h := by
  rw [ambientEquiv_mk]
  unfold realAmbientPoint realMatrixPoint adelicMatrixPoint
  rw [realSLNormalize_projective,map_one]

lemma integralFiniteGroup_isOpen (n : ℕ) : IsOpen (integralFiniteGroup n : Set (GL (Fin n) RationalFiniteAdeles)) := by
  have hI : IsOpen {a : RationalFiniteAdeles | ∀ p, a p ∈ rationalLocalIntegers p} :=
    RestrictedProduct.isOpen_forall_mem (fun p => rationalIntegersOpen.out p)
  have hV : IsOpen {g : GL (Fin n) RationalFiniteAdeles | ∀ i j p, g.val i j p ∈ rationalLocalIntegers p} :=
    by
      have he : {g : GL (Fin n) RationalFiniteAdeles | ∀ i j p, g.val i j p ∈ rationalLocalIntegers p} =
          ⋂ i, ⋂ j, (fun g : GL (Fin n) RationalFiniteAdeles => g.val i j) ⁻¹' {a | ∀ p, a p ∈ rationalLocalIntegers p} := by ext; simp
      rw [he]
      exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => hI.preimage
        ((continuous_apply j).comp ((continuous_apply i).comp
          (Units.continuous_val : Continuous (fun g : GL (Fin n) RationalFiniteAdeles => g.val))))))
  exact hV.inter (hV.preimage continuous_inv)

lemma continuous_rowRegular {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
    [IsModuleTopology R S] [Fintype ι] [DecidableEq ι] (b : Basis ι R S) :
    Continuous (rowRegular b) := by
  have hb := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  apply continuous_matrix
  intro i j
  simp only [rowRegular_apply]
  exact ((continuous_apply j).comp hb).comp (continuous_id.mul_const (b i))

lemma continuous_rowRegularUnits {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
    [IsModuleTopology R S] [Fintype ι] [DecidableEq ι] (b : Basis ι R S) :
    Continuous (rowRegularUnits b) := (continuous_rowRegular b).units_map

lemma continuous_adelicIdelePoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (σ : OrderedEmbeddings n K) (g : GL (Fin n) RationalFiniteAdeles) :
    Continuous (adelicIdelePoint hodd hn b σ g) := by
  let H : (TensorAdeles K)ˣ → GL (Fin n) ℝ := fun t =>
    GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) t) * realBasisGL hn b σ
  let F : (TensorAdeles K)ˣ → GL (Fin n) RationalFiniteAdeles := fun t =>
    GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)
      (rowRegularUnits (b.baseChange RationalAdeles) t) * g
  have hH : Continuous H := ((Continuous.generalLinearGroup_map continuous_fst).comp
    (continuous_rowRegularUnits (b.baseChange RationalAdeles))).mul_const _
  have hF : Continuous F := ((Continuous.generalLinearGroup_map continuous_snd).comp
    (continuous_rowRegularUnits (b.baseChange RationalAdeles))).mul_const _
  have he (t : (TensorAdeles K)ˣ) : adelicIdelePoint hodd hn b σ g t =
      (ambientEquiv hodd hn b).symm (adelicMatrixPoint (H t) (F t)) := by
    congr 1
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨c,hc⟩ := finite_matrix_rational_reduction hn b (F t)
  have hcF : Continuous (fun s => GeneralLinearGroup.map rationalFiniteEmbedding c * F s) :=
    continuous_const.mul hF
  have hne : ∀ᶠ s in 𝓝 t, IntegralFiniteGL (GeneralLinearGroup.map rationalFiniteEmbedding c * F s) :=
    ((integralFiniteGroup_isOpen n).preimage hcF).mem_nhds hc
  have hloc : Continuous (fun s => (Quotient.mk _
      (realSLNormalize hodd (GeneralLinearGroup.map (algebraMap ℚ ℝ) c * H s)) : X n)) :=
    continuous_quotient_mk'.comp ((continuous_realSLNormalize hodd).comp (continuous_const.mul hH))
  apply hloc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hne] with s hs
  rw [he,adelicMatrixPoint_reduction _ _ _ hs]
  apply (ambientEquiv hodd hn b).injective
  rw [Equiv.apply_symm_apply,ambientEquiv_realSLNormalize]

lemma continuous_adelicTorusPoint {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (σ : OrderedEmbeddings n K) (g : GL (Fin n) RationalFiniteAdeles) :
    Continuous (adelicTorusPoint hodd hn b σ g) :=
  (continuous_adelicIdelePoint hodd hn b σ g).quotient_lift _

end PrimeDegreePackets.Adelic

end

end OAI
