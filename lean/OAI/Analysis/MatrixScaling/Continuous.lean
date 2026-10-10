import OAI.Analysis.MatrixScaling.Critical
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Order.Basic

namespace OAI

/-! Continuous dependence of the unique normalized scaling. -/

namespace Kaplansky

theorem continuous_unique_minimizer {X K : Type*}
    [TopologicalSpace X] [TopologicalSpace K] [CompactSpace K]
    (g : X × K → ℝ) (hg : Continuous g) (m : X → K)
    (hmin : ∀ x z, g (x,m x) ≤ g (x,z))
    (hunique : ∀ x y, (∀ z, g (x,y) ≤ g (x,z)) → y = m x) :
    Continuous m := by
  let G : Set (X × K) := {p | ∀ z, g p ≤ g (p.1,z)}
  have hG : IsClosed G := by
    simp only [G, Set.ofPred_forall]
    apply isClosed_iInter
    intro z
    exact isClosed_le hg (hg.comp (continuous_fst.prodMk continuous_const))
  rw [continuous_iff_isClosed]
  intro s hs
  have heq : m ⁻¹' s = Prod.fst '' (G ∩ Prod.snd ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x,m x), ⟨hmin x, hx⟩, rfl⟩
    · rintro ⟨⟨x',y⟩,⟨hy,hys⟩,hxy⟩
      change x' = x at hxy
      subst x'
      have he := hunique x y hy
      simpa only [Set.mem_preimage, he] using hys
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ (hG.inter (hs.preimage continuous_snd))

end Kaplansky

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

theorem continuous_scalingPotential {Y : Type*} [TopologicalSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) (hpos : ∀ y, (P y).PosDef) :
    Continuous (fun y => scalingPotential (T y) (P y)) := by
  have hp : Continuous (fun y => (P y).det.re) := Complex.continuous_re.comp hP.matrix_det
  have hd := continuous_scalingMap T hT P hP
  have hq : Continuous (fun y => (1+scalingMap (T y) (P y)).det.re) :=
    Complex.continuous_re.comp (continuous_const.add hd).matrix_det
  exact (hq.log (fun y => ne_of_gt (posDef_det_re_pos
    (Matrix.PosDef.one.add_posSemidef (scalingMap_positive (T y) (hpos y).posSemidef))))).sub
    ((hp.log (fun y => ne_of_gt (posDef_det_re_pos (hpos y)))).const_mul (3/2))

theorem exists_continuous_scaling_minimizer {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ P : Y → Matrix (Fin d) (Fin d) ℂ, Continuous P ∧ ∀ y, (P y).PosDef ∧
      ∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef → scalingPotential (T y) (P y) ≤ scalingPotential (T y) Q := by
  choose P hP using fun y => (existsUnique_scaling_minimizer (T y) (hexpand y)).exists
  have hidentity := continuous_scalingPotential T hT (fun _ => 1) continuous_const
    (fun _ => Matrix.PosDef.one)
  obtain ⟨C,hC⟩ := (isCompact_range hidentity).bddAbove
  obtain ⟨ε,hε,hbound⟩ := uniform_scaling_sublevels T hT hexpand
  let B := C-(d-1)*((3/2)*Real.log ε)
  let a := Real.exp (-2*B/3)
  let b := Real.exp (2*B-4*Real.log ε)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 ≤ b := (Real.exp_pos _).le
  let K := spectralWindow d a b
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_spectralWindow (d := d) ha.le hb)
  have hmem (y : Y) : (⟨P y,(hP y).1.1⟩ : HermitianMatrices d) ∈ K := by
    apply hbound C y (P y) (hP y).1
    exact ((hP y).2 1 Matrix.PosDef.one).trans (hC ⟨y,rfl⟩)
  let m : Y → K := fun y => ⟨⟨P y,(hP y).1.1⟩,hmem y⟩
  let g : Y × K → ℝ := fun z => scalingPotential (T z.1) z.2.val.val
  have hg : Continuous g :=
    continuous_scalingPotential (fun z : Y × K => T z.1) (hT.comp continuous_fst)
      (fun z : Y × K => z.2.val.val)
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
      (fun z => spectralWindow_posDef ha z.2.property)
  have hm : Continuous m := by
    apply continuous_unique_minimizer g hg m
    · intro y z
      exact (hP y).2 z.val.val (spectralWindow_posDef ha z.property)
    · intro y z hz
      have hglob : ∀ Q : Matrix (Fin d) (Fin d) ℂ, Q.PosDef →
          scalingPotential (T y) z.val.val ≤ scalingPotential (T y) Q := by
        intro Q hQ
        exact (hz (m y)).trans ((hP y).2 Q hQ)
      have he := scaling_minimizer_unique (T y) (hexpand y)
        (spectralWindow_posDef ha z.property) (hP y).1 hglob (hP y).2
      apply Subtype.ext
      exact Subtype.ext he
  refine ⟨P,?_,hP⟩
  exact continuous_subtype_val.comp (continuous_subtype_val.comp hm)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem gramFactor_inverse_identity (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A) :
    A.conjTranspose * (A*A.conjTranspose)⁻¹ * A = 1 := by
  have hi : A⁻¹*A=1 := Matrix.nonsing_inv_mul A (A.isUnit_iff_isUnit_det.mp hA)
  have his : A.conjTranspose * (A⁻¹).conjTranspose = 1 := by
    rw [← Matrix.conjTranspose_mul, hi, Matrix.conjTranspose_one]
  rw [Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_assoc, his, Matrix.one_mul, hi]

theorem exists_scaled_tuple (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ X : Fin n → Matrix (Fin r) (Fin d) ℂ,
      (∑ i, (X i).conjTranspose * X i) = 1 ∧
      ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        ∑ i, X i * (X i).conjTranspose).PosSemidef := by
  obtain ⟨P,⟨hP,hmin⟩,_⟩ := existsUnique_scaling_minimizer T hexpand
  have hcrit := scaling_minimizer_critical T hP hmin
  let Q := 1+scalingMap T P
  have hQ : Q.PosDef := Matrix.PosDef.one.add_posSemidef (scalingMap_positive T hP.posSemidef)
  obtain ⟨A,hA,hAA⟩ := posDef_gram_factor hP
  obtain ⟨B,hB,hBB⟩ := posDef_gram_factor hQ
  let J := B⁻¹
  have hJ : J.conjTranspose*J = Q⁻¹ := by
    rw [← hBB, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv]
  have hAP : A.conjTranspose*P⁻¹*A = 1 := by
    rw [← hAA]
    exact gramFactor_inverse_identity A hA
  have hJB : J*B=1 := Matrix.nonsing_inv_mul B (B.isUnit_iff_isUnit_det.mp hB)
  have hJQ : J*Q*J.conjTranspose=1 := by
    rw [← hBB]
    have hs : B.conjTranspose*J.conjTranspose=1 := by
      rw [← Matrix.conjTranspose_mul, hJB, Matrix.conjTranspose_one]
    rw [← Matrix.mul_assoc, hJB, Matrix.one_mul, hs]
  refine ⟨normalizedTuple T A J, ?_, ?_⟩
  · rw [normalizedTuple_column, hJ, hcrit, Matrix.mul_smul, Matrix.smul_mul, hAP, smul_smul]
    norm_num
  · rw [normalizedTuple_row, hAA]
    have hD : scalingMap T P = Q-1 := by dsimp [Q]; abel
    rw [hD, Matrix.mul_sub, Matrix.sub_mul, hJQ, Matrix.mul_one, smul_sub]
    have he : (2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        ((2/3 : ℂ) • 1 - (2/3 : ℂ) • (J*J.conjTranspose)) =
        (2/3 : ℂ) • (J*J.conjTranspose) := by abel
    rw [he]
    exact (Matrix.posSemidef_self_mul_conjTranspose J).smul (by constructor <;> norm_num)

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Topology
namespace Kaplansky
variable {n d r : ℕ}

/-- The normalization relations for any invertible Gram factors of a
minimizer and its target matrix. -/
theorem normalizedTuple_of_minimizer (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef)
    (hmin : ∀ R : Matrix (Fin d) (Fin d) ℂ, R.PosDef → scalingPotential T P ≤ scalingPotential T R)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A) (hAA : A*A.conjTranspose=P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : IsUnit B) (hBB : B*B.conjTranspose=1+scalingMap T P) :
    (∑ i, (normalizedTuple T A B⁻¹ i).conjTranspose * normalizedTuple T A B⁻¹ i) = 1 ∧
      ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        ∑ i, normalizedTuple T A B⁻¹ i * (normalizedTuple T A B⁻¹ i).conjTranspose).PosSemidef := by
  have hcrit := scaling_minimizer_critical T hP hmin
  let Q := 1+scalingMap T P
  let J := B⁻¹
  change B*B.conjTranspose=Q at hBB
  have hJ : J.conjTranspose*J = Q⁻¹ := by
    rw [← hBB, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv]
  have hAP : A.conjTranspose*P⁻¹*A = 1 := by
    rw [← hAA]
    exact gramFactor_inverse_identity A hA
  have hJB : J*B=1 := Matrix.nonsing_inv_mul B (B.isUnit_iff_isUnit_det.mp hB)
  have hJQ : J*Q*J.conjTranspose=1 := by
    rw [← hBB]
    have hs : B.conjTranspose*J.conjTranspose=1 := by
      rw [← Matrix.conjTranspose_mul, hJB, Matrix.conjTranspose_one]
    rw [← Matrix.mul_assoc, hJB, Matrix.one_mul, hs]
  refine ⟨?_, ?_⟩
  · rw [normalizedTuple_column, hJ, hcrit, Matrix.mul_smul, Matrix.smul_mul, hAP, smul_smul]
    norm_num
  · rw [normalizedTuple_row, hAA]
    have hD : scalingMap T P = Q-1 := by dsimp [Q]; abel
    rw [hD, Matrix.mul_sub, Matrix.sub_mul, hJQ, Matrix.mul_one, smul_sub]
    have he : (2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        ((2/3 : ℂ) • 1 - (2/3 : ℂ) • (J*J.conjTranspose)) =
        (2/3 : ℂ) • (J*J.conjTranspose) := by abel
    rw [he]
    exact (Matrix.posSemidef_self_mul_conjTranspose J).smul (by constructor <;> norm_num)

theorem matrix_sqrt_factor {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    IsUnit (CFC.sqrt P) ∧ CFC.sqrt P * (CFC.sqrt P).conjTranspose = P := by
  refine ⟨CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hP.isStrictlyPositive, ?_⟩
  have hs : (CFC.sqrt P).conjTranspose = CFC.sqrt P := (CFC.sqrt_nonneg P).isSelfAdjoint.star_eq
  rw [hs, CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg]

theorem continuous_matrix_sqrt {Y : Type*} [TopologicalSpace Y]
    (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) (hpos : ∀ y, (P y).PosDef) :
    Continuous (fun y => CFC.sqrt (P y)) :=
  CFC.continuousOn_sqrt.comp_continuous hP (fun y => (hpos y).posSemidef.nonneg)

theorem continuous_matrix_inverse {Y : Type*} [TopologicalSpace Y]
    (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) (hunit : ∀ y, IsUnit (P y)) :
    Continuous (fun y => (P y)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hi : ContinuousAt Ring.inverse (P y).det := by
    rw [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀
      ((P y).isUnit_iff_isUnit_det.mp (hunit y)).ne_zero
  exact (continuousAt_matrix_inv (P y) hi).comp hP.continuousAt

theorem exists_continuous_scaled_tuple {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)), 2*Module.finrank ℂ S ≤
      Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ X : Y → Fin n → Matrix (Fin r) (Fin d) ℂ, Continuous X ∧ ∀ y,
      (∑ i, (X y i).conjTranspose * X y i) = 1 ∧
      ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
        ∑ i, X y i * (X y i).conjTranspose).PosSemidef := by
  obtain ⟨P,hP,hmin⟩ := exists_continuous_scaling_minimizer T hT hexpand
  let Q := fun y => 1+scalingMap (T y) (P y)
  have hQ : Continuous Q := continuous_const.add (continuous_scalingMap T hT P hP)
  have hQpos (y : Y) : (Q y).PosDef :=
    Matrix.PosDef.one.add_posSemidef (scalingMap_positive (T y) (hmin y).1.posSemidef)
  let A := fun y => CFC.sqrt (P y)
  let B := fun y => CFC.sqrt (Q y)
  have hA := continuous_matrix_sqrt P hP (fun y => (hmin y).1)
  have hB := continuous_matrix_sqrt Q hQ hQpos
  have hBi := continuous_matrix_inverse B hB (fun y => (matrix_sqrt_factor (hQpos y)).1)
  refine ⟨fun y => normalizedTuple (T y) (A y) (B y)⁻¹, ?_, ?_⟩
  · apply continuous_pi
    intro i
    exact (continuous_const : Continuous (fun _ : Y => (Real.sqrt (2/3 : ℝ) : ℂ))).smul
      ((hBi.matrix_mul ((continuous_apply i).comp hT)).matrix_mul hA)
  · intro y
    exact normalizedTuple_of_minimizer (T y) (hmin y).1 (hmin y).2 (A y)
      (matrix_sqrt_factor (hmin y).1).1 (matrix_sqrt_factor (hmin y).1).2 (B y)
      (matrix_sqrt_factor (hQpos y)).1 (matrix_sqrt_factor (hQpos y)).2

end Kaplansky

end

end OAI
