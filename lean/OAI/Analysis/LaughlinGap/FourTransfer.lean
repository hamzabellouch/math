import Mathlib
import OAI.Analysis.LaughlinGap.ExtendedPair
import OAI.Analysis.LaughlinGap.FourAllowance
import OAI.Analysis.LaughlinGap.FourComparison

namespace OAI

/-! Four Transfer. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

noncomputable def fourDimensionRatio (Q D : ℕ) : ℝ :=
  (4*(Q:ℝ)-1-2*(D:ℝ))/(2*(Q:ℝ)-1)

lemma fourDimensionRatio_tendsto (D : ℕ) :
    Tendsto (fun Q => fourDimensionRatio Q D) atTop (𝓝 2) := by
  have ht : Tendsto (fun Q : ℕ => (4-(1+2*(D:ℝ))/Q)/(2-(1:ℝ)/Q))
      atTop (𝓝 (2:ℝ)) := by
    convert ((tendsto_const_nhds (x := (4:ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1+2*(D:ℝ)))).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))) (by norm_num : (2:ℝ)-0 ≠ 0) using 1
    norm_num [Pi.div_def]
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hn : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold fourDimensionRatio
  field_simp [hn]
  ring

lemma fourDimensionRatio_eq {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q) :
    fourDimensionRatio Q D = ((4*Q-1-2*D:ℕ):ℝ)/((2*Q-1:ℕ):ℝ) := by
  rw [fourDimensionRatio,Nat.cast_sub (by omega : 2*D ≤ 4*Q-1),
    Nat.cast_sub (by omega : 1 ≤ 4*Q),Nat.cast_sub (by omega : 1 ≤ 2*Q)]
  norm_cast

variable {ι : Type*} [Fintype ι]

noncomputable def fourComparison (rows : ι → RowData) (ε : ℝ) (Q D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℝ :=
  fourDimensionRatio Q D • fourCopyTarget D -
    ∑ a, rowFourMatrix (fourWeightCoefficient Q) D (rows a) + ε • 1

noncomputable def fourComparisonStar (rows : ι → RowData) (ε : ℝ) (D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℝ :=
  (2:ℝ) • fourCopyTarget D -
    ∑ a, rowFourMatrix fourWeightCoefficientStar D (rows a) + ε • 1

lemma fourComparison_symmetric (rows : ι → RowData) (ε : ℝ) (Q D : ℕ) :
    (fourComparison rows ε Q D).IsHermitian := by
  unfold fourComparison
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.sub
    · exact (fourCopyTarget_symmetric D).smul (by rfl)
    · apply Matrix.IsHermitian.ext
      intro u v
      simp only [Matrix.sum_apply,star_trivial]
      exact Finset.sum_congr rfl (fun a _ => (rowFourMatrix_symmetric _ _ _).apply u v)
  · exact Matrix.isHermitian_one.smul (by rfl)

lemma fourComparisonStar_symmetric (rows : ι → RowData) (ε : ℝ) (D : ℕ) :
    (fourComparisonStar rows ε D).IsHermitian := by
  unfold fourComparisonStar
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.sub
    · exact (fourCopyTarget_symmetric D).smul (by rfl)
    · apply Matrix.IsHermitian.ext
      intro u v
      simp only [Matrix.sum_apply,star_trivial]
      exact Finset.sum_congr rfl (fun a _ => (rowFourMatrix_symmetric _ _ _).apply u v)
  · exact Matrix.isHermitian_one.smul (by rfl)

lemma fourComparison_tendsto (rows : ι → RowData) (ε : ℝ) (D : ℕ)
    (u v : FourCopy D) : Tendsto (fun Q => fourComparison rows ε Q D u v) atTop
      (𝓝 (fourComparisonStar rows ε D u v)) := by
  simp only [fourComparison,fourComparisonStar,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  exact (((fourDimensionRatio_tendsto D).mul_const _).sub
    (tendsto_finsetSum Finset.univ (fun a _ => rowFourMatrix_tendsto D (rows a) u v))).add_const _

def localTripleP {D : ℕ} (hD : D ≤ 23) (b : OrbitalTriple D) : Fin 24 :=
  ⟨b.val.1,by have := b.property; omega⟩
def localTripleJ {D : ℕ} (hD : D ≤ 23) (b : OrbitalTriple D) : Fin 25 :=
  ⟨b.val.2.1,by have := b.property; omega⟩
def localTripleK {D : ℕ} (hD : D ≤ 23) (b : OrbitalTriple D) : Fin 25 :=
  ⟨b.val.2.2,by have := b.property; omega⟩

noncomputable def fourHighestRowsStar (D : ℕ) :
    Matrix (FourCopy D) (OrbitalTriple D) ℝ := fun r b =>
  fourBodyCoefficientStar D D r.val.val b.val.1 b.val.2.1 b.val.2.2

noncomputable def fourLocalHighestStar {D : ℕ} (hD : D ≤ 23)
    (r : FourCopy D) : Module.End ℂ (Occupation.Hilbert 25) :=
  ∑ b : OrbitalTriple D, (fourHighestRowsStar D r b : ℂ) •
    (Occupation.annihilation (localTripleK hD b) * Occupation.annihilation (localTripleJ hD b) *
      Occupation.localPairStar 25 (localTripleP hD b).val)

lemma fourHighestRows_tendsto (D : ℕ) (r : FourCopy D) (b : OrbitalTriple D) :
    Tendsto (fun Q => fourHighestRows Q D r b) atTop (𝓝 (fourHighestRowsStar D r b)) :=
  fourBodyCoefficient_tendsto (Nat.le_of_lt_succ r.val.isLt) le_rfl _ _ _

def FourCertificate (rows : ι → RowData) (ε : ℝ) (D : ℕ) (hD : D ≤ 23) : Prop :=
  (Occupation.createdGram (fourLocalHighestStar hD) *
    (fourComparisonStar rows ε D).map (algebraMap ℝ ℂ) *
      Occupation.createdGram (fourLocalHighestStar hD)).PosSemidef

lemma complexify_four_highest {Q D : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (r : FourCopy D) :
    complexify (fourAnnihilator Q D D r.val.val) =
      Occupation.extendTo (show 25 ≤ Q+1 by omega)
        (∑ b : OrbitalTriple D, (fourHighestRows Q D r b : ℂ) •
          (Occupation.annihilation (localTripleK hD b) * Occupation.annihilation (localTripleJ hD b) *
            Occupation.localPair 25 Q (localTripleP hD b).val)) := by
  rw [fourAnnihilator_high_local (by omega) (by omega),complexify_combination]
  simp only [map_sum,map_smul,map_mul,Occupation.extendTo_annihilation]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Occupation.extendTo_localPair _ (by have := (localTripleP hD b).isLt; omega)]
  simp only [localFourCoordinates,orbitalTripleFinite,map_mul,complexify_annihilation,
    complexify_physicalPair,localTripleP,localTripleJ,localTripleK]
  rfl

lemma lift_symmetric {α β : Type*} [Fintype α] [Fintype β]
    (B : α → Matrix β β ℝ) {C : Matrix α α ℝ} (hC : C.IsHermitian) :
    (lift B C).IsHermitian := by
  classical
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [lift_transpose,(Matrix.conjTranspose_eq_transpose_of_trivial C).symm,hC.eq]

lemma posSemidef_of_complex_re {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : A.IsHermitian)
    (h : ∀ x : EuclideanSpace ℂ α, 0 ≤ (inner ℂ x (complexify A x)).re) : A.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hA,fun x => ?_⟩
  simpa [complexify,Matrix.toLpLin_apply,EuclideanSpace.inner_toLp_toLp,
    Matrix.mulVec,dotProduct,Complex.mul_re,Complex.add_re,mul_comm] using
      h (WithLp.toLp 2 (fun i => (x i : ℂ)))

lemma complexify_square_sum_inner {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (B : β → Matrix α α ℝ) (c : ℝ) (x : EuclideanSpace ℂ α) :
    (inner ℂ x (complexify (c • ∑ p, (B p).transpose * B p) x)).re =
      c * ∑ p, ‖complexify (B p) x‖^2 := by
  simp only [map_smul,map_sum,map_mul,complexify_transpose,LinearMap.smul_apply,
    LinearMap.sum_apply,Module.End.mul_apply,inner_smul_right_eq_smul,inner_sum,
    LinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

lemma complexify_four_local_lift {Q D : ℕ} (hQ : 24 ≤ Q) (hD : D ≤ 23)
    (C : Matrix (FourCopy D) (FourCopy D) ℝ) :
    complexify (lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val) C) =
      Occupation.extendTo (show 25 ≤ Q+1 by omega)
        (matrixLift (fun r => ∑ b : OrbitalTriple D, (fourHighestRows Q D r b : ℂ) •
          (Occupation.annihilation (localTripleK hD b) * Occupation.annihilation (localTripleJ hD b) *
            Occupation.localPair 25 Q (localTripleP hD b).val)) (C.map (algebraMap ℝ ℂ))) := by
  rw [complexify_lift,Occupation.extendTo_matrixLift]
  simp only [complexify_four_highest hQ hD]

theorem four_local_transfer (rows : ι → RowData) (ε : ℝ) {D : ℕ} (hD : D ≤ 23)
    (hc : FourCertificate rows ε D hD) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ᶠ Q in atTop, ∀ _hQ : 24 ≤ Q,
        -(ρ Q) • (∑ p : Fin 24, (physicalPair Q p.val).transpose * physicalPair Q p.val) ≤
          lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val) (fourComparison rows ε Q D) := by
  classical
  have hc₀ := (fourComparisonStar_symmetric rows ε D).map (algebraMap ℝ ℂ) (fun x => by simp)
  obtain ⟨ρ,hpos,hlim,hbound⟩ := Occupation.local_four_family_transfer_to
    (localTripleP hD) (localTripleJ hD) (localTripleK hD)
    (fun Q => fourHighestRows Q D) (fourHighestRowsStar D)
    (fun Q => (fourComparison rows ε Q D).map (algebraMap ℝ ℂ))
    ((fourComparisonStar rows ε D).map (algebraMap ℝ ℂ))
    (fourHighestRows_tendsto D)
    (fun r s => Complex.continuous_ofReal.continuousAt.tendsto.comp (fourComparison_tendsto rows ε D r s))
    hc₀ hc
  refine ⟨ρ,hpos,hlim,?_⟩
  filter_upwards [hbound] with Q bound
  intro hQ
  apply sub_nonneg.mp
  apply Matrix.PosSemidef.nonneg
  apply posSemidef_of_complex_re
  · exact (lift_symmetric _ (fourComparison_symmetric rows ε Q D)).sub
      ((Matrix.posSemidef_sum Finset.univ (fun p _ =>
        transpose_square_positive (physicalPair Q (p : Fin 24).val))).isHermitian.smul (by rfl))
  · intro x
    have hb := bound (Q+1) (by omega) x
    simp only [map_sub,LinearMap.sub_apply,inner_sub_right,Complex.sub_re]
    rw [complexify_four_local_lift hQ hD,complexify_square_sum_inner]
    simp only [complexify_physicalPair]
    apply sub_nonneg.mpr
    have hpair (p : Fin 24) := Occupation.extendTo_localPair (show 25 ≤ Q+1 by omega)
      (show p.val+1 < 25 by omega) (Q := Q)
    simpa only [hpair] using hb

end LaughlinGap.RealOccupation

end

end OAI
