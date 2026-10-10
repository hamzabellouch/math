import OAI.InformationTheory.PhotonNumber.FiniteVariation

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap

namespace TensorLp
open scoped ENNReal
variable {A B : Type*}

theorem positive_quadratic_slices {Z : H A →L[ℂ] H A} (hZ : Z.IsPositive)
    (x : H (A × B)) :
    ENNReal.ofReal (inner ℂ x (liftLeft Z x)).re=
      ∑' b, ENNReal.ofReal (inner ℂ (slice x b) (Z (slice x b))).re := by
  have hs : HasSum (fun b => (inner ℂ (slice x b) (Z (slice x b))).re)
      (inner ℂ x (liftLeft Z x)).re := by
    simpa only [Complex.reCLM_apply,slice_liftLeft] using
      (hasSum_slice_inner x (liftLeft Z x)).mapL Complex.reCLM
  have hn (b : B) : 0 ≤ (inner ℂ (slice x b) (Z (slice x b))).re :=
    hZ.re_inner_nonneg_right (slice x b)
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hn hs.summable]
end TensorLp

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {J : Type*}

theorem weightedConditional_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη y B x)).re=
      ∑' j, ∑' e, Q (slice (beamUnitary η hη
        (tensor (inverseWeight 2 x) (inverseWeight 2 (y j)))) e) := by
  have hp := liftLeft_positive (B:=NumberIndex n) hB
  have hs : HasSum (fun j => (inner ℂ (weightedColumn η hη (y j) x)
      (liftLeft B (weightedColumn η hη (y j) x))).re)
      (inner ℂ x (weightedConditional η hη y B x)).re := by
    exact (EnsemblePullback.hasSum_entry (weightedColumn_summable η hη y hy)
      (liftLeft B) x x).mapL Complex.reCLM
  have hn (j : J) : 0 ≤ (inner ℂ (weightedColumn η hη (y j) x)
      (liftLeft B (weightedColumn η hη (y j) x))).re :=
    hp.re_inner_nonneg_right (weightedColumn η hη (y j) x)
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg hn hs.summable]
  apply tsum_congr
  intro j
  rw [positive_quadratic_slices hB]
  apply tsum_congr
  intro e
  rw [hQ]
  congr 1
  rw [← slice_liftLeft,weightedColumn_inverse]
theorem weightedConditionalRight_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (y : J → Fock n) (hy : Summable (fun j => ‖y j‖^2))
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη y B x)).re=
      ∑' j, ∑' e, Q (slice (beamUnitary η hη
        (tensor (inverseWeight 2 (y j)) (inverseWeight 2 x))) e) := by
  have hp := liftLeft_positive (B:=NumberIndex n) hB
  have hs : HasSum (fun j => (inner ℂ (weightedColumnRight η hη (y j) x)
      (liftLeft B (weightedColumnRight η hη (y j) x))).re)
      (inner ℂ x (weightedConditionalRight η hη y B x)).re := by
    exact (EnsemblePullback.hasSum_entry (weightedColumnRight_summable η hη y hy)
      (liftLeft B) x x).mapL Complex.reCLM
  have hn (j : J) : 0 ≤ (inner ℂ (weightedColumnRight η hη (y j) x)
      (liftLeft B (weightedColumnRight η hη (y j) x))).re :=
    hp.re_inner_nonneg_right (weightedColumnRight η hη (y j) x)
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg hn hs.summable]
  apply tsum_congr
  intro j
  rw [positive_quadratic_slices hB]
  apply tsum_congr
  intro e
  rw [hQ]
  congr 1
  rw [← slice_liftLeft,weightedColumnRight_inverse]
end BeamLadder

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ}
theorem weightedConditional_root_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (σ : State n) (hm : FiniteMoment 4 σ)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη (weightedRoot 2 σ hm) B x)).re=
      ∑' eb, Q (firstKraus η hη σ eb (inverseWeight 2 x)) := by
  rw [weightedConditional_form η hη _ (weightedRoot_summable 2 σ hm) B hB Q hQ]
  simp only [inverse_weightedRoot,firstKraus_apply,ENNReal.tsum_prod']
  exact ENNReal.tsum_comm

theorem weightedConditionalRight_root_form (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (σ : State n) (hm : FiniteMoment 4 σ)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη (weightedRoot 2 σ hm) B x)).re=
      ∑' eb, Q (secondKraus η hη σ eb (inverseWeight 2 x)) := by
  rw [weightedConditionalRight_form η hη _ (weightedRoot_summable 2 σ hm) B hB Q hQ]
  simp only [inverse_weightedRoot,secondKraus_apply,ENNReal.tsum_prod']
  exact ENNReal.tsum_comm

namespace GibbsData
variable {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

theorem logarithmic_weight_nonneg (j : G.J) : 0 ≤ -Real.log (gibbsWeight G.eigenval j) := by
  let : Nonempty G.J := G.nonempty
  apply neg_nonneg.mpr
  apply Real.log_nonpos (gibbsWeight_pos G.eigenval G.heat j).le
  have hh := (gibbsWeight_hasSum G.eigenval G.heat).summable.le_tsum j
    (fun i _ => (gibbsWeight_pos G.eigenval G.heat i).le)
  rwa [(gibbsWeight_hasSum G.eigenval G.heat).tsum_eq] at hh

theorem quarticLogarithm_positive (hk : 0<k) : G.quarticLogarithm.IsPositive := by
  have hA := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (gibbsFactor_strictPositive rootNumberWeight rootNumberWeight_one_le hk G.positive).nonneg
  have hs : G.quarticLogarithm.IsSymmetric := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    unfold quarticLogarithm logarithmSandwich
    apply IsSelfAdjoint.add hA.isSelfAdjoint
    have hi : IsSelfAdjoint ((inversePower (rootNumberWeight (n:=n)) rootNumberWeight_one_le 4)*
        inversePower rootNumberWeight rootNumberWeight_one_le 4) := by
      simpa only [pow_two] using
        (inversePower_positive (rootNumberWeight (n:=n)) rootNumberWeight_one_le 4).isSelfAdjoint.pow 2
    exact (show IsSelfAdjoint (Real.log (heatPartition G.eigenval):ℂ) from Complex.conj_ofReal _).smul hi
  refine ⟨hs,fun x => ?_⟩
  change 0 ≤ RCLike.re (inner ℂ (G.quarticLogarithm x) x)
  rw [inner_re_symm]
  exact (G.quarticLogarithm_parseval hk x).nonneg
    (fun j => mul_nonneg (G.logarithmic_weight_nonneg j) (sq_nonneg _))

theorem quarticLogarithm_form (hk : 0<k) (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (G.quarticLogarithm x)).re=
      basisMoment G.basis (fun j => ENNReal.ofReal (-Real.log (gibbsWeight G.eigenval j)))
        (inverseWeight 2 x) := by
  have hs := G.quarticLogarithm_parseval hk x
  rw [inversePower_root_four] at hs
  rw [basisMoment_ofReal G.basis _ G.logarithmic_weight_nonneg _ hs.summable,hs.tsum_eq]

end GibbsData

def WeightedColumns.canonical (ρ : State n) (hm : FiniteMoment 6 ρ) : WeightedColumns ρ where
  Index := NumberIndex n
  vector := weightedRoot 3 ρ hm
  summable := weightedRoot_summable 3 ρ hm
  normalized := by simpa only [inverse_weightedRoot] using rootColumn_norm ρ
  density := by simpa only [inverse_weightedRoot] using rootColumn_operator ρ

theorem weightedRoot_inverse_one (ρ : State n) (hm : FiniteMoment 6 ρ)
    (hm4 : FiniteMoment 4 ρ) (i : NumberIndex n) :
    inverseWeight 1 (weightedRoot 3 ρ hm i)=weightedRoot 2 ρ hm4 i := by
  apply lp.ext
  funext k
  have hw : (numberWeight k:ℂ) ≠ 0 := by
    exact_mod_cast (show numberWeight k ≠ 0 by linarith [numberWeight_one_le k])
  simp only [inverseWeight_apply,weightedRoot_apply,Complex.ofReal_pow,pow_one]
  field_simp

namespace WeightedColumns

theorem canonical_slice (ρ : State n) (hm : FiniteMoment 6 ρ) (hm4 : FiniteMoment 4 ρ)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) :
    (canonical ρ hm).slice η hη B=weightedConditional η hη (weightedRoot 2 ρ hm4) B := by
  unfold slice canonical
  congr 1
  funext i
  exact weightedRoot_inverse_one ρ hm hm4 i

theorem canonical_sliceRight (ρ : State n) (hm : FiniteMoment 6 ρ) (hm4 : FiniteMoment 4 ρ)
    (η : ℝ) (hη : η ∈ Set.Icc 0 1) (B : Fock n →L[ℂ] Fock n) :
    (canonical ρ hm).sliceRight η hη B=weightedConditionalRight η hη (weightedRoot 2 ρ hm4) B := by
  unfold sliceRight canonical
  congr 1
  funext i
  exact weightedRoot_inverse_one ρ hm hm4 i
end WeightedColumns

theorem weightedConditional_positive (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {J : Type*} (y : J → Fock n) {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) :
    (weightedConditional η hη y B).IsPositive :=
  EnsemblePullback.pullback_positive _ (liftLeft_positive hB)

theorem weightedConditionalRight_positive (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {J : Type*} (y : J → Fock n) {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) :
    (weightedConditionalRight η hη y B).IsPositive :=
  EnsemblePullback.pullback_positive _ (liftLeft_positive hB)

theorem weightedConditional_twopass_form (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη (weightedRoot 2 σ hσ)
        (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re=
      ∑' ij, Q (composeKraus (firstKraus θ hθ τD) (firstKraus η hη σ) ij (inverseWeight 2 x)) := by
  rw [weightedConditional_root_form η hη σ hσ _
    (weightedConditional_positive θ hθ _ hB)
    (fun z => ∑' e, Q (firstKraus θ hθ τD e z))
    (weightedConditional_root_form θ hθ τD hD B hB Q hQ)]
  simp only [composeKraus,ContinuousLinearMap.comp_apply]
  rw [ENNReal.tsum_prod' (f := fun ij :
    (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n) =>
      Q (firstKraus θ hθ τD ij.1 (firstKraus η hη σ ij.2 (inverseWeight 2 x))))]
  exact ENNReal.tsum_comm

theorem weightedConditionalRight_twopass_form (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (Q : Fock n → ℝ≥0∞)
    (hQ : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=Q (inverseWeight 2 x))
    (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη (weightedRoot 2 σ hσ)
        (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re=
      ∑' ij, Q (composeKraus (firstKraus θ hθ τD) (secondKraus η hη σ) ij (inverseWeight 2 x)) := by
  rw [weightedConditionalRight_root_form η hη σ hσ _
    (weightedConditional_positive θ hθ _ hB)
    (fun z => ∑' e, Q (firstKraus θ hθ τD e z))
    (weightedConditional_root_form θ hθ τD hD B hB Q hQ)]
  simp only [composeKraus,ContinuousLinearMap.comp_apply]
  rw [ENNReal.tsum_prod' (f := fun ij :
    (NumberIndex n × NumberIndex n) × (NumberIndex n × NumberIndex n) =>
      Q (firstKraus θ hθ τD ij.1 (secondKraus η hη σ ij.2 (inverseWeight 2 x))))]
  exact ENNReal.tsum_comm

theorem spectral_physical_twopass_identification {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞)
    (B C : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (hC : C.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=basisMoment b w (inverseWeight 2 x))
    (hCe : ∀ x, ENNReal.ofReal (inner ℂ x (C x)).re=
      sliceMoment b w (composeKraus (firstKraus θ hθ τD) (firstKraus η hη σ))
        (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) :
    C=weightedConditional η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) := by
  have hp := weightedConditional_positive η hη (weightedRoot 2 σ hσ)
    (weightedConditional_positive θ hθ (weightedRoot 2 τD hD) hB)
  apply positive_eq_of_quadratic hC hp
  intro x
  apply (ENNReal.ofReal_eq_ofReal_iff (hC.re_inner_nonneg_right x) (hp.re_inner_nonneg_right x)).mp
  change ENNReal.ofReal (inner ℂ x (C x)).re =
    ENNReal.ofReal (inner ℂ x (weightedConditional η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re
  rw [hCe,inversePower_root_four,weightedConditional_twopass_form η θ hη hθ σ τD hσ hD B hB
    (basisMoment b w) hBe]
  rfl

theorem spectral_physical_right_twopass_identification {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τD : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 τD)
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞)
    (B C : Fock n →L[ℂ] Fock n) (hB : B.IsPositive) (hC : C.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=basisMoment b w (inverseWeight 2 x))
    (hCe : ∀ x, ENNReal.ofReal (inner ℂ x (C x)).re=
      sliceMoment b w (composeKraus (firstKraus θ hθ τD) (secondKraus η hη σ))
        (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) :
    C=weightedConditionalRight η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) := by
  have hp := weightedConditionalRight_positive η hη (weightedRoot 2 σ hσ)
    (weightedConditional_positive θ hθ (weightedRoot 2 τD hD) hB)
  apply positive_eq_of_quadratic hC hp
  intro x
  apply (ENNReal.ofReal_eq_ofReal_iff (hC.re_inner_nonneg_right x) (hp.re_inner_nonneg_right x)).mp
  change ENNReal.ofReal (inner ℂ x (C x)).re =
    ENNReal.ofReal (inner ℂ x (weightedConditionalRight η hη (weightedRoot 2 σ hσ)
      (weightedConditional θ hθ (weightedRoot 2 τD hD) B) x)).re
  rw [hCe,inversePower_root_four,weightedConditionalRight_twopass_form η θ hη hθ σ τD hσ hD B hB
    (basisMoment b w) hBe]
  rfl
end

section
open QuantumTrace TensorLp

theorem output_logarithm_representation {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 x) := by
  let V : Unit → Fock n →L[ℂ] Fock n := fun _ => 1
  have hV : ∀ x : Fock n, HasSum (fun i => ‖V i x‖^2) (‖x‖^2) := by
    intro x
    simpa only [V,one_apply_eq_self,Finset.univ_unique,Finset.sum_singleton]
      using (hasSum_fintype (fun i : Unit => ‖V i x‖^2))
  have hE : ∀ x : Fock n,
      (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V i x)) ≤
        vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+
          ENNReal.ofReal 0*ENNReal.ofReal (‖x‖^2) := by
    intro x
    simp only [V,one_apply_eq_self,tsum_fintype,Fintype.sum_unique,ENNReal.ofReal_zero,zero_mul,add_zero,le_refl]
  obtain ⟨C,hC,hCe⟩ := logarithmic_slice_representation ρ hr hκ hκ1 hle b p hp hs he
    V 0 le_rfl hV hE
  let R := inversePower (rootNumberWeight (n:=n)) rootNumberWeight_one_le 3
  have hRa : R.adjoint=R := inversePower_adjoint _ _ _
  have hCR : (R*C*R).IsPositive := by
    simpa only [hRa, ← ContinuousLinearMap.mul_def, mul_assoc] using hC.adjoint_conj R
  refine ⟨R*C*R,hCR,fun x => ?_⟩
  have hquad : inner ℂ x ((R*C*R) x)=inner ℂ (R x) (C (R x)) := by
    change inner ℂ x (R (C (R x)))=_
    exact ((inversePower_positive rootNumberWeight rootNumberWeight_one_le 3).isSymmetric
      x (C (R x))).symm
  rw [hquad,hCe,energyInverse_mul_three]
  simp only [sliceMoment,V,one_apply_eq_self,tsum_fintype,Fintype.sum_unique]
end

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)

theorem exact_physical_first_logarithmic_identity {J : Type*}
    (R : Regularization n) (σ : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 R.τD)
    (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x))
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
        (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)).V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ D : Fock n →L[ℂ] Fock n, D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      G.quarticLogarithm = (k:ℂ) • (1 : Fock n →L[ℂ] Fock n)+
        (α:ℂ) • (weightedConditional R.η R.hη (weightedRoot 2 σ hσ)
          (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩
            (weightedRoot 2 R.τD hD) B))+(β:ℂ) • D+
        (Real.log (heatPartition G.eigenval):ℂ) •
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
            inversePower rootNumberWeight rootNumberWeight_one_le 4) := by
  obtain ⟨C,D,hC,hD',hCe,hDe,hid⟩ := G.exact_logarithmic_identity
    (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)) τ hr hδ hδ1 hle
      b p hp hs he hα hβ hform
  have hphysical := spectral_physical_twopass_identification R.η (1-R.δ) R.hη
    ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ σ R.τD hσ hD b
      (fun j => ENNReal.ofReal (-Real.log (p j))) B C hB hC hBe hCe
  exact ⟨D,hD',hDe,by simpa only [hphysical] using hid⟩

theorem exact_physical_second_logarithmic_identity {J : Type*}
    (R : Regularization n) (σ : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 R.τD)
    (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x))
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
        (R.secondFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)).V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ D : Fock n →L[ℂ] Fock n, D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      G.quarticLogarithm = (k:ℂ) • (1 : Fock n →L[ℂ] Fock n)+
        (α:ℂ) • (weightedConditionalRight R.η R.hη (weightedRoot 2 σ hσ)
          (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩
            (weightedRoot 2 R.τD hD) B))+(β:ℂ) • D+
        (Real.log (heatPartition G.eigenval):ℂ) •
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
            inversePower rootNumberWeight rootNumberWeight_one_le 4) := by
  obtain ⟨C,D,hC,hD',hCe,hDe,hid⟩ := G.exact_logarithmic_identity
    (R.secondFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)) τ hr hδ hδ1 hle
      b p hp hs he hα hβ hform
  have hphysical := spectral_physical_right_twopass_identification R.η (1-R.δ) R.hη
    ⟨sub_nonneg.mpr R.hδ.2, sub_le_self _ R.hδ.1⟩ σ R.τD hσ hD b
      (fun j => ENNReal.ofReal (-Real.log (p j))) B C hB hC hBe hCe
  exact ⟨D,hD',hDe,by simpa only [hphysical] using hid⟩
end GibbsData
end

namespace Regularization
open QuantumTrace
variable {n : ℕ} (R : Regularization n)

theorem minimum_centered_gibbs_data (ρ σ : State n) (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ),
        (∀ x, ENNReal.ofReal (inner ℂ x (G1.B x)).re =
          ENNReal.ofReal (R.c*(1-R.κ)/R.a1)*sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
            (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).V (energyInverse n x)+
          ENNReal.ofReal (R.b1/R.a1)*numberVectorMoment (energyInverse n x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (G2.B x)).re =
          ENNReal.ofReal (R.c*(1-R.κ)/R.a2)*sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
            (R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).V (energyInverse n x)+
          ENNReal.ofReal (R.b2/R.a2)*numberVectorMoment (energyInverse n x)) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G1.basis (gibbsWeight G1.eigenval)
            (BKM.center G1.basis (gibbsWeight G1.eigenval)
              ((R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).dual Z)) ≤
            (R.a1/R.c)*BKM.quadratic b p Z) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G2.basis (gibbsWeight G2.eigenval)
            (BKM.center G2.basis (gibbsWeight G2.eigenval)
              ((R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).dual Z)) ≤
            (R.a2/R.c)*BKM.quadratic b p Z) := by
  classical
  have hle : (R.κ : ℂ) • (thermalState n r hr).op ≤ (R.output ρ σ).op := by
    rw [← hτ]
    exact mixture_replacement_le R.κ R.hκ (R.rawOutput ρ σ) R.τ0
  obtain ⟨J,b,p,hp,hs,he⟩ := exists_faithful_eigenbasis_of_thermal_le (R.output ρ σ) hr hκ hle
  have hmin1 (ρ' : State n) (hmρ' : FiniteMoment 4 ρ') := hmin ρ' σ hmρ' hmσ
  have hmin2 (σ' : State n) (hmσ' : FiniteMoment 4 σ') := hmin ρ σ' hmρ hmσ'
  obtain ⟨G1,hG1,hh1⟩ := minimum_centered_hessian_data
    (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)) R.τ0 hr hτ R.κ R.hκ hκ
    R.c R.a1 R.b1 R.ζ R.hc R.ha1 R.hb1.le R.hζ ρ hmρ b p hp hs he (by
      intro ρ' hmρ'
      have h := hmin1 ρ' hmρ'
      dsimp only [objective] at h
      change R.c*entropy (R.output ρ σ)-R.a1*entropy ρ+R.b1*energy ρ+R.ζ*numberMoment 4 ρ ≤
        R.c*entropy (R.output ρ' σ)-R.a1*entropy ρ'+R.b1*energy ρ'+R.ζ*numberMoment 4 ρ'
      linarith)
  obtain ⟨G2,hG2,hh2⟩ := minimum_centered_hessian_data
    (R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)) R.τ0 hr hτ R.κ R.hκ hκ
    R.c R.a2 R.b2 R.ζ R.hc R.ha2 R.hb2.le R.hζ σ hmσ b p hp hs he (by
      intro σ' hmσ'
      have h := hmin2 σ' hmσ'
      dsimp only [objective] at h
      change R.c*entropy (R.output ρ σ)-R.a2*entropy σ+R.b2*energy σ+R.ζ*numberMoment 4 σ ≤
        R.c*entropy (R.output ρ σ')-R.a2*entropy σ'+R.b2*energy σ'+R.ζ*numberMoment 4 σ'
      linarith)
  exact ⟨J,b,p,hp,hs,he,G1,G2,hG1,hG2,hh1,hh2⟩

end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp
namespace Regularization
variable {n : ℕ} (R : Regularization n)

theorem minimum_physical_log_data (ρ σ : State n) (hmρ : FiniteMoment 4 ρ)
    (hmσ : FiniteMoment 4 σ) (hmD : FiniteMoment 4 R.τD)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
        (B D1 D2 : Fock n →L[ℂ] Fock n), B.IsPositive ∧ D1.IsPositive ∧ D2.IsPositive ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
          basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D1 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D2 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (G1.quarticLogarithm = ((R.ζ/R.a1:ℝ):ℂ) • (1 : Fock n →L[ℂ] Fock n)+
          ((R.c*(1-R.κ)/R.a1:ℝ):ℂ) •
            (weightedConditional R.η R.hη (weightedRoot 2 σ hmσ)
              (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                (weightedRoot 2 R.τD hmD) B))+
          ((R.b1/R.a1:ℝ):ℂ) • D1+(Real.log (heatPartition G1.eigenval):ℂ) •
            (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
              inversePower rootNumberWeight rootNumberWeight_one_le 4)) ∧
        (G2.quarticLogarithm = ((R.ζ/R.a2:ℝ):ℂ) • (1 : Fock n →L[ℂ] Fock n)+
          ((R.c*(1-R.κ)/R.a2:ℝ):ℂ) •
            (weightedConditionalRight R.η R.hη (weightedRoot 2 ρ hmρ)
              (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                (weightedRoot 2 R.τD hmD) B))+
          ((R.b2/R.a2:ℝ):ℂ) • D2+(Real.log (heatPartition G2.eigenval):ℂ) •
            (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
              inversePower rootNumberWeight rootNumberWeight_one_le 4)) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G1.basis (gibbsWeight G1.eigenval)
            (BKM.center G1.basis (gibbsWeight G1.eigenval)
              ((R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).dual Z)) ≤
            (R.a1/R.c)*BKM.quadratic b p Z) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G2.basis (gibbsWeight G2.eigenval)
            (BKM.center G2.basis (gibbsWeight G2.eigenval)
              ((R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).dual Z)) ≤
            (R.a2/R.c)*BKM.quadratic b p Z) := by
  obtain ⟨J,b,p,hp,hs,he,G1,G2,hf1,hf2,hh1,hh2⟩ :=
    R.minimum_centered_gibbs_data ρ σ hmρ hmσ hr hτ hκ hmin
  have hle : (R.κ : ℂ) • (thermalState n r hr).op ≤ (R.output ρ σ).op := by
    rw [← hτ]
    exact mixture_replacement_le R.κ R.hκ (R.rawOutput ρ σ) R.τ0
  obtain ⟨B,hB,hBe⟩ := output_logarithm_representation (R.output ρ σ) hr hκ R.hκ.2 hle b p hp hs he
  have hBe' (x : Fock n) : ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x) := by
    simpa only [inversePower_root_four] using hBe x
  have hα1 : 0 ≤ R.c*(1-R.κ)/R.a1 :=
    div_nonneg (mul_nonneg R.hc.le (sub_nonneg.mpr R.hκ.2)) R.ha1.le
  have hα2 : 0 ≤ R.c*(1-R.κ)/R.a2 :=
    div_nonneg (mul_nonneg R.hc.le (sub_nonneg.mpr R.hκ.2)) R.ha2.le
  obtain ⟨D1,hD1,heD1,hid1⟩ := G1.exact_physical_first_logarithmic_identity R σ hmσ hmD
    (R.output ρ σ) hr hκ R.hκ.2 hle b p hp hs he hα1
      (div_nonneg R.hb1.le R.ha1.le) B hB hBe' hf1
  obtain ⟨D2,hD2,heD2,hid2⟩ := G2.exact_physical_second_logarithmic_identity R ρ hmρ hmD
    (R.output ρ σ) hr hκ R.hκ.2 hle b p hp hs he hα2
      (div_nonneg R.hb2.le R.ha2.le) B hB hBe' hf2
  exact ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe',heD1,heD2,hid1,hid2,hh1,hh2⟩
end Regularization
end EntropyPhotonNumber

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ} {I : Type*}

theorem pairing_add (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (A B : Fock n →L[ℂ] Fock n) :
    pairing r x (A+B)=pairing r x A+pairing r x B := by
  apply (pairing_hasSum (numberBasis n) r x hx (A+B)).unique
  convert! (pairing_hasSum (numberBasis n) r x hx A).add
    (pairing_hasSum (numberBasis n) r x hx B) using 1
  ext k
  simp only [add_apply,inner_add_right]

theorem pairing_smul (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (c : ℂ) (A : Fock n →L[ℂ] Fock n) :
    pairing r x (c • A)=c*pairing r x A := by
  apply (pairing_hasSum (numberBasis n) r x hx (c • A)).unique
  convert! (pairing_hasSum (numberBasis n) r x hx A).mul_left c using 1
  ext k
  simp only [smul_apply,inner_smul_right]

theorem pairing_scalar_inverse (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (c : ℂ) :
    pairing r x (c • (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
      inversePower rootNumberWeight rootNumberWeight_one_le 4))=0 := by
  rw [pairing_smul r x hx,inversePower_root_four]
  change c*pairing r x (inverseWeight 2 ∘L inverseWeight 2)=0
  rw [← inverseWeight_add,pairing_inverse_zero,mul_zero]
end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {k : ℝ} {ρ : State n}
namespace GibbsData
variable (G : GibbsData n k ρ)
theorem exact_physical_first_logarithmic_pairing {J : Type*}
    (s : ℝ) (X : WeightedColumns ρ)
    (R : Regularization n) (σ : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 R.τD)
    (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x))
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
        (R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)).V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ D : Fock n →L[ℂ] Fock n, D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      WeightedGenerator.pairing s X.vector G.quarticLogarithm =
        (k:ℂ)*WeightedGenerator.pairing s X.vector (1 : Fock n →L[ℂ] Fock n)+
        (α:ℂ)*WeightedGenerator.pairing s X.vector
          (weightedConditional R.η R.hη (weightedRoot 2 σ hσ)
            (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
              (weightedRoot 2 R.τD hD) B))+
        (β:ℂ)*WeightedGenerator.pairing s X.vector D := by
  obtain ⟨D,hD',hDe,hid⟩ := G.exact_physical_first_logarithmic_identity R σ hσ hD
    τ hr hδ hδ1 hle b p hp hs he hα hβ B hB hBe hform
  refine ⟨D,hD',hDe,?_⟩
  have hh := congrArg (WeightedGenerator.pairing s X.vector) hid
  simpa only [WeightedGenerator.pairing_add s X.vector X.summable,
    WeightedGenerator.pairing_scalar_inverse s X.vector X.summable,
    WeightedGenerator.pairing_smul s X.vector X.summable,add_zero] using hh

theorem exact_physical_second_logarithmic_pairing {J : Type*}
    (s : ℝ) (X : WeightedColumns ρ)
    (R : Regularization n) (σ : State n) (hσ : FiniteMoment 4 σ) (hD : FiniteMoment 4 R.τD)
    (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x))
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j)))
        (R.secondFlow σ (finiteMoment_finiteEnergy (by norm_num) hσ)).V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ D : Fock n →L[ℂ] Fock n, D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      WeightedGenerator.pairing s X.vector G.quarticLogarithm =
        (k:ℂ)*WeightedGenerator.pairing s X.vector (1 : Fock n →L[ℂ] Fock n)+
        (α:ℂ)*WeightedGenerator.pairing s X.vector
          (weightedConditionalRight R.η R.hη (weightedRoot 2 σ hσ)
            (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
              (weightedRoot 2 R.τD hD) B))+
        (β:ℂ)*WeightedGenerator.pairing s X.vector D := by
  obtain ⟨D,hD',hDe,hid⟩ := G.exact_physical_second_logarithmic_identity R σ hσ hD
    τ hr hδ hδ1 hle b p hp hs he hα hβ B hB hBe hform
  refine ⟨D,hD',hDe,?_⟩
  have hh := congrArg (WeightedGenerator.pairing s X.vector) hid
  simpa only [WeightedGenerator.pairing_add s X.vector X.summable,
    WeightedGenerator.pairing_scalar_inverse s X.vector X.summable,
    WeightedGenerator.pairing_smul s X.vector X.summable,add_zero] using hh

end GibbsData
end

namespace Regularization

section
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} (R : Regularization n)

private theorem pairing_balance_algebra (a1 a2 c k b1 b2 t l1 l2 w1 w2 s1 s2 d1 d2 : ℂ)
    (ha1 : a1 ≠ 0) (ha2 : a2 ≠ 0)
    (h1 : l1=k/a1*w1+c*t/a1*s1+b1/a1*d1)
    (h2 : l2=k/a2*w2+c*t/a2*s2+b2/a2*d2) :
    a1*l1+a2*l2=c*t*(s1+s2)+b1*d1+b2*d2+k*(w1+w2) := by
  rw [h1,h2]
  field_simp [ha1,ha2]; ring

theorem minimum_physical_pairing_balance (ρ σ : State n) (hmρ : FiniteMoment 4 ρ)
    (hmσ : FiniteMoment 4 σ) (hmD : FiniteMoment 4 R.τD)
    {r : ℝ} (hr : 0 < r) (hτ : R.τ0 = thermalState n r hr) (hκ : 0 < R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j) = (p j : ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
        (B D1 D2 : Fock n →L[ℂ] Fock n), B.IsPositive ∧ D1.IsPositive ∧ D2.IsPositive ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
          basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D1 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D2 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ (s1 s2 : ℝ) (X : WeightedColumns ρ) (Y : WeightedColumns σ),
          (R.a1:ℂ)*WeightedGenerator.pairing s1 X.vector G1.quarticLogarithm+
          (R.a2:ℂ)*WeightedGenerator.pairing s2 Y.vector G2.quarticLogarithm=
          (R.c:ℂ)*((1-R.κ:ℝ):ℂ)*
            (WeightedGenerator.pairing s1 X.vector
              (weightedConditional R.η R.hη (weightedRoot 2 σ hmσ)
                (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                  (weightedRoot 2 R.τD hmD) B))+
             WeightedGenerator.pairing s2 Y.vector
              (weightedConditionalRight R.η R.hη (weightedRoot 2 ρ hmρ)
                (weightedConditional (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
                  (weightedRoot 2 R.τD hmD) B)))+
          (R.b1:ℂ)*WeightedGenerator.pairing s1 X.vector D1+
          (R.b2:ℂ)*WeightedGenerator.pairing s2 Y.vector D2+
          (R.ζ:ℂ)*(WeightedGenerator.pairing s1 X.vector (1 : Fock n →L[ℂ] Fock n)+
            WeightedGenerator.pairing s2 Y.vector (1 : Fock n →L[ℂ] Fock n))) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G1.basis (gibbsWeight G1.eigenval)
            (BKM.center G1.basis (gibbsWeight G1.eigenval)
              ((R.firstFlow σ (finiteMoment_finiteEnergy (by norm_num) hmσ)).dual Z)) ≤
            (R.a1/R.c)*BKM.quadratic b p Z) ∧
        (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace b p →
          (1-R.κ)^2*BKM.quadratic G2.basis (gibbsWeight G2.eigenval)
            (BKM.center G2.basis (gibbsWeight G2.eigenval)
              ((R.secondFlow ρ (finiteMoment_finiteEnergy (by norm_num) hmρ)).dual Z)) ≤
            (R.a2/R.c)*BKM.quadratic b p Z) := by
  obtain ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,hid1,hid2,hh1,hh2⟩ :=
    R.minimum_physical_log_data ρ σ hmρ hmσ hmD hr hτ hκ hmin
  refine ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,?_,hh1,hh2⟩
  intro s1 s2 X Y
  have he1 := congrArg (WeightedGenerator.pairing s1 X.vector) hid1
  have he2 := congrArg (WeightedGenerator.pairing s2 Y.vector) hid2
  simp only [WeightedGenerator.pairing_add s1 X.vector X.summable,
    WeightedGenerator.pairing_scalar_inverse s1 X.vector X.summable,
    WeightedGenerator.pairing_smul s1 X.vector X.summable,add_zero,
    Complex.ofReal_div,Complex.ofReal_mul] at he1
  simp only [WeightedGenerator.pairing_add s2 Y.vector Y.summable,
    WeightedGenerator.pairing_scalar_inverse s2 Y.vector Y.summable,
    WeightedGenerator.pairing_smul s2 Y.vector Y.summable,add_zero,
    Complex.ofReal_div,Complex.ofReal_mul] at he2
  apply pairing_balance_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ he1 he2
  · exact_mod_cast R.ha1.ne'
  · exact_mod_cast R.ha2.ne'
end

open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} (R : Regularization n)

theorem canonical_output_generator (ρ σ : State n)
    (hmρ : FiniteMoment 6 ρ) (hmσ : FiniteMoment 6 σ)
    (hmD : FiniteMoment 6 R.τD) (hmO : FiniteMoment 6 R.τ0)
    (a b d r0 : ℝ) (hd : 0<d) (hr0 : 0<r0)
    (heq : r0=(1-R.δ)*(R.η*a+(1-R.η)*b)+(1-(1-R.δ))*d)
    (hD : ∀ k l, entry R.τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry R.τ0.op k l=if k=l then (thermalWeight n r0 k:ℂ) else 0)
    (B : Fock n →L[ℂ] Fock n) :
    ∃ hm0 : FiniteMoment 6 (R.output ρ σ),
      WeightedGenerator.pairing r0 (WeightedColumns.canonical (R.output ρ σ) hm0).vector B=
      ((1-R.κ:ℝ):ℂ)*
        (WeightedGenerator.pairing a (WeightedColumns.canonical ρ hmρ).vector
          ((WeightedColumns.canonical σ hmσ).slice R.η R.hη
            ((WeightedColumns.canonical R.τD hmD).slice (1-R.δ)
              ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ B))+
         WeightedGenerator.pairing b (WeightedColumns.canonical σ hmσ).vector
          ((WeightedColumns.canonical ρ hmρ).sliceRight R.η R.hη
            ((WeightedColumns.canonical R.τD hmD).slice (1-R.δ)
              ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ B))) := by
  subst r0
  have hmM := beamOutput_finiteMoment R.η R.hη hmρ hmσ
  have hmG : FiniteMoment 6 (R.rawOutput ρ σ) :=
    beamOutput_finiteMoment (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ hmM hmD
  have hm0 : FiniteMoment 6 (R.output ρ σ) :=
    mixture_finiteMoment 6 (1-R.κ) ⟨sub_nonneg.mpr R.hκ.2,sub_le_self _ R.hκ.1⟩ hmG hmO
  refine ⟨hm0,?_⟩
  apply weighted_replaced_threeport_generator R.η (1-R.δ) R.κ a b d R.hη
    ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ ρ σ R.τD
      (beamOutput R.η R.hη ρ σ) (R.rawOutput ρ σ) R.τ0 (R.output ρ σ)
      (beamOutput_spec R.η R.hη ρ σ)
      (beamOutput_spec (1-R.δ) ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
        (beamOutput R.η R.hη ρ σ) R.τD)
      (WeightedColumns.canonical ρ hmρ) (WeightedColumns.canonical σ hmσ)
      (WeightedColumns.canonical R.τD hmD)
      (WeightedColumns.canonical (beamOutput R.η R.hη ρ σ) hmM)
      (WeightedColumns.canonical (R.rawOutput ρ σ) hmG)
      (WeightedColumns.canonical R.τ0 hmO)
      (WeightedColumns.canonical (R.output ρ σ) hm0) hd hr0 hD hO ?_ B
  change ((1-R.κ:ℝ):ℂ) • (R.rawOutput ρ σ).op+
    ((1-(1-R.κ):ℝ):ℂ) • R.τ0.op=
    ((1-R.κ:ℝ):ℂ) • (R.rawOutput ρ σ).op+(R.κ:ℂ) • R.τ0.op
  rw [sub_sub_cancel]
end Regularization

open QuantumTrace Annihilation BeamLadder TensorLp

private theorem thermal_state_entries (n : ℕ) (r : ℝ) (hr : 0<r) (k l : NumberIndex n) :
    entry (thermalState n r hr).op k l=if k=l then (thermalWeight n r k:ℂ) else 0 := by
  rw [entry,← numberBasis_apply n k,← numberBasis_apply n l]
  change inner ℂ (numberBasis n k) ((diagonalState _ _ _).op (numberBasis n l))=_
  rw [diagonalState_eigen,inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k l]
  split_ifs with h
  · subst l
    simp only [mul_one]
  · simp only [mul_zero]

namespace Regularization
variable {n : ℕ} (R : Regularization n)

theorem minimum_generator_log_balance (ρ σ : State n)
    (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    (s1 s2 d r0 : ℝ) (hd : 0<d) (hr0 : 0<r0)
    (heq : r0=(1-R.δ)*(R.η*s1+(1-R.η)*s2)+(1-(1-R.δ))*d)
    (hD : R.τD=thermalState n d hd) (hτ : R.τ0=thermalState n r0 hr0)
    (hκ : 0<R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0<p j) ∧ HasSum p 1 ∧ (∀ j, (R.output ρ σ).op (b j)=(p j:ℂ) • b j) ∧
      ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
        (B D1 D2 : Fock n →L[ℂ] Fock n), B.IsPositive ∧ D1.IsPositive ∧ D2.IsPositive ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (B x)).re=
          basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D1 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        (∀ x, ENNReal.ofReal (inner ℂ x (D2 x)).re=
          numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
        ∃ (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ) (h60 : FiniteMoment 6 (R.output ρ σ)),
        (R.a1:ℂ)*WeightedGenerator.pairing s1 (WeightedColumns.canonical ρ h6ρ).vector G1.quarticLogarithm+
        (R.a2:ℂ)*WeightedGenerator.pairing s2 (WeightedColumns.canonical σ h6σ).vector G2.quarticLogarithm=
        (R.c:ℂ)*WeightedGenerator.pairing r0 (WeightedColumns.canonical (R.output ρ σ) h60).vector B+
        (R.b1:ℂ)*WeightedGenerator.pairing s1 (WeightedColumns.canonical ρ h6ρ).vector D1+
        (R.b2:ℂ)*WeightedGenerator.pairing s2 (WeightedColumns.canonical σ h6σ).vector D2+
        (R.ζ:ℂ)*(WeightedGenerator.pairing s1 (WeightedColumns.canonical ρ h6ρ).vector
          (1 : Fock n →L[ℂ] Fock n)+
          WeightedGenerator.pairing s2 (WeightedColumns.canonical σ h6σ).vector
          (1 : Fock n →L[ℂ] Fock n)) := by
  have h6D : FiniteMoment 6 R.τD := by rw [hD]; exact thermalState_finiteMoment n 6 d hd
  have h4D : FiniteMoment 4 R.τD := finiteMoment_mono (by norm_num) h6D
  have h6O : FiniteMoment 6 R.τ0 := by rw [hτ]; exact thermalState_finiteMoment n 6 r0 hr0
  obtain ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,hbal,_,_⟩ :=
    R.minimum_physical_pairing_balance ρ σ hmρ hmσ h4D hr0 hτ hκ hmin
  have h6ρ : FiniteMoment 6 ρ := finiteMoment_mono (by norm_num) G1.moment
  have h6σ : FiniteMoment 6 σ := finiteMoment_mono (by norm_num) G2.moment
  obtain ⟨h60,hcov⟩ := R.canonical_output_generator ρ σ h6ρ h6σ h6D h6O
    s1 s2 d r0 hd hr0 heq
    (by intro k l; rw [hD]; exact thermal_state_entries n d hd k l)
    (by intro k l; rw [hτ]; exact thermal_state_entries n r0 hr0 k l) B
  have hb := hbal s1 s2 (WeightedColumns.canonical ρ h6ρ) (WeightedColumns.canonical σ h6σ)
  have hθ : 1-R.δ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
  change WeightedGenerator.pairing r0 (WeightedColumns.canonical (R.output ρ σ) h60).vector B=
    ((1-R.κ:ℝ):ℂ)*(WeightedGenerator.pairing s1 (WeightedColumns.canonical ρ h6ρ).vector
      ((WeightedColumns.canonical σ h6σ).slice R.η R.hη
        ((WeightedColumns.canonical R.τD h6D).slice (1-R.δ) hθ B))+
      WeightedGenerator.pairing s2 (WeightedColumns.canonical σ h6σ).vector
      ((WeightedColumns.canonical ρ h6ρ).sliceRight R.η R.hη
        ((WeightedColumns.canonical R.τD h6D).slice (1-R.δ) hθ B))) at hcov
  rw [WeightedColumns.canonical_slice R.τD h6D h4D,
    WeightedColumns.canonical_slice σ h6σ hmσ,
    WeightedColumns.canonical_sliceRight ρ h6ρ hmρ] at hcov
  rw [mul_assoc (R.c:ℂ),← hcov] at hb
  exact ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,h6ρ,h6σ,h60,hb⟩
end Regularization
end EntropyPhotonNumber

end

end OAI
