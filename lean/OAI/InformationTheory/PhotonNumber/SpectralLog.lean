import OAI.InformationTheory.PhotonNumber.ThermalMetric

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace SquareAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

abbrev H (I : Type*) := lp (fun _ : I => ℂ) 2

def vector (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2)) (x : E) : H I :=
  ⟨fun i => f i x, (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs x)⟩

@[simp] theorem vector_apply (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (x : E) (i : I) : vector f hs x i = f i x := rfl

theorem hasSum_square (x : H I) : HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.hasSum_norm (p := 2) (by norm_num) x)

theorem vector_norm_sq (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (x : E) : ‖vector f hs x‖^2 = ∑' i, ‖f i x‖^2 :=
  (hasSum_square (vector f hs x)).tsum_eq.symm

def linearMap (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2)) :
    E →ₗ[ℂ] H I where
  toFun := vector f hs
  map_add' := fun x y => by apply lp.ext; funext i; exact map_add (f i) x y
  map_smul' := fun c x => by apply lp.ext; funext i; exact map_smul (f i) c x

theorem vector_norm_le (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) (x : E) :
    ‖vector f hs x‖ ≤ Real.sqrt C*‖x‖ := by
  have hh := hb x
  rw [← vector_norm_sq f hs x] at hh
  have he := Real.sq_sqrt hC
  have hp := mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg x)
  nlinarith [sq_nonneg (‖vector f hs x‖-Real.sqrt C*‖x‖)]

def continuousMap (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) : E →L[ℂ] H I :=
  (linearMap f hs).mkContinuous (Real.sqrt C) (vector_norm_le f hs hC hb)

@[simp] theorem continuousMap_apply (f : I → E →ₗ[ℂ] ℂ)
    (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) (x : E) :
    continuousMap f hs C hC hb x = vector f hs x := rfl

variable [CompleteSpace E]

def gram (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) : E →L[ℂ] E :=
  (continuousMap f hs C hC hb).adjoint ∘L continuousMap f hs C hC hb

theorem gram_positive (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) :
    (gram f hs C hC hb).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self _

theorem gram_quadratic (f : I → E →ₗ[ℂ] ℂ) (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) (x : E) :
    (inner ℂ x (gram f hs C hC hb x)).re = ∑' i, ‖f i x‖^2 := by
  exact ((continuousMap f hs C hC hb).apply_norm_sq_eq_inner_adjoint_right x).symm.trans
    (vector_norm_sq f hs x)

theorem exists_positive_representation (f : I → E →ₗ[ℂ] ℂ)
    (hs : ∀ x, Summable (fun i => ‖f i x‖^2))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, (∑' i, ‖f i x‖^2) ≤ C*‖x‖^2) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧ ∀ x, (inner ℂ x (B x)).re = ∑' i, ‖f i x‖^2 :=
  ⟨gram f hs C hC hb, gram_positive f hs C hC hb, gram_quadratic f hs C hC hb⟩

end SquareAnalysis

namespace QuantumTrace
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

def logCoordinates (b : HilbertBasis J ℂ E) (c : J → ℝ) (V : E →L[ℂ] E) (j : J) : E →ₗ[ℂ] ℂ :=
  (Real.sqrt (c j):ℂ) • ((innerSL ℂ (b j)).toLinearMap.comp V.toLinearMap)

omit [CompleteSpace E] in
theorem logCoordinates_square (b : HilbertBasis J ℂ E) (c : J → ℝ) (hc : ∀ j, 0≤c j)
    (V : E →L[ℂ] E) (j : J) (x : E) :
    ‖logCoordinates b c V j x‖^2=c j*‖inner ℂ (b j) (V x)‖^2 := by
  change ‖(Real.sqrt (c j):ℂ)*inner ℂ (b j) (V x)‖^2=_
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (hc j)]

theorem spectral_form_representation (b : HilbertBasis J ℂ E) (c : J → ℝ)
    (hc : ∀ j, 0≤c j) (V : E →L[ℂ] E) (hV : V.IsSymmetric)
    (hs : ∀ y, Summable (fun j => c j*‖inner ℂ (b j) (V y)‖^2))
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ y, (∑' j, c j*‖inner ℂ (b j) (V y)‖^2)≤C*‖y‖^2) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧
      (∀ y, HasSum (fun j => c j*‖inner ℂ (b j) (V y)‖^2) (inner ℂ y (B y)).re) ∧
      ∀ (j : J) (y : E) (z : ℂ), V y=z • b j → B y=(c j:ℂ) • V (z • b j) := by
  classical
  let f := logCoordinates b c V
  have hf (y : E) : Summable (fun j => ‖f j y‖^2) := by
    simpa only [f,logCoordinates_square b c hc] using hs y
  have hfB (y : E) : (∑' j, ‖f j y‖^2)≤C*‖y‖^2 := by
    simpa only [f,logCoordinates_square b c hc] using hb y
  let A := SquareAnalysis.continuousMap f hf C hC hfB
  refine ⟨SquareAnalysis.gram f hf C hC hfB, SquareAnalysis.gram_positive f hf C hC hfB, ?_, ?_⟩
  · intro y
    rw [SquareAnalysis.gram_quadratic]
    simpa only [f,logCoordinates_square b c hc] using (hf y).hasSum
  · intro j y z hy
    have hAy : A y=((Real.sqrt (c j):ℂ)*z) • (lp.single (E := fun _ : J => ℂ) 2 j (1:ℂ)) := by
      apply lp.ext
      funext i
      change (Real.sqrt (c i):ℂ)*inner ℂ (b i) (V y)=_
      rw [hy,inner_smul_right]
      by_cases hi : i=j
      · subst i
        simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one, lp.single_apply]
      · have hii : inner ℂ (b i) (b j)=0 := b.orthonormal.inner_eq_zero hi
        simp [hii,lp.single_apply,Ne.symm hi]
    apply ext_inner_left ℂ
    intro x
    change inner ℂ x (A.adjoint (A y))=inner ℂ x ((c j:ℂ) • V (z • b j))
    rw [A.adjoint_inner_right,hAy,inner_smul_right,lp.inner_single_right]
    simp only [RCLike.inner_apply,one_mul]
    change ((Real.sqrt (c j):ℂ)*z)*conj (f j x)=_
    change ((Real.sqrt (c j):ℂ)*z)*conj ((Real.sqrt (c j):ℂ)*inner ℂ (b j) (V x))=_
    rw [map_mul,Complex.conj_ofReal,inner_smul_right,map_smul,inner_smul_right]
    have he : inner ℂ x (V (b j))=conj (inner ℂ (b j) (V x)) := by
      rw [← inner_conj_symm]
      exact congrArg conj (hV (b j) x)
    rw [he]
    have hsqrt : (Real.sqrt (c j):ℂ)^2=(c j:ℂ) := by exact_mod_cast Real.sq_sqrt (hc j)
    linear_combination (z*conj (inner ℂ (b j) (V x)))*hsqrt
end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace Annihilation

structure SpectralLogData (n : ℕ) (ρ : State n) where
  J : Type
  basis : HilbertBasis J ℂ (Fock n)
  probability : J → ℝ
  probability_pos : ∀ j, 0 < probability j
  probability_sum : HasSum probability 1
  eigen : ∀ j, ρ.op (basis j)=(probability j:ℂ) • basis j
  spectralColumns : J → Fock n
  spectralColumns_summable : Summable (fun j => ‖spectralColumns j‖^2)
  spectralColumns_inverse : ∀ j, inverseWeight 3 (spectralColumns j)=
    CrossEnsemble.eigenEnsemble basis probability j
  logSandwich : Fock n →L[ℂ] Fock n
  logSandwich_symmetric : logSandwich.IsSymmetric
  logSandwich_parseval : ∀ y, HasSum
    (fun j => -Real.log (probability j)*‖inner ℂ (basis j) (inverseWeight 2 y)‖^2)
    (inner ℂ y (logSandwich y)).re
  logSandwich_preimage : ∀ j, logSandwich (inverseWeight 1 (spectralColumns j))=
    ((-Real.log (probability j):ℝ):ℂ) • inverseWeight 5 (spectralColumns j)

namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n}

def toSpectralLogData (G : GibbsData n k ρ) (hk : 0<k) : SpectralLogData n ρ where
  J := G.J
  basis := G.basis
  probability := G.probability
  probability_pos := G.probability_pos
  probability_sum := G.probability_sum
  eigen := G.eigen
  spectralColumns := G.spectralColumns
  spectralColumns_summable := G.spectralColumns_summable
  spectralColumns_inverse := G.spectralColumns_inverse
  logSandwich := G.logSandwich
  logSandwich_symmetric := G.logSandwich_symmetric hk
  logSandwich_parseval := G.logSandwich_parseval hk
  logSandwich_preimage := fun j => G.logSandwich_preimage hk j _ (G.spectralColumns_inverse j)
end GibbsData
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

def logCoefficient (j : G.J) : ℝ := -Real.log (G.probability j)
theorem logCoefficient_nonneg (j : G.J) : 0 ≤ G.logCoefficient j := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (G.probability_pos j).le
  exact G.probability_sum.tsum_eq ▸ G.probability_sum.summable.le_tsum j (fun i _ => (G.probability_pos i).le)
theorem spectralColumns_normalized :
    HasSum (fun r => ‖inverseWeight 3 (G.spectralColumns r)‖^2) 1 := by
  simpa only [G.spectralColumns_inverse,
    CrossEnsemble.eigenEnsemble_norm G.basis G.probability (fun r => (G.probability_pos r).le)]
    using G.probability_sum

theorem spectralColumns_operator (hm : FiniteMoment 6 ρ) :
    CrossEnsemble.operator (weightedRoot 3 ρ hm) (weightedRoot 3 ρ hm)=
      CrossEnsemble.operator G.spectralColumns G.spectralColumns := by
  exact weightedRoot_operator_eq ρ hm G.basis G.probability
    (fun r => (G.probability_pos r).le) G.probability_sum.summable G.eigen
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse

theorem thermalGenerator_logarithmic_trace (hm : FiniteMoment 6 ρ) (t : ℝ) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re =
      ∑ j, ∑' a : G.J × G.J,
        (G.logCoefficient a.1-G.logCoefficient a.2)*
        ((t+1)*G.probability a.2-t*G.probability a.1)*
        ‖WeightedGenerator.loweringEntry G.basis G.probability G.spectralColumns j a.1 a.2‖^2 := by
  rw [WeightedGenerator.pairing_eq_of_operator_eq G.basis
    (weightedRoot_summable 3 ρ hm) G.spectralColumns_summable (G.spectralColumns_operator hm)]
  exact WeightedGenerator.thermal_log_spectral G.basis G.probability G.probability_pos
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse
    G.logSandwich G.logSandwich_symmetric G.logCoefficient G.logCoefficient_nonneg
    G.logSandwich_parseval G.logSandwich_preimage t

end SpectralLogData
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

def annihilationMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  loweringEntry G.basis G.probability G.spectralColumns j a.1 a.2

def annihilationMean (j : Fin n) : ℂ := diagonalMean G.probability (G.annihilationMatrix j)

def centeredMatrix (j : Fin n) (a : G.J × G.J) : ℂ :=
  centeredEntry G.basis G.probability G.spectralColumns j (G.annihilationMean j) a.1 a.2

theorem annihilation_mean_summable (j : Fin n) :
    Summable (fun r => (G.probability r:ℂ)*G.annihilationMatrix j (r,r)) := by
  apply diagonal_mean_summable G.probability (fun r => (G.probability_pos r).le)
    G.probability_sum.summable
  have hh := nonlog_summable G.basis G.spectralColumns G.spectralColumns_summable j false
  simpa only [spectralGain_lowering_sq G.basis G.probability G.probability_pos,
    annihilationMatrix] using hh

theorem centeredMatrix_mean_zero (j : Fin n) :
    HasSum (fun r => (G.probability r:ℂ)*G.centeredMatrix j (r,r)) 0 := by
  classical
  simpa only [centeredMatrix, centeredEntry, ↓reduceIte, annihilationMean, annihilationMatrix]
    using diagonal_centering G.probability G.probability_sum
      (G.annihilationMatrix j) (G.annihilation_mean_summable j)

theorem centeredMatrix_six_sums (j : Fin n) :
    Summable (fun a : G.J × G.J => G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.2*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.1*G.probability a.1*‖G.centeredMatrix j a‖^2) ∧
    Summable (fun a : G.J × G.J => G.logCoefficient a.2*G.probability a.1*‖G.centeredMatrix j a‖^2) :=
  centered_six_sums G.basis G.probability G.probability_pos G.probability_sum.summable
    G.spectralColumns G.spectralColumns_summable G.spectralColumns_inverse
    G.logSandwich (G.logSandwich_symmetric) G.logCoefficient G.logCoefficient_nonneg
    (G.logSandwich_parseval)
    G.logSandwich_preimage j (G.annihilationMean j)

theorem centeredMatrix_defect_summable (t : ℝ) (j : Fin n) :
    Summable (fun a : G.J × G.J =>
      (1-frequency t (G.probability a.1) (G.probability a.2))*
      defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2) := by
  rcases G.centeredMatrix_six_sums j with ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact defect_series_summable t G.probability G.logCoefficient (fun _ => rfl)
    (G.centeredMatrix j) h₁ h₂ h₃ h₄ h₅ h₆

def defect (t : ℝ) (ht : 0<t) (j : Fin n) :
    centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable →L[ℂ] ℂ :=
  (defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j)).comp
    (centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable).subtypeL

theorem defect_norm_sq (t : ℝ) (ht : 0<t) (j : Fin n) :
    ‖G.defect t ht j‖^2=∑' a : G.J × G.J,
      (1-frequency t (G.probability a.1) (G.probability a.2))*
      defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 :=
  centered_defect_norm_sq t ht G.probability G.probability_pos G.probability_sum.summable
    (G.centeredMatrix j) (G.centeredMatrix_defect_summable t j) (G.centeredMatrix_mean_zero j)

def centeredEnergy : ℝ := ∑ j, ∑' r,
  ‖centeredLadder j (G.annihilationMean j) false (G.spectralColumns r)‖^2

theorem thermalGenerator_centered_logarithmic_trace (hm : FiniteMoment 6 ρ) (t : ℝ) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re =
      ∑ j, ∑' a : G.J × G.J,
        (G.logCoefficient a.1-G.logCoefficient a.2)*
        defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 := by
  classical
  rw [G.thermalGenerator_logarithmic_trace hm t]
  apply Finset.sum_congr rfl
  intro j _
  apply tsum_congr
  intro a
  by_cases he : a.1=a.2
  · simp only [he, sub_self, zero_mul]
  · simp only [centeredMatrix, centeredEntry, he, ↓reduceIte, sub_zero, defectCoefficient]

theorem entropy_production (hm : FiniteMoment 6 ρ) (t : ℝ) (ht : 0<t) :
    (WeightedGenerator.pairing t (weightedRoot 3 ρ hm) G.logSandwich).re/h t =
      (∑ j, ‖G.defect t ht j‖^2)-(G.centeredEnergy-(n:ℝ)*t) := by
  rw [G.thermalGenerator_centered_logarithmic_trace hm t, Finset.sum_div]
  have hj (j : Fin n) :
      (∑' a : G.J × G.J, (G.logCoefficient a.1-G.logCoefficient a.2)*
        defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2)/h t =
        ‖G.defect t ht j‖^2-
        ∑' a : G.J × G.J, defectCoefficient t (G.probability a.1) (G.probability a.2)*‖G.centeredMatrix j a‖^2 := by
    rw [G.defect_norm_sq t ht j]
    have hh := G.centeredMatrix_six_sums j
    exact production_series_subtraction t G.probability G.logCoefficient (fun _ => rfl)
      (G.centeredMatrix j) (G.centeredMatrix_defect_summable t j)
      (coefficient_series_summable t G.probability (G.centeredMatrix j) hh.1 hh.2.1)
  simp only [hj, Finset.sum_sub_distrib]
  congr 1
  exact centered_K_sum G.basis G.probability G.probability_pos G.spectralColumns
    G.spectralColumns_summable G.spectralColumns_inverse G.spectralColumns_normalized G.annihilationMean t

end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

theorem spectral_weighted_columns (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0≤p j) (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j)
    (hm : FiniteMoment 6 ρ) :
    ∃ x : J → Fock n, Summable (fun j => ‖x j‖^2) ∧
      ∀ j, inverseWeight 3 (x j)=CrossEnsemble.eigenEnsemble b p j := by
  have hm' : Summable (fun i => (numberWeight i^3)^2*
      (inner ℂ (sequenceBasis (NumberIndex n) i) (ρ.op (sequenceBasis _ i))).re) := by
    have hb (i : NumberIndex n) : sequenceBasis (NumberIndex n) i = numberKet i := by
      ext a
      by_cases ha : i=a <;> simp [sequenceBasis_apply, numberKet, ha]
    simpa only [← pow_mul, show (3*2:ℕ)=6 from rfl, numberWeight, totalNumber, Nat.cast_sum,
      FiniteMoment, entry, hb] using hm
  obtain ⟨x, hx, hs, _⟩ := weighted_spectral_vectors b ρ.op p hp he
    (fun i => numberWeight i^3) hm'
  refine ⟨x, hs, fun j => ?_⟩
  apply lp.ext
  funext i
  simp only [inverseWeight_apply, hx, CrossEnsemble.eigenEnsemble, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  have hw : (numberWeight i : ℂ) ≠ 0 := by
    exact_mod_cast (show numberWeight i ≠ 0 by linarith [numberWeight_one_le i])
  field_simp

theorem exists_spectralLogData_of_bound (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j) (hm : FiniteMoment 6 ρ)
    (hfin : ∀ y, Summable (fun j => -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 y)‖^2))
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ y, (∑' j, -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 y)‖^2)≤C*‖y‖^2) :
    Nonempty (SpectralLogData n ρ) := by
  have hc (j : J) : 0≤-Real.log (p j) := by
    apply neg_nonneg.mpr
    exact Real.log_nonpos (hp j).le (hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le))
  obtain ⟨B,hB,hBsum,hBe⟩ := spectral_form_representation b (fun j => -Real.log (p j)) hc
    (inverseWeight 2) (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 2)) hfin hC hb
  obtain ⟨x,hx,hix⟩ := spectral_weighted_columns b p (fun j => (hp j).le) he hm
  refine ⟨{
    J := J
    basis := b
    probability := p
    probability_pos := hp
    probability_sum := hs
    eigen := he
    spectralColumns := x
    spectralColumns_summable := hx
    spectralColumns_inverse := hix
    logSandwich := B
    logSandwich_symmetric := hB.isSymmetric
    logSandwich_parseval := hBsum
    logSandwich_preimage := ?_ }⟩
  intro j
  have hi : inverseWeight 2 (inverseWeight 1 (x j))=(Real.sqrt (p j):ℂ) • b j := by
    change (inverseWeight 2 ∘L inverseWeight 1) (x j)=_
    rw [← inverseWeight_add]
    exact hix j
  have hh := hBe j (inverseWeight 1 (x j)) (Real.sqrt (p j):ℂ) hi
  have hz : inverseWeight 2 ((Real.sqrt (p j):ℂ) • b j)=inverseWeight 5 (x j) := by
    rw [← hi]
    change (inverseWeight 2 ∘L inverseWeight 2 ∘L inverseWeight 1) (x j)=_
    rw [← inverseWeight_add,← inverseWeight_add]
  simpa only [hz] using hh
end

def numberBasis (n : ℕ) : HilbertBasis (NumberIndex n) ℂ (Fock n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem numberBasis_apply (n : ℕ) (k : NumberIndex n) :
    numberBasis n k = numberKet k := by
  classical
  exact ((numberBasis n).repr_symm_single k).symm

theorem trace_one_numberBasis {n : ℕ} (ρ : State n) :
    HasSum (fun k => (inner ℂ (numberBasis n k) (ρ.op (numberBasis n k))).re) 1 := by
  simpa only [numberBasis_apply, entry] using ρ.trace_one

end EntropyPhotonNumber

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I : Type*}

def diagonalVector (b : HilbertBasis I ℂ E) (p : I → ℝ) (i : I) : E :=
  (Real.sqrt (p i) : ℂ) • b i

omit [CompleteSpace E] in
@[simp] theorem diagonalVector_norm_sq (b : HilbertBasis I ℂ E) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (i : I) : ‖diagonalVector b p i‖^2 = p i := by
  simp [diagonalVector, norm_smul, b.orthonormal.norm_eq_one, Real.sq_sqrt (hp i)]

theorem diagonalVector_eigen (b : HilbertBasis I ℂ E) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (i : I) :
    operator (diagonalVector b p) (b i) = (p i : ℂ) • b i := by
  classical
  have hv : Summable (fun j => ‖diagonalVector b p j‖^2) := by
    simpa only [diagonalVector_norm_sq b p hp] using hs
  have he (j : I) : InnerProductSpace.rankOne ℂ (diagonalVector b p j)
      (diagonalVector b p j) (b i) = if j=i then (p i : ℂ) • b i else 0 := by
    simp only [InnerProductSpace.rankOne_apply, diagonalVector, inner_smul_left,
      orthonormal_iff_ite.mp b.orthonormal]
    split_ifs with h
    · subst j
      have hsq : (Real.sqrt (p i) : ℂ) * (Real.sqrt (p i) : ℂ) = (p i : ℂ) := by
        norm_cast
        exact Real.mul_self_sqrt (hp i)
      simp only [Complex.conj_ofReal, mul_one, smul_smul, hsq]
    · simp only [mul_zero, zero_smul]
  have hh := ((ContinuousLinearMap.apply ℂ E (b i)).hasSum (hasSum_rankOne hv))
  simpa only [ContinuousLinearMap.apply_apply, he, tsum_ite_eq] using hh.tsum_eq.symm

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

def diagonalState {n : ℕ} (p : NumberIndex n → ℝ) (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) : State n where
  op := TraceEnsemble.operator (diagonalVector (numberBasis n) p)
  positive := TraceEnsemble.positive (by simpa only [diagonalVector_norm_sq _ p hp] using hs.summable)
  trace_one := by
    simpa only [numberBasis_apply, entry] using TraceEnsemble.trace
      (by simpa only [diagonalVector_norm_sq _ p hp] using hs :
        HasSum (fun k => ‖diagonalVector (numberBasis n) p k‖^2) 1) (numberBasis n)

@[simp] theorem diagonalState_eigen {n : ℕ} (p : NumberIndex n → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) (k : NumberIndex n) :
    (diagonalState p hp hs).op (numberBasis n k) = (p k : ℂ) • numberBasis n k :=
  diagonalVector_eigen _ _ hp hs.summable k

@[simp] theorem diagonalState_diagonal {n : ℕ} (p : NumberIndex n → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) (k : NumberIndex n) :
    (entry (diagonalState p hp hs).op k k).re = p k := by
  rw [entry, ← numberBasis_apply n k, diagonalState_eigen, inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k k, ite_eq_left rfl, mul_one, Complex.ofReal_re]

def thermalState (n : ℕ) (r : ℝ) (hr : 0 < r) : State n :=
  diagonalState (thermalWeight n r) (fun k => (thermalWeight_pos n hr k).le)
    (hasSum_thermalWeight n hr)

@[simp] theorem thermalState_diagonal (n : ℕ) (r : ℝ) (hr : 0 < r) (k : NumberIndex n) :
    (entry (thermalState n r hr).op k k).re = thermalWeight n r k :=
  diagonalState_diagonal _ _ _ _

def mixture {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) (ρ σ : State n) : State n where
  op := (t : ℂ) • ρ.op + ((1-t : ℝ) : ℂ) • σ.op
  positive := by
    have h₁ := ρ.positive.smul_of_nonneg (c := (t : ℂ)) (by exact_mod_cast ht.1)
    have h₂ := σ.positive.smul_of_nonneg (c := ((1-t : ℝ) : ℂ)) (by exact_mod_cast (sub_nonneg.mpr ht.2))
    exact h₁.add h₂
  trace_one := by
    convert! (ρ.trace_one.mul_left t).add (σ.trace_one.mul_left (1-t)) using 1
    · funext k
      simp only [entry, add_apply, smul_apply,
        inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    · ring

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

theorem log_apply_eigenvector {T : E →L[ℂ] E} (hT : IsStrictlyPositive T)
    {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
    CFC.log T x = (Real.log p : ℂ) • x := by
  have hs := (ContinuousLinearMap.nonneg_iff_isPositive.mp hT.nonneg).isSymmetric
  change cfc Real.log T x = _
  rw [cfc_real_eq_complex Real.log hs.isSelfAdjoint]
  have hf : ContinuousOn (fun z : ℂ => (Real.log z.re : ℂ)) (spectrum ℂ T) := by
    intro z hz
    have hp : 0 < z.re :=
      (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos (R := ℝ) T hs.isSelfAdjoint).mp hT
        z.re (hs.isSelfAdjoint.spectrumRestricts.apply_mem hz)
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log hp.ne').comp Complex.continuous_re.continuousAt)).continuousWithinAt
  simpa using cfc_apply_eigenvector hs he _ hf

def regularNegLog (T : E →L[ℂ] E) (ε : ℝ) : E →L[ℂ] E :=
  Real.log (1+ε) • 1 - CFC.log (T + ε • 1)

theorem add_scalar_strictPositive {T : E →L[ℂ] E} (hT : T.IsPositive)
    {ε : ℝ} (hε : 0 < ε) : IsStrictlyPositive (T + ε • 1) := by
  exact (IsStrictlyPositive.smul hε isStrictlyPositive_one).nonneg_add
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)

theorem regularNegLog_eigen {T : E →L[ℂ] E} (hT : T.IsPositive)
    {ε : ℝ} (hε : 0 < ε) {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
    regularNegLog T ε x = ((Real.log (1+ε)-Real.log (p+ε) : ℝ) : ℂ) • x := by
  have ht : (T + ε • 1) x = ((p+ε : ℝ) : ℂ) • x := by
    simp [he, add_smul]
  rw [regularNegLog, sub_apply,
    log_apply_eigenvector (add_scalar_strictPositive hT hε) ht]
  simp [sub_smul]

theorem regularNegLog_antitone {R T : E →L[ℂ] E} (hR : R.IsPositive)
    (hRT : R ≤ T) {ε : ℝ} (hε : 0 < ε) : regularNegLog T ε ≤ regularNegLog R ε := by
  have hRT' : R + ε • (1 : E →L[ℂ] E) ≤ T + ε • 1 := add_le_add_left hRT _
  have hRp : IsStrictlyPositive (R + ε • (1 : E →L[ℂ] E)) := add_scalar_strictPositive hR hε
  have hh : CFC.log (R + ε • (1 : E →L[ℂ] E)) ≤ CFC.log (T + ε • 1) := by
    apply CFC.log_le_log
    · exact hRT'
    · exact hRp
  change Real.log (1+ε) • 1 - CFC.log (T + ε • 1) ≤
    Real.log (1+ε) • 1 - CFC.log (R + ε • 1)
  exact sub_le_sub_left hh _

theorem regularNegLog_scalar_bounds {p ε : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hε : 0 ≤ ε) : 0 ≤ Real.log (1+ε)-Real.log (p+ε) ∧
      Real.log (1+ε)-Real.log (p+ε) ≤ -Real.log p := by
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  · have hh : p*(1+ε) ≤ p+ε := by nlinarith
    have hl := Real.log_le_log (mul_pos hp (by linarith)) hh
    rw [Real.log_mul hp.ne' (by linarith : (1+ε : ℝ) ≠ 0)] at hl
    linarith

theorem negativeLog_form_mono (b : HilbertBasis I ℂ E) (c : HilbertBasis J ℂ E)
    {T R : E →L[ℂ] E} (hT : T.IsPositive) (hR : R.IsPositive) (hRT : R ≤ T)
    (p : I → ℝ) (q : J → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hp1 : ∀ i, p i ≤ 1) (hq1 : ∀ j, q j ≤ 1)
    (heT : ∀ i, T (b i) = (p i : ℂ) • b i)
    (heR : ∀ j, R (c j) = (q j : ℂ) • c j) (x : E)
    (hfin : Summable (fun j => -Real.log (q j)*‖inner ℂ (c j) x‖^2)) :
    Summable (fun i => -Real.log (p i)*‖inner ℂ (b i) x‖^2) ∧
      (∑' i, -Real.log (p i)*‖inner ℂ (b i) x‖^2) ≤
        ∑' j, -Real.log (q j)*‖inner ℂ (c j) x‖^2 := by
  have hnp (i : I) : 0 ≤ -Real.log (p i)*‖inner ℂ (b i) x‖^2 :=
    mul_nonneg (neg_nonneg.mpr (Real.log_nonpos (hp i).le (hp1 i))) (sq_nonneg _)
  have hpartial (s : Finset I) :
      ∑ i ∈ s, -Real.log (p i)*‖inner ℂ (b i) x‖^2 ≤
        ∑' j, -Real.log (q j)*‖inner ℂ (c j) x‖^2 := by
    have hbdd (ε : ℝ) (hε : 0 < ε) :
        ∑ i ∈ s, (Real.log (1+ε)-Real.log (p i+ε))*‖inner ℂ (b i) x‖^2 ≤
          ∑' j, -Real.log (q j)*‖inner ℂ (c j) x‖^2 := by
      have ht := hasSum_quadratic_eigenbasis b (regularNegLog T ε)
        (fun i => Real.log (1+ε)-Real.log (p i+ε))
        (fun i => regularNegLog_eigen hT hε (heT i)) x
      have hr := hasSum_quadratic_eigenbasis c (regularNegLog R ε)
        (fun j => Real.log (1+ε)-Real.log (q j+ε))
        (fun j => regularNegLog_eigen hR hε (heR j)) x
      have hquad : (inner ℂ x (regularNegLog T ε x)).re ≤
          (inner ℂ x (regularNegLog R ε x)).re := by
        have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp
          (sub_nonneg.mpr (regularNegLog_antitone hR hRT hε))).re_inner_nonneg_right x
        simpa [inner_sub_right] using hh
      calc
        _ ≤ (inner ℂ x (regularNegLog T ε x)).re := by
          rw [← ht.tsum_eq]
          exact ht.summable.sum_le_tsum s (fun i _ =>
            mul_nonneg (regularNegLog_scalar_bounds (hp i) (hp1 i) hε.le).1 (sq_nonneg _))
        _ ≤ (inner ℂ x (regularNegLog R ε x)).re := hquad
        _ ≤ _ := by
          rw [← hr.tsum_eq]
          exact Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right
            (regularNegLog_scalar_bounds (hq j) (hq1 j) hε.le).2 (sq_nonneg _)) hr.summable hfin
    have hc : ContinuousAt (fun ε : ℝ =>
      ∑ i ∈ s, (Real.log (1+ε)-Real.log (p i+ε))*‖inner ℂ (b i) x‖^2) 0 := by
      apply tendsto_finsetSum
      intro i _
      apply ContinuousAt.mul_const
      apply ContinuousAt.sub
      · exact (Real.continuousAt_log (by norm_num : (1+(0:ℝ)) ≠ 0)).comp
          (continuousAt_const.add continuousAt_id)
      · exact (Real.continuousAt_log (by simpa using (hp i).ne')).comp
          (continuousAt_const.add continuousAt_id)
    have hl : Filter.Tendsto (fun ε : ℝ =>
        ∑ i ∈ s, (Real.log (1+ε)-Real.log (p i+ε))*‖inner ℂ (b i) x‖^2)
        (𝓝[>] 0) (𝓝 (∑ i ∈ s, -Real.log (p i)*‖inner ℂ (b i) x‖^2)) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto hl (eventually_mem_nhdsWithin.mono fun ε hε => hbdd ε hε)
  have hs := summable_of_sum_le hnp hpartial
  refine ⟨hs, ?_⟩
  exact le_of_tendsto hs.hasSum (Filter.Eventually.of_forall hpartial)

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I : Type*}

theorem eigenbasis_quadratic_pos (b : HilbertBasis I ℂ E) (T : E →L[ℂ] E)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (he : ∀ i, T (b i) = (p i : ℂ) • b i)
    {x : E} (hx : x ≠ 0) : 0 < (inner ℂ x (T x)).re := by
  classical
  have hex : ∃ i, inner ℂ (b i) x ≠ 0 := by
    by_contra! h
    apply hx
    apply b.repr.injective
    apply lp.ext
    funext i
    rw [map_zero, HilbertBasis.repr_apply_apply]
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hs := hasSum_quadratic_eigenbasis b T p he x
  have hn : ∀ i, 0 ≤ p i*‖inner ℂ (b i) x‖^2 := fun i => mul_nonneg (hp i).le (sq_nonneg _)
  have ht := hs.summable.le_tsum i (fun j _ => hn j)
  rw [hs.tsum_eq] at ht
  exact (mul_pos (hp i) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi))).trans_le ht

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace

theorem mixture_replacement_le {n : ℕ} (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (ρ τ : State n) :
    (κ : ℂ) • τ.op ≤ (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ ρ τ).op := by
  have hp := ρ.positive.smul_of_nonneg (c := ((1-κ : ℝ) : ℂ))
    (by exact_mod_cast sub_nonneg.mpr hκ.2)
  have he : 1-(1-κ) = κ := by ring
  simpa only [mixture, he, add_sub_cancel_right] using
    le_add_of_nonneg_left (ContinuousLinearMap.nonneg_iff_isPositive.mpr hp)

theorem exists_faithful_eigenbasis_of_thermal_le {n : ℕ} (ρ : State n)
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op) :
    ∃ (J : Type) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ HasSum p 1 ∧ ∀ j, ρ.op (b j) = (p j : ℂ) • b j := by
  obtain ⟨J, b, p, hp, hs, he⟩ := exists_positive_eigenbasis (numberBasis n) ρ.positive
    (trace_one_numberBasis ρ)
  refine ⟨J, b, p, ?_, hs, he⟩
  intro j
  have ht := eigenbasis_quadratic_pos (numberBasis n) ((κ : ℂ) • (thermalState n r hr).op)
    (fun k => κ*thermalWeight n r k) (fun k => mul_pos hκ (thermalWeight_pos n hr k))
    (fun k => by simp only [smul_apply, thermalState, diagonalState_eigen, smul_smul,
      Complex.ofReal_mul]) (b.orthonormal.ne_zero j)
  have hh := (ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hle)).re_inner_nonneg_right (b j)
  have hvalue : (inner ℂ (b j) (ρ.op (b j))).re = p j := by
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  simp only [sub_apply, inner_sub_right] at hh
  change 0 ≤ (inner ℂ (b j) (ρ.op (b j))).re -
    (inner ℂ (b j) (((κ : ℂ) • (thermalState n r hr).op) (b j))).re at hh
  rw [hvalue] at hh
  linarith

def vectorEnergy {n : ℕ} (x : Fock n) : ℝ :=
  ∑' k, (totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2

def FiniteVectorEnergy {n : ℕ} (x : Fock n) : Prop :=
  Summable (fun k => (totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2)

theorem thermal_negativeLog_hasSum {n : ℕ} {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    (x : Fock n) (hx : FiniteVectorEnergy x) :
    HasSum (fun k => -Real.log (κ*thermalWeight n r k)*‖inner ℂ (numberBasis n k) x‖^2)
      ((-Real.log κ+n*Real.log (r+1))*‖x‖^2+Real.log ((r+1)/r)*vectorEnergy x) := by
  have h := ((basis_hasSum_norm_sq (numberBasis n) x).mul_left
    (-Real.log κ+n*Real.log (r+1))).add (hx.hasSum.mul_left (Real.log ((r+1)/r)))
  convert! h using 1
  funext k
  rw [Real.log_mul hκ.ne' (thermalWeight_pos n hr k).ne']
  have he : -Real.log (thermalWeight n r k) =
      n*Real.log (r+1)+(totalNumber k : ℝ)*Real.log ((r+1)/r) := by
    simpa only [totalNumber, Nat.cast_sum] using log_thermalWeight n hr k
  rw [neg_add, he]
  ring

theorem negativeLog_le_thermal {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (x : Fock n) (hx : FiniteVectorEnergy x) :
    Summable (fun j => -Real.log (p j)*‖inner ℂ (b j) x‖^2) ∧
      (∑' j, -Real.log (p j)*‖inner ℂ (b j) x‖^2) ≤
        (-Real.log κ+n*Real.log (r+1))*‖x‖^2+Real.log ((r+1)/r)*vectorEnergy x := by
  have ht := thermal_negativeLog_hasSum hr hκ x hx
  have hp1 (j : J) : p j ≤ 1 := hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)
  have hq1 (k : NumberIndex n) : κ*thermalWeight n r k ≤ 1 := by
    have h := (hasSum_thermalWeight n hr).summable.le_tsum k (fun i _ => (thermalWeight_pos n hr i).le)
    rw [(hasSum_thermalWeight n hr).tsum_eq] at h
    nlinarith [thermalWeight_pos n hr k]
  have hR := (thermalState n r hr).positive.smul_of_nonneg (c := (κ : ℂ)) (by exact_mod_cast hκ.le)
  have h := negativeLog_form_mono b (numberBasis n) ρ.positive hR hle p
    (fun k => κ*thermalWeight n r k) hp (fun k => mul_pos hκ (thermalWeight_pos n hr k)) hp1 hq1 he
    (fun k => by simp only [smul_apply, thermalState, diagonalState_eigen, smul_smul,
      Complex.ofReal_mul]) x ht.summable
  exact ⟨h.1, h.2.trans_eq ht.tsum_eq⟩

end

open QuantumTrace Annihilation
variable {n : ℕ}

theorem inverseWeight_two_norm (x : Fock n) : ‖inverseWeight 2 x‖≤‖x‖ := by
  change ‖WeightedShift.pull id Function.injective_id
    (fun k : NumberIndex n => ((numberWeight k^2)⁻¹:ℂ)) 1 (by norm_num)
    (coefficient_inverse_bound 2) x‖≤‖x‖
  simpa only [one_mul] using WeightedShift.pull_bound id Function.injective_id
    (fun k : NumberIndex n => ((numberWeight k^2)⁻¹:ℂ)) 1 (by norm_num)
    (coefficient_inverse_bound 2) x

theorem inverseWeight_two_energy_term (x : Fock n) (i : NumberIndex n) :
    (totalNumber i:ℝ)*‖inner ℂ (numberBasis n i) (inverseWeight 2 x)‖^2≤‖x i‖^2 := by
  simp only [numberBasis_apply, numberKet, lp.inner_single_left, RCLike.inner_apply,
    map_one, mul_one, inverseWeight_apply, norm_mul, mul_pow, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hW := numberWeight_one_le i
  have hw : 0<numberWeight i := by linarith
  have hN : (totalNumber i:ℝ)≤numberWeight i^4 := by
    have he : (totalNumber i:ℝ)=numberWeight i-1 := by
      simp only [totalNumber,numberWeight,Nat.cast_sum];ring
    rw [he]
    nlinarith [sq_nonneg (numberWeight i^2-1),sq_nonneg (numberWeight i-1)]
  have hi : (totalNumber i:ℝ)*((numberWeight i)^2)⁻¹^2≤1 := by
    rw [← inv_pow]
    rw [← pow_mul]
    norm_num only [Nat.reduceMul]
    simpa only [inv_pow] using (mul_inv_le_iff₀ (pow_pos hw 4)).mpr
      (show (totalNumber i:ℝ)≤1*numberWeight i^4 by simpa only [one_mul] using hN)
  nlinarith [sq_nonneg ‖x i‖,mul_le_mul_of_nonneg_right hi (sq_nonneg ‖x i‖)]

theorem inverseWeight_two_finiteEnergy (x : Fock n) : FiniteVectorEnergy (inverseWeight 2 x) := by
  apply (SquareAnalysis.hasSum_square x).summable.of_nonneg_of_le
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  exact inverseWeight_two_energy_term x

theorem inverseWeight_two_energy (x : Fock n) : vectorEnergy (inverseWeight 2 x)≤‖x‖^2 := by
  rw [vectorEnergy,← (SquareAnalysis.hasSum_square x).tsum_eq]
  exact (inverseWeight_two_finiteEnergy x).tsum_le_tsum (inverseWeight_two_energy_term x)
    (SquareAnalysis.hasSum_square x).summable

theorem exists_spectralLogData_of_thermal_le (ρ : State n) {r κ : ℝ}
    (hr : 0<r) (hκ : 0<κ) (hκ1 : κ≤1)
    (hle : (κ:ℂ) • (thermalState n r hr).op≤ρ.op) (hm : FiniteMoment 6 ρ) :
    Nonempty (SpectralLogData n ρ) := by
  obtain ⟨J,b,p,hp,hs,he⟩ := exists_faithful_eigenbasis_of_thermal_le ρ hr hκ hle
  let A := -Real.log κ+n*Real.log (r+1)
  let D := Real.log ((r+1)/r)
  have hA : 0≤A := by
    exact add_nonneg (neg_nonneg.mpr (Real.log_nonpos hκ.le hκ1))
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith)))
  have hD : 0≤D := by
    exact Real.log_nonneg ((le_div_iff₀ hr).mpr (by linarith))
  have hh (y : Fock n) := negativeLog_le_thermal ρ hr hκ hκ1 hle b p hp hs he
    (inverseWeight 2 y) (inverseWeight_two_finiteEnergy y)
  apply exists_spectralLogData_of_bound b p hp hs he hm (fun y => (hh y).1)
    (C := A+D) (add_nonneg hA hD)
  intro y
  exact (hh y).2.trans (by
    have h1 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (inverseWeight_two_norm y) 2) hA
    have h2 := mul_le_mul_of_nonneg_left (inverseWeight_two_energy y) hD
    change A*‖inverseWeight 2 y‖^2+D*vectorEnergy (inverseWeight 2 y)≤(A+D)*‖y‖^2
    nlinarith)
end EntropyPhotonNumber

end

end OAI
