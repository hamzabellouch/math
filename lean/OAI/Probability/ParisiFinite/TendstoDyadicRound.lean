import Mathlib
import OAI.Probability.ParisiFinite.Model

namespace OAI

/-! Tendsto Dyadic Round. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℝ≥0 → Ω → ℝ}

lemma tendsto_dyadicRound (t : ℝ≥0) : Tendsto (fun n => dyadicRound n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  have hlim : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hl : Tendsto (fun n : ℕ => (t:ℝ)-(1/2:ℝ)^n) atTop (𝓝 (t:ℝ)) := by
    simpa using tendsto_const_nhds.sub hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds ?_ ?_
  · intro n
    have hh := lt_dyadicRound_add n t
    have hh' : (t:ℝ)<(dyadicRound n t:ℝ)+(1/2:ℝ)^n := by exact_mod_cast hh
    linarith
  · intro n
    exact NNReal.coe_le_coe.mpr (dyadicRound_le n t)

lemma preBrownian_tendstoInMeasure (hX : IsPreBrownianReal X P) {s : ℕ → ℝ≥0} {t : ℝ≥0}
    (hs : Tendsto s atTop (𝓝 t)) : TendstoInMeasure P (fun n => X (s n)) atTop (X t) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hbound (n : ℕ) : P {ω | ε≤dist (X (s n) ω) (X t ω)} ≤
      ENNReal.ofReal (gaussianFourth*(dist (s n) t)^2/(ε/2)^4) := by
    have hl := hX.hasLaw_sub (s n) t
    have hh := fourth_tail_bound hl (show 0<ε/2 by positivity)
    apply (measure_mono (show {ω | ε≤dist (X (s n) ω) (X t ω)} ⊆
        {ω | ε/2 < |(X (s n)-X t) ω|} from fun ω hω => by
          simp only [Set.mem_ofPred_eq,Pi.sub_apply] at hω ⊢
          rw [Real.dist_eq] at hω
          linarith)).trans
    convert hh using 1
    congr 2
  have hd : Tendsto (fun n => dist (s n) t) atTop (𝓝 0) := by
    simpa using hs.dist (tendsto_const_nhds (x:=t))
  have hlim : Tendsto (fun n => ENNReal.ofReal (gaussianFourth*(dist (s n) t)^2/(ε/2)^4))
      atTop (𝓝 0) := by
    simpa only [comp_def,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_div,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto _ |>.comp ((hd.pow 2).const_mul gaussianFourth |>.div_const ((ε/2)^4))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound
end BrownianConstruction

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℝ≥0 → Ω → ℝ}

def continuousModification (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  dyadicLimit (fun s => X s ω) t

lemma continuousModification_ae_continuous (hX : IsPreBrownianReal X P) :
    ∀ᵐ ω ∂P, Continuous (fun t => continuousModification X t ω) := by
  filter_upwards [ae_dyadicGood hX] with ω hω
  exact continuous_dyadicLimit (by norm_num) (by norm_num) hω

lemma continuousModification_ae_eq (hX : IsPreBrownianReal X P) (t : ℝ≥0) :
    X t =ᵐ[P] continuousModification X t := by
  have hround := preBrownian_tendstoInMeasure hX (tendsto_dyadicRound t)
  have hlim : TendstoInMeasure P (fun n => X (dyadicRound n t)) atTop (continuousModification X t) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hX.aemeasurable _).aestronglyMeasurable)
    filter_upwards [ae_dyadicGood hX] with ω hω
    exact tendsto_dyadicLimit (by norm_num) (by norm_num) hω t
  exact tendstoInMeasure_ae_unique hround hlim

lemma continuousModification_isBrownian (hX : IsPreBrownianReal X P) :
    IsBrownianReal (continuousModification X) P :=
  ⟨hX.congr (continuousModification_ae_eq hX),continuousModification_ae_continuous hX⟩
end BrownianConstruction

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction

abbrev BrownianHilbert := Lp ℝ 2 (volume : Measure ℝ)
def brownianBasisIndex : Set BrownianHilbert := Classical.choose (exists_hilbertBasis ℝ BrownianHilbert)
def brownianBasis : HilbertBasis brownianBasisIndex ℝ BrownianHilbert :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℝ BrownianHilbert))
abbrev BrownianSample := brownianBasisIndex → ℝ
def brownianMeasure : Measure BrownianSample := gaussianProduct brownianBasisIndex
instance brownianMeasure_probability : IsProbabilityMeasure brownianMeasure := by
  unfold brownianMeasure
  infer_instance
def brownianMotion : ℝ≥0 → BrownianSample → ℝ :=
  continuousModification (preBrownian brownianBasis)
theorem brownianMotion_isBrownian : IsBrownianReal brownianMotion brownianMeasure :=
  continuousModification_isBrownian (preBrownian_isPreBrownian brownianBasis)
end BrownianConstruction

 

 

 

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

 
abbrev Configuration (n : ℕ) := Fin n → Bool

 
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

abbrev Disorder (n : ℕ) := Edge n → ℝ
abbrev State (n : ℕ) := Configuration n → ℂ
abbrev Operator (n : ℕ) := Matrix (Configuration n) (Configuration n) ℂ

 
def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi fun _ => gaussianReal 0 1

def spin {n : ℕ} (σ : Configuration n) (i : Fin n) : ℝ :=
  if σ i then -1 else 1

 
def hamiltonian (n : ℕ) (J : Disorder n) (σ : Configuration n) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ e : Edge n, J e * spin σ e.1.1 * spin σ e.1.2

 
def pauliZ {n : ℕ} (i : Fin n) : Operator n :=
  Matrix.diagonal fun σ => (spin σ i : ℂ)

 
def pauliX {n : ℕ} (i : Fin n) : Operator n :=
  fun σ τ => if σ = Function.update τ i (!(τ i)) then 1 else 0

 
def cost (n : ℕ) (J : Disorder n) : Operator n :=
  ((Real.sqrt (n : ℝ))⁻¹ : ℂ) •
    ∑ e : Edge n, (J e : ℂ) • (pauliZ e.1.1 * pauliZ e.1.2)

def mixer (n : ℕ) : Operator n := ∑ i : Fin n, pauliX i

 
def plus (n : ℕ) : State n :=
  fun _ => ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ)

 
def evolution {n : ℕ} (t : ℝ) (A : Operator n) : Operator n :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • A)

 
def circuit {n : ℕ} (J : Disorder n) :
    (p : ℕ) → (Fin p → ℝ) → (Fin p → ℝ) → Operator n
  | 0, _, _ => 1
  | p + 1, γ, β =>
      evolution (β (Fin.last p)) (mixer n) *
        evolution (γ (Fin.last p)) (cost n J) *
          circuit J p (fun i => γ i.castSucc) (fun i => β i.castSucc)

def qaoaState (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ) : State n :=
  (circuit J p γ β).mulVec (plus n)

 
def energyDensity (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ) : ℝ :=
  (∑ σ : Configuration n,
    star (qaoaState n p J γ β σ) *
      (cost n J).mulVec (qaoaState n p J γ β) σ).re / (n : ℝ)

def expectedEnergy (n p : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  ∫ J, energyDensity n p J γ β ∂disorderLaw n

 
def groundMaximum (n : ℕ) (J : Disorder n) : ℝ :=
  sSup (Set.range (hamiltonian n J))

def expectedGround (n : ℕ) : ℝ :=
  (∫ J, groundMaximum n J ∂disorderLaw n) / (n : ℝ)

 
def Pstar : ℝ := limUnder atTop expectedGround

 
def value (p : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  limUnder atTop (fun n => expectedEnergy n p γ β)

def Q (p : ℕ) : ℝ :=
  sSup (Set.range fun θ : (Fin p → ℝ) × (Fin p → ℝ) => value p θ.1 θ.2)

 
theorem cost_eq_diagonal (n : ℕ) (J : Disorder n) :
    cost n J = Matrix.diagonal (fun σ => (hamiltonian n J σ : ℂ)) := by
  classical
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp [cost, pauliZ, Matrix.diagonal_mul_diagonal, hamiltonian,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sum, mul_assoc]
  · simp [cost, pauliZ, Matrix.diagonal_mul_diagonal, h,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

 
theorem flip_flip {n : ℕ} (i : Fin n) (σ : Configuration n) :
    Function.update (Function.update σ i (!(σ i))) i
        (!(Function.update σ i (!(σ i)) i)) = σ := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

theorem flip_eq_iff {n : ℕ} (i : Fin n) (σ τ : Configuration n) :
    σ = Function.update τ i (!(τ i)) ↔
      τ = Function.update σ i (!(σ i)) := by
  constructor <;> intro h <;> subst_vars <;> simp

theorem cost_hermitian (n : ℕ) (J : Disorder n) :
    (cost n J).IsHermitian := by
  rw [cost_eq_diagonal]
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp
  · simp [Matrix.conjTranspose_apply, h, Ne.symm h]

theorem pauliX_hermitian {n : ℕ} (i : Fin n) :
    (pauliX i).IsHermitian := by
  ext σ τ
  simp [Matrix.conjTranspose_apply, pauliX, flip_eq_iff i τ σ]

theorem mixer_hermitian (n : ℕ) : (mixer n).IsHermitian := by
  unfold mixer Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun i _ => pauliX_hermitian i

@[simp] theorem evolution_zero {n : ℕ} (A : Operator n) :
    evolution 0 A = 1 := by
  simp [evolution]

 
theorem evolution_unitary {n : ℕ} (t : ℝ) (A : Operator n)
    (hA : A.IsHermitian) : evolution t A ∈ unitary (Operator n) := by
  let B : Operator n := (-(t : ℂ) * Complex.I) • A
  have hs : Bᴴ = -B := by
    change star ((-(t : ℂ) * Complex.I) • A) = -_
    rw [star_smul, hA.star_eq]
    simp [B, star_mul, mul_comm, neg_smul]
  change NormedSpace.exp B ∈ unitary (Operator n)
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hs]
  constructor
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl B).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl B).neg_right,
      add_neg_cancel, NormedSpace.exp_zero]

 
theorem circuit_unitary {n : ℕ} (J : Disorder n) (p : ℕ)
    (γ β : Fin p → ℝ) : circuit J p γ β ∈ unitary (Operator n) := by
  induction p with
  | zero => exact (unitary _).one_mem
  | succ p ih =>
      exact (unitary _).mul_mem
        ((unitary _).mul_mem
          (evolution_unitary _ _ (mixer_hermitian n))
          (evolution_unitary _ _ (cost_hermitian n J)))
        (ih _ _)

 
def mass {n : ℕ} (ψ : State n) : ℝ := ∑ σ, Complex.normSq (ψ σ)

theorem mass_eq_dot {n : ℕ} (ψ : State n) :
    (mass ψ : ℂ) = star ψ ⬝ᵥ ψ := by
  simp [mass, dotProduct, Complex.normSq_eq_conj_mul_self]

theorem unitary_preserves_mass {n : ℕ} {A : Operator n}
    (hA : A ∈ unitary (Operator n)) (ψ : State n) :
    mass (A.mulVec ψ) = mass ψ := by
  apply Complex.ofReal_injective
  rw [mass_eq_dot, mass_eq_dot, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have h : Aᴴ * A = 1 := Unitary.star_mul_self_of_mem hA
  rw [h, Matrix.one_mulVec]

 
theorem plus_mass (n : ℕ) : mass (plus n) = 1 := by
  have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  simp only [mass, plus, Complex.normSq_ofReal, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← sq, inv_pow, Real.sq_sqrt hp.le]
  exact mul_inv_cancel₀ (ne_of_gt hp)

 
theorem qaoaState_mass (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ) :
    mass (qaoaState n p J γ β) = 1 := by
  rw [qaoaState, unitary_preserves_mass (circuit_unitary J p γ β), plus_mass]

 

theorem energyDensity_eq (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ) :
    energyDensity n p J γ β =
      (∑ σ, Complex.normSq (qaoaState n p J γ β σ) * hamiltonian n J σ) /
        (n : ℝ) := by
  unfold energyDensity
  rw [cost_eq_diagonal]
  simp only [Matrix.mulVec_diagonal, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, zero_mul,
    add_zero, sub_zero, Complex.normSq_apply]
  ring

theorem hamiltonian_le_groundMaximum (n : ℕ) (J : Disorder n)
    (σ : Configuration n) : hamiltonian n J σ ≤ groundMaximum n J := by
  exact le_csSup (Set.finite_range _).bddAbove ⟨σ, rfl⟩

 
theorem energyDensity_le_groundMaximum (n p : ℕ) (J : Disorder n)
    (γ β : Fin p → ℝ) :
    energyDensity n p J γ β ≤ groundMaximum n J / (n : ℝ) := by
  rw [energyDensity_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    ∑ σ, Complex.normSq (qaoaState n p J γ β σ) * hamiltonian n J σ ≤
        ∑ σ, Complex.normSq (qaoaState n p J γ β σ) * groundMaximum n J :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
        (hamiltonian_le_groundMaximum n J σ) (Complex.normSq_nonneg _)
    _ = groundMaximum n J := by
      rw [← Finset.sum_mul]
      change mass (qaoaState n p J γ β) * groundMaximum n J = _
      rw [qaoaState_mass, one_mul]

@[simp] theorem spin_abs {n : ℕ} (σ : Configuration n) (i : Fin n) :
    |spin σ i| = 1 := by
  unfold spin
  split <;> norm_num

 
def couplingEnvelope (n : ℕ) (J : Disorder n) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ e, |J e|

theorem couplingEnvelope_nonneg (n : ℕ) (J : Disorder n) :
    0 ≤ couplingEnvelope n J :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem hamiltonian_abs_le (n : ℕ) (J : Disorder n) (σ : Configuration n) :
    |hamiltonian n J σ| ≤ couplingEnvelope n J := by
  unfold hamiltonian couplingEnvelope
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  calc
    |∑ e : Edge n, J e * spin σ e.1.1 * spin σ e.1.2| ≤
        ∑ e : Edge n, |J e * spin σ e.1.1 * spin σ e.1.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e : Edge n, |J e| := by simp [abs_mul]

theorem groundMaximum_abs_le (n : ℕ) (J : Disorder n) :
    |groundMaximum n J| ≤ couplingEnvelope n J := by
  apply abs_le.mpr
  constructor
  · have h := (abs_le.mp (hamiltonian_abs_le n J (fun _ => false))).1
    exact h.trans (hamiltonian_le_groundMaximum n J _)
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨σ, rfl⟩
    exact (abs_le.mp (hamiltonian_abs_le n J σ)).2

theorem energyDensity_abs_le (n p : ℕ) (J : Disorder n)
    (γ β : Fin p → ℝ) :
    |energyDensity n p J γ β| ≤ couplingEnvelope n J / (n : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [energyDensity_eq, abs_div, abs_of_nonneg hn]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    |∑ σ, Complex.normSq (qaoaState n p J γ β σ) * hamiltonian n J σ| ≤
        ∑ σ, |Complex.normSq (qaoaState n p J γ β σ) * hamiltonian n J σ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ, Complex.normSq (qaoaState n p J γ β σ) * |hamiltonian n J σ| := by
      simp only [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
    _ ≤ ∑ σ, Complex.normSq (qaoaState n p J γ β σ) * couplingEnvelope n J :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
        (hamiltonian_abs_le n J σ) (Complex.normSq_nonneg _)
    _ = couplingEnvelope n J := by
      rw [← Finset.sum_mul]
      change mass (qaoaState n p J γ β) * couplingEnvelope n J = _
      rw [qaoaState_mass, one_mul]

 
theorem hamiltonian_continuous (n : ℕ) (σ : Configuration n) :
    Continuous (fun J => hamiltonian n J σ) := by
  unfold hamiltonian
  fun_prop

theorem cost_evolution_continuous (n : ℕ) (t : ℝ) :
    Continuous (fun J => evolution t (cost n J)) := by
  simp_rw [evolution, cost_eq_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  apply Continuous.matrix_diagonal
  apply NormedSpace.exp_continuous.comp
  apply continuous_pi
  intro σ
  exact continuous_const.mul (Complex.continuous_ofReal.comp (hamiltonian_continuous n σ))

theorem circuit_continuous (n p : ℕ) (γ β : Fin p → ℝ) :
    Continuous (fun J : Disorder n => circuit J p γ β) := by
  induction p with
  | zero => exact continuous_const
  | succ p ih =>
      exact (continuous_const.matrix_mul (cost_evolution_continuous n _)).matrix_mul
        (ih _ _)

theorem qaoaState_continuous (n p : ℕ) (γ β : Fin p → ℝ) :
    Continuous (fun J => qaoaState n p J γ β) :=
  (circuit_continuous n p γ β).matrix_mulVec continuous_const

theorem energyDensity_continuous (n p : ℕ) (γ β : Fin p → ℝ) :
    Continuous (fun J => energyDensity n p J γ β) := by
  simp_rw [energyDensity_eq]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro σ _
  exact (Complex.continuous_normSq.comp
    ((continuous_apply σ).comp (qaoaState_continuous n p γ β))).mul
    (hamiltonian_continuous n σ)

theorem groundMaximum_continuous (n : ℕ) : Continuous (groundMaximum n) := by
  have h (J : Disorder n) : groundMaximum n J =
      Finset.univ.sup' Finset.univ_nonempty (hamiltonian n J) := by
    simp [groundMaximum, Finset.sup'_eq_csSup_image]
  simp_rw [show groundMaximum n = fun J =>
      Finset.univ.sup' Finset.univ_nonempty (hamiltonian n J) from funext h]
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun σ _ =>
    hamiltonian_continuous n σ

theorem coupling_integrable (n : ℕ) (e : Edge n) :
    Integrable (fun J : Disorder n => J e) (disorderLaw n) := by
  change Integrable (fun J : Disorder n => id (J e))
    (Measure.pi fun _ : Edge n => gaussianReal 0 1)
  apply integrable_comp_eval
  exact MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := 0) (v := 1) 1)

theorem couplingEnvelope_integrable (n : ℕ) :
    Integrable (couplingEnvelope n) (disorderLaw n) := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ fun e _ => (coupling_integrable n e).abs

theorem groundMaximum_integrable (n : ℕ) :
    Integrable (groundMaximum n) (disorderLaw n) := by
  apply (couplingEnvelope_integrable n).mono'
    (groundMaximum_continuous n).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun J => by
    simpa only [Real.norm_eq_abs] using groundMaximum_abs_le n J

theorem energyDensity_integrable (n p : ℕ) (γ β : Fin p → ℝ) :
    Integrable (fun J => energyDensity n p J γ β) (disorderLaw n) := by
  apply ((couplingEnvelope_integrable n).div_const (n : ℝ)).mono'
    (energyDensity_continuous n p γ β).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun J => by
    simpa only [Real.norm_eq_abs] using energyDensity_abs_le n p J γ β

 

theorem expectedEnergy_le_expectedGround (n p : ℕ) (γ β : Fin p → ℝ) :
    expectedEnergy n p γ β ≤ expectedGround n := by
  unfold expectedEnergy expectedGround
  rw [← integral_div]
  exact integral_mono (energyDensity_integrable n p γ β)
    ((groundMaximum_integrable n).div_const _) fun J =>
      energyDensity_le_groundMaximum n p J γ β

 
@[simp] theorem circuit_pad {n : ℕ} (J : Disorder n) (p : ℕ)
    (γ β : Fin p → ℝ) :
    circuit J (p + 1) (Fin.snoc γ 0) (Fin.snoc β 0) = circuit J p γ β := by
  simp [circuit]

@[simp] theorem expectedEnergy_pad (n p : ℕ) (γ β : Fin p → ℝ) :
    expectedEnergy n (p + 1) (Fin.snoc γ 0) (Fin.snoc β 0) =
      expectedEnergy n p γ β := by
  simp [expectedEnergy, energyDensity, qaoaState]

@[simp] theorem value_pad (p : ℕ) (γ β : Fin p → ℝ) :
    value (p + 1) (Fin.snoc γ 0) (Fin.snoc β 0) = value p γ β := by
  simp [value]

 
@[simp] theorem spin_sq {n : ℕ} (σ : Configuration n) (i : Fin n) : spin σ i ^ 2 = 1 := by
  simp only [spin]
  split <;> norm_num

 

theorem sum_symmetric_pairs (n : ℕ) (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) = (∑ i, F i i) + 2 * ∑ e : Edge n, F e.1.1 e.1.2 := by
  classical
  have he (i j : Fin n) : F i j =
      (if i = j then F i i else 0) +
        (if i < j then F i j else 0) + (if j < i then F i j else 0) := by
    rcases lt_trichotomy i j with hij | heq | hji
    · simp [hij, hij.ne, not_lt_of_ge hij.le]
    · subst j; simp
    · simp [hji, hji.ne', not_lt_of_ge hji.le]
  have hedge : (∑ e : Edge n, F e.1.1 e.1.2) = ∑ i, ∑ j, if i < j then F i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun e : Fin n × Fin n => e.1 < e.2))
      (by simp) (fun e => F e.1 e.2), Finset.sum_filter, Fintype.sum_prod_type]
  have hsym : (∑ i : Fin n, ∑ j : Fin n, if j < i then F i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then F i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hF j i]
  calc
    _ = ∑ i, ∑ j, ((if i = j then F i i else 0) +
        (if i < j then F i j else 0) + (if j < i then F i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact he i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [hsym, ← hedge]
      simp
      ring

 
def skCoeff (n : ℕ) (σ : Configuration n) (e : Edge n) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * spin σ e.1.1 * spin σ e.1.2

theorem hamiltonian_eq_coeff (n : ℕ) (J : Disorder n) (σ : Configuration n) :
    hamiltonian n J σ = ∑ e, skCoeff n σ e * J e := by
  simp only [hamiltonian, skCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

 
def overlapSum {n : ℕ} (σ τ : Configuration n) : ℝ := ∑ i, spin σ i * spin τ i

 
theorem edge_overlap (n : ℕ) (σ τ : Configuration n) :
    (2 : ℝ) * (∑ e : Edge n, (spin σ e.1.1 * spin τ e.1.1) *
        (spin σ e.1.2 * spin τ e.1.2)) = overlapSum σ τ ^ 2 - (n : ℝ) := by
  have h := sum_symmetric_pairs n
    (fun i j => (spin σ i * spin τ i) * (spin σ j * spin τ j))
    (fun i j => mul_comm _ _)
  have hdiag : (∑ i, (spin σ i * spin τ i) * (spin σ i * spin τ i)) = (n : ℝ) := by
    simp_rw [← sq, mul_pow, spin_sq, one_mul]
    simp
  have htotal : (∑ i, ∑ j, (spin σ i * spin τ i) * (spin σ j * spin τ j)) =
      overlapSum σ τ ^ 2 := by
    rw [sq, overlapSum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hdiag, htotal] at h
  linarith

@[simp] theorem overlapSum_self {n : ℕ} (σ : Configuration n) : overlapSum σ σ = (n : ℝ) := by
  simp [overlapSum, ← sq]

 
theorem coeff_covariance {n : ℕ} (hn : 0 < n) (σ τ : Configuration n) :
    (∑ e, skCoeff n σ e * skCoeff n τ e) =
      (overlapSum σ τ ^ 2 - (n : ℝ)) / (2 * (n : ℝ)) := by
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he : (∑ e, skCoeff n σ e * skCoeff n τ e) =
      (Real.sqrt (n : ℝ))⁻¹ ^ 2 *
        ∑ e : Edge n, (spin σ e.1.1 * spin τ e.1.1) * (spin σ e.1.2 * spin τ e.1.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    unfold skCoeff
    ring
  rw [he, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have ho := edge_overlap n σ τ
  field_simp
  simp only [mul_assoc] at ho ⊢
  nlinarith

 
theorem coeff_increment {n : ℕ} (hn : 0 < n) (σ τ : Configuration n) :
    (∑ e, (skCoeff n σ e - skCoeff n τ e) ^ 2) =
      (n : ℝ) - overlapSum σ τ ^ 2 / (n : ℝ) := by
  have he : (∑ e, (skCoeff n σ e - skCoeff n τ e) ^ 2) =
      (∑ e, skCoeff n σ e * skCoeff n σ e) + (∑ e, skCoeff n τ e * skCoeff n τ e) -
        2 * (∑ e, skCoeff n σ e * skCoeff n τ e) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he, coeff_covariance hn, coeff_covariance hn, coeff_covariance hn, overlapSum_self, overlapSum_self]
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

end SKQAOA

end

end OAI
