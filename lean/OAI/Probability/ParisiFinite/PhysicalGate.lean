import Mathlib
import OAI.Probability.ParisiFinite.Count

namespace OAI

/-! Physical Gate. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

 

def physicalGate (n : ℕ) (J : Disorder n) : PointedTree.Gate → Operator n
  | .cost t => evolution t (cost n J)
  | .mixer t => evolution t (mixer n)

def physicalWord (n : ℕ) (J : Disorder n) : List PointedTree.Gate → Operator n
  | [] => 1
  | g :: w => physicalGate n J g * physicalWord n J w

def gateGamma : PointedTree.Gate → ℝ
  | .cost t => t
  | .mixer _ => 0

def gateBeta : PointedTree.Gate → ℝ
  | .cost _ => 0
  | .mixer t => t

 

def wordGamma : (w : List PointedTree.Gate) → Fin w.length → ℝ
  | [], i => Fin.elim0 i
  | g :: w, i => Fin.lastCases (gateGamma g) (wordGamma w) i

def wordBeta : (w : List PointedTree.Gate) → Fin w.length → ℝ
  | [], i => Fin.elim0 i
  | g :: w, i => Fin.lastCases (gateBeta g) (wordBeta w) i

@[simp] theorem physicalWord_nil (n : ℕ) (J : Disorder n) :
    physicalWord n J [] = 1 := rfl

@[simp] theorem physicalWord_cons (n : ℕ) (J : Disorder n)
    (g : PointedTree.Gate) (w : List PointedTree.Gate) :
    physicalWord n J (g :: w) = physicalGate n J g * physicalWord n J w := rfl

 
theorem physicalWord_eq_circuit (w : List PointedTree.Gate) (n : ℕ) (J : Disorder n) :
    physicalWord n J w = circuit J w.length (wordGamma w) (wordBeta w) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    cases g <;> simp [physicalWord, physicalGate, circuit, wordGamma, wordBeta,
      gateGamma, gateBeta, ih]

@[simp] theorem physicalWord_append (n : ℕ) (J : Disorder n)
    (w v : List PointedTree.Gate) :
    physicalWord n J (w ++ v) = physicalWord n J w * physicalWord n J v := by
  induction w with
  | nil => simp
  | cons g w ih => simp [ih, mul_assoc]

theorem physicalGate_unitary (n : ℕ) (J : Disorder n) (g : PointedTree.Gate) :
    physicalGate n J g ∈ unitary (Operator n) := by
  cases g with
  | mixer t => exact evolution_unitary t _ (mixer_hermitian n)
  | cost t => exact evolution_unitary t _ (cost_hermitian n J)

theorem physicalWord_unitary (n : ℕ) (J : Disorder n) (w : List PointedTree.Gate) :
    physicalWord n J w ∈ unitary (Operator n) := by
  rw [physicalWord_eq_circuit]
  exact circuit_unitary J _ _ _

 
def inverseGate : PointedTree.Gate → PointedTree.Gate
  | .cost t => .cost (-t)
  | .mixer t => .mixer (-t)

def inverseWord (w : List PointedTree.Gate) : List PointedTree.Gate :=
  w.reverse.map inverseGate

@[simp] theorem evolution_neg_adjoint {n : ℕ} (A : Operator n) (hA : A.IsHermitian)
    (t : ℝ) : evolution (-t) A = (evolution t A)ᴴ := by
  unfold evolution
  rw [← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, hA]
  simp [star_mul, mul_comm]

@[simp] theorem physicalGate_inverse (n : ℕ) (J : Disorder n) (g : PointedTree.Gate) :
    physicalGate n J (inverseGate g) = (physicalGate n J g)ᴴ := by
  cases g with
  | mixer t => exact evolution_neg_adjoint _ (mixer_hermitian n) t
  | cost t => exact evolution_neg_adjoint _ (cost_hermitian n J) t

@[simp] theorem physicalWord_inverse (n : ℕ) (J : Disorder n) (w : List PointedTree.Gate) :
    physicalWord n J (inverseWord w) = (physicalWord n J w)ᴴ := by
  induction w with
  | nil => simp [inverseWord]
  | cons g w ih =>
    simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, physicalWord_append, physicalWord_cons, physicalWord_nil,
      mul_one, physicalGate_inverse, Matrix.conjTranspose_mul]
    rw [← ih]
    rfl

 
def wordExpectedEnergy (n : ℕ) (w : List PointedTree.Gate) : ℝ :=
  ∫ J, (quad ((physicalWord n J w).mulVec (plus n)) (cost n J)).re / (n : ℝ)
    ∂disorderLaw n

theorem wordExpectedEnergy_eq (n : ℕ) (w : List PointedTree.Gate) :
    wordExpectedEnergy n w = expectedEnergy n w.length (wordGamma w) (wordBeta w) := by
  simp only [wordExpectedEnergy, physicalWord_eq_circuit, expectedEnergy, energyDensity,
    qaoaState, quad, dotProduct, Pi.star_apply]

 

theorem finite_word_realizable (w : List PointedTree.Gate) :
    ∃ (p : ℕ) (γ β : Fin p → ℝ),
      (∀ (n : ℕ) (J : Disorder n), physicalWord n J w = circuit J p γ β) ∧
      ∀ n : ℕ, wordExpectedEnergy n w = expectedEnergy n p γ β := by
  exact ⟨w.length, wordGamma w, wordBeta w, physicalWord_eq_circuit w,
    fun n => wordExpectedEnergy_eq n w⟩

end SKQAOA

 

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

 
def mixerPhase (n : ℕ) (t : ℝ) : ℂ :=
  ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I)^n

@[simp] theorem star_mixerPhase_mul (n : ℕ) (t : ℝ) :
    star (mixerPhase n t) * mixerPhase n t = 1 := by
  unfold mixerPhase
  rw [star_pow, ← mul_pow]
  have h : star ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) *
      ((Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I) = 1 := by
    simp only [star_sub, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    calc
      _ = (((Real.cos t)^2 + (Real.sin t)^2 : ℝ) : ℂ) := by
        simp only [Complex.ofReal_add, Complex.ofReal_pow]
        linear_combination -(Real.sin t : ℂ)^2 * Complex.I_sq
      _ = 1 := by rw [Real.cos_sq_add_sin_sq]; norm_num
  rw [h, one_pow]

theorem mixer_evolution_plus (n : ℕ) (t : ℝ) :
    (evolution t (mixer n)).mulVec (plus n) = mixerPhase n t • plus n := by
  funext σ
  simp only [Matrix.mulVec, dotProduct, plus, mixer_evolution_apply,
    ← Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if σ i = b then (Real.cos t : ℂ) else -(Real.sin t : ℂ) * Complex.I)]
  have h (i : Fin n) :
      (∑ b : Bool, if σ i = b then (Real.cos t : ℂ) else -(Real.sin t : ℂ) * Complex.I) =
        (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
    cases σ i <;> simp [sub_eq_add_neg, add_comm]
  simp_rw [h]
  simp [mixerPhase]

 
theorem quad_phase {n : ℕ} (ψ : State n) (A : Operator n) (z : ℂ)
    (hz : star z * z = 1) : quad (z • ψ) A = quad ψ A := by
  simp only [quad, Matrix.mulVec_smul, star_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, mul_comm z (star z), hz, one_mul]

theorem cost_evolution_preserves_quad (n : ℕ) (J : Disorder n) (t : ℝ) (ψ : State n) :
    quad ((evolution t (cost n J)).mulVec ψ) (cost n J) = quad ψ (cost n J) := by
  rw [quad_mulVec]
  have hc : cost n J * evolution t (cost n J) = evolution t (cost n J) * cost n J := by
    rw [cost_evolution_eq_diagonal, cost_eq_diagonal]
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext σ
    exact mul_comm _ _
  have hu : (evolution t (cost n J))ᴴ * evolution t (cost n J) = 1 :=
    (Unitary.mem_iff.mp (evolution_unitary t _ (cost_hermitian n J))).1
  rw [mul_assoc, hc, ← mul_assoc, hu, one_mul]

 
def commutatorWord (t : ℝ) : List PointedTree.Gate :=
  [.cost t, .mixer t, .cost (-t), .mixer (-t)]

 

theorem commutator_quad (n : ℕ) (J : Disorder n) (t : ℝ) :
    quad ((physicalWord n J (commutatorWord t)).mulVec (plus n)) (cost n J) =
      quad (qaoaState n 1 J (fun _ => -t) (fun _ => t)) (cost n J) := by
  simp only [commutatorWord, physicalWord_cons, physicalWord_nil, physicalGate, mul_one,
    ← Matrix.mulVec_mulVec]
  rw [cost_evolution_preserves_quad, mixer_evolution_plus]
  simp only [Matrix.mulVec_smul]
  rw [quad_phase _ _ _ (star_mixerPhase_mul n (-t))]
  rw [qaoaState_one]
  rfl

 
theorem commutator_expectedEnergy (n : ℕ) (t : ℝ) :
    wordExpectedEnergy n (commutatorWord t) =
      -t * ((n : ℝ)-1)/(n : ℝ) * Real.sin (4*t) *
        Real.exp (-2*t^2*((n : ℝ)-1)/(n : ℝ)) := by
  have h : wordExpectedEnergy n (commutatorWord t) =
      expectedEnergy n 1 (fun _ => -t) (fun _ => t) := by
    unfold wordExpectedEnergy expectedEnergy energyDensity
    apply integral_congr_ae
    filter_upwards [] with J
    rw [commutator_quad]
    rfl
  rw [h, expectedEnergy_one]
  simp

 
def sizeCorrection (n : ℕ) : ℝ := ((n : ℝ)-1)/(n : ℝ)

theorem sizeCorrection_mem (n : ℕ) : sizeCorrection n ∈ Set.Icc (0 : ℝ) 1 := by
  rcases n with _ | n
  · simp [sizeCorrection]
  · have hn : 0 < (n+1 : ℝ) := by positivity
    constructor
    · unfold sizeCorrection
      exact div_nonneg (by norm_num) (by positivity)
    · unfold sizeCorrection
      rw [div_le_one (by positivity)]
      linarith

 

theorem commutator_scalar_remainder (a t : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    |(-t*a*Real.sin (4*t)*Real.exp (-2*t^2*a)) + 4*a*t^2| ≤ 20*t^4 := by
  have hexp : 0 < Real.exp (-2*t^2*a) := Real.exp_pos _
  have harg : -2*t^2*a ≤ 0 := by nlinarith [sq_nonneg t, ha.1]
  have hle : Real.exp (-2*t^2*a) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr harg
  have hlow := Real.add_one_le_exp (-2*t^2*a)
  have hsin := Real.abs_sub_sin_le (4*t)
  have hd : (-t*a*Real.sin (4*t)*Real.exp (-2*t^2*a)) + 4*a*t^2 =
      t*a*((4*t-Real.sin (4*t))*Real.exp (-2*t^2*a) +
        4*t*(1-Real.exp (-2*t^2*a))) := by ring
  rw [hd, abs_mul]
  calc
    _ ≤ |t*a| * (|(4*t-Real.sin (4*t))*Real.exp (-2*t^2*a)| +
        |4*t*(1-Real.exp (-2*t^2*a))|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |t| *a*(|4*t-Real.sin (4*t)| *Real.exp (-2*t^2*a) +
        (4* |t|)*(1-Real.exp (-2*t^2*a))) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha.1,
        abs_of_pos hexp, abs_of_nonneg (by linarith : 0 ≤ 1-Real.exp (-2*t^2*a))]
      norm_num
    _ ≤ |t| *a*((|4*t|^3/6)*1 + (4* |t|)*(2*t^2*a)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) ha.1)
      apply add_le_add
      · exact mul_le_mul hsin hle hexp.le (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ ≤ 20*t^4 := by
      rw [abs_mul]
      norm_num
      have hs : |t|^2 = t^2 := sq_abs t
      have ht4 : |t|^4 = t^4 := by rw [show (4 : ℕ)=2*2 from rfl, pow_mul, hs, ← pow_mul]
      have ha2 : a^2 ≤ 1 := by nlinarith [ha.1, ha.2]
      have hh : 0 ≤ t^4 := by positivity
      calc
        _ = ((64/6 : ℝ)*a + 8*a^2)*t^4 := by
          rw [← hs, ← ht4]
          ring
        _ ≤ 20*t^4 := by
          apply mul_le_mul_of_nonneg_right _ hh
          nlinarith [ha.2, ha2]

 
theorem commutator_uniform_energy_expansion (t : ℝ) (n : ℕ) :
    |wordExpectedEnergy n (commutatorWord t) + 4*sizeCorrection n*t^2| ≤ 20*t^4 := by
  rw [commutator_expectedEnergy]
  have h := commutator_scalar_remainder (sizeCorrection n) t (sizeCorrection_mem n)
  unfold sizeCorrection at h ⊢
  convert h using 1; congr 2; ring_nf

end SKQAOA

 

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

theorem wordExpectedEnergy_costMixer (n : ℕ) (γ β : ℝ) :
    wordExpectedEnergy n [.mixer β, .cost γ] =
      expectedEnergy n 1 (fun _ => γ) (fun _ => β) := by
  unfold wordExpectedEnergy expectedEnergy energyDensity
  apply integral_congr_ae
  filter_upwards [] with J
  simp only [physicalWord_cons, physicalWord_nil, physicalGate, mul_one,
    ← Matrix.mulVec_mulVec, qaoaState_one, costState]
  rfl

@[simp] theorem wordExpectedEnergy_cost_only (n : ℕ) (γ : ℝ) :
    wordExpectedEnergy n [.cost γ] = 0 := by
  have h := wordExpectedEnergy_costMixer n γ 0
  have he : physicalWord n (by exact 0) [.cost γ] =
      physicalWord n (by exact 0) [.mixer 0, .cost γ] := by simp [physicalGate]
  have he' : wordExpectedEnergy n [.mixer 0, .cost γ] =
      wordExpectedEnergy n [.cost γ] := by
    simp only [wordExpectedEnergy, physicalWord_cons, physicalWord_nil, physicalGate,
      evolution_zero, one_mul]
  rw [he', expectedEnergy_one] at h
  simpa using h

 

theorem energy_only_not_a_congruence :
    ∃ w v c : List PointedTree.Gate,
      (∀ n : ℕ, wordExpectedEnergy n w = wordExpectedEnergy n v) ∧
      ∃ L : ℝ, 0 < L ∧
        Tendsto (fun n => wordExpectedEnergy n (c ++ w) -
          wordExpectedEnergy n (c ++ v)) atTop (𝓝 L) := by
  refine ⟨[.cost (1/2)], [.cost 0], [.mixer (Real.pi/8)], ?_,
    Real.exp (-1/2)/2, div_pos (Real.exp_pos _) (by norm_num), ?_⟩
  · intro n
    simp
  · have hz (n : ℕ) : wordExpectedEnergy n [.mixer (Real.pi/8), .cost 0] = 0 := by
      rw [wordExpectedEnergy_costMixer, expectedEnergy_one]
      simp
    have ht := tendsto_expectedEnergy_one (fun _ => (1/2 : ℝ)) (fun _ => Real.pi/8)
    convert ht using 1
    · funext n
      simp only [List.cons_append, List.nil_append, hz, sub_zero,
        wordExpectedEnergy_costMixer]
    · norm_num
      rw [show 4*(Real.pi/8)=Real.pi/2 by ring, Real.sin_pi_div_two]
      ring

end SKQAOA

 

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA

 

theorem quad_mixer_pair {n : ℕ} (ψ : State n) (i j : Fin n) (t : ℝ) :
    quad ((evolution t (mixer n)).mulVec ψ) (pauliZ i * pauliZ j) =
      ((1 + Real.cos (4*t))/2 : ℝ) * quad ψ (pauliZ i * pauliZ j) +
      ((1 - Real.cos (4*t))/2 : ℝ) * quad ψ (pauliY i * pauliY j) +
      (Real.sin (4*t)/2 : ℝ) *
        (quad ψ (pauliZ i * pauliY j) + quad ψ (pauliY i * pauliZ j)) := by
  rw [quad_mulVec, conjugate_mul _ _ _
    (Unitary.mul_star_self_of_mem (evolution_unitary _ _ (mixer_hermitian n))),
    mixer_conjugate_pauliZ, mixer_conjugate_pauliZ]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, quad_add, quad_smul]
  have hcc : Real.cos (2*t)^2 = (1 + Real.cos (4*t))/2 := by
    have h := Real.cos_two_mul (2*t)
    have hs := Real.sin_sq_add_cos_sq (2*t)
    rw [show 2*(2*t)=4*t by ring] at h
    nlinarith
  have hss : Real.sin (2*t)^2 = (1 - Real.cos (4*t))/2 := by
    nlinarith [Real.sin_sq_add_cos_sq (2*t)]
  have hsc : Real.sin (2*t)*Real.cos (2*t) = Real.sin (4*t)/2 := by
    have h := Real.sin_two_mul (2*t)
    rw [show 2*(2*t)=4*t by ring] at h
    linarith
  have hc : (Real.cos (2*t) : ℂ)^2 = (((1+Real.cos (4*t))/2 : ℝ) : ℂ) := by
    exact_mod_cast hcc
  have hs : (Real.sin (2*t) : ℂ)^2 = (((1-Real.cos (4*t))/2 : ℝ) : ℂ) := by
    exact_mod_cast hss
  have hcs : (Real.sin (2*t) : ℂ)*(Real.cos (2*t) : ℂ) =
      ((Real.sin (4*t)/2 : ℝ) : ℂ) := by exact_mod_cast hsc
  rw [←hc, ←hs, ←hcs]
  ring

 

theorem quad_mixer_pair_interpolation {n : ℕ} (ψ : State n) (i j : Fin n) (t : ℝ) :
    quad ((evolution t (mixer n)).mulVec ψ) (pauliZ i * pauliZ j) =
      ((1 + Real.cos (4*t) - Real.sin (4*t))/2 : ℝ) *
        quad ψ (pauliZ i * pauliZ j) +
      ((1 - Real.cos (4*t) - Real.sin (4*t))/2 : ℝ) *
        quad ((evolution (Real.pi/4) (mixer n)).mulVec ψ) (pauliZ i * pauliZ j) +
      (Real.sin (4*t) : ℂ) *
        quad ((evolution (Real.pi/8) (mixer n)).mulVec ψ) (pauliZ i * pauliZ j) := by
  simp only [quad_mixer_pair]
  rw [show 4*(Real.pi/4)=Real.pi by ring,
      show 4*(Real.pi/8)=Real.pi/2 by ring]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two, Real.cos_pi_div_two]
  push_cast
  ring

 

theorem quad_mixer_cost_interpolation {n : ℕ} (J : Disorder n) (ψ : State n) (t : ℝ) :
    quad ((evolution t (mixer n)).mulVec ψ) (cost n J) =
      ((1 + Real.cos (4*t) - Real.sin (4*t))/2 : ℝ) * quad ψ (cost n J) +
      ((1 - Real.cos (4*t) - Real.sin (4*t))/2 : ℝ) *
        quad ((evolution (Real.pi/4) (mixer n)).mulVec ψ) (cost n J) +
      (Real.sin (4*t) : ℂ) *
        quad ((evolution (Real.pi/8) (mixer n)).mulVec ψ) (cost n J) := by
  simp only [quad_cost]
  simp_rw [quad_mixer_pair_interpolation ψ _ _ t]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_comm, mul_left_comm]

theorem integrable_word_energy (n : ℕ) (w : List PointedTree.Gate) :
    Integrable (fun J : Disorder n =>
      (quad ((physicalWord n J w).mulVec (plus n)) (cost n J)).re / (n : ℝ))
      (disorderLaw n) := by
  simp only [physicalWord_eq_circuit]
  exact energyDensity_integrable n w.length (wordGamma w) (wordBeta w)

theorem wordExpectedEnergy_mixer_interpolation (n : ℕ) (w : List PointedTree.Gate)
    (t : ℝ) :
    wordExpectedEnergy n (.mixer t :: w) =
      ((1 + Real.cos (4*t) - Real.sin (4*t))/2) * wordExpectedEnergy n w +
      ((1 - Real.cos (4*t) - Real.sin (4*t))/2) *
        wordExpectedEnergy n (.mixer (Real.pi/4) :: w) +
      Real.sin (4*t) * wordExpectedEnergy n (.mixer (Real.pi/8) :: w) := by
  have he (J : Disorder n) :
      (quad ((physicalWord n J (.mixer t :: w)).mulVec (plus n)) (cost n J)).re /
        (n : ℝ) =
      ((1 + Real.cos (4*t) - Real.sin (4*t))/2) *
        ((quad ((physicalWord n J w).mulVec (plus n)) (cost n J)).re / (n : ℝ)) +
      ((1 - Real.cos (4*t) - Real.sin (4*t))/2) *
        ((quad ((physicalWord n J (.mixer (Real.pi/4) :: w)).mulVec (plus n))
          (cost n J)).re / (n : ℝ)) +
      Real.sin (4*t) *
        ((quad ((physicalWord n J (.mixer (Real.pi/8) :: w)).mulVec (plus n))
          (cost n J)).re / (n : ℝ)) := by
    simp only [physicalWord_cons, physicalGate, ←Matrix.mulVec_mulVec]
    rw [quad_mixer_cost_interpolation J _ t]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  simp only [wordExpectedEnergy]
  simp_rw [he]
  have ha := (integrable_word_energy n w).const_mul
    ((1 + Real.cos (4*t) - Real.sin (4*t))/2)
  have hb := (integrable_word_energy n (.mixer (Real.pi/4) :: w)).const_mul
    ((1 - Real.cos (4*t) - Real.sin (4*t))/2)
  have hc := (integrable_word_energy n (.mixer (Real.pi/8) :: w)).const_mul (Real.sin (4*t))
  have hadd := integral_add (ha.add hb) hc
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add ha hb]
  simp only [integral_const_mul]

 
theorem abs_wordExpectedEnergy_le (n : ℕ) (w : List PointedTree.Gate) :
    |wordExpectedEnergy n w| ≤ expectedGround n := by
  rw [wordExpectedEnergy_eq]
  exact abs_expectedEnergy_le_expectedGround n _ _ _

 

theorem terminal_mixer_energy_lipschitz (n : ℕ) (w : List PointedTree.Gate)
    (t s : ℝ) :
    |wordExpectedEnergy n (.mixer t :: w) - wordExpectedEnergy n (.mixer s :: w)| ≤
      12 * expectedGround n * |t-s| := by
  let A := wordExpectedEnergy n w
  let B := wordExpectedEnergy n (.mixer (Real.pi/4) :: w)
  let D := wordExpectedEnergy n (.mixer (Real.pi/8) :: w)
  have ha := abs_le.mp (abs_wordExpectedEnergy_le n w)
  have hb := abs_le.mp (abs_wordExpectedEnergy_le n (.mixer (Real.pi/4) :: w))
  have hd := abs_le.mp (abs_wordExpectedEnergy_le n (.mixer (Real.pi/8) :: w))
  have hG : 0 ≤ expectedGround n := (abs_nonneg _).trans (abs_wordExpectedEnergy_le n w)
  have hv : |(A-B)/2| ≤ expectedGround n := by
    apply abs_le.mpr
    dsimp [A,B]
    constructor <;> linarith
  have hz : |D-(A+B)/2| ≤ 2*expectedGround n := by
    apply abs_le.mpr
    dsimp [A,B,D]
    constructor <;> linarith
  have hdiff :
      wordExpectedEnergy n (.mixer t :: w) - wordExpectedEnergy n (.mixer s :: w) =
      ((A-B)/2)*(Real.cos (4*t)-Real.cos (4*s)) +
      (D-(A+B)/2)*(Real.sin (4*t)-Real.sin (4*s)) := by
    rw [wordExpectedEnergy_mixer_interpolation n w t, wordExpectedEnergy_mixer_interpolation n w s]
    dsimp [A,B,D]
    ring
  have hcos : |Real.cos (4*t)-Real.cos (4*s)| ≤ 4*|t-s| := by
    simpa only [←mul_sub, abs_mul, show |(4:ℝ)|=4 by norm_num] using Real.abs_cos_sub_cos_le (4*t) (4*s)
  have hsin : |Real.sin (4*t)-Real.sin (4*s)| ≤ 4*|t-s| := by
    simpa only [←mul_sub, abs_mul, show |(4:ℝ)|=4 by norm_num] using Real.abs_sin_sub_sin_le (4*t) (4*s)
  rw [hdiff]
  calc
    _ ≤ |(A-B)/2*(Real.cos (4*t)-Real.cos (4*s))| +
        |(D-(A+B)/2)*(Real.sin (4*t)-Real.sin (4*s))| := abs_add_le _ _
    _ = |(A-B)/2| * |Real.cos (4*t)-Real.cos (4*s)| +
        |D-(A+B)/2| * |Real.sin (4*t)-Real.sin (4*s)| := by rw [abs_mul, abs_mul]
    _ ≤ expectedGround n*(4*|t-s|) + (2*expectedGround n)*(4*|t-s|) :=
      add_le_add (mul_le_mul hv hcos (abs_nonneg _) hG)
        (mul_le_mul hz hsin (abs_nonneg _) (by positivity))
    _ = 12*expectedGround n*|t-s| := by ring

end SKQAOA

 

open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.Locality

 

def IsSupported {n : ℕ} (S : Finset (Fin n)) (A : Operator n) : Prop :=
  ∀ i, i ∉ S → Commute A (pauliX i) ∧ Commute A (pauliZ i)

variable {n : ℕ} {S T : Finset (Fin n)} {A B : Operator n}

theorem IsSupported.mono (hA : IsSupported S A) (hST : S ⊆ T) : IsSupported T A := by
  intro i hi
  exact hA i (fun h => hi (hST h))

theorem supported_zero (S : Finset (Fin n)) : IsSupported S (0 : Operator n) := by
  intro i hi
  exact ⟨Commute.zero_left _,Commute.zero_left _⟩

theorem supported_one (S : Finset (Fin n)) : IsSupported S (1 : Operator n) := by
  intro i hi
  exact ⟨Commute.one_left _,Commute.one_left _⟩

theorem IsSupported.add (hA : IsSupported S A) (hB : IsSupported S B) :
    IsSupported S (A+B) := by
  intro i hi
  exact ⟨(hA i hi).1.add_left (hB i hi).1,(hA i hi).2.add_left (hB i hi).2⟩

theorem IsSupported.mul (hA : IsSupported S A) (hB : IsSupported S B) :
    IsSupported S (A*B) := by
  intro i hi
  exact ⟨(hA i hi).1.mul_left (hB i hi).1,(hA i hi).2.mul_left (hB i hi).2⟩

theorem IsSupported.smul (hA : IsSupported S A) (c : ℂ) : IsSupported S (c • A) := by
  intro i hi
  exact ⟨(hA i hi).1.smul_left c,(hA i hi).2.smul_left c⟩

theorem supported_atSite {i : Fin n} (hi : i ∈ S) (A : Matrix Bool Bool ℂ) :
    IsSupported S (TensorMatrix.atSite i A) := by
  intro j hj
  have hij : i ≠ j := by rintro rfl; exact hj hi
  rw [pauliX_eq_atSite,pauliZ_eq_atSite]
  exact ⟨TensorMatrix.atSite_commute hij _ _,TensorMatrix.atSite_commute hij _ _⟩

theorem supported_pauliX {i : Fin n} (hi : i ∈ S) : IsSupported S (pauliX i) := by
  rw [pauliX_eq_atSite]
  exact supported_atSite hi _

theorem supported_pauliZ {i : Fin n} (hi : i ∈ S) : IsSupported S (pauliZ i) := by
  rw [pauliZ_eq_atSite]
  exact supported_atSite hi _

theorem pauliZ_hermitian (i : Fin n) : (pauliZ i).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro σ
  exact Complex.conj_ofReal _

theorem IsSupported.adjoint (hA : IsSupported S A) : IsSupported S Aᴴ := by
  intro i hi
  have hx := (hA i hi).1.star_star
  have hz := (hA i hi).2.star_star
  have heX : (pauliX i)ᴴ=pauliX i := pauliX_hermitian i
  have heZ : (pauliZ i)ᴴ=pauliZ i := pauliZ_hermitian i
  simpa only [Matrix.star_eq_conjTranspose,heX,heZ] using And.intro hx hz

theorem IsSupported.exp (hA : IsSupported S A) : IsSupported S (NormedSpace.exp A) := by
  intro i hi
  exact ⟨(hA i hi).1.exp_left,(hA i hi).2.exp_left⟩

theorem IsSupported.evolve (hA : IsSupported S A) (t : ℝ) :
    IsSupported S (SKQAOA.evolution t A) :=
  (hA.smul _).exp

theorem supported_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Operator n)
    (hf : ∀i∈s, IsSupported S (f i)) : IsSupported S (∑i∈s,f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supported_zero S
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

 
theorem commute_conjugate (U A B : Operator n) (hU : U ∈ unitary (Operator n))
    (h : Commute A (U*B*Uᴴ)) : Commute (Uᴴ*A*U) B := by
  have hl : Uᴴ*U=1 := Unitary.star_mul_self_of_mem hU
  have hr : U*Uᴴ=1 := Unitary.mul_star_self_of_mem hU
  change (Uᴴ*A*U)*B=B*(Uᴴ*A*U)
  calc
    _ = Uᴴ*(A*(U*B*Uᴴ))*U := by
      calc
        _ = Uᴴ*A*U*B*(Uᴴ*U) := by rw [hl]; simp
        _ = _ := by noncomm_ring
    _ = Uᴴ*((U*B*Uᴴ)*A)*U := by rw [h.eq]
    _ = (Uᴴ*U)*B*Uᴴ*A*U := by noncomm_ring
    _ = _ := by rw [hl]; noncomm_ring

 
theorem IsSupported.mixer_conjugate (hA : IsSupported S A) (t : ℝ) :
    IsSupported S ((evolution t (mixer n))ᴴ*A*evolution t (mixer n)) := by
  intro i hi
  have hX := (hA i hi).1
  have hZ := (hA i hi).2
  have hub := evolution_unitary t _ (mixer_hermitian n)
  have hmix : Commute (mixer n) (pauliX i) := by
    apply Commute.sum_left
    intro j hj
    by_cases hji : j=i
    · subst j
      exact Commute.refl _
    · rw [pauliX_eq_atSite,pauliX_eq_atSite]
      exact TensorMatrix.atSite_commute hji _ _
  have huX : Commute (evolution t (mixer n)) (pauliX i) :=
    (hmix.smul_left _).exp_left
  have hr : evolution t (mixer n)*(evolution t (mixer n))ᴴ=1 :=
    Unitary.mul_star_self_of_mem hub
  have hx : evolution t (mixer n)*pauliX i*(evolution t (mixer n))ᴴ=pauliX i := by
    rw [huX.eq,mul_assoc,hr,mul_one]
  have hz : evolution t (mixer n)*pauliZ i*(evolution t (mixer n))ᴴ =
      (Real.cos (2*(-t)) : ℂ) • pauliZ i + (Real.sin (2*(-t)) : ℂ) • pauliY i := by
    have h := mixer_conjugate_pauliZ i (-t)
    simpa only [evolution_neg_adjoint _ (mixer_hermitian n),Matrix.conjTranspose_conjTranspose]
      using h
  constructor
  · apply commute_conjugate _ _ _ hub
    rwa [hx]
  · apply commute_conjugate _ _ _ hub
    rw [hz,pauliY_eq]
    exact (hZ.smul_right _).add_right (((hX.mul_right hZ).smul_right Complex.I).smul_right _)

end SKQAOA.Locality

end

end OAI
