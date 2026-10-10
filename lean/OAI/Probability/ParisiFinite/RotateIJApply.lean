import Mathlib
import OAI.Probability.ParisiFinite.SpinMatrix

namespace OAI

/-! Rotate I J Apply. -/

noncomputable section

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped Topology
open Filter
open scoped BigOperators Matrix
open scoped Matrix Matrix.Norms.L2Operator
namespace QuaternionControl
open PulseControl SeedControl
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι]
local instance rotateIJQFieldNormedAlgebra : NormedAlgebra ℚ (QField ι) :=
  NormedAlgebra.restrictScalars ℚ ℝ (QField ι)

@[simp] theorem rotateIJ_apply (a b : ℝ) (h : a^2+b^2=1) (q : Quaternion ℝ) :
    rotateIJ a b h q = ⟨q.re,a*q.imI-b*q.imJ,b*q.imI+a*q.imJ,q.imK⟩ := rfl

@[simp] theorem toPauli_apply (q : Quaternion ℝ) :
    toPauli q = !![(q.re:ℂ)-Complex.I*q.imI, -(q.imJ:ℂ)+Complex.I*q.imK;
      (q.imJ:ℂ)+Complex.I*q.imK, (q.re:ℂ)+Complex.I*q.imI] := rfl

def matrixMap (a b : ℝ) (hab : a^2+b^2=1) : QField ι →ₐ[ℝ] (ι → SpinMatrix) where
  toFun q i := toPauli (rotateIJ a b hab (q i))
  map_zero' := by funext i; change toPauli (rotateIJ a b hab 0) = 0; simp only [map_zero]
  map_one' := by funext i; change toPauli (rotateIJ a b hab 1) = 1; simp only [map_one]
  map_add' q r := by funext i; change toPauli (rotateIJ a b hab (q i+r i)) = _; simp only [map_add,Pi.add_apply]
  map_mul' q r := by funext i; change toPauli (rotateIJ a b hab (q i*r i)) = _; simp only [map_mul,Pi.mul_apply]
  commutes' r := by
    funext i
    change toPauli (rotateIJ a b hab (algebraMap ℝ (Quaternion ℝ) r)) = algebraMap ℝ SpinMatrix r
    rw [(rotateIJ a b hab).commutes,toPauli.commutes]

omit [Fintype ι] in
@[simp] theorem matrixMap_apply (a b : ℝ) (hab : a^2+b^2=1) (q : QField ι) (i : ι) :
    matrixMap a b hab q i = toPauli (rotateIJ a b hab (q i)) := rfl

omit [Fintype ι] in
def spinGen (a b : ℝ) (c d : ι → ℝ) (e : Bool) : ι → SpinMatrix :=
  if e then fun i => c i • (a • z+b • y) else fun i => d i • ((-b) • z+a • y)

omit [Fintype ι] in
theorem matrixMap_gen (a b : ℝ) (hab : a^2+b^2=1) (c d : ι → ℝ) :
    matrixMap a b hab ∘ gen c d = spinGen a b c d := by
  funext e i
  cases e
  · change toPauli (rotateIJ a b hab (⟨0,0,d i,0⟩ : Quaternion ℝ)) = d i • ((-b) • z+a • y)
    change !![(0:ℂ)-Complex.I*((a*0-b*d i:ℝ):ℂ), -(b*0+a*d i:ℝ)+Complex.I*0;
      (b*0+a*d i:ℝ)+Complex.I*0, (0:ℂ)+Complex.I*((a*0-b*d i:ℝ):ℂ)] = d i • ((-b) • z+a • y)
    ext j k
    fin_cases j <;> fin_cases k <;> simp [z,y] <;> ring
  · change toPauli (rotateIJ a b hab (⟨0,c i,0,0⟩ : Quaternion ℝ)) = c i • (a • z+b • y)
    change !![(0:ℂ)-Complex.I*((a*c i-b*0:ℝ):ℂ), -(b*c i+a*0:ℝ)+Complex.I*0;
      (b*c i+a*0:ℝ)+Complex.I*0, (0:ℂ)+Complex.I*((a*c i-b*0:ℝ):ℂ)] = c i • (a • z+b • y)
    ext j k
    fin_cases j <;> fin_cases k <;> simp [z,y] <;> ring

omit [Fintype ι] in
theorem matrixMap_qX (a b : ℝ) (hab : a^2+b^2=1) (t : ℝ) :
    matrixMap a b hab (qX (fun _ : ι => -t)) = fun _ : ι => t • x := by
  funext i
  change toPauli (rotateIJ a b hab (⟨0,0,0,-t⟩ : Quaternion ℝ)) = t • x
  change !![(0:ℂ)-Complex.I*((a*0-b*0:ℝ):ℂ), -(b*0+a*0:ℝ)+Complex.I*((-t:ℝ):ℂ);
    (b*0+a*0:ℝ)+Complex.I*((-t:ℝ):ℂ), (0:ℂ)+Complex.I*((a*0-b*0:ℝ):ℂ)] = t • x
  ext j k
  fin_cases j <;> fin_cases k <;> simp [x] <;> ring

 

theorem exact_spin_ensemble (v : ι → ℝ × ℝ) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : ℝ, a^2+b^2=1 ∧ ∀ t : ℝ,
      NormedSpace.exp (fun _ : ι => t • x) ∈ zeroClockWords
        (spinGen a b (fun i => a*(v i).1+b*(v i).2) (fun i => -b*(v i).1+a*(v i).2)) := by
  obtain ⟨a,b,hab,hn,hs⟩ := exists_separating_frame v hv
  refine ⟨a,b,hab,fun t => ?_⟩
  let c := fun i => a*(v i).1+b*(v i).2
  let d := fun i => -b*(v i).1+a*(v i).2
  have heq : ∀ i j, c i^2=c j^2 → (c i=c j ∧ d i=d j) ∨ (c i= -c j ∧ d i= -d j) := by
    intro i j hh
    rcases hs i j hh with h | h
    · left; simp [c,d,h]
    · right; simp only [c,d,h,Prod.fst_neg,Prod.snd_neg]; constructor <;> ring
  have hr := common_X_exact c d hn heq (-t)
  let F : QField ι →ₐ[ℝ] (ι → SpinMatrix) := matrixMap a b hab
  have hF : Continuous F := F.toLinearMap.continuous_of_finiteDimensional
  have hm := zeroClock_map F hF (gen c d) hr
  rw [show F ∘ gen c d = spinGen a b c d from matrixMap_gen a b hab c d] at hm
  have he : F (NormedSpace.exp (qX (fun _ : ι => -t))) = NormedSpace.exp (fun _ : ι => t • x) := by
    convert! NormedSpace.map_exp F.toRingHom hF (qX (fun _ : ι => -t)) using 1
    change NormedSpace.exp (fun _ : ι => t • x) = NormedSpace.exp (matrixMap a b hab (qX (fun _ : ι => -t)))
    rw [matrixMap_qX]
  rwa [he] at hm

end QuaternionControl

namespace PulseControl
variable {κ : Type*} [DecidableEq κ]

@[simp] theorem pulseClock_reverse (w : List (κ × ℝ)) : pulseClock w.reverse = pulseClock w := by
  simp [pulseClock,List.map_reverse]

 
theorem pulseClock_eq_sum (w : List (κ × ℝ)) (e : κ) :
    pulseClock w e = ((w.filter (fun p => decide (p.1=e))).map Prod.snd).sum := by
  induction w with
  | nil => simp [pulseClock]
  | cons p w ih =>
    simp only [pulseClock,List.map_cons,List.sum_cons,Pi.add_apply] at ih ⊢
    by_cases h : p.1=e
    · simp [h,ih]
    · have h' : e ≠ p.1 := Ne.symm h
      simp [h,h',ih]
end PulseControl

namespace QuaternionControl
open PulseControl SeedControl
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι]
local instance rotateIJSpinFieldNormedAlgebra : NormedAlgebra ℚ (ι → SpinMatrix) :=
  NormedAlgebra.restrictScalars ℚ ℝ (ι → SpinMatrix)
local instance rotateIJSpinMatrixNormedAlgebra : NormedAlgebra ℚ SpinMatrix :=
  NormedAlgebra.restrictScalars ℚ ℝ SpinMatrix

theorem matrix_exp_apply (A : ι → SpinMatrix) (i : ι) :
    NormedSpace.exp A i = NormedSpace.exp (A i) := by
  convert! NormedSpace.map_exp (Pi.evalRingHom (fun _ : ι => SpinMatrix) i) (continuous_apply i) A

theorem spin_pulseValue_apply (G : Bool → ι → SpinMatrix) (w : List (Bool×ℝ)) (i : ι) :
    pulseValue G w i = pulseValue (fun e => G e i) w := by
  exact pulseValue_map (Pi.evalAlgHom ℝ (fun _ : ι => SpinMatrix) i) (continuous_apply i) G w

 
theorem selective_rotations_zero_clocks (v : ι → ℝ×ℝ) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : ℝ, a^2+b^2=1 ∧ ∀ t : ℝ, ∃ w : List (Bool×ℝ),
      (∀ e : Bool, ((w.filter (fun p => decide (p.1=e))).map Prod.snd).sum = 0) ∧
      ∀ i : ι,
        (w.reverse.map (fun p => NormedSpace.exp (p.2 •
          spinGen a b (fun j => a*(v j).1+b*(v j).2)
            (fun j => -b*(v j).1+a*(v j).2) p.1 i))).prod =
        NormedSpace.exp (t • x) := by
  obtain ⟨a,b,hab,ht⟩ := exact_spin_ensemble v hv
  refine ⟨a,b,hab,fun t => ?_⟩
  obtain ⟨w,hw,he⟩ := ht t
  refine ⟨w.reverse,?_,fun i => ?_⟩
  · intro e
    rw [← pulseClock_eq_sum,pulseClock_reverse,hw]
    rfl
  · have h := congrArg (fun A : ι → SpinMatrix => A i) he
    rw [spin_pulseValue_apply,matrix_exp_apply] at h
    simpa only [List.reverse_reverse,pulseValue] using h
end QuaternionControl

namespace SKQAOA
open scoped ComplexConjugate

 

def History (n : ℕ) : ℕ → Type
  | 0 => Unit
  | p+1 => Configuration n × History n p

instance historyFintype (n : ℕ) : (p : ℕ) → Fintype (History n p)
  | 0 => inferInstanceAs (Fintype Unit)
  | p+1 => @instFintypeProd (Configuration n) (History n p) inferInstance (historyFintype n p)

 
def historyMix (n : ℕ) : (p : ℕ) → (Fin p → ℝ) → Configuration n → History n p → ℂ
  | 0, _, _, _ => ((Real.sqrt ((2:ℝ)^n))⁻¹ : ℝ)
  | p+1, β, σ, h => evolution (β (Fin.last p)) (mixer n) σ h.1 *
      historyMix n p (fun i => β i.castSucc) h.1 h.2

 
def historyPhase (n : ℕ) : (p : ℕ) → (Fin p → ℝ) → History n p → Edge n → ℂ
  | 0, _, _, _ => 0
  | p+1, γ, h, e => -(γ (Fin.last p) : ℂ)*Complex.I*(skCoeff n h.1 e : ℂ)+
      historyPhase n p (fun i => γ i.castSucc) h.2 e

@[simp] theorem sum_history_zero (n : ℕ) (f : History n 0 → ℂ) :
    ∑ h, f h = f () := by
  let : Unique (History n 0) := inferInstanceAs (Unique Unit)
  exact Fintype.sum_unique f

theorem sum_history_succ (n p : ℕ) (f : History n (p+1) → ℂ) :
    ∑ h, f h = ∑ σ : Configuration n, ∑ h : History n p, f (σ,h) :=
  Fintype.sum_prod_type f

theorem historyPhase_succ_sum (n p : ℕ) (J : Disorder n) (γ : Fin (p+1) → ℝ)
    (σ : Configuration n) (h : History n p) :
    (∑ e, historyPhase n (p+1) γ (σ,h) e*(J e : ℂ))=
      -(γ (Fin.last p):ℂ)*Complex.I*(hamiltonian n J σ : ℂ)+
        ∑ e, historyPhase n p (fun i => γ i.castSucc) h e*(J e : ℂ) := by
  simp only [historyPhase,add_mul,Finset.sum_add_distrib]
  congr 1
  rw [hamiltonian_eq_coeff]
  push_cast
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem cost_evolution_mulVec (n : ℕ) (J : Disorder n) (γ : ℝ) (ψ : State n) :
    (evolution γ (cost n J)).mulVec ψ=
      fun σ => Complex.exp (-(γ:ℂ)*Complex.I*(hamiltonian n J σ : ℂ))*ψ σ := by
  funext σ
  simp only [cost_evolution_eq_diagonal,Matrix.mulVec_diagonal]

 
theorem qaoaState_history (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ)
    (σ : Configuration n) :
    qaoaState n p J γ β σ = ∑ h : History n p,
      historyMix n p β σ h * Complex.exp (∑ e, historyPhase n p γ h e*(J e : ℂ)) := by
  induction p generalizing σ with
  | zero =>
    rw [sum_history_zero]
    simp [qaoaState,circuit,plus,historyMix,historyPhase]
  | succ p ih =>
    have he : qaoaState n (p+1) J γ β =
        (evolution (β (Fin.last p)) (mixer n)).mulVec
          ((evolution (γ (Fin.last p)) (cost n J)).mulVec
            (qaoaState n p J (fun i => γ i.castSucc) (fun i => β i.castSucc))) := by
      simp only [qaoaState,circuit,Matrix.mulVec_mulVec,Matrix.mul_assoc]
    rw [he,cost_evolution_mulVec,sum_history_succ]
    change (∑ τ, evolution (β (Fin.last p)) (mixer n) σ τ *
      (Complex.exp (-(γ (Fin.last p):ℂ)*Complex.I*(hamiltonian n J τ : ℂ))*
        qaoaState n p J (fun i => γ i.castSucc) (fun i => β i.castSucc) τ))=_
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [ih,Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [historyPhase_succ_sum,Complex.exp_add]
    simp only [historyMix]
    ring

 

def pairedPhase (n p : ℕ) (γ : Fin p → ℝ) (a b : History n p) (e : Edge n) : ℂ :=
  star (historyPhase n p γ a e)+historyPhase n p γ b e

def pairedMix (n p : ℕ) (β : Fin p → ℝ) (σ : Configuration n) (a b : History n p) : ℂ :=
  star (historyMix n p β σ a)*historyMix n p β σ b

theorem qaoaState_pair_history (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ)
    (σ : Configuration n) :
    star (qaoaState n p J γ β σ)*qaoaState n p J γ β σ =
      ∑ a : History n p, ∑ b : History n p, pairedMix n p β σ a b *
        Complex.exp (∑ e, pairedPhase n p γ a b e*(J e : ℂ)) := by
  rw [qaoaState_history]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum,map_mul,Complex.star_def,
    ← Complex.exp_conj,Complex.conj_ofReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have he : (∑ e, star (historyPhase n p γ a e)*(J e : ℂ))+
      (∑ e, historyPhase n p γ b e*(J e : ℂ)) =
      ∑ e, pairedPhase n p γ a b e*(J e : ℂ) := by
    simp only [pairedPhase,add_mul,Finset.sum_add_distrib]
  rw [← he,Complex.exp_add]
  simp only [pairedMix,Complex.star_def]
  ring

 
theorem integrable_history_coordinate (n p : ℕ) (γ β : Fin p → ℝ)
    (σ : Configuration n) (a b : History n p) (e : Edge n) :
    Integrable (fun J : Disorder n => pairedMix n p β σ a b *
      ((J e : ℂ)*Complex.exp (∑ f, pairedPhase n p γ a b f*(J f : ℂ)))) (disorderLaw n) :=
  (GaussianFourier.integrable_coord_exp_sum (pairedPhase n p γ a b) e).const_mul _

theorem integral_history_coordinate (n p : ℕ) (γ β : Fin p → ℝ)
    (σ : Configuration n) (a b : History n p) (e : Edge n) :
    (∫ J : Disorder n, pairedMix n p β σ a b *
      ((J e : ℂ)*Complex.exp (∑ f, pairedPhase n p γ a b f*(J f : ℂ))) ∂disorderLaw n) =
      pairedMix n p β σ a b * pairedPhase n p γ a b e *
        Complex.exp (∑ f, (pairedPhase n p γ a b f)^2/2) := by
  rw [integral_const_mul]
  change _ * (∫ J : Disorder n, _ ∂GaussianFourier.law (Edge n)) = _
  rw [GaussianFourier.integral_coord_exp_sum,mul_assoc]

end SKQAOA

namespace SKQAOA

 
theorem quad_cost_history_basis (n : ℕ) (J : Disorder n) (ψ : State n) :
    quad ψ (cost n J)=∑ σ : Configuration n, ∑ e : Edge n,
      (skCoeff n σ e : ℂ)*((J e : ℂ)*(star (ψ σ)*ψ σ)) := by
  simp only [quad,dotProduct,cost_eq_diagonal,Matrix.mulVec_diagonal,Pi.star_apply,
    hamiltonian_eq_coeff,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem coordinate_state_history (n p : ℕ) (J : Disorder n) (γ β : Fin p → ℝ)
    (σ : Configuration n) (e : Edge n) :
    (J e : ℂ)*(star (qaoaState n p J γ β σ)*qaoaState n p J γ β σ)=
      ∑ a : History n p, ∑ b : History n p, pairedMix n p β σ a b *
        ((J e : ℂ)*Complex.exp (∑ f, pairedPhase n p γ a b f*(J f : ℂ))) := by
  rw [qaoaState_pair_history]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem integrable_coordinate_state (n p : ℕ) (γ β : Fin p → ℝ)
    (σ : Configuration n) (e : Edge n) :
    Integrable (fun J : Disorder n =>
      (J e : ℂ)*(star (qaoaState n p J γ β σ)*qaoaState n p J γ β σ)) (disorderLaw n) := by
  simp_rw [coordinate_state_history]
  exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun b _ => integrable_history_coordinate n p γ β σ a b e))

theorem integral_coordinate_state (n p : ℕ) (γ β : Fin p → ℝ)
    (σ : Configuration n) (e : Edge n) :
    (∫ J : Disorder n,
      (J e : ℂ)*(star (qaoaState n p J γ β σ)*qaoaState n p J γ β σ) ∂disorderLaw n)=
      ∑ a : History n p, ∑ b : History n p, pairedMix n p β σ a b *
        pairedPhase n p γ a b e * Complex.exp (∑ f, (pairedPhase n p γ a b f)^2/2) := by
  simp_rw [coordinate_state_history]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
    (fun b _ => integrable_history_coordinate n p γ β σ a b e))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum _ (fun b _ => integrable_history_coordinate n p γ β σ a b e)]
  simp_rw [integral_history_coordinate]

theorem integrable_quad_cost (n p : ℕ) (γ β : Fin p → ℝ) :
    Integrable (fun J : Disorder n => quad (qaoaState n p J γ β) (cost n J)) (disorderLaw n) := by
  simp_rw [quad_cost_history_basis]
  exact integrable_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun e _ =>
    (integrable_coordinate_state n p γ β σ e).const_mul _))

 

theorem expectedEnergy_history (n p : ℕ) (γ β : Fin p → ℝ) :
    expectedEnergy n p γ β =
      (∑ σ : Configuration n, ∑ e : Edge n, (skCoeff n σ e : ℂ)*
        (∑ a : History n p, ∑ b : History n p, pairedMix n p β σ a b *
          pairedPhase n p γ a b e * Complex.exp (∑ f, (pairedPhase n p γ a b f)^2/2))).re /
        (n : ℝ) := by
  have he : (fun J : Disorder n => energyDensity n p J γ β)=
      fun J => (quad (qaoaState n p J γ β) (cost n J)).re/(n:ℝ) := rfl
  have hi : (∫ J, (quad (qaoaState n p J γ β) (cost n J)).re ∂disorderLaw n) =
      (∫ J, quad (qaoaState n p J γ β) (cost n J) ∂disorderLaw n).re :=
    integral_re (integrable_quad_cost n p γ β)
  rw [expectedEnergy,he,integral_div,hi]
  congr 2
  simp_rw [quad_cost_history_basis]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun e _ =>
    (integrable_coordinate_state n p γ β σ e).const_mul _))]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_finsetSum _ (fun e _ => (integrable_coordinate_state n p γ β σ e).const_mul _)]
  simp_rw [integral_const_mul,integral_coordinate_state]

end SKQAOA

end

end OAI
