import Mathlib
import OAI.Probability.ParisiFinite.Field
import OAI.Probability.ParisiFinite.RotateIJApply

namespace OAI

/-! Count. -/

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
namespace BinaryOccupations
open scoped InnerProductSpace

 
def count (D : ℕ) (s : Finset (Fin D)) : Fin (D+1) :=
  ⟨s.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_univ s)⟩

@[simp] theorem count_eq_iff (D : ℕ) (s : Finset (Fin D)) (m : Fin (D+1)) :
    count D s=m ↔ s.card=m.val := Fin.ext_iff

theorem count_surjective (D : ℕ) : Function.Surjective (count D) := by
  intro m
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (show m.val≤(Finset.univ : Finset (Fin D)).card by simpa using Nat.le_of_lt_succ m.isLt)
  exact ⟨s,(count_eq_iff D s m).mpr hs⟩

 
theorem fiber_card (D : ℕ) (m : Fin (D+1)) :
    Fintype.card {s : Finset (Fin D) // count D s=m}=D.choose m.val := by
  calc
    _ = Fintype.card {s : Finset (Fin D) // s.card=m.val} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun s => count_eq_iff D s m))
    _ = _ := by simp

 

def embedding (D : ℕ) :
    EuclideanSpace ℂ (Fin (D+1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Finset (Fin D)) :=
  FiniteOccupations.lift (count D) (count_surjective D)

@[simp] theorem embedding_apply (D : ℕ) (u : EuclideanSpace ℂ (Fin (D+1)))
    (s : Finset (Fin D)) :
    embedding D u s=(Real.sqrt (D.choose s.card : ℝ) : ℂ)⁻¹*u (count D s) := by
  change FiniteOccupations.weight (count D) (count D s)*u (count D s)=_
  rw [FiniteOccupations.weight,fiber_card]
  rfl

 
theorem mem_range_iff_card (D : ℕ) (u : EuclideanSpace ℂ (Finset (Fin D))) :
    u∈Set.range (embedding D) ↔ ∀s t : Finset (Fin D), s.card=t.card → u s=u t := by
  rw [embedding,FiniteOccupations.mem_range_iff]
  simp only [count,Fin.mk.injEq]

end BinaryOccupations

namespace SKQAOA

 
def extendAngles {p : ℕ} (γ : Fin p → ℝ) : (k : ℕ) → Fin (p+k) → ℝ
  | 0 => γ
  | k+1 => Fin.snoc (extendAngles γ k) 0

@[simp] theorem expectedEnergy_extendAngles (n p k : ℕ) (γ β : Fin p → ℝ) :
    expectedEnergy n (p+k) (extendAngles γ k) (extendAngles β k)=expectedEnergy n p γ β := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Nat.add_succ,extendAngles,expectedEnergy_pad] using ih

@[simp] theorem value_extendAngles (p k : ℕ) (γ β : Fin p → ℝ) :
    value (p+k) (extendAngles γ k) (extendAngles β k)=value p γ β := by
  simp [value]

end SKQAOA

namespace SKQAOA

 

theorem explicit_ground_lower_bound : Real.exp (-1/2)/2 ≤ Pstar := by
  have ht : Tendsto (fun n => expectedEnergy n 1 (fun _ => 1/2) (fun _ => Real.pi/8))
      atTop (𝓝 (Real.exp (-1/2)/2)) := by
    convert tendsto_expectedEnergy_one (fun _ => 1/2) (fun _ => Real.pi/8) using 1
    norm_num
    rw [show 4*(Real.pi/8)=Real.pi/2 by ring,Real.sin_pi_div_two]
    ring
  exact le_of_tendsto_of_tendsto ht tendsto_expectedGround
    (Filter.Eventually.of_forall fun n => expectedEnergy_le_expectedGround n 1 _ _)

theorem Pstar_pos : 0 < Pstar :=
  lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) explicit_ground_lower_bound

 

theorem exists_positive_word_every_depth (p : ℕ) (hp : 1≤p) :
    ∃γ β : Fin p → ℝ,
      Tendsto (fun n => expectedEnergy n p γ β) atTop (𝓝 (Real.exp (-1/2)/2)) ∧
      value p γ β=Real.exp (-1/2)/2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
  refine ⟨extendAngles (fun _ : Fin 1 => 1/2) k,
    extendAngles (fun _ : Fin 1 => Real.pi/8) k,?_,?_⟩
  · simp only [expectedEnergy_extendAngles]
    have ht := tendsto_expectedEnergy_one (fun _ => 1/2) (fun _ => Real.pi/8)
    rw [←value_one (fun _ => 1/2) (fun _ => Real.pi/8),explicit_one_layer_value] at ht
    exact ht
  · simpa only [value_extendAngles] using explicit_one_layer_value

end SKQAOA

namespace SKQAOA

open MeasureTheory ProbabilityTheory Filter

@[simp] theorem hamiltonian_neg_disorder (n : ℕ) (J : Disorder n) (σ : Configuration n) :
    hamiltonian n (-J) σ = -hamiltonian n J σ := by
  simp [hamiltonian,Finset.sum_neg_distrib]

 

theorem neg_energyDensity_le_groundMaximum (n p : ℕ) (J : Disorder n)
    (γ β : Fin p → ℝ) :
    -energyDensity n p J γ β ≤ groundMaximum n (-J)/(n : ℝ) := by
  rw [energyDensity_eq,←neg_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    -(∑σ,Complex.normSq (qaoaState n p J γ β σ)*hamiltonian n J σ) =
        ∑σ,Complex.normSq (qaoaState n p J γ β σ)*hamiltonian n (-J) σ := by
      simp [Finset.sum_neg_distrib]
    _ ≤ ∑σ,Complex.normSq (qaoaState n p J γ β σ)*groundMaximum n (-J) :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left
        (hamiltonian_le_groundMaximum n (-J) σ) (Complex.normSq_nonneg _)
    _ = groundMaximum n (-J) := by
      rw [←Finset.sum_mul]
      change mass (qaoaState n p J γ β)*groundMaximum n (-J)=_
      rw [qaoaState_mass,one_mul]

 

theorem disorder_neg_preserving (n : ℕ) :
    MeasurePreserving (fun J : Disorder n => -J) (disorderLaw n) (disorderLaw n) := by
  refine measurePreserving_pi (fun _ : Edge n => gaussianReal 0 1)
    (fun _ : Edge n => gaussianReal 0 1) (f := fun (_ : Edge n) (x : ℝ) => -x) ?_
  intro e
  exact ⟨measurable_neg,by simpa using gaussianReal_map_neg (μ := 0) (v := 1)⟩

 

theorem abs_expectedEnergy_le_expectedGround (n p : ℕ) (γ β : Fin p → ℝ) :
    |expectedEnergy n p γ β| ≤ expectedGround n := by
  apply abs_le.mpr
  refine ⟨?_,expectedEnergy_le_expectedGround n p γ β⟩
  have hp := disorder_neg_preserving n
  have hi := hp.integrable_comp_of_integrable ((groundMaximum_integrable n).div_const (n : ℝ))
  have h := integral_mono (energyDensity_integrable n p γ β).neg hi
    (fun J => neg_energyDensity_le_groundMaximum n p J γ β)
  have he : (∫J : Disorder n,groundMaximum n (-J)/(n : ℝ) ∂disorderLaw n)=expectedGround n := by
    calc
      _ = ∫J : Disorder n,groundMaximum n J/(n : ℝ) ∂disorderLaw n :=
        hp.integral_comp (MeasurableEquiv.neg (Disorder n)).measurableEmbedding
          (fun J => groundMaximum n J/(n : ℝ))
      _ = _ := integral_div _ _
  change (∫J : Disorder n,-energyDensity n p J γ β ∂disorderLaw n) ≤
    (∫J : Disorder n,groundMaximum n (-J)/(n : ℝ) ∂disorderLaw n) at h
  rw [integral_neg,he] at h
  change -(∫J : Disorder n,energyDensity n p J γ β ∂disorderLaw n) ≤ _ at h
  change -expectedGround n ≤ (∫J : Disorder n,energyDensity n p J γ β ∂disorderLaw n)
  linarith

 

theorem eventually_uniform_expectedEnergy_bound {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀p : ℕ, ∀γ β : Fin p → ℝ,
      |expectedEnergy n p γ β| < Pstar+ε := by
  have he : ∀ᶠ n in atTop, expectedGround n < Pstar+ε :=
    tendsto_expectedGround.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [he] with n hn p γ β
  exact (abs_expectedEnergy_le_expectedGround n p γ β).trans_lt hn

end SKQAOA

 

open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.SiteHistories

 
def Bits : ℕ → Type
  | 0 => Unit
  | p+1 => Bool × Bits p

instance bitsFintype : (p : ℕ) → Fintype (Bits p)
  | 0 => inferInstanceAs (Fintype Unit)
  | p+1 => @instFintypeProd Bool (Bits p) inferInstance (bitsFintype p)

instance bitsDecidableEq : (p : ℕ) → DecidableEq (Bits p)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | p+1 => @instDecidableEqProd Bool (Bits p) inferInstance (bitsDecidableEq p)

def atVertex (n : ℕ) : (p : ℕ) → History n p → Fin n → Bits p
  | 0, _, _ => ()
  | p+1, h, i => (h.1 i,atVertex n p h.2 i)

def assemble (n : ℕ) : (p : ℕ) → (Fin n → Bits p) → History n p
  | 0, _ => ()
  | p+1, h => (fun i => (h i).1,assemble n p (fun i => (h i).2))

@[simp] theorem atVertex_assemble (n p : ℕ) (h : Fin n → Bits p) :
    atVertex n p (assemble n p h)=h := by
  induction p with
  | zero => funext i; change (():Unit)=h i; exact Subsingleton.elim _ _
  | succ p ih =>
    funext i
    change ((h i).1,atVertex n p (assemble n p (fun i => (h i).2)) i)=h i
    rw [ih]
    exact Prod.eta _

@[simp] theorem assemble_atVertex (n p : ℕ) (h : History n p) :
    assemble n p (atVertex n p h)=h := by
  induction p with
  | zero => change (():Unit)=h; exact Subsingleton.elim _ _
  | succ p ih =>
    change (h.1,assemble n p (atVertex n p h.2))=h
    rw [ih]
    exact Prod.eta _

def historyEquiv (n p : ℕ) : History n p ≃ (Fin n → Bits p) where
  toFun := atVertex n p
  invFun := assemble n p
  left_inv := assemble_atVertex n p
  right_inv := atVertex_assemble n p

def step (t : ℝ) (σ τ : Bool) : ℂ :=
  if σ=τ then (Real.cos t:ℂ) else -(Real.sin t:ℂ)*Complex.I

def mix : (p : ℕ) → (Fin p → ℝ) → Bool → Bits p → ℂ
  | 0, _, _, _ => ((Real.sqrt 2)⁻¹:ℝ)
  | p+1, β, σ, h => step (β (Fin.last p)) σ h.1 * mix p (fun i => β i.castSucc) h.1 h.2

lemma sqrt_nat_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x^n)=(Real.sqrt x)^n := by
  apply (Real.sqrt_eq_iff_mul_self_eq (pow_nonneg hx n) (pow_nonneg (Real.sqrt_nonneg x) n)).mpr
  rw [←mul_pow,Real.mul_self_sqrt hx]

 
theorem historyMix_factor (n p : ℕ) (β : Fin p → ℝ) (σ : Configuration n)
    (h : History n p) :
    historyMix n p β σ h = ∏i, mix p β (σ i) (atVertex n p h i) := by
  induction p generalizing σ with
  | zero => simp [historyMix,mix,sqrt_nat_pow 2 (by norm_num)]
  | succ p ih =>
    simp only [historyMix,mix,atVertex]
    rw [mixer_evolution_apply,ih,←Finset.prod_mul_distrib]
    rfl

 
abbrev Site (p : ℕ) := Bool × Bits p × Bits p

def weight (p : ℕ) (β : Fin p → ℝ) (s : Site p) : ℂ :=
  star (mix p β s.1 s.2.1)*mix p β s.1 s.2.2

def trajectoriesEquiv (n p : ℕ) :
    (Configuration n × History n p × History n p) ≃ (Fin n → Site p) where
  toFun h i := (h.1 i,atVertex n p h.2.1 i,atVertex n p h.2.2 i)
  invFun h := (fun i => (h i).1,assemble n p (fun i => (h i).2.1),
    assemble n p (fun i => (h i).2.2))
  left_inv h := by simp
  right_inv h := by funext i; simp

@[simp] theorem trajectoriesEquiv_apply (n p : ℕ)
    (h : Configuration n × History n p × History n p) (i : Fin n) :
    trajectoriesEquiv n p h i=(h.1 i,atVertex n p h.2.1 i,atVertex n p h.2.2 i) := rfl

theorem pairedMix_factor (n p : ℕ) (β : Fin p → ℝ) (σ : Configuration n)
    (a b : History n p) :
    pairedMix n p β σ a b = ∏i, weight p β (σ i,atVertex n p a i,atVertex n p b i) := by
  rw [pairedMix,historyMix_factor,historyMix_factor]
  simp only [star_prod,←Finset.prod_mul_distrib,weight]

 
theorem sum_pairedMix (n p : ℕ) (β : Fin p → ℝ) :
    (∑σ : Configuration n, ∑a : History n p, ∑b : History n p,
      pairedMix n p β σ a b)=1 := by
  have h (σ : Configuration n) := qaoaState_pair_history n p (fun _ => 0) (fun _ => 0) β σ
  simp only [Complex.ofReal_zero,mul_zero,Finset.sum_const_zero,Complex.exp_zero,mul_one] at h
  simp_rw [←h]
  change star (qaoaState n p (fun _ => 0) (fun _ => 0) β) ⬝ᵥ
    qaoaState n p (fun _ => 0) (fun _ => 0) β = 1
  rw [←mass_eq_dot,qaoaState_mass]
  norm_num

 
theorem sum_weight (p : ℕ) (β : Fin p → ℝ) : ∑s : Site p, weight p β s=1 := by
  have h := sum_pairedMix 1 p β
  simp_rw [pairedMix_factor] at h
  have hs := (trajectoriesEquiv 1 p).sum_comp (fun f => ∏i,weight p β (f i))
  rw [Fintype.sum_prod_type] at hs
  simp_rw [Fintype.sum_prod_type] at hs
  simp only [trajectoriesEquiv_apply] at hs
  rw [hs] at h
  rw [←Fintype.prod_sum] at h
  simpa using h

lemma norm_step_le_one (t : ℝ) (σ τ : Bool) : ‖step t σ τ‖ ≤ 1 := by
  unfold step
  split_ifs <;> simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one]
  · exact Real.abs_cos_le_one t
  · exact Real.abs_sin_le_one t

lemma norm_mix_le_one (p : ℕ) (β : Fin p → ℝ) (σ : Bool) (h : Bits p) :
    ‖mix p β σ h‖ ≤ 1 := by
  induction p generalizing σ with
  | zero =>
    simp only [mix,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply inv_le_one_of_one_le₀
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  | succ p ih =>
    rw [mix,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_step_le_one _ _ _)).trans (ih _ _ _)

lemma norm_weight_le_one (p : ℕ) (β : Fin p → ℝ) (s : Site p) :
    ‖weight p β s‖ ≤ 1 := by
  rw [weight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_mix_le_one _ _ _ _)).trans
    (norm_mix_le_one _ _ _ _)

def bitSpin (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem abs_bitSpin (b : Bool) : |bitSpin b|=1 := by cases b <;> norm_num [bitSpin]

def interaction : (p : ℕ) → (Fin p → ℝ) → Bits p → Bits p → ℝ
  | 0, _, _, _ => 0
  | p+1, γ, a, b => γ (Fin.last p)*bitSpin a.1*bitSpin b.1 +
      interaction p (fun i => γ i.castSucc) a.2 b.2

def angleMass : (p : ℕ) → (Fin p → ℝ) → ℝ
  | 0, _ => 0
  | p+1, γ => |γ (Fin.last p)|+angleMass p (fun i => γ i.castSucc)

lemma angleMass_nonneg (p : ℕ) (γ : Fin p → ℝ) : 0 ≤ angleMass p γ := by
  induction p with
  | zero => rfl
  | succ p ih => exact add_nonneg (abs_nonneg _) (ih _)

lemma abs_interaction_le (p : ℕ) (γ : Fin p → ℝ) (a b : Bits p) :
    |interaction p γ a b| ≤ angleMass p γ := by
  induction p with
  | zero => simp [interaction,angleMass]
  | succ p ih =>
    calc
      _ ≤ |γ (Fin.last p)*bitSpin a.1*bitSpin b.1| +
          |interaction p (fun i => γ i.castSucc) a.2 b.2| := abs_add_le _ _
      _ ≤ |γ (Fin.last p)|+angleMass p (fun i => γ i.castSucc) := by
        simp only [abs_mul,abs_bitSpin,mul_one]
        exact add_le_add le_rfl (ih _ _ _)
      _ = _ := rfl

 
def delta (p : ℕ) (γ : Fin p → ℝ) (s t : Site p) : ℝ :=
  interaction p γ s.2.1 t.2.1 - interaction p γ s.2.2 t.2.2

lemma abs_delta_le (p : ℕ) (γ : Fin p → ℝ) (s t : Site p) :
    |delta p γ s t| ≤ 2*angleMass p γ := by
  calc
    _ ≤ |interaction p γ s.2.1 t.2.1|+|interaction p γ s.2.2 t.2.2| := abs_sub _ _
    _ ≤ angleMass p γ+angleMass p γ := add_le_add (abs_interaction_le _ _ _ _) (abs_interaction_le _ _ _ _)
    _ = _ := by ring

theorem historyPhase_local (n p : ℕ) (γ : Fin p → ℝ) (a : History n p) (e : Edge n) :
    historyPhase n p γ a e = -Complex.I*((Real.sqrt (n:ℝ))⁻¹:ℂ)*
      (interaction p γ (atVertex n p a e.1.1) (atVertex n p a e.1.2):ℂ) := by
  induction p with
  | zero => simp [historyPhase,interaction]
  | succ p ih =>
    simp only [historyPhase,interaction,atVertex]
    rw [ih]
    simp only [skCoeff,spin,bitSpin,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_inv]
    ring

theorem pairedPhase_local (n p : ℕ) (γ : Fin p → ℝ)
    (h : Configuration n × History n p × History n p) (e : Edge n) :
    pairedPhase n p γ h.2.1 h.2.2 e = Complex.I*((Real.sqrt (n:ℝ))⁻¹:ℂ)*
      (delta p γ (trajectoriesEquiv n p h e.1.1) (trajectoriesEquiv n p h e.1.2):ℂ) := by
  rw [pairedPhase,historyPhase_local,historyPhase_local]
  simp only [delta,trajectoriesEquiv_apply,star_mul,star_neg,Complex.star_def,
    Complex.conj_I,neg_neg,Complex.conj_ofReal,Complex.ofReal_sub,map_inv₀]
  ring

 
def edgeKernel (n p : ℕ) (γ : Fin p → ℝ) (s t : Site p) : ℝ :=
  Real.exp (-(delta p γ s t)^2*((n:ℝ)⁻¹)/2)

lemma edgeKernel_pos (n p : ℕ) (γ : Fin p → ℝ) (s t : Site p) :
    0 < edgeKernel n p γ s t := Real.exp_pos _

lemma edgeKernel_le_one (n p : ℕ) (γ : Fin p → ℝ) (s t : Site p) :
    edgeKernel n p γ s t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg n))) (by norm_num)

lemma abs_edgeKernel_sub_one_le (n p : ℕ) (γ : Fin p → ℝ) (s t : Site p) :
    |edgeKernel n p γ s t-1| ≤ (2*angleMass p γ)^2*((n:ℝ)⁻¹)/2 := by
  have hd := abs_delta_le p γ s t
  have hsq : (delta p γ s t)^2 ≤ (2*angleMass p γ)^2 := by
    nlinarith [sq_abs (delta p γ s t),abs_nonneg (delta p γ s t),angleMass_nonneg p γ]
  have he := Real.add_one_le_exp (-(delta p γ s t)^2*((n:ℝ)⁻¹)/2)
  rw [abs_of_nonpos (sub_nonpos.mpr (edgeKernel_le_one n p γ s t))]
  have hmul := mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr (Nat.cast_nonneg n))
  change _ ≤ _
  dsimp [edgeKernel] at *
  linarith

 
theorem exp_pairedPhase_sq (n p : ℕ) (γ : Fin p → ℝ)
    (h : Configuration n × History n p × History n p) (e : Edge n) :
    Complex.exp ((pairedPhase n p γ h.2.1 h.2.2 e)^2/2)=
      (edgeKernel n p γ (trajectoriesEquiv n p h e.1.1) (trajectoriesEquiv n p h e.1.2):ℂ) := by
  rw [pairedPhase_local,edgeKernel,Complex.ofReal_exp]
  congr 1
  simp only [mul_pow,Complex.I_sq,←Complex.ofReal_pow,inv_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast
  ring

end SKQAOA.SiteHistories

 

open scoped BigOperators

namespace FiniteHistory

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]

def expectation (q : A → ℂ) (F : (V → A) → ℂ) : ℂ :=
  ∑a : V → A, (∏i, q (a i))*F a

 

theorem restrict_expectation (q : A → ℂ) (hq : ∑a,q a=1)
    (S : Finset V) (F : (S → A) → ℂ) :
    expectation q (fun (a : V → A) => F (fun i : S => a i)) =
      expectation q F := by
  let e := Equiv.piEquivPiSubtypeProd (fun i : V => i∈S) (fun _ => A)
  let G : ((S → A) × ({i : V // i∉S} → A)) → ℂ :=
    fun ab => ((∏i:S,q (ab.1 i))*F ab.1)*(∏i:{i:V // i∉S},q (ab.2 i))
  have hs := e.sum_comp G
  have hg (a : V → A) : G (e a) = (∏i,q (a i))*F (fun i:S => a i) := by
    simp only [G,e,Equiv.piEquivPiSubtypeProd_apply]
    rw [mul_right_comm]
    congr 1
    convert Fintype.prod_subtype_mul_prod_subtype (fun i : V => i∈S) (fun i => q (a i)) using 1
    congr 2
    ext x
    simp

  simp_rw [hg] at hs
  dsimp only [expectation]
  rw [hs,Fintype.sum_prod_type]
  dsimp only [G]
  simp_rw [←Finset.mul_sum,←Fintype.prod_sum (fun _ : {i:V // i∉S} => q),hq]
  simp

lemma norm_expectation_le (q : A → ℂ) (F : (V → A) → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀a, ‖F a‖ ≤ C) :
    ‖expectation q F‖ ≤ (∑a, ‖q a‖)^(Fintype.card V)*C := by
  calc
    _ ≤ ∑a:V→A, ‖(∏i,q (a i))*F a‖ := norm_sum_le _ _
    _ ≤ ∑a:V→A, (∏i,‖q (a i)‖)*C := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hF a) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (Finset.norm_prod_le _ _) hC)
    _ = (∑a, ‖q a‖)^(Fintype.card V)*C := by
      rw [←Finset.sum_mul,←Fintype.prod_sum (fun _ : V => fun a:A => ‖q a‖)]
      simp

variable [Nonempty A]

def extend (S : Finset V) (a : S → A) : V → A :=
  fun i => if h : i∈S then a ⟨i,h⟩ else Classical.choice (inferInstance : Nonempty A)

omit [Fintype V] [Fintype A] in
@[simp] lemma extend_apply (S : Finset V) (a : S → A) (i : S) : extend S a i=a i := by
  simp [extend,i.property]

 

theorem norm_expectation_le_of_local (q : A → ℂ) (hq : ∑a,q a=1)
    (S : Finset V) (F : (V → A) → ℂ)
    (hlocal : ∀a b, (∀i∈S, a i=b i) → F a=F b)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀a, ‖F a‖ ≤ C) :
    ‖expectation q F‖ ≤ (∑a, ‖q a‖)^S.card*C := by
  have he : F=(fun a => F (extend S (fun i:S => a i))) := by
    funext a
    apply hlocal
    intro i hi
    simp [extend,hi]
  rw [he,restrict_expectation q hq S (fun a => F (extend S a))]
  have hh := norm_expectation_le q (fun a:S→A => F (extend S a)) hC (fun a => hF _)
  simpa using hh

end FiniteHistory

 

open scoped BigOperators Topology
open Filter

namespace SKQAOA.SiteHistories

 

lemma tendsto_scaled_exp (c : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*(Real.exp (c/(n:ℝ))-1)) atTop (𝓝 c) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (c*t)) c 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_mul c).exp using 1 <;> simp
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝[≠] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_inv_atTop_nhds_zero_nat,?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,inv_eq_zero] using
      (show (n:ℝ)≠0 by exact_mod_cast (by omega : n≠0))
  simpa only [Function.comp_def,zero_add,mul_zero,Real.exp_zero,smul_eq_mul,inv_inv,
    div_eq_mul_inv] using hd.tendsto_slope_zero.comp hi

def kernelScaled (n p : ℕ) (γ : Fin p → ℝ) (u v : Site p) : ℝ :=
  (n:ℝ)*(edgeKernel n p γ u v-1)

lemma tendsto_kernel (p : ℕ) (γ : Fin p → ℝ) (u v : Site p) :
    Tendsto (fun n : ℕ => edgeKernel n p γ u v) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => -(delta p γ u v)^2/(2*(n:ℝ))) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := -(delta p γ u v)^2/2)).mul
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero,zero_mul,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using this
  convert Real.continuous_exp.continuousAt.tendsto.comp ht using 1
  · funext n
    simp only [edgeKernel,Function.comp_def]
    congr 1
    ring
  · simp

lemma tendsto_kernelScaled (p : ℕ) (γ : Fin p → ℝ) (u v : Site p) :
    Tendsto (fun n : ℕ => kernelScaled n p γ u v) atTop (𝓝 (-(delta p γ u v)^2/2)) := by
  have ht := tendsto_scaled_exp (-(delta p γ u v)^2/2)
  convert ht using 1
  funext n
  unfold kernelScaled edgeKernel
  congr 3
  ring

 

def graphCoefficient (N m p : ℕ) (γ β : Fin p → ℝ) (r : Edge m)
    (H : Finset (Edge m)) : ℂ :=
  FiniteHistory.expectation (weight p β) (fun a : Fin m → Site p =>
    (bitSpin (a r.1.1).1:ℂ)*(bitSpin (a r.1.2).1:ℂ)*Complex.I*
      (delta p γ (a r.1.1) (a r.1.2):ℂ)*
      (edgeKernel N p γ (a r.1.1) (a r.1.2):ℂ)*
        ∏e∈H,if e=r then 0 else (kernelScaled N p γ (a e.1.1) (a e.1.2):ℂ))

def graphCoefficientLimit (m p : ℕ) (γ β : Fin p → ℝ) (r : Edge m)
    (H : Finset (Edge m)) : ℂ :=
  FiniteHistory.expectation (weight p β) (fun a : Fin m → Site p =>
    (bitSpin (a r.1.1).1:ℂ)*(bitSpin (a r.1.2).1:ℂ)*Complex.I*
      (delta p γ (a r.1.1) (a r.1.2):ℂ)*
        ∏e∈H,if e=r then 0 else (-(delta p γ (a e.1.1) (a e.1.2):ℂ)^2/2))

 

theorem tendsto_graphCoefficient (m p : ℕ) (γ β : Fin p → ℝ) (r : Edge m)
    (H : Finset (Edge m)) :
    Tendsto (fun N => graphCoefficient N m p γ β r H) atTop
      (𝓝 (graphCoefficientLimit m p γ β r H)) := by
  unfold graphCoefficient graphCoefficientLimit FiniteHistory.expectation
  apply tendsto_finsetSum
  intro a ha
  apply Tendsto.const_mul
  have hk := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_kernel p γ (a r.1.1) (a r.1.2))
  have hp : Tendsto (fun N => ∏e∈H,if e=r then (0:ℂ) else
      (kernelScaled N p γ (a e.1.1) (a e.1.2):ℂ)) atTop
      (𝓝 (∏e∈H,if e=r then 0 else (-(delta p γ (a e.1.1) (a e.1.2):ℂ)^2/2))) := by
    apply tendsto_finsetProd
    intro e he
    by_cases her : e=r
    · simp only [her,ite_true]
      exact tendsto_const_nhds
    · simp only [her,ite_false]
      convert Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_kernelScaled p γ (a e.1.1) (a e.1.2)) using 1 <;> push_cast <;> rfl
  simpa only [Function.comp_def,Complex.ofReal_one,mul_one] using (hk.const_mul
    ((bitSpin (a r.1.1).1:ℂ)*(bitSpin (a r.1.2).1:ℂ)*Complex.I*
      (delta p γ (a r.1.1) (a r.1.2):ℂ))).mul hp

end SKQAOA.SiteHistories

 

open scoped BigOperators

namespace FiniteHistory
variable {V W A : Type*} [Fintype V] [Fintype W] [Fintype A] [DecidableEq V] [DecidableEq W]

 
theorem expectation_equiv (q : A → ℂ) (e : V ≃ W) (F : (W → A) → ℂ) :
    expectation q (fun a : V → A => F (a ∘ e.symm))=expectation q F := by
  let ψ : (V → A) ≃ (W → A) := Equiv.arrowCongr e (Equiv.refl A)
  have he (a : V → A) : (∏i:V,q (a i))*(F (a ∘ e.symm))=
      (∏j:W,q (ψ a j))*F (ψ a) := by
    have hp : (∏j:W,q (ψ a j))=(∏i:V,q (a i)) := by
      simpa [ψ] using e.symm.prod_comp (fun i : V => q (a i))
    rw [hp]
    rfl
  dsimp only [expectation]
  simp_rw [he]
  exact ψ.sum_comp (fun a : W → A => (∏j:W,q (a j))*F a)

 

theorem expectation_embedding (q : A → ℂ) (hq : ∑a,q a=1)
    (f : W ↪ V) (F : (W → A) → ℂ) :
    expectation q (fun a : V → A => F (a ∘ f))=expectation q F := by
  classical
  let S : Finset V := Finset.univ.image f
  let e : W ≃ S := Equiv.ofBijective (fun w => ⟨f w,Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩⟩)
    (by
      constructor
      · intro u v h
        exact f.injective (congrArg Subtype.val h)
      · intro v
        obtain ⟨w,hw,he⟩ := Finset.mem_image.mp v.property
        exact ⟨w,Subtype.ext he⟩)
  have he (a : V → A) : F (a ∘ f)=F ((fun i : S => a i) ∘ e) := rfl
  simp_rw [he]
  rw [restrict_expectation q hq S (fun a => F (a ∘ e))]
  exact expectation_equiv q e.symm F
end FiniteHistory

end

end OAI
