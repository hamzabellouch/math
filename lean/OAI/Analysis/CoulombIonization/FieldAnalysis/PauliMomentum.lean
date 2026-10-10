import Mathlib
import OAI.Analysis.CoulombIonization.Variational.PhaseBathtub

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PauliMomentum_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

abbrev NeumannSpinMode := (Fin 3 → ℕ) × Fin 2

def discretePhaseDensity (S : Finset NeumannSpinMode) (p : Space) : ℝ :=
  coherentFactor*∑ q ∈ S, (momentumCell q.1).indicator (fun _ => (1:ℝ)) p

lemma discretePhaseDensity_nonneg (S : Finset NeumannSpinMode) (p : Space) :
    0 ≤ discretePhaseDensity S p := by
  apply mul_nonneg coherentFactor_pos.le
  apply Finset.sum_nonneg
  intro q _
  exact Set.indicator_nonneg (fun _ _ => by norm_num) p

lemma discretePhaseDensity_pauli (S : Finset NeumannSpinMode) (p : Space) :
    discretePhaseDensity S p ≤ 2*coherentFactor := by
  classical
  let A := S.filter (fun q => p ∈ momentumCell q.1)
  have he : (∑ q ∈ S, (momentumCell q.1).indicator (fun _ => (1:ℝ)) p) = (A.card:ℝ) := by
    simp only [A,Finset.card_filter, Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hp : p ∈ momentumCell q.1 <;> simp [hp]
  have hc : A.card ≤ 2 := by
    have hh : A.card ≤ (Finset.univ : Finset (Fin 2)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _)
      intro q hq r hr hqr
      apply Prod.ext _ hqr
      by_contra hs
      exact Set.disjoint_left.mp (momentumCell_disjoint hs)
        (Finset.mem_filter.mp hq).2 (Finset.mem_filter.mp hr).2
    simpa using hh
  unfold discretePhaseDensity
  rw [he,mul_comm (2:ℝ)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) coherentFactor_pos.le

lemma momentumCell_finite (n : Fin 3 → ℕ) : volume (momentumCell n) < ⊤ := by
  rw [volume_momentumCell]
  exact ENNReal.ofReal_lt_top

lemma momentumCell_integrable (n : Fin 3 → ℕ) :
    Integrable ((momentumCell n).indicator (fun _ => (1:ℝ))) := by
  apply (integrable_indicator_iff (measurableSet_momentumCell n)).2
  exact integrableOn_const (momentumCell_finite n).ne

lemma momentumCell_mass (n : Fin 3 → ℕ) :
    coherentFactor*(∫ p : Space, (momentumCell n).indicator (fun _ => (1:ℝ)) p) = 1 := by
  rw [integral_indicator (measurableSet_momentumCell n),integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,
    volume_momentumCell,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*Real.pi)^3)]
  exact inv_mul_cancel₀ (by positivity)

lemma discretePhaseDensity_integrable (S : Finset NeumannSpinMode) :
    Integrable (discretePhaseDensity S) := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun q _ => momentumCell_integrable q.1)

lemma discretePhaseDensity_mass (S : Finset NeumannSpinMode) :
    (∫ p, discretePhaseDensity S p) = S.card := by
  unfold discretePhaseDensity
  rw [integral_const_mul,integral_finsetSum _ (fun q _ => momentumCell_integrable q.1),Finset.mul_sum]
  simp only [momentumCell_mass,Finset.sum_const,nsmul_eq_mul,mul_one]

lemma momentumCell_kinetic_integrable (n : Fin 3 → ℕ) :
    IntegrableOn (fun p : Space => ‖p‖^2) (momentumCell n) := by
  let B := Real.pi^2*∑ i, ((n i:ℝ)+1)^2
  have hB : IntegrableOn (fun _ : Space => B) (momentumCell n) :=
    integrableOn_const (momentumCell_finite n).ne
  apply hB.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_momentumCell n)] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖p‖)]
  exact momentumCell_norm_sq hp

lemma momentumCell_indicator_kinetic_integrable (n : Fin 3 → ℕ) :
    Integrable ((momentumCell n).indicator (fun p : Space => ‖p‖^2)) :=
  (integrable_indicator_iff (measurableSet_momentumCell n)).2 (momentumCell_kinetic_integrable n)

lemma discretePhaseDensity_kinetic_eq (S : Finset NeumannSpinMode) :
    (fun p => ‖p‖^2*discretePhaseDensity S p) =
      fun p => coherentFactor*∑ q ∈ S, (momentumCell q.1).indicator (fun p : Space => ‖p‖^2) p := by
  ext p
  simp only [discretePhaseDensity,Set.indicator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

lemma discretePhaseDensity_kinetic_integrable (S : Finset NeumannSpinMode) :
    Integrable (fun p => ‖p‖^2*discretePhaseDensity S p) := by
  rw [discretePhaseDensity_kinetic_eq]
  apply Integrable.const_mul
  exact integrable_finsetSum S fun q _ => momentumCell_indicator_kinetic_integrable q.1

lemma discretePhaseDensity_kinetic_integral (S : Finset NeumannSpinMode) :
    (∫ p, ‖p‖^2*discretePhaseDensity S p) =
      ∑ q ∈ S, coherentFactor*∫ p in momentumCell q.1, ‖p‖^2 := by
  rw [discretePhaseDensity_kinetic_eq,integral_const_mul,
    integral_finsetSum S (fun q _ => momentumCell_indicator_kinetic_integrable q.1),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_indicator (measurableSet_momentumCell q.1)]

lemma momentumCell_kinetic_bound (n : Fin 3 → ℕ) :
    coherentFactor*(∫ p in momentumCell n, ‖p‖^2) ≤ Real.pi^2*∑ i, ((n i:ℝ)+1)^2 := by
  let B := Real.pi^2*∑ i, ((n i:ℝ)+1)^2
  have hB : IntegrableOn (fun _ : Space => B) (momentumCell n) :=
    integrableOn_const (momentumCell_finite n).ne
  have hb : (∫ p in momentumCell n, ‖p‖^2) ≤ ∫ _p in momentumCell n, B :=
    setIntegral_mono_on (momentumCell_kinetic_integrable n) hB
      (measurableSet_momentumCell n) (fun p hp => momentumCell_norm_sq hp)
  have hh := mul_le_mul_of_nonneg_left hb coherentFactor_pos.le
  rw [integral_const] at hh
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,volume_momentumCell,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*Real.pi)^3)] at hh
  have he : coherentFactor*((2*Real.pi)^3*B) = B := by
    unfold coherentFactor
    rw [←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
  rwa [he] at hh

theorem neumann_lattice_bathtub (S : Finset NeumannSpinMode) :
    tfKinetic*(S.card:ℝ)^(5/3:ℝ) ≤
      (Real.pi^2/2)*∑ q ∈ S, ∑ i, ((q.1 i:ℝ)+1)^2 := by
  have hb := phase_bathtub (Filter.Eventually.of_forall (discretePhaseDensity_nonneg S))
    (Filter.Eventually.of_forall (discretePhaseDensity_pauli S))
    (discretePhaseDensity_integrable S) (discretePhaseDensity_kinetic_integrable S)
  rw [discretePhaseDensity_mass] at hb
  refine hb.trans ?_
  rw [discretePhaseDensity_kinetic_integral,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have ht := mul_le_mul_of_nonneg_left (momentumCell_kinetic_bound q.1) (by norm_num : (0:ℝ) ≤ 1/2)
  linarith

end Work_PauliMomentum_scope

open MeasureTheory Set
open scoped BigOperators ENNReal

def neumannRemainderConstant : ℝ := tfKinetic + 3*Real.pi^2/2

lemma neumannRemainderConstant_pos : 0 < neumannRemainderConstant := by
  unfold neumannRemainderConstant
  unfold tfKinetic
  positivity

lemma square_shift_bound (a r : ℝ) (hr : 0 < r) :
    (a+1)^2 ≤ (1+1/r)*a^2+1+r := by
  have h := sq_nonneg (a-r)
  have hd : 0 ≤ (a-r)^2/r := div_nonneg h hr.le
  field_simp at hd ⊢
  nlinarith

theorem neumann_lattice_lower (S : Finset NeumannSpinMode) :
    tfKinetic*(S.card:ℝ)^(5/3:ℝ) -
        neumannRemainderConstant*((S.card:ℝ)^(4/3:ℝ)+(S.card:ℝ)) ≤
      (Real.pi^2/2)*∑ q ∈ S, ∑ i, (q.1 i:ℝ)^2 := by
  classical
  by_cases hS : S.card = 0
  · have : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [Real.zero_rpow (by norm_num : (5/3:ℝ) ≠ 0),
      Real.zero_rpow (by norm_num : (4/3:ℝ) ≠ 0)]
  let M : ℝ := S.card
  let r : ℝ := M^(1/3:ℝ)
  let A : ℝ := tfKinetic*M^(5/3:ℝ)
  let E : ℝ := (Real.pi^2/2)*∑ q ∈ S, ∑ i, (q.1 i:ℝ)^2
  have hM : 0 < M := by
    change 0 < (S.card:ℝ)
    exact_mod_cast Nat.pos_of_ne_zero hS
  have hr : 0 < r := Real.rpow_pos_of_pos hM _
  have hMr : M*r = M^(4/3:ℝ) := by
    dsimp [r]
    calc
      M*M^(1/3:ℝ) = M^(1:ℝ)*M^(1/3:ℝ) := by rw [Real.rpow_one]
      _ = M^(4/3:ℝ) := by rw [←Real.rpow_add hM]; norm_num
  have hAr : A/r = tfKinetic*M^(4/3:ℝ) := by
    dsimp [A,r]
    rw [mul_div_assoc,←Real.rpow_sub hM]
    norm_num
  have hb : A ≤ (1+1/r)*E + (3*Real.pi^2/2)*M*(1+r) := by
    have hh := neumann_lattice_bathtub S
    have hs : (∑ q ∈ S, ∑ i, ((q.1 i:ℝ)+1)^2) ≤
        (1+1/r)*(∑ q ∈ S, ∑ i, (q.1 i:ℝ)^2)+3*M*(1+r) := by
      calc
        _ ≤ ∑ q ∈ S, ∑ i : Fin 3, ((1+1/r)*(q.1 i:ℝ)^2+1+r) := by
          exact Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun i _ => square_shift_bound _ _ hr
        _ = _ := by
          simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_const,
            Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
          dsimp [M]
          ring
    have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ Real.pi^2/2)
    apply hh.trans
    dsimp [E]
    nlinarith
  change A-neumannRemainderConstant*(M^(4/3:ℝ)+M) ≤ E
  by_cases hE : A ≤ E
  · exact (sub_le_self _ (mul_nonneg neumannRemainderConstant_pos.le
      (add_nonneg (Real.rpow_nonneg hM.le _) hM.le))).trans hE
  · have hEA : E ≤ A := (lt_of_not_ge hE).le
    have he : E/r ≤ A/r := div_le_div_of_nonneg_right hEA hr.le
    rw [hAr] at he
    have hc : (3*Real.pi^2/2)*M*(1+r) = (3*Real.pi^2/2)*(M+M^(4/3:ℝ)) := by
      rw [mul_assoc, mul_add, mul_one,hMr]
    rw [hc] at hb
    have hid : (1+1/r)*E = E+E/r := by ring
    rw [hid] at hb
    have ht : 0 ≤ tfKinetic*M := mul_nonneg (by unfold tfKinetic; positivity) hM.le
    unfold neumannRemainderConstant
    nlinarith

theorem neumann_mode_list_lower {N : ℕ} (n : (Fin N × Fin 3) → ℕ) (s : Fin N → Fin 2)
    (h : Function.Injective (fun i => ((fun a : Fin 3 => n (i,a)),s i))) :
    tfKinetic*(N:ℝ)^(5/3:ℝ)-neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ)) ≤
      (1/2:ℝ)*∑ i : Fin N × Fin 3, (Real.pi*(n i:ℝ))^2 := by
  classical
  let e : Fin N ↪ NeumannSpinMode := ⟨_,h⟩
  have hb := neumann_lattice_lower (Finset.univ.map e)
  simp only [Finset.card_map,Finset.card_univ,Fintype.card_fin,Finset.sum_map] at hb
  dsimp only [e] at hb
  refine hb.trans_eq ?_
  rw [Fintype.sum_prod_type]
  simp only [mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  change (Real.pi^2/2)*(n (i,a):ℝ)^2 = (1/2:ℝ)*(Real.pi^2*(n (i,a):ℝ)^2)
  ring

end CoulombAtom

end

end OAI
