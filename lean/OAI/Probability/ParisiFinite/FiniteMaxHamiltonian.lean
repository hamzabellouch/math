import Mathlib
import OAI.Probability.ParisiFinite.CostState

namespace OAI

/-! Finite Max Hamiltonian. -/

noncomputable section

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
namespace SKQAOA
open SKGaussian

theorem finiteMax_hamiltonian (n : ℕ) (J : Disorder n) :
    finiteMax (hamiltonian n J) = groundMaximum n J := by
  rw [groundMaximum_eq_finiteMax,field_skCoeff]

theorem log_card_configuration (n : ℕ) :
    Real.log (Fintype.card (Configuration n) : ℝ) = (n : ℝ) * Real.log 2 := by
  simp [Configuration,Real.log_pow]

theorem finite_pressure_bounds {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) (J : Disorder n) :
    β * groundMaximum n J ≤ logPartition (fun σ => β * hamiltonian n J σ) ∧
    logPartition (fun σ => β * hamiltonian n J σ) ≤
      β * groundMaximum n J + (n : ℝ) * Real.log 2 := by
  have hm := finiteMax_const_mul (hamiltonian n J) hβ
  rw [finiteMax_hamiltonian] at hm
  constructor
  · rw [← hm]
    exact finiteMax_le_logPartition _
  · have h := logPartition_le (fun σ => β * hamiltonian n J σ)
    rwa [hm,log_card_configuration] at h

theorem pressure_bounds {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    β * expectedMaximum n ≤ pressure β n ∧
    pressure β n ≤ β * expectedMaximum n + (n : ℝ) * Real.log 2 := by
  have : IsProbabilityMeasure (disorderLaw n) := by unfold disorderLaw; infer_instance
  have h1 := integral_mono ((ground_integrable n).const_mul β) (pressure_integrable β n)
    (fun J => (finite_pressure_bounds hβ n J).1)
  have h2 := integral_mono (pressure_integrable β n)
    (((ground_integrable n).const_mul β).add (integrable_const ((n : ℝ)*Real.log 2)))
    (fun J => (finite_pressure_bounds hβ n J).2)
  simp only [integral_const_mul] at h1
  simp only [Pi.add_apply] at h2
  rw [integral_add ((ground_integrable n).const_mul β) (integrable_const _),
    integral_const_mul,integral_const] at h2
  simpa [pressure,expectedMaximum] using And.intro h1 h2

theorem pressure_linear_bound {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    pressure β n ≤ (n : ℝ) * (β * gaussianAbsoluteMean + Real.log 2) := by
  have h := mul_le_mul_of_nonneg_left (expectedMaximum_le n) hβ
  linarith [(pressure_bounds hβ n).2]

 

theorem tendsto_freeEnergy {β : ℝ} (hβ : 0 < β) :
    Tendsto (freeEnergy β) atTop (𝓝 (limitingFreeEnergy β)) := by
  have hs : Subadditive (fun n => -pressure β n) := by
    intro n m
    linarith [pressure_superadditive β n m]
  have hb : BddBelow (Set.range fun n => -pressure β n / (n : ℝ)) := by
    refine ⟨-(β*gaussianAbsoluteMean+Real.log 2),?_⟩
    rintro _ ⟨n,rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [pressure_zero,neg_zero,Nat.cast_zero,div_zero]
      have hg : 0 ≤ gaussianAbsoluteMean := integral_nonneg fun x => abs_nonneg x
      have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      exact neg_nonpos.mpr (add_nonneg (mul_nonneg hβ.le hg) hl)
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      apply (le_div_iff₀ hn').mpr
      linarith [pressure_linear_bound hβ.le n]
  have ht := ((hs.tendsto_lim hb).neg).div_const β
  have he : (fun n => -(-pressure β n / (n : ℝ)) / β) = freeEnergy β := by
    funext n
    simp [freeEnergy,neg_div]
  rw [he] at ht
  have hp : limitingFreeEnergy β = -hs.lim / β := ht.limUnder_eq
  rw [hp]
  exact ht

theorem freeEnergy_bounds {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 0 < n) :
    expectedGround n ≤ freeEnergy β n ∧
    freeEnergy β n ≤ expectedGround n + Real.log 2 / β := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hlo,hhi⟩ := pressure_bounds hβ.le n
  change expectedMaximum n / (n : ℝ) ≤ pressure β n / (n : ℝ) / β ∧
    pressure β n / (n : ℝ) / β ≤ expectedMaximum n / (n : ℝ) + Real.log 2 / β
  constructor
  · apply (le_div_iff₀ hβ).mpr
    apply (le_div_iff₀ hn').mpr
    convert! hlo using 1
    field_simp [hn'.ne']
  · apply (div_le_iff₀ hβ).mpr
    apply (div_le_iff₀ hn').mpr
    convert! hhi using 1
    field_simp [hn'.ne', hβ.ne']

 

theorem limitingFreeEnergy_bounds {β : ℝ} (hβ : 0 < β) :
    Pstar ≤ limitingFreeEnergy β ∧
    limitingFreeEnergy β ≤ Pstar + Real.log 2 / β := by
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_expectedGround (tendsto_freeEnergy hβ)
      (eventually_gt_atTop 0 |>.mono fun n hn => (freeEnergy_bounds hβ hn).1)
  · exact le_of_tendsto_of_tendsto (tendsto_freeEnergy hβ)
      (tendsto_expectedGround.add_const (Real.log 2 / β))
      (eventually_gt_atTop 0 |>.mono fun n hn => (freeEnergy_bounds hβ hn).2)

end SKQAOA

 

 

open scoped Topology
open Filter

namespace PulseControl

section Banach
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A] [NormOneClass A]

omit [NormedAlgebra ℚ A] [NormOneClass A] in
theorem exp_hasFDerivAt_zero :
    HasFDerivAt (NormedSpace.exp : A → A) (ContinuousLinearMap.id ℝ A) 0 := by
  convert! (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := A)).hasFDerivAt using 1
  ext a
  simp [NormedSpace.expSeries, continuousMultilinearCurryFin1_apply]

omit [NormedAlgebra ℚ A] [NormOneClass A] in
theorem exp_curve_deriv_zero (X : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
  have hs : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X)
  have he : HasFDerivAt (NormedSpace.exp : A → A) (ContinuousLinearMap.id ℝ A) ((0 : ℝ) • X) := by
    simpa using (exp_hasFDerivAt_zero (A := A))
  convert! he.comp_hasDerivAt (0 : ℝ) hs using 1

omit [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A] in
theorem norm_pow_sub_pow_le {U V : A} (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (n : ℕ) :
    ‖U^n - V^n‖ ≤ (n : ℝ)*‖U-V‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ‖V^n‖ ≤ 1 := (norm_pow_le V n).trans (by simpa using pow_le_pow_left₀ (norm_nonneg V) hV n)
    calc
      ‖U^(n+1)-V^(n+1)‖ = ‖(U^n-V^n)*U+V^n*(U-V)‖ := by congr 1; simp only [pow_succ]; noncomm_ring
      _ ≤ ‖(U^n-V^n)*U‖+‖V^n*(U-V)‖ := norm_add_le _ _
      _ ≤ ‖U^n-V^n‖*‖U‖+‖V^n‖*‖U-V‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (n : ℝ)*‖U-V‖+‖U-V‖ := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_left hU (norm_nonneg _)).trans (by simpa using ih)
        · exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _)
      _ = _ := by push_cast; ring

 

theorem tendsto_tangent_powers {f : ℝ → A} {X : A}
    (hf : HasDerivAt f X 0) (hf0 : f 0 = 1)
    (hfn : ∀ t, ‖f t‖ ≤ 1) (he : ∀ t : ℝ, ‖NormedSpace.exp (t • X)‖ ≤ 1) (t : ℝ) :
    Tendsto (fun n : ℕ => (f (t/(n : ℝ)))^n) atTop (𝓝 (NormedSpace.exp (t • X))) := by
  by_cases ht : t = 0
  · subst t
    simp [hf0]
  have hd := hf.sub (exp_curve_deriv_zero X)
  have hh : Tendsto (fun x : ℝ => ‖x‖⁻¹ * ‖f x-NormedSpace.exp (x • X)‖) (𝓝 0) (𝓝 0) := by
    simpa [hf0] using hasDerivAt_iff_tendsto.mp hd
  have hinv : Tendsto (fun n : ℕ => t/(n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := t)).mul tendsto_inv_atTop_nhds_zero_nat
  have herr : Tendsto (fun n : ℕ => (n : ℝ)*‖f (t/(n : ℝ))-NormedSpace.exp ((t/(n : ℝ)) • X)‖)
      atTop (𝓝 0) := by
    have h := (hh.comp hinv).const_mul ‖t‖
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)
    simp only [Function.comp_apply]
    rw [norm_div, Real.norm_of_nonneg (Nat.cast_nonneg n)]
    field_simp [norm_ne_zero_iff.mpr ht]
  have hdist : Tendsto (fun n : ℕ => ‖(f (t/(n : ℝ)))^n-NormedSpace.exp (t • X)‖)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) ?_ herr
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)
    have hx : NormedSpace.exp (t • X) = NormedSpace.exp ((t/(n : ℝ)) • X)^n := by
      rw [← NormedSpace.exp_nsmul]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp
    rw [hx]
    exact norm_pow_sub_pow_le (hfn _) (he _) n
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hdist

omit [NormedAlgebra ℝ A] [NormOneClass A] in
theorem exp_mul_exp_neg (X : A) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← NormedSpace.exp_add_of_commute (Commute.refl X).neg_right, add_neg_cancel, NormedSpace.exp_zero]

omit [NormedAlgebra ℝ A] [NormOneClass A] in
theorem exp_neg_mul_exp (X : A) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  rw [← NormedSpace.exp_add_of_commute (Commute.refl X).neg_left, neg_add_cancel, NormedSpace.exp_zero]

variable [StarRing A] [CStarRing A] [StarModule ℝ A] [Nontrivial A]

omit [NormOneClass A] in
theorem norm_exp_smul_le {X : A} (hX : X ∈ skewAdjoint A) (t : ℝ) :
    ‖NormedSpace.exp (t • X)‖ ≤ 1 := by
  exact (CStarRing.norm_of_mem_unitary (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.smul_mem t hX))).le

theorem tangent_mem_closed_submonoid (S : Submonoid A) (hS : IsClosed (S : Set A))
    (hU : ∀ x ∈ S, x ∈ unitary A) {f : ℝ → A} {X : A}
    (hf : HasDerivAt f X 0) (hf0 : f 0 = 1) (hm : ∀ t, f t ∈ S)
    (hX : X ∈ skewAdjoint A) (t : ℝ) : NormedSpace.exp (t • X) ∈ S := by
  apply hS.mem_of_tendsto (tendsto_tangent_powers hf hf0
    (fun t => (CStarRing.norm_of_mem_unitary (hU _ (hm t))).le) (norm_exp_smul_le hX) t)
  exact Eventually.of_forall (fun n => S.pow_mem (hm _) n)

 
def tangents (S : Submonoid A) (hS : IsClosed (S : Set A))
    (hU : ∀ x ∈ S, x ∈ unitary A) : Submodule ℝ A where
  carrier := {X | X ∈ skewAdjoint A ∧ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ S}
  zero_mem' := by simp [NormedSpace.exp_zero, S.one_mem]
  add_mem' := by
    intro X Y hX hY
    refine ⟨(skewAdjoint A).add_mem hX.1 hY.1, fun t => ?_⟩
    have hd : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X)*NormedSpace.exp (s • Y)) (X+Y) 0 := by
      convert! (exp_curve_deriv_zero X).mul (exp_curve_deriv_zero Y) using 1; simp
    exact tangent_mem_closed_submonoid S hS hU hd (by simp) (fun s => S.mul_mem (hX.2 s) (hY.2 s))
      ((skewAdjoint A).add_mem hX.1 hY.1) t
  smul_mem' := by
    intro r X hX
    refine ⟨skewAdjoint.smul_mem r hX.1,fun t => ?_⟩
    simpa [smul_smul] using hX.2 (t*r)

theorem mem_tangents {S : Submonoid A} {hS hU} {X : A} :
    X ∈ tangents S hS hU ↔ X ∈ skewAdjoint A ∧ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ S := Iff.rfl

theorem isClosed_tangents (S : Submonoid A) (hS : IsClosed (S : Set A))
    (hU : ∀ x ∈ S, x ∈ unitary A) : IsClosed (tangents S hS hU : Set A) := by
  change IsClosed ({X : A | star X = -X} ∩ {X : A | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ S})
  apply IsClosed.inter (isClosed_eq continuous_star continuous_neg)
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun t => hS.preimage (NormedSpace.exp_continuous.comp (continuous_const_smul t)))

omit [NormedAlgebra ℚ A] [NormOneClass A] [StarRing A] [CStarRing A] [StarModule ℝ A] [Nontrivial A] in
theorem conjugation_deriv_zero (X Y : A) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)*Y*NormedSpace.exp (-t • X)) (X*Y-Y*X) 0 := by
  have hn : HasDerivAt (fun t : ℝ => NormedSpace.exp (-t • X)) (-X) 0 := by
    convert! exp_curve_deriv_zero (-X) using 1; simp
  convert! ((exp_curve_deriv_zero X).mul_const Y).mul hn using 1; simp [sub_eq_add_neg]

omit [NormedAlgebra ℚ A] [NormOneClass A] [Nontrivial A] [CompleteSpace A] in
 
theorem star_exp_smul {X : A} (hX : X ∈ skewAdjoint A) (t : ℝ) :
    star (NormedSpace.exp (t • X)) = NormedSpace.exp (-t • X) := by
  rw [NormedSpace.star_exp, star_smul, star_trivial, skewAdjoint.mem_iff.mp hX, smul_neg, neg_smul]

theorem commutator_loop_tangent_mem (S : Submonoid A) (hS : IsClosed (S : Set A))
    (hU : ∀ x ∈ S, x ∈ unitary A) {X Y : A}
    (hX : X ∈ skewAdjoint A) (hY : Y ∈ skewAdjoint A)
    (hloop : ∀ u v : ℝ,
      NormedSpace.exp (u • X)*NormedSpace.exp (v • Y)*
        NormedSpace.exp (-u • X)*NormedSpace.exp (-v • Y) ∈ S) :
    X*Y-Y*X ∈ tangents S hS hU := by
  have hD (u : ℝ) :
      NormedSpace.exp (u • X)*Y*NormedSpace.exp (-u • X)-Y ∈ tangents S hS hU := by
    let U := NormedSpace.exp (u • X)
    let V := NormedSpace.exp (-u • X)
    have hUV : U*V=1 := by simpa [U,V,neg_smul] using exp_mul_exp_neg (u • X)
    have hUs : star U=V := star_exp_smul hX u
    have hVs : star V=U := by simpa [U,V] using star_exp_smul hX (-u)
    have hsk : U*Y*V-Y ∈ skewAdjoint A := by
      rw [skewAdjoint.mem_iff]
      simp only [star_sub, star_mul, hUs, hVs, skewAdjoint.mem_iff.mp hY]
      noncomm_ring
    refine ⟨hsk,fun t => ?_⟩
    have hn : HasDerivAt (fun v : ℝ => NormedSpace.exp (-v • Y)) (-Y) 0 := by
      convert! exp_curve_deriv_zero (-Y) using 1; simp
    have hd : HasDerivAt (fun v : ℝ => U*NormedSpace.exp (v • Y)*V*NormedSpace.exp (-v • Y))
        (U*Y*V-Y) 0 := by
      convert! (((exp_curve_deriv_zero Y).const_mul U).mul_const V).mul hn using 1
      simp [hUV,sub_eq_add_neg]
    exact tangent_mem_closed_submonoid S hS hU hd (by simp [hUV]) (hloop u) hsk t
  apply (isClosed_tangents S hS hU).mem_of_tendsto (conjugation_deriv_zero X Y).tendsto_slope
  apply Eventually.of_forall
  intro u
  simpa [slope, vsub_eq_sub] using (tangents S hS hU).smul_mem u⁻¹ (hD u)

theorem normalized_bracket_mem (S : Submonoid A) (hS : IsClosed (S : Set A))
    (hU : ∀ x ∈ S, x ∈ unitary A) {X Y : A}
    (hX : X ∈ skewAdjoint A) (hY : Y ∈ tangents S hS hU)
    (hN : ∀ u : ℝ, ∀ V ∈ S,
      NormedSpace.exp (u • X)*V*NormedSpace.exp (-u • X) ∈ S) :
    X*Y-Y*X ∈ tangents S hS hU := by
  apply commutator_loop_tangent_mem S hS hU hX hY.1
  intro u v
  exact S.mul_mem (hN u _ (hY.2 v)) (hY.2 (-v))

end Banach

section Words
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A] [DecidableEq κ]

def pulseValue (G : κ → A) (w : List (κ × ℝ)) : A :=
  (w.map (fun p => NormedSpace.exp (p.2 • G p.1))).prod

def pulseClock (w : List (κ × ℝ)) : κ → ℝ :=
  (w.map (fun p => Pi.single p.1 p.2)).sum

omit [DecidableEq κ] in
@[simp] theorem pulseValue_nil (G : κ → A) : pulseValue G [] = 1 := rfl

omit [DecidableEq κ] in
@[simp] theorem pulseValue_append (G : κ → A) (w v : List (κ × ℝ)) :
    pulseValue G (w++v) = pulseValue G w * pulseValue G v := by
  simp [pulseValue]

@[simp] theorem pulseClock_nil : pulseClock ([] : List (κ × ℝ)) = 0 := rfl

@[simp] theorem pulseClock_append (w v : List (κ × ℝ)) :
    pulseClock (w++v) = pulseClock w + pulseClock v := by
  simp [pulseClock]

 
def zeroClockWords (G : κ → A) : Submonoid A where
  carrier := {U | ∃ w : List (κ × ℝ), pulseClock w = 0 ∧ pulseValue G w = U}
  one_mem' := ⟨[],rfl,rfl⟩
  mul_mem' := by
    rintro U V ⟨w,hw,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨w++v,by simp [hw,hv],by simp⟩

theorem commutator_loop_mem (G : κ → A) (a b : κ) (u v : ℝ) :
    NormedSpace.exp (u • G a)*NormedSpace.exp (v • G b)*
      NormedSpace.exp (-u • G a)*NormedSpace.exp (-v • G b) ∈ zeroClockWords G := by
  refine ⟨[(a,u),(b,v),(a,-u),(b,-v)],?_,?_⟩
  · ext i
    simp only [pulseClock, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Pi.add_apply, Pi.zero_apply, Pi.single_apply]
    split_ifs <;> ring
  · simp [pulseValue, mul_assoc]

theorem conjugate_word_mem (G : κ → A) (a : κ) (u : ℝ) {U : A}
    (hU : U ∈ zeroClockWords G) :
    NormedSpace.exp (u • G a)*U*NormedSpace.exp (-u • G a) ∈ zeroClockWords G := by
  obtain ⟨w,hw,rfl⟩ := hU
  refine ⟨[(a,u)]++w++[(a,-u)],?_,?_⟩
  · rw [pulseClock_append, pulseClock_append, hw]
    ext i
    simp [pulseClock, Pi.single_apply]
    split_ifs <;> ring
  · simp [pulseValue, mul_assoc]

theorem conjugate_closure_mem (G : κ → A) (a : κ) (u : ℝ) {U : A}
    (hU : U ∈ (zeroClockWords G).topologicalClosure) :
    NormedSpace.exp (u • G a)*U*NormedSpace.exp (-u • G a) ∈
      (zeroClockWords G).topologicalClosure := by
  have hc : Continuous (fun V : A =>
      NormedSpace.exp (u • G a)*V*NormedSpace.exp (-u • G a)) := by fun_prop
  change U ∈ (fun V : A => NormedSpace.exp (u • G a)*V*NormedSpace.exp (-u • G a)) ⁻¹'
    ((zeroClockWords G).topologicalClosure : Set A)
  apply closure_minimal (s := (zeroClockWords G : Set A))
    (t := (fun V : A => NormedSpace.exp (u • G a)*V*NormedSpace.exp (-u • G a)) ⁻¹'
      ((zeroClockWords G).topologicalClosure : Set A)) ?_
    ((zeroClockWords G).isClosed_topologicalClosure.preimage hc) hU
  intro V hV
  exact (zeroClockWords G).le_topologicalClosure (conjugate_word_mem G a u hV)

variable [NormedAlgebra ℚ A] [CompleteSpace A] [StarRing A] [CStarRing A] [StarModule ℝ A]

theorem zeroClockWords_le_unitary (G : κ → A) (hG : ∀ a, G a ∈ skewAdjoint A) :
    zeroClockWords G ≤ unitary A := by
  rintro U ⟨w,hw,rfl⟩
  apply (unitary A).list_prod_mem
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem p.2 (hG p.1))

theorem closure_le_unitary (G : κ → A) (hG : ∀ a, G a ∈ skewAdjoint A) :
    (zeroClockWords G).topologicalClosure ≤ unitary A :=
  (zeroClockWords G).topologicalClosure_minimal (zeroClockWords_le_unitary G hG) isClosed_unitary

variable [NormOneClass A] [Nontrivial A]

def zeroClockTangents (G : κ → A) (hG : ∀ a, G a ∈ skewAdjoint A) : Submodule ℝ A :=
  tangents _ (zeroClockWords G).isClosed_topologicalClosure (closure_le_unitary G hG)

theorem bracket_mem_zeroClockTangents (G : κ → A) (hG : ∀ a, G a ∈ skewAdjoint A) (a b : κ) :
    G a * G b - G b * G a ∈ zeroClockTangents G hG := by
  apply commutator_loop_tangent_mem _ _ _ (hG a) (hG b)
  intro u v
  exact (zeroClockWords G).le_topologicalClosure (commutator_loop_mem G a b u v)

theorem bracket_closed_zeroClockTangents (G : κ → A) (hG : ∀ a, G a ∈ skewAdjoint A)
    (a : κ) {Y : A} (hY : Y ∈ zeroClockTangents G hG) :
    G a * Y - Y * G a ∈ zeroClockTangents G hG := by
  apply normalized_bracket_mem _ _ _ (hG a) hY
  intro u U hU
  exact conjugate_closure_mem G a u hU

 

theorem approximate_zeroClock (G : κ → A) (hG : ∀ a, G a ∈ skewAdjoint A)
    {X : A} (hX : X ∈ zeroClockTangents G hG) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : List (κ × ℝ), pulseClock w = 0 ∧
      ‖pulseValue G w - NormedSpace.exp (t • X)‖ < ε := by
  obtain ⟨U,hU,hd⟩ := Metric.mem_closure_iff.mp (hX.2 t) ε hε
  obtain ⟨w,hw,rfl⟩ := hU
  exact ⟨w,hw,by simpa only [dist_eq_norm, norm_sub_rev] using hd⟩

end Words
end PulseControl

namespace ExactPulseControl
open PulseControl

section Tangents
variable {A κ : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [DecidableEq κ]

omit [NormedAlgebra ℚ A] in
theorem contDiff_exp_curve (X : A) : ContDiff ℝ 1 (fun t : ℝ => NormedSpace.exp (t • X)) := by
  have h : ContDiff ℝ 1 (NormedSpace.exp : A → A) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : A → A) Set.univ from
      fun a _ => NormedSpace.exp_analytic a).contDiff
  exact h.comp (contDiff_id.smul contDiff_const)

 

def actualTangents (G : κ → A) : Submodule ℝ A where
  carrier := {X | ∃ f : ℝ → A, ContDiff ℝ 1 f ∧ f 0 = 1 ∧
    HasDerivAt f X 0 ∧ ∀ t, f t ∈ zeroClockWords G}
  zero_mem' := ⟨fun _ => 1,contDiff_const,rfl,hasDerivAt_const _ _,fun _ => (zeroClockWords G).one_mem⟩
  add_mem' := by
    rintro X Y ⟨f,hf,hf0,hdf,hmf⟩ ⟨g,hg,hg0,hdg,hmg⟩
    refine ⟨fun t => f t*g t,hf.mul hg,by simp [hf0,hg0],?_,fun t => (zeroClockWords G).mul_mem (hmf t) (hmg t)⟩
    convert! hdf.mul hdg using 1; simp [hf0,hg0]
  smul_mem' := by
    rintro r X ⟨f,hf,hf0,hdf,hmf⟩
    refine ⟨fun t => f (r*t),hf.comp (contDiff_const.mul contDiff_id),by simpa using hf0,?_,fun t => hmf _⟩
    convert! hdf.scomp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul r) (by simp) using 1; simp

variable [FiniteDimensional ℝ A]

omit [NormedAlgebra ℚ A] [CompleteSpace A] in
theorem actualTangents_closed (G : κ → A) : IsClosed (actualTangents G : Set A) :=
  (actualTangents G).closed_of_finiteDimensional

theorem bracket_actualTangents (G : κ → A) (a b : κ) :
    G a*G b-G b*G a ∈ actualTangents G := by
  have hD (u : ℝ) : NormedSpace.exp (u • G a)*G b*NormedSpace.exp (-u • G a)-G b ∈ actualTangents G := by
    let U := NormedSpace.exp (u • G a)
    let V := NormedSpace.exp (-u • G a)
    have hUV : U*V=1 := by simpa [U,V,neg_smul] using exp_mul_exp_neg (u • G a)
    have hn : HasDerivAt (fun v : ℝ => NormedSpace.exp (-v • G b)) (-G b) 0 := by
      convert! exp_curve_deriv_zero (-G b) using 1; simp
    refine ⟨fun v => U*NormedSpace.exp (v • G b)*V*NormedSpace.exp (-v • G b),?_,by simp [hUV],?_,
      fun v => commutator_loop_mem G a b u v⟩
    · apply ContDiff.mul
      · exact (contDiff_const.mul (contDiff_exp_curve (G b))).mul contDiff_const
      · convert contDiff_exp_curve (-G b) using 1; funext v; simp
    · convert! (((exp_curve_deriv_zero (G b)).const_mul U).mul_const V).mul hn using 1
      simp [hUV,sub_eq_add_neg]
      simp [U,V,neg_smul]
  apply (actualTangents_closed G).mem_of_tendsto (conjugation_deriv_zero (G a) (G b)).tendsto_slope
  apply Eventually.of_forall
  intro u
  simpa [slope,vsub_eq_sub] using (actualTangents G).smul_mem u⁻¹ (hD u)

theorem bracket_closed_actualTangents (G : κ → A) (a : κ) {Y : A} (hY : Y ∈ actualTangents G) :
    G a*Y-Y*G a ∈ actualTangents G := by
  obtain ⟨f,hf,hf0,hdf,hmf⟩ := hY
  have hD (u : ℝ) : NormedSpace.exp (u • G a)*Y*NormedSpace.exp (-u • G a)-Y ∈ actualTangents G := by
    let U := NormedSpace.exp (u • G a)
    let V := NormedSpace.exp (-u • G a)
    have hUV : U*V=1 := by simpa [U,V,neg_smul] using exp_mul_exp_neg (u • G a)
    have hn : HasDerivAt (fun v : ℝ => f (-v)) (-Y) 0 := by
      convert! hdf.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp) using 1; simp
    refine ⟨fun v => U*f v*V*f (-v),
      ((contDiff_const.mul hf).mul contDiff_const).mul (hf.comp contDiff_neg),?_,?_,?_⟩
    · simp [hf0,hUV]
    · convert! ((hdf.const_mul U).mul_const V).mul hn using 1
      simp [hf0,hUV,sub_eq_add_neg]
      simp [U,V,neg_smul]
    · intro v
      exact (zeroClockWords G).mul_mem (conjugate_word_mem G a u (hmf v)) (hmf (-v))
  apply (actualTangents_closed G).mem_of_tendsto (conjugation_deriv_zero (G a) Y).tendsto_slope
  apply Eventually.of_forall
  intro u
  simpa [slope,vsub_eq_sub] using (actualTangents G).smul_mem u⁻¹ (hD u)

end Tangents
end ExactPulseControl

namespace ExactPulseControl
open PulseControl

section Submersion
variable {A E κ ι : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasStrictFDerivAt_list_prod_one (l : List ι) (f : ι → E → A)
    (D : ι → E →L[ℝ] A) (x : E) (h0 : ∀ i ∈ l, f i x=1)
    (hd : ∀ i ∈ l, HasStrictFDerivAt (f i) (D i) x) :
    HasStrictFDerivAt (fun t => (l.map (fun i => f i t)).prod) (l.map D).sum x := by
  induction l with
  | nil => simpa using hasStrictFDerivAt_const (𝕜 := ℝ) (1 : A) x
  | cons i l ih =>
    have ht := (hd i (by simp)).mul' (ih (fun j hj => h0 j (by simp [hj])) (fun j hj => hd j (by simp [hj])))
    have hp : (l.map (fun i => f i x)).prod=1 := by
      rw [List.prod_eq_one]; intro y hy
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
      exact h0 j (by simp [hj])
    convert! ht using 1; simp [h0 i (by simp),hp,add_comm]

variable [CompleteSpace A] [DecidableEq κ] [CompleteSpace E]

omit [CompleteSpace A] in
 

theorem projected_reachable_nhds {m : ℕ} (G : κ → A) (X : Fin m → A)
    (hX : ∀ i, X i ∈ actualTangents G) (π : A →L[ℝ] E)
    (hD : (π.comp (∑ i, ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)).smulRight (X i))).range=⊤)
    (P : Set A) (hP : P ∈ 𝓝 (1 : A)) :
    {y : E | ∃ x ∈ zeroClockWords G, x ∈ P ∧ π x=y} ∈ 𝓝 (π 1) := by
  choose f hf hf0 hdf hmf using hX
  let D (i : Fin m) : (Fin m → ℝ) →L[ℝ] A := (ContinuousLinearMap.proj i).smulRight (X i)
  let F : (Fin m → ℝ) → A := fun t => (List.ofFn (fun i => f i (t i))).prod
  have hF0 : F 0 = 1 := by simp [F,hf0]
  have hFd : HasStrictFDerivAt F (∑ i, D i) 0 := by
    have hd (i : Fin m) : HasStrictFDerivAt (fun t : Fin m → ℝ => f i (t i)) (D i) 0 := by
      have hfi := ((hf i).contDiffAt.hasStrictDerivAt' (hdf i) (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).hasStrictFDerivAt
      convert! hfi.comp (0 : Fin m → ℝ) ((ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).hasStrictFDerivAt) using 1
    have hh := hasStrictFDerivAt_list_prod_one (List.finRange m) (fun i (t : Fin m → ℝ) => f i (t i)) D 0
      (by intro i _; exact hf0 i) (by intro i _; exact hd i)
    convert! hh using 1
    · simp [F,List.ofFn_eq_map]
  have hFm (t : Fin m → ℝ) : F t ∈ zeroClockWords G := by
    apply (zeroClockWords G).list_prod_mem
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hmf i (t i)
  have hh := ((π.hasStrictFDerivAt).comp 0 hFd).map_nhds_eq_of_surj hD
  rw [hF0] at hh
  rw [← hh, Filter.mem_map']
  filter_upwards [hFd.continuousAt (by simpa [hF0] using hP)] with t ht
  exact ⟨F t,hFm t,ht,rfl⟩

end Submersion
end ExactPulseControl

namespace ExactPulseControl
open PulseControl
variable {A E κ : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace A] [DecidableEq κ]

omit [CompleteSpace A] in
theorem surjective_tangents_reachable_nhds (G : κ → A) (π : A →L[ℝ] E)
    (hπ : ∀ y, ∃ X ∈ actualTangents G, π X=y)
    (P : Set A) (hP : P ∈ 𝓝 (1 : A)) :
    {y : E | ∃ x ∈ zeroClockWords G, x ∈ P ∧ π x=y} ∈ 𝓝 (π 1) := by
  let b := Module.finBasis ℝ E
  choose X hX hXπ using fun i => hπ (b i)
  apply projected_reachable_nhds G X hX π ?_ P hP
  rw [LinearMap.range_eq_top]
  intro y
  refine ⟨b.repr y,?_⟩
  change π ((∑ i, ((ContinuousLinearMap.proj i : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ)).smulRight (X i)) (b.repr y))=y
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,map_sum,map_smul,hXπ]
  exact b.sum_repr y
end ExactPulseControl

end

end OAI
