import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.WeightedInner
import OAI.Analysis.CoulombRadii.Localization.DeletionEnvelope

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb
namespace RecordedEnsemble

theorem Conserves.weightedInner_expectation_le {J n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ} (hwm : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (hcore : T.CoreSupported (imsShell 0 u)ᶜ) {A : Set Space} (hA : MeasurableSet A)
    (hout : T.OutSupported A) (M : T.InnerEnvelope S h u) :
    potentialForm (weightedInnerField S h w) ψ ≤
      Real.sqrt (localCountSecondMoment ψ A)*T.dataRMS M.value := by
  have hW := weightedInnerField_measurable (n:=n) S h hwm
  have hwabs y : |w y| ≤ 1 := by rw [abs_of_nonneg (hw0 y)]; exact hw1 y
  have hWB := weightedInnerField_abs_le (n:=n) S hatom hu hh hwabs hws
  have HT := hT (weightedInnerField S h w) hW ⟨_,hWB⟩
  simp only [Function.comp_def,weightedInnerField_reindex] at HT
  have Hlocal p : potentialForm (weightedInnerField S h w) (T.vector p) ≤
      (T.out p:ℝ)*sliceExpectation (T.vector p) (M.value p) := by
    have hWBp := weightedInnerField_abs_le (n:=T.out p+T.core p) S hatom hu hh hwabs hws
    have hWp := weightedInnerField_measurable (n:=T.out p+T.core p) S h hwm
    rw [←sliceExpectation_coreConditionalObservable (T.vector p) _ hWp hWBp]
    unfold sliceExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_const_mul]
    apply integral_mono_ae (coreConditionalObservable_weight_integrable (T.vector p) _ hWp
      (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg (totalCharge_nonneg S) hu.le) (by positivity))) hWBp s)
      ((M.integrable p s).const_mul (T.out p:ℝ))
    filter_upwards [(hcore p).coreSlice s] with x hx
    by_cases hm : mass ((T.vector p).coreSlice s x)=0
    · simp only [hm,zero_mul,mul_zero,le_refl]
    · have H := conditional_weighted_inner_le S hatom (T.vector p) hu hh hwm hw0 hw1 hws s x
        (lt_of_le_of_ne (mass_nonneg _) (Ne.symm hm)) hx.normalized (M.nonneg p s x) (M.dominates p s x)
      have HH := mul_le_mul_of_nonneg_left H (mass_nonneg ((T.vector p).coreSlice s x))
      nlinarith
  have HB := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => Hlocal p)
  rw [HT] at HB
  apply HB.trans
  let R : ℝ := ∑ p, (T.out p:ℝ)*sliceExpectation (T.vector p) (M.value p)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun s _ => integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (M.nonneg p s x)))))
  have HC := slice_ensemble_count_cauchy T.out T.core T.vector M.value M.integrable M.square_integrable
  have ho := out_square_le hT hA hout
  have hsecond : 0 ≤ ∑ p, sliceExpectation (T.vector p) (fun s x => (M.value p s x)^2) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg
      (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have HH := HC.trans (mul_le_mul_of_nonneg_right ho hsecond)
  change R^2 ≤ localCountSecondMoment ψ A*_ at HH
  have hN : 0 ≤ localCountSecondMoment ψ A := localCountSecondMoment_nonneg ψ A
  apply (sq_le_sq₀ hR (mul_nonneg (Real.sqrt_nonneg _) (T.dataRMS_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hN,T.dataRMS_sq]
  exact HH

end RecordedEnsemble

theorem atomic_weighted_shell_deletion : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j, S.position j=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E →
    ∀ {t : ℝ}, 0<t → ∀ ell : ℕ, ∀ w : Space → ℝ, Measurable w →
      (∀ y, 0 ≤ w y) → (∀ y, w y ≤ 1) →
      (∀ y∉imsShell 0 ((2:ℝ)^ell*t), w y=0) →
      potentialForm (weightedInnerField S (t/4) w) ψ ≤
        C*(screenMass 0 (t/4))^2*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
  obtain ⟨Cm,hCm,Hm⟩ := exists_atomic_deletion_envelope
  obtain ⟨Cc,hCc,Hc⟩ := atomic_annular_second_moment (α:=1/2) (β:=4) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt Cc*Cm,mul_nonneg (Real.sqrt_nonneg _) hCm,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht ell w hwm hw0 hw1 hws
  have hu : 0 < (2:ℝ)^ell*t := by positivity
  obtain ⟨T,hT,hf,ho,hcs,hos,hmas,he,M,hM⟩ := Hm S hatom ψ hψ hm hE hstate ht ell
  let A := {x : Space | ((2:ℝ)^ell*t)/2<‖x‖ ∧ ‖x‖<4*((2:ℝ)^ell*t)}
  have hA : MeasurableSet A := ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hpow : (1:ℝ) ≤ 2^ell := one_le_pow₀ (by norm_num)
  have htu : t/4 ≤ (2:ℝ)^ell*t := by nlinarith
  have H := hT.weightedInner_expectation_le S hatom hu (show t/4 ≤ ((2:ℝ)^ell*t)/2 by nlinarith)
    hwm hw0 hw1 hws hcs hA hos M
  have Hc1 : localCountSecondMoment ψ A ≤ Cc*(screenMass 0 ((2:ℝ)^ell*t))^2 := by
    simpa only [A,div_eq_mul_inv,one_mul,mul_comm (2:ℝ)⁻¹] using
      Hc S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) hu
  have Hc2 : Real.sqrt (localCountSecondMoment ψ A) ≤ Real.sqrt Cc*screenMass 0 (t/4) := by
    calc
      _ ≤ Real.sqrt (Cc*(screenMass 0 ((2:ℝ)^ell*t))^2) := Real.sqrt_le_sqrt Hc1
      _ = Real.sqrt Cc*screenMass 0 ((2:ℝ)^ell*t) := by
        rw [Real.sqrt_mul hCc,Real.sqrt_sq (screenMass_pos _ _).le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (screenMass_zero_mono (by positivity) htu) (Real.sqrt_nonneg _)
  apply H.trans
  have HH := mul_le_mul Hc2 hM (T.dataRMS_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le)
  exact HH.trans_eq (by ring)

end Coulomb
end

end

end OAI
