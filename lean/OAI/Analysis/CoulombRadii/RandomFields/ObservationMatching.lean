import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.ObservationAtomic

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

lemma observationProductDensity_ne_zero_support {I : Type*} [Fintype I]
    {u : I → ℝ} (hu : observationProductDensity u≠0) (i : I) : |u i|<1 := by
  have hi : observationNoiseDensity (u i)≠0 := fun h => hu (Finset.prod_eq_zero (Finset.mem_univ i) h)
  by_contra h
  apply hi
  rw [observationNoiseDensity_formula,ite_eq_right h,mul_zero]

lemma arrayEventLikelihood_pos_matching {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h≠0)
    (s : Set ((H × (Fin n × Fin 3)) → ℝ)) (x : Configuration n)
    (hp : 0 < arrayEventLikelihood ℓ s x) :
    ∃ u : (H × (Fin n × Fin 3)) → ℝ, (∀ ia, |u ia|<1) ∧
      (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)∈s := by
  by_contra hn
  push Not at hn
  have he : arrayEventLikelihood ℓ s x=0 := by
    rw [arrayEventLikelihood_integral ℓ hℓ,observationNoiseLaw_pi_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    by_cases hu : observationProductDensity u=0
    · simp [hu]
    · simp [Set.indicator_of_notMem (hn u (observationProductDensity_ne_zero_support hu))]
  linarith

def observationArrayPositions {H : Type*} {n : ℕ} (h : H)
    (y : (H × (Fin n × Fin 3)) → ℝ) : Configuration n :=
  fun i => WithLp.toLp 2 (fun a => y (h,i,a))

lemma observationArrayPositions_displacement {H : Type*} {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (x : Configuration n)
    {u : (H × (Fin n × Fin 3)) → ℝ} (hu : ∀ ia, |u ia|<1) (h : H) (i : Fin n) :
    ‖observationArrayPositions h (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia) i-x i‖ ≤
      Real.sqrt 3*ℓ h := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le)).mp
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  calc
    _ = ∑ a : Fin 3, (ℓ h*u (h,i,a))^2 := by
      apply Finset.sum_congr rfl
      intro a _
      change (x i a+ℓ h*u (h,i,a)-x i a)^2=_
      ring
    _ ≤ ∑ _a : Fin 3, (ℓ h)^2 := Finset.sum_le_sum (fun a _ => by
      have H := (sq_le_sq₀ (abs_nonneg (u (h,i,a))) (by norm_num : (0:ℝ)≤1)).2 (hu (h,i,a)).le
      rw [sq_abs,one_pow] at H
      nlinarith [mul_le_mul_of_nonneg_left H (sq_nonneg (ℓ h))])
    _ = _ := by simp

lemma observed_annular_count_le {n : ℕ} (x y : Configuration n)
    {a b A B d : ℝ} (hd : ∀ i, ‖y i-x i‖≤d)
    (hA : A+d<a) (hB : b+d<B) :
    rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} y ≤
      Coulomb.localCount {z : Position | A<‖z‖ ∧ ‖z‖<B} (flattenConfiguration n x) := by
  unfold rawCount Coulomb.localCount
  apply Finset.sum_le_sum
  intro i _
  simp only [position_flattenConfiguration]
  by_cases hi : a≤‖y i‖ ∧ ‖y i‖≤b
  · have hx : A<‖x i‖ ∧ ‖x i‖<B := by
      have h1 := norm_le_norm_add_norm_sub (y i) (x i)
      have h2 := norm_le_norm_add_norm_sub (x i) (y i)
      rw [norm_sub_rev (x i) (y i)] at h2
      constructor <;> linarith [hd i]
    simp [hi,hx]
  · simpa [Set.indicator, hi] using
      (Set.indicator_nonneg (s:={z : Position | A<‖z‖ ∧ ‖z‖<B}) (fun _ _ => (zero_le_one : (0:ℝ)≤1)) (x i))

lemma observed_annular_event_implies_raw_count {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {a b A B T : ℝ} (hA : A+Real.sqrt 3*ℓ h<a) (hB : b+Real.sqrt 3*ℓ h<B)
    (x : Configuration n)
    (hp : 0<arrayEventLikelihood ℓ
      {y | T<rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} x) :
    T<Coulomb.localCount {z : Position | A<‖z‖ ∧ ‖z‖<B} (flattenConfiguration n x) := by
  obtain ⟨u,hu,hs⟩ := arrayEventLikelihood_pos_matching ℓ (fun h => (hℓ h).ne') _ x hp
  exact hs.trans_le (observed_annular_count_le x _
    (fun i => observationArrayPositions_displacement ℓ hℓ x hu h i) hA hB)

lemma measurable_observationArrayPositions {H : Type*} {n : ℕ} (h : H) :
    Measurable (@observationArrayPositions H n h) := by
  unfold observationArrayPositions
  fun_prop

lemma observed_annular_event_measurable {H : Type*} {n : ℕ} (h : H) (a b T : ℝ) :
    MeasurableSet {y : (H × (Fin n × Fin 3)) → ℝ |
      T<rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} := by
  exact measurableSet_lt measurable_const ((measurable_rawCount
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).measurableSet).comp (measurable_observationArrayPositions h))

lemma observed_annular_event_symmetric {H : Type*} {n : ℕ} (h : H) (a b T : ℝ)
    (p : Equiv.Perm (Fin n)) (y : (H × (Fin n × Fin 3)) → ℝ) :
    permuteObservationArray p y∈{y | T<rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} ↔
      y∈{y | T<rawCount {z : Position | a≤‖z‖ ∧ ‖z‖≤b} (observationArrayPositions h y)} := by
  have he : observationArrayPositions h (permuteObservationArray p y)=observationArrayPositions h y ∘ p := rfl
  simp only [Set.mem_ofPred_eq,he,rawCount,Function.comp_apply]
  have hh := Equiv.sum_comp p (fun i => {z : Position | a≤‖z‖ ∧ ‖z‖≤b}.indicator (fun _ => (1:ℝ)) (observationArrayPositions h y i))
  exact congrArg (fun q => T<q) hh |> Iff.of_eq
end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

lemma stateWeightedIntegral_mono_bounded {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F G : Configuration n → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    {C D : ℝ} (hFb : ∀ x, |F x| ≤ C) (hGb : ∀ x, |G x| ≤ D) (hFG : ∀ x, F x ≤ G x) :
    stateWeightedIntegral ψ F ≤ stateWeightedIntegral ψ G := by
  unfold stateWeightedIntegral
  apply Finset.sum_le_sum
  intro σ _
  exact integral_mono (stateWeighted_integrable hd hF hFb σ) (stateWeighted_integrable hd hG hGb σ)
    (fun x => mul_le_mul_of_nonneg_right (hFG x) (sq_nonneg _))

lemma stateWeightedIntegral_const_mul {n : ℕ} (ψ : Wavefunction n)
    (F : Configuration n → ℝ) (c : ℝ) :
    stateWeightedIntegral ψ (fun x => c*F x)=c*stateWeightedIntegral ψ F := by
  unfold stateWeightedIntegral
  simp_rw [mul_assoc,integral_const_mul,Finset.mul_sum]

lemma event_count_square_lower {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) {F : Configuration n → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1)
    {A : Set Position} (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T)
    (hmatch : ∀ x, 0<F x → T ≤ Coulomb.localCount A (flattenConfiguration n x))
    (hp : 0<stateWeightedIntegral ψ F) :
    T^2 ≤ (stateWeightedIntegral ψ F)⁻¹*stateWeightedIntegral ψ
      (fun x => F x*(Coulomb.localCount A (flattenConfiguration n x))^2) := by
  have hcm : Measurable (fun x : Configuration n => Coulomb.localCount A (flattenConfiguration n x)) :=
    (Coulomb.localCount_measurable hA).comp (flattenConfiguration n).continuous.measurable
  have H := stateWeightedIntegral_mono_bounded hd
    (F:=fun x => T^2*F x) (G:=fun x => F x*(Coulomb.localCount A (flattenConfiguration n x))^2)
    (measurable_const.mul hF)
    (hF.mul (hcm.pow_const 2)) (C:=T^2) (D:=(n:ℝ)^2)
    (fun x => by rw [abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (hF0 x)]; exact mul_le_of_le_one_right (sq_nonneg _) (hF1 x))
    (fun x => by
      rw [abs_of_nonneg (mul_nonneg (hF0 x) (sq_nonneg _))]
      exact (mul_le_of_le_one_left (sq_nonneg _) (hF1 x)).trans
        (pow_le_pow_left₀ (Coulomb.localCount_nonneg A _) (Coulomb.localCount_le A _) 2))
    (fun x => by
      by_cases hx : F x=0
      · simp [hx]
      · have H2 := pow_le_pow_left₀ hT (hmatch x (lt_of_le_of_ne (hF0 x) (Ne.symm hx))) 2
        nlinarith [mul_le_mul_of_nonneg_left H2 (hF0 x)])
  rw [stateWeightedIntegral_const_mul] at H
  calc
    T^2=(stateWeightedIntegral ψ F)⁻¹*(T^2*stateWeightedIntegral ψ F) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hp.le)

lemma observationEventOffset_mono_probability {H : Type*} [Fintype H]
    (ℓ : H → ℝ) (D : ℝ) {p q : ℝ} (hp : 0<p) (hpq : p ≤ q) (hq : q ≤ 1) :
    D+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log q)^5  ≤
    D+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p)^5 := by
  have hlog := Real.log_le_log hp hpq
  have hlog0 := Real.log_nonpos ((hp.trans_le hpq).le) hq
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) (by linarith) 5)
    (mul_nonneg observationEventEnergyConstant_pos.le (observationWidthSquareSum_nonneg ℓ)))

theorem atomic_observed_annular_count_tail {α β : ℝ} (hα : 0<α) (hαβ : α<β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {H : Type*} [Fintype H] {n : ℕ}
    (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n},
    FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ : Wavefunction n) (h : Gradient n), FormDomain χ h → normSquared χ=1 → energy Z ψ g ≤ energy Z χ h) →
    ∀ {E D₀ : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D₀ → 0 ≤ D₀ → ∀ (ℓ : H → ℝ), (∀ h,0<ℓ h) →
    ∀ (h : H) {r a b T p₀ : ℝ}, 0<r → 0 ≤ T → 0<p₀ →
    α*r+Real.sqrt 3*ℓ h<a → b+Real.sqrt 3*ℓ h<β*r →
    C*(Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log p₀)^5) r)^2<T^2 →
    stateWeightedIntegral ψ (arrayEventLikelihood ℓ
      {y | T<rawCount {z : Position | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} (observationArrayPositions h y)}) ≤ p₀ := by
  obtain ⟨C,hC,hbound⟩ := atomic_arrayEvent_annular_second_moment hα hαβ
  refine ⟨C,hC,?_⟩
  intro H _ n Z hZ ψ g hd hn hmin E D₀ hE hbase hD ℓ hℓ h r a b T p₀ hr hT hp₀ hA hB hth
  let s : Set ((H × (Fin n × Fin 3)) → ℝ) := {y | T<rawCount {z : Position | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} (observationArrayPositions h y)}
  have hs : MeasurableSet s := observed_annular_event_measurable h a b T
  by_contra hc
  have hp : 0<stateWeightedIntegral ψ (arrayEventLikelihood ℓ s) := hp₀.trans (lt_of_not_ge hc)
  have hp1 := stateWeightedIntegral_le_one hd hn (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
  have hlow := event_count_square_lower hd (arrayEventLikelihood_contDiff ℓ hs).continuous.measurable
    (arrayEventLikelihood_nonneg ℓ hs) (arrayEventLikelihood_le_one ℓ hs)
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).measurableSet hT
    (fun x hx => (observed_annular_event_implies_raw_count ℓ hℓ h hA hB x hx).le) hp
  have hu := hbound Z hZ hd hn hmin hE hbase hD ℓ hℓ hs
    (observed_annular_event_symmetric h a b T) hp hr
  have hδ := observationEventOffset_mono_probability ℓ D₀ hp₀ (le_of_not_ge hc) hp1
  have hmass : Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*
      (1-Real.log (stateWeightedIntegral ψ (arrayEventLikelihood ℓ s)))^5) r  ≤
    Coulomb.screenMass (D₀+observationEventEnergyConstant*observationWidthSquareSum ℓ*(1-Real.log p₀)^5) r := by
    unfold Coulomb.screenMass
    exact add_le_add le_rfl (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hδ hr.le))
  exact (not_lt_of_ge (hlow.trans (hu.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Coulomb.screenMass_pos _ _).le hmass 2) hC)))) hth
end NeutralAtom

end

end OAI
