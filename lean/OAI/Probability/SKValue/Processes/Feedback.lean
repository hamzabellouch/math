import Mathlib
import OAI.Probability.SKValue.Gaussian.CoupledCoordinates
import OAI.Probability.SKValue.Equations.ValueStrip
import OAI.Probability.SKValue.Equations.CubicEnvelopeMean
import OAI.Probability.SKValue.Control.Controls

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

noncomputable def meshControl {Ω : Type*} (T : ℝ) (N : ℕ) (H : Fin N → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ j : Fin N, if meshTime T N j < t ∧ (t : ℝ)  ≤  meshTime T N (j+1) then H j ω else 0

lemma progressive_interval {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {a b : ℝ} {H : Ω → ℝ} (_ : 0 ≤ a)
    (hH : Measurable[f (Real.toNNReal a)] H) :
    IsProgressive f (fun t ω ↦ if a < (t : ℝ) ∧ (t : ℝ)  ≤  b then H ω else 0) := by
  intro t
  by_cases hat : Real.toNNReal a  ≤  t
  · let : MeasurableSpace Ω := f t
    have hHm : Measurable H := hH.mono (f.mono hat) le_rfl
    exact (hHm.comp measurable_snd).ite
      ((measurableSet_lt measurable_const (measurable_coe_nnreal_real.comp
        (measurable_subtype_coe.comp measurable_fst))).inter
        (measurableSet_le (measurable_coe_nnreal_real.comp
          (measurable_subtype_coe.comp measurable_fst)) measurable_const)) measurable_const
  · have he : (fun p : Iic t × Ω ↦ if a < (p.1 : ℝ≥0) ∧ ((p.1 : ℝ≥0) : ℝ)  ≤  b then H p.2 else 0) =
        fun _ ↦ (0 : ℝ) := by
      funext p
      apply ite_eq_right
      intro hp
      exact hat ((Real.toNNReal_le_iff_le_coe).2 (hp.1.le.trans (by exact_mod_cast p.1.2)))
    rw [he]
    exact measurable_const

lemma meshControl_progressive {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} {H : Fin N → Ω → ℝ}
    (hH : ∀ j : Fin N, Measurable[f (Real.toNNReal (meshTime T N j))] (H j)) :
    IsProgressive f (meshControl T N H) := by
  apply IsProgressive.finsetSum
  intro j _
  exact progressive_interval (mesh_time_mem_total hT j.isLt.le).1 (hH j)

lemma mesh_intervals_disjoint {T : ℝ} (hT : 0 ≤ T) {N : ℕ} {i j : Fin N} {t : ℝ}
    (hi : meshTime T N i < t ∧ t  ≤  meshTime T N (i+1))
    (hj : meshTime T N j < t ∧ t  ≤  meshTime T N (j+1)) : i=j := by
  have hδ : 0  ≤  stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have hlt : ∀ a b : ℕ, a+1 ≤ b → meshTime T N (a+1) ≤ meshTime T N b := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hδ
  apply Fin.ext
  by_contra he
  rcases lt_or_gt_of_ne he with hij | hji
  · have hh := hlt i j hij
    linarith [hi.2,hj.1]
  · have hh := hlt j i hji
    linarith [hi.1,hj.2]

lemma meshControl_eq {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (H : Fin N → Ω → ℝ)
    {j : Fin N} {t : ℝ≥0} (ht : meshTime T N j < t ∧ (t : ℝ)  ≤  meshTime T N (j+1)) (ω : Ω) :
    meshControl T N H t ω=H j ω := by
  unfold meshControl
  rw [Finset.sum_eq_single j]
  · simp only [ite_eq_left ht]
  · intro i _ hij
    exact ite_eq_right (fun hi ↦ hij (mesh_intervals_disjoint hT hi ht))
  · simp

lemma meshControl_bound {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (H : Fin N → Ω → ℝ)
    (hH : ∀ j ω, |H j ω| ≤ 1) (t : ℝ≥0) (ω : Ω) : |meshControl T N H t ω| ≤ 1 := by
  by_cases he : ∃ j : Fin N, meshTime T N j < t ∧ (t : ℝ)  ≤  meshTime T N (j+1)
  · obtain ⟨j,hj⟩ := he
    rw [meshControl_eq hT H hj]
    exact hH j ω
  · have hh : meshControl T N H t ω=0 := by
      unfold meshControl
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (fun hj ↦ he ⟨j,hj⟩)
    rw [hh]
    norm_num

lemma meshControl_momentIntegral {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 0<N)
    (H : Fin N → Ω → ℝ) {γ : ℝ → ℝ} (hγ : IntervalIntegrable γ volume 0 T)
    (k : ℕ) (ω : Ω) :
    controlAccum γ (meshControl T N H) k T ω =
      ∑ j : Fin N, (∫ s in meshTime T N j..meshTime T N (j+1), γ s)*(H j ω)^k := by
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have htime (j : ℕ) (hj : j ≤ N) := mesh_time_mem_total hT hj
  have horder (j : ℕ) : meshTime T N j ≤ meshTime T N (j+1) := by
    dsimp [meshTime]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hδ
  have hlast : meshTime T N N=T := by
    dsimp [meshTime,stepSize]
    field_simp
  have he (j : Fin N) :
      (fun s ↦ γ s*(meshControl T N H (Real.toNNReal s) ω)^k) =ᵐ[
        volume.restrict (uIoc (meshTime T N j) (meshTime T N (j+1)))]
      (fun s ↦ γ s*(H j ω)^k) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (horder j)] at hs
    have hs0 : 0 ≤ s := (htime j j.isLt.le).1.trans hs.1.le
    rw [meshControl_eq hT H (by simpa only [Real.coe_toNNReal _ hs0,Set.mem_Ioc] using hs)]
  have hi (j : ℕ) (hj : j<N) : IntervalIntegrable
      (fun s ↦ γ s*(meshControl T N H (Real.toNNReal s) ω)^k) volume
      (meshTime T N j) (meshTime T N (j+1)) := by
    apply ((intervalIntegrable_substrip hT hγ (htime j hj.le)
      (htime (j+1) hj)).mul_const ((H ⟨j,hj⟩ ω)^k)).congr_ae
    exact (he ⟨j,hj⟩).symm
  have hs := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [hlast,show meshTime T N 0=0 by simp [meshTime]] at hs
  rw [controlAccum,←hs,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_congr_ae_restrict (he j),intervalIntegral.integral_mul_const]

lemma monotone_interval_quadrature {γ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : MonotoneOn γ (Icc a b)) :
    |(∫ s in a..b, γ s)-(b-a)*γ a| ≤ (b-a)*(γ b-γ a) := by
  have hi : IntervalIntegrable γ volume a b := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hγ
  have hdiff : (∫ s in a..b, γ s)-(b-a)*γ a =∫ s in a..b, γ s-γ a := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,smul_eq_mul]
  rw [hdiff]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun s ↦ γ s-γ a) (C := γ b-γ a) (fun s hs ↦ by
      rw [uIoc_of_le hab] at hs
      have hs' : s∈Icc a b := ⟨hs.1.le,hs.2⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hγ ⟨le_rfl,hab⟩ hs' hs.1.le))]
      exact sub_le_sub_right (hγ hs' ⟨hab,le_rfl⟩ hs.2) _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hh

lemma meshControl_quadrature {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 0<N)
    (H : Fin N → Ω → ℝ) (hH : ∀ j ω, |H j ω| ≤ 1)
    {γ : ℝ → ℝ} (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (k : ℕ) (ω : Ω) :
    |controlAccum γ (meshControl T N H) k T ω-
      ∑ j : Fin N, stepSize T N*γ (meshTime T N j)*(H j ω)^k| ≤
      stepSize T N*(γ T-γ 0) := by
  have hi : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hγ
  rw [meshControl_momentIntegral hT hN H hi, ←Finset.sum_sub_distrib]
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have htime (j : ℕ) (hj : j ≤ N) := mesh_time_mem_total hT hj
  have hgap (j : ℕ) : meshTime T N (j+1)-meshTime T N j=stepSize T N := by
    dsimp [meshTime]
    push_cast
    ring
  have horder (j : ℕ) : meshTime T N j ≤ meshTime T N (j+1) := by
    linarith [hgap j]
  have hloc (j : Fin N) :
      |(∫ s in meshTime T N j..meshTime T N (j+1), γ s)*(H j ω)^k-
        stepSize T N*γ (meshTime T N j)*(H j ω)^k| ≤
      stepSize T N*(γ (meshTime T N (j+1))-γ (meshTime T N j)) := by
    rw [←sub_mul,abs_mul]
    have hh := monotone_interval_quadrature (horder j)
      (hγ.mono (Icc_subset_Icc (htime j j.isLt.le).1 (htime (j+1) j.isLt).2))
    rw [hgap] at hh
    have hp : |(H j ω)^k| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hH j ω)
    exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans (by simpa only [mul_one] using hh)
  calc
    _ ≤ ∑ j : Fin N, |(∫ s in meshTime T N j..meshTime T N (j+1), γ s)*(H j ω)^k-
        stepSize T N*γ (meshTime T N j)*(H j ω)^k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, stepSize T N*(γ (meshTime T N (j+1))-γ (meshTime T N j)) :=
      Finset.sum_le_sum (fun j _ ↦ hloc j)
    _ = _ := by
      rw [←Finset.mul_sum, sum_steps_sub (fun j ↦ γ (meshTime T N j))]
      have hlast : meshTime T N N=T := by
        dsimp [meshTime,stepSize]
        field_simp
      change stepSize T N*(γ (meshTime T N N)-γ (meshTime T N 0)) = _
      rw [hlast]
      simp only [meshTime,Nat.cast_zero,zero_mul]

lemma coupled_euler_past_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t))
    {T : ℝ} (hT : 0<T) {N : ℕ} (hN : 0<N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ j<N, Measurable (u (meshTime T N j))) :
    ∀ j ≤ N, StronglyMeasurable[Filtration.natural B hBm (Real.toNNReal (meshTime T N j))]
      (coupledEuler T γ u B N j) := by
  let f := Filtration.natural B hBm
  intro j
  induction j with
  | zero =>
    intro _
    convert (stronglyMeasurable_const : StronglyMeasurable[f (Real.toNNReal (meshTime T N 0))] (fun _ : Ω ↦ (0 : ℝ))) using 1
    funext ω
    exact coupled_euler_zero T γ u B N ω
  | succ j ih =>
    intro hjN
    have hj : j<N := hjN
    have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
    have ht : Real.toNNReal (meshTime T N j) ≤ Real.toNNReal (meshTime T N (j+1)) := by
      apply Real.toNNReal_mono
      apply mul_le_mul_of_nonneg_right _ hδ
      exact_mod_cast Nat.le_succ j
    have hY := (ih hj.le).mono (f.mono ht)
    have hB0 := (Filtration.stronglyAdapted_natural hBm (Real.toNNReal (meshTime T N j))).mono (f.mono ht)
    have hB1 := Filtration.stronglyAdapted_natural hBm (Real.toNNReal (meshTime T N (j+1)))
    have hU := ((hu j hj).comp hY.measurable).stronglyMeasurable.const_mul
      (stepSize T N*γ (meshTime T N j))
    convert ((hY.add hB1).sub hB0).add hU using 1
    funext ω
    rw [coupled_euler_step B hT γ u hN hj ω]
    rfl

lemma coupled_euler_drift_sum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T : ℝ} (hT : 0<T) {N : ℕ} (hN : 0<N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (ω : Ω) :
    coupledEuler T γ u B N N ω = B (Real.toNNReal T) ω-B 0 ω+
      ∑ j : Fin N, stepSize T N*γ (meshTime T N j)*u (meshTime T N j) (coupledEuler T γ u B N j ω) := by
  have he (j : Fin N) :
      coupledEuler T γ u B N (j+1) ω-coupledEuler T γ u B N j ω =
        (B (Real.toNNReal (meshTime T N (j+1))) ω-B (Real.toNNReal (meshTime T N j)) ω)+
          stepSize T N*γ (meshTime T N j)*u (meshTime T N j) (coupledEuler T γ u B N j ω) := by
    rw [coupled_euler_step B hT γ u hN j.isLt ω]
    dsimp [meshTime,stepSize]
    ring
  have hh := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin N))=Finset.univ) (fun j _ ↦ he j)
  rw [sum_steps_sub (fun j ↦ coupledEuler T γ u B N j ω),Finset.sum_add_distrib,
    sum_steps_sub (fun j ↦ B (Real.toNNReal (meshTime T N j)) ω),coupled_euler_zero] at hh
  have hlast : meshTime T N N=T := by dsimp [meshTime,stepSize]; field_simp
  simpa only [sub_zero,hlast,show meshTime T N 0=0 by simp [meshTime],Real.toNNReal_zero] using hh

noncomputable def feedbackControl {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (γ : ℝ → ℝ)
    (V : ℝ → ℝ → ℝ) (T : ℝ) (N : ℕ) : ℝ≥0 → Ω → ℝ :=
  meshControl T N (fun j ω ↦ deriv (V (meshTime T N j))
    (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))

lemma ValueStrip.feedback_progressive {Ω : Type*} [m : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    IsProgressive (Filtration.natural B hBm) (feedbackControl B γ V T N) := by
  apply meshControl_progressive hT.le
  intro j
  have hu (i : ℕ) (hi : i ≤ N) : Continuous (deriv (V (meshTime T N i))) :=
    (h.smooth _ (mesh_time_mem_total hT.le hi)).continuous_deriv (by norm_num)
  exact (hu j j.isLt.le).measurable.comp
    (coupled_euler_past_measurable hBm hT hN γ (fun t ↦ deriv (V t))
      (fun i hi ↦ (hu i hi.le).measurable) j j.isLt.le).measurable

lemma ValueStrip.feedback_bound {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (h : ValueStrip T γ V K L) (N : ℕ) (s : ℝ≥0) (ω : Ω) :
    |feedbackControl B γ V T N s ω| ≤ 1 :=
  meshControl_bound hT _ (fun j _ ↦ h.bounded _ (mesh_time_mem_total hT j.isLt.le) _) s ω

lemma ValueStrip.feedback_state_error {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N)
    (ω : Ω) (hB0 : B 0 ω=0) :
    |controlState B γ (feedbackControl B γ V T N) 0 T ω-
      coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω| ≤ stepSize T N*(γ T-γ 0) := by
  have hh := meshControl_quadrature hT.le hN
    (fun (j : Fin N) ω ↦ deriv (V (meshTime T N j))
      (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))
    (fun j ω ↦ h.bounded _ (mesh_time_mem_total hT.le j.isLt.le) _)
    h.gamma_mono 1 ω
  rw [controlState,coupled_euler_drift_sum B hT hN,hB0]
  simpa only [pow_one,zero_add,sub_zero,add_sub_add_left_eq_sub,feedbackControl] using hh

lemma ValueStrip.feedback_energy_error {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) (ω : Ω) :
    |(1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω-
      valueMeshEnergy T N γ V N (coupledCoordinates T N B ω)| ≤
        (1/2 : ℝ)*stepSize T N*(γ T-γ 0) := by
  have hh := meshControl_quadrature hT.le hN
    (fun (j : Fin N) ω ↦ deriv (V (meshTime T N j))
      (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))
    (fun j ω ↦ h.bounded _ (mesh_time_mem_total hT.le j.isLt.le) _)
    h.gamma_mono 2 ω
  have he : valueMeshEnergy T N γ V N (coupledCoordinates T N B ω) = (1/2 : ℝ)*
      ∑ j : Fin N, stepSize T N*γ (meshTime T N j)*
        (deriv (V (meshTime T N j)) (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))^2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ stepSize T N*γ (meshTime T N j)*
      (deriv (V (meshTime T N j)) (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))^2)]
    dsimp only [valueMeshEnergy,coupledEuler]
    simp only [ite_eq_right hN.ne',Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,←mul_sub,abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq (by ring)

end SKValue

end

end OAI
