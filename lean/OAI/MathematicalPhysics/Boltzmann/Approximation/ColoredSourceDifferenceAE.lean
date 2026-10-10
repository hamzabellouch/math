import OAI.MathematicalPhysics.Boltzmann.Approximation.ColoredDifferenceAlgebra
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss

namespace OAI

section

/-! # Collision integrand differences for a finite family in the sum norm -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem finite_integrand_abs_difference {X I : Type*} (s : Finset I) {q R E : ℝ}
    (hR : 0 ≤ R) (hE : 0 ≤ E) (c d : I → X × Velocity → ℝ)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hd : ∀ i ∈ s, ∀ p, 0 ≤ d i p ∧ d i p ≤ R)
    (hcd : ∀ p, (∑ i ∈ s, |c i p-d i p|) ≤ E)
    (b : ℝ) (x : X) (v : Velocity) (w : Velocity × Sphere) :
    (∑ i ∈ s, |CollisionCutoff.integrand b (fun u => density q (c i) (x,u)) v w-
      CollisionCutoff.integrand b (fun u => density q (d i) (x,u)) v w|) ≤
      (2*R*E)*GainOrder.integrand (H q) v w := by
  let a := scatterLeft v w.1 w.2
  let z := scatterRight v w.1 w.2
  let C := CollisionCutoff.kernel b v w.1 w.2*H q a*H q z
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (H_nonneg _ _)) (H_nonneg _ _)
  have he (i) : |CollisionCutoff.integrand b (fun u => density q (c i) (x,u)) v w-
      CollisionCutoff.integrand b (fun u => density q (d i) (x,u)) v w| =
      C* |c i (x,a)*c i (x,z)-d i (x,a)*d i (x,z)| := by
    rw [← abs_of_nonneg hC,← abs_mul]
    congr 1
    dsimp [CollisionCutoff.integrand,density,C,a,z]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hsum := ColoredAlgebra.sum_abs_product_difference_le s hR
    (fun i => c i (x,a)) (fun i => c i (x,z)) (fun i => d i (x,a)) (fun i => d i (x,z))
    (fun i hi => hc i hi _) (fun i hi => hd i hi _) (hcd _) (hcd _)
  apply (mul_le_mul_of_nonneg_left hsum hC).trans
  have hk : C ≤ GainOrder.integrand (H q) v w := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (CollisionCutoff.kernel_le b v w.1 w.2) (H_nonneg _ _)) (H_nonneg _ _)
  exact (mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 2*R*E)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # A gain estimate in the sum of absolute component differences -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem finite_gain_difference_sum {X I : Type*} [MeasurableSpace X]
    (s : Finset I) {q R E : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E)
    {c d : I → X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hdm : ∀ i ∈ s, Measurable (d i))
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hd : ∀ i ∈ s, ∀ p, 0 ≤ d i p ∧ d i p ≤ R)
    (hcd : ∀ p, (∑ i ∈ s, |c i p-d i p|) ≤ E)
    (b : ℝ) (p : X × Velocity) :
    (∑ i ∈ s, |gain q b (c i) p-gain q b (d i) p|) ≤ 2*R*E*HotApplication.realBound q := by
  classical
  by_cases hp : p.2 ∈ good q
  · let f (i : I) := CollisionCutoff.integrand b (fun v => density q (c i) (p.1,v)) p.2
    let g (i : I) := CollisionCutoff.integrand b (fun v => density q (d i) (p.1,v)) p.2
    let μ := (volume : Measure Velocity).prod sphereArea
    have hfi (i) (hi : i ∈ s) : Integrable (f i) μ := integrable_cutoff (hcm i hi) (hc i hi) b p hp
    have hgi (i) (hi : i ∈ s) : Integrable (g i) μ := integrable_cutoff (hdm i hi) (hd i hi) b p hp
    have hai (i) (hi : i ∈ s) : Integrable (fun w => |f i w-g i w|) μ := (hfi i hi |>.sub (hgi i hi)).abs
    have hterm (i) (hi : i ∈ s) : |gain q b (c i) p-gain q b (d i) p| ≤
        (∫ w, |f i w-g i w| ∂μ)/H q p.2 := by
      simp only [gain,ite_eq_left hp]
      change |(∫ w, f i w ∂μ)/H q p.2-(∫ w, g i w ∂μ)/H q p.2| ≤ _
      rw [← sub_div,abs_div,abs_of_pos (H_pos q p.2),← integral_sub (hfi i hi) (hgi i hi)]
      exact div_le_div_of_nonneg_right abs_integral_le_integral_abs (H_nonneg q p.2)
    calc
      _ ≤ ∑ i ∈ s, (∫ w, |f i w-g i w| ∂μ)/H q p.2 := Finset.sum_le_sum hterm
      _ = (∫ w, ∑ i ∈ s, |f i w-g i w| ∂μ)/H q p.2 := by
        rw [← Finset.sum_div,integral_finsetSum _ hai]
      _ ≤ (∫ w, (2*R*E)*GainOrder.integrand (H q) p.2 w ∂μ)/H q p.2 := by
        apply div_le_div_of_nonneg_right _ (H_nonneg q p.2)
        apply integral_mono (integrable_finsetSum s hai) ((integrable_H_gain hp).const_mul _)
        exact finite_integrand_abs_difference s hR hE c d hc hd hcd b p.1 p.2
      _ = ((2*R*E)*BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 p.2)/H q p.2 := by
        rw [integral_const_mul]
        rfl
      _ ≤ ((2*R*E)*(HotApplication.realBound q*H q p.2))/H q p.2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (H_gain_bound hp) (by positivity)) (H_nonneg q p.2)
      _ = _ := by field_simp [(H_pos q p.2).ne']
  · simp only [gain,ite_eq_right hp,sub_self,abs_zero,Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (HotApplication.realBound_pos q).le

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Difference of the colored collision sources in the sum norm -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

theorem finite_coldSource_difference_sum {X I : Type*} [MeasurableSpace X]
    (s : Finset I) {q b L R D E : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D) (hE : 0 ≤ E)
    {F G : X × Velocity → ℝ} {c d : I → X × Velocity → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i ∈ s, Measurable (c i)) (hdm : ∀ i ∈ s, Measurable (d i))
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hG : ∀ p, 0 ≤ G p ∧ G p ≤ R)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hd : ∀ i ∈ s, ∀ p, 0 ≤ d i p ∧ d i p ≤ R)
    (hFG : ∀ p, |F p-G p| ≤ D)
    (hcd : ∀ p, (∑ i ∈ s, |c i p-d i p|) ≤ E)
    (hdsum : ∀ p, (∑ i ∈ s, d i p) ≤ R) (p : X × Velocity) :
    (∑ i ∈ s, |coldSource q b L F (c i) p-coldSource q b L G (d i) p|) ≤
      2*R*E*HotApplication.realBound q+
        (L+R*CutoffLipschitz.frequencyConstant q b)*E+D*CutoffLipschitz.frequencyConstant q b*R := by
  let B := CutoffLipschitz.frequencyConstant q b
  have hB : 0 ≤ B := CutoffLipschitz.frequencyConstant_nonneg hb q
  have hνF : 0 ≤ frequency q b F p := frequency_nonneg (fun p => (hF p).1) q b p
  have hνFb : frequency q b F p ≤ R*B := frequency_bound hq hb hFm hF p
  have hνdiff : |frequency q b F p-frequency q b G p| ≤ D*B :=
    frequency_difference hq hb hFm hGm hF hG hFG p
  have hLF : |L-frequency q b F p| ≤ L+R*B := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hL,abs_of_nonneg hνF]
    exact add_le_add le_rfl hνFb
  have hLoss (i) (hi : i ∈ s) :
      |(L-frequency q b F p)*c i p-(L-frequency q b G p)*d i p| ≤
        (L+R*B)* |c i p-d i p| + (D*B)*d i p := by
    calc
      _ = |(L-frequency q b F p)*(c i p-d i p)+
          (frequency q b G p-frequency q b F p)*d i p| := by congr 1; ring
      _ ≤ |L-frequency q b F p| * |c i p-d i p| +
          |frequency q b G p-frequency q b F p| * |d i p| := by
        simpa only [abs_mul] using abs_add_le
          ((L-frequency q b F p)*(c i p-d i p)) ((frequency q b G p-frequency q b F p)*d i p)
      _ ≤ _ := by
        rw [abs_sub_comm (frequency q b G p),abs_of_nonneg (hd i hi p).1]
        exact add_le_add (mul_le_mul_of_nonneg_right hLF (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hνdiff (hd i hi p).1)
  calc
    _ ≤ ∑ i ∈ s, (|gain q b (c i) p-gain q b (d i) p| +
        |(L-frequency q b F p)*c i p-(L-frequency q b G p)*d i p|) := by
      apply Finset.sum_le_sum
      intro i _
      have he : coldSource q b L F (c i) p-coldSource q b L G (d i) p =
          (gain q b (c i) p-gain q b (d i) p)+
            ((L-frequency q b F p)*c i p-(L-frequency q b G p)*d i p) := by
        unfold coldSource
        ring
      rw [he]
      exact abs_add_le _ _
    _ ≤ (∑ i ∈ s, |gain q b (c i) p-gain q b (d i) p|)+
        (∑ i ∈ s, ((L+R*B)* |c i p-d i p| + (D*B)*d i p)) := by
      rw [Finset.sum_add_distrib]
      exact add_le_add le_rfl (Finset.sum_le_sum hLoss)
    _ ≤ (2*R*E*HotApplication.realBound q)+(L+R*B)*E+(D*B)*R := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      have hgain := finite_gain_difference_sum (q := q) s hR hE hcm hdm hc hd hcd b p
      have hcold := mul_le_mul_of_nonneg_left (hcd p) (add_nonneg hL (mul_nonneg hR hB))
      have hdtotal := mul_le_mul_of_nonneg_left (hdsum p) (mul_nonneg hD hB)
      exact (add_le_add hgain (add_le_add hcold hdtotal)).trans_eq (add_assoc _ _ _).symm
    _ = _ := rfl

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # The colored sum-norm source estimate for a.e. close representatives -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem finite_coldForcing_difference_ae {I : Type*} [Countable I]
    (s : Finset I) {q b L R D E : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D) (hE : 0 ≤ E)
    {F G : ℝ × JetPrototype.Phase → ℝ} {c d : I → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hcm : ∀ i, Measurable (c i)) (hdm : ∀ i, Measurable (d i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hc : ∀ i u, 0 ≤ c i u ∧ c i u ≤ R) (hd : ∀ i u, 0 ≤ d i u ∧ d i u ≤ R)
    (hFG : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ D)
    (hcd : ∀ᵐ u ∂spacetimeVolume, (∑ i ∈ s, |c i u-d i u|) ≤ E)
    (hdsum : ∀ u, (∑ i ∈ s, d i u) ≤ R) :
    ∀ᵐ u ∂spacetimeVolume,
      (∑ i ∈ s, |coldForcing q b L F (c i) u-coldForcing q b L G (d i) u|) ≤
        2*R*E*HotApplication.realBound q+
          (L+R*CutoffLipschitz.frequencyConstant q b)*E+D*CutoffLipschitz.frequencyConstant q b*R := by
  classical
  let H (u : ℝ × JetPrototype.Phase) := max (G u-D) (min (F u) (G u+D))
  have hHm : Measurable H := (hGm.sub_const D).max (hFm.min (hGm.add_const D))
  have hHb (u) : 0 ≤ H u ∧ H u ≤ R := by
    dsimp [H]
    exact ⟨(le_min (hF u).1 (add_nonneg (hG u).1 hD)).trans (le_max_right _ _),
      max_le (by linarith [(hG u).2]) ((min_le_left _ _).trans (hF u).2)⟩
  have hHD (u) : |H u-G u| ≤ D := by
    rw [abs_sub_le_iff]
    have hlo : G u-D ≤ H u := le_max_left _ _
    have hhi : H u ≤ G u+D := max_le (by linarith) (min_le_right _ _)
    constructor <;> linarith
  have hHF : H =ᵐ[spacetimeVolume] F := by
    filter_upwards [hFG] with u hu
    obtain ⟨h₁,h₂⟩ := abs_sub_le_iff.mp hu
    dsimp [H]
    rw [min_eq_left (by linarith),max_eq_right (by linarith)]
  let P (u : ℝ × JetPrototype.Phase) := (∑ i ∈ s, |c i u-d i u|) ≤ E
  let c' (i : I) (u : ℝ × JetPrototype.Phase) := if P u then c i u else 0
  let d' (i : I) (u : ℝ × JetPrototype.Phase) := if P u then d i u else 0
  have hPm : MeasurableSet {u | P u} := measurableSet_le
    (Finset.measurable_sum s (fun i _ => (hcm i |>.sub (hdm i)).abs)) measurable_const
  have hc'm (i) : Measurable (c' i) := (hcm i).ite hPm measurable_const
  have hd'm (i) : Measurable (d' i) := (hdm i).ite hPm measurable_const
  have hc'b (i) (u) : 0 ≤ c' i u ∧ c' i u ≤ R := by
    dsimp [c']; split_ifs; exact hc i u; exact ⟨le_rfl,hR⟩
  have hd'b (i) (u) : 0 ≤ d' i u ∧ d' i u ≤ R := by
    dsimp [d']; split_ifs; exact hd i u; exact ⟨le_rfl,hR⟩
  have hcd' (u) : (∑ i ∈ s, |c' i u-d' i u|) ≤ E := by
    by_cases hu : P u
    · simpa only [c',d',ite_eq_left hu] using hu
    · simpa only [c',d',ite_eq_right hu,sub_self,abs_zero,Finset.sum_const_zero] using hE
  have hdsum' (u) : (∑ i ∈ s, d' i u) ≤ R := by
    by_cases hu : P u
    · simpa only [d',ite_eq_left hu] using hdsum u
    · simpa only [d',ite_eq_right hu,Finset.sum_const_zero] using hR
  have hc'e (i) : c' i =ᵐ[spacetimeVolume] c i := by
    filter_upwards [hcd] with u hu
    exact ite_eq_left hu
  have hd'e (i) : d' i =ᵐ[spacetimeVolume] d i := by
    filter_upwards [hcd] with u hu
    exact ite_eq_left hu
  have hec : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L H (c' i) u = coldForcing q b L F (c i) u :=
    ae_all_iff.mpr (fun i => (coldForcing_congr_cold (hc'e i) q b L H).trans
      (coldForcing_congr_total hHF q b L (c i)))
  have hed : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L G (d' i) u = coldForcing q b L G (d i) u :=
    ae_all_iff.mpr (fun i => coldForcing_congr_cold (hd'e i) q b L G)
  filter_upwards [hec,hed] with u hcu hdu
  have h := HotRepresentative.finite_coldSource_difference_sum s hq hb hL hR hD hE
    (GaussianLocal.measurable_state hHm) (GaussianLocal.measurable_state hGm)
    (fun i _ => GaussianLocal.measurable_state (hc'm i)) (fun i _ => GaussianLocal.measurable_state (hd'm i))
    (fun p => hHb (p.1.1,(p.1.2,p.2))) (fun p => hG (p.1.1,(p.1.2,p.2)))
    (fun i _ p => hc'b i (p.1.1,(p.1.2,p.2))) (fun i _ p => hd'b i (p.1.1,(p.1.2,p.2)))
    (fun p => hHD (p.1.1,(p.1.2,p.2))) (fun p => hcd' (p.1.1,(p.1.2,p.2)))
    (fun p => hdsum' (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
  change (∑ i ∈ s, |coldForcing q b L H (c' i) u-coldForcing q b L G (d' i) u|) ≤ _ at h
  simpa only [hcu,hdu] using h

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
