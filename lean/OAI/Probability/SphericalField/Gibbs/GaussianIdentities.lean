import Mathlib
import OAI.Probability.SphericalField.Gibbs.Energy

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

namespace SphericalPerceptron
section QuantitativeGaussianGG
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma replicaMean_const {H : S → ℝ} (hH : Measurable H) {A : ℝ}
    (hA : 0 ≤ A) (hHA : ∀ x, |H x| ≤ A) (n : ℕ) (c : ℝ) :
    gibbsReplicaMean μ H n (fun _ => c) = c := by
  have := tilt_law_probability μ hH hA hHA 1
  rw [gibbsReplicaMean,tilt_replica_integral μ hH hA hHA]
  simp

lemma replicaMean_annealed_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {H : Ω → S → ℝ}
    (hH : Measurable (Function.uncurry H)) {A : Ω → ℝ}
    (hA : ∀ ω, 0 ≤ A ω) (hHA : ∀ ω x, |H ω x| ≤ A ω)
    {n : ℕ} {G : (Fin n → S) → ℝ} (hG : Measurable G)
    {D : ℝ} (hD : 0 ≤ D) (hGD : ∀ x, |G x| ≤ D) :
    Integrable (fun ω => gibbsReplicaMean μ (H ω) n G) P :=
  Integrable.of_bound (replicaMean_measurable μ hH hG).aestronglyMeasurable D
    (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs] using replicaMean_bound μ
        (show Measurable (H ω) from hH.comp (measurable_const.prodMk measurable_id)) hG (hA ω) hD (hHA ω) hGD)

omit μ [IsProbabilityMeasure μ] in
lemma fieldCovariance_measurable {m : ℕ} {v : Fin m → S → ℝ}
    (hv : ∀ i, Measurable (v i)) : Measurable (Function.uncurry (fieldCovariance m v)) := by
  change Measurable (fun p : S×S => ∑ i : Fin m, v i p.1*v i p.2)
  exact Finset.measurable_sum _ fun i _ => ((hv i).comp measurable_fst).mul ((hv i).comp measurable_snd)

omit μ [IsProbabilityMeasure μ] in
lemma fieldCovariance_comp_measurable {Ω : Type*} [MeasurableSpace Ω]
    {m : ℕ} {v : Fin m → S → ℝ} (hv : ∀ i, Measurable (v i))
    {a b : Ω → S} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun ω => fieldCovariance m v (a ω) (b ω)) := by
  exact Finset.measurable_sum _ fun i _ => ((hv i).comp ha).mul ((hv i).comp hb)

omit μ [IsProbabilityMeasure μ] [MeasurableSpace S] in
lemma fieldCovariance_bound {m : ℕ} {v : Fin m → S → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hvC : ∀ i x, |v i x| ≤ C) (x y : S) :
    |fieldCovariance m v x y| ≤ (m:ℝ)*C^2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ : Fin m, C^2 := Finset.sum_le_sum fun i _ => by
      rw [abs_mul,pow_two]; exact mul_le_mul (hvC i x) (hvC i y) (abs_nonneg _) hC
    _ = _ := by simp

lemma gaussian_field_energy_mean (m : ℕ) {v : Fin (m+1) → S → ℝ} {h : S → ℝ}
    (hv : ∀ i, Measurable (v i)) (hh : Measurable h) {C A k : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hvC : ∀ i x, |v i x| ≤ C) (hhA : ∀ x, |h x| ≤ A)
    (hdiag : ∀ x, fieldCovariance (m+1) v x x = k) (s : ℝ) :
    let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*gaussianField (m+1) v g x
    (∫ g, tiltMean μ (H g) (gaussianField (m+1) v g) 1 ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      s * (k-∫ g, gibbsReplicaMean μ (H g) 2 (fun x => fieldCovariance (m+1) v (x 1) (x 0))
        ∂Measure.pi (fun _ => gaussianReal 0 1)) := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin (m+1) => gaussianReal 0 1)
  let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*gaussianField (m+1) v g x
  let B := fun (g : Fin (m+1) → ℝ) => A+|s| * ((∑ i, |g i|)*C)
  have hH : Measurable (Function.uncurry H) := (hh.comp measurable_snd).add ((gaussianField_measurable hv).const_mul s)
  have hB (g) : 0 ≤ B g := by dsimp [B]; positivity
  have hb (g) (x) : |H g x| ≤ B g :=
    (abs_add_le _ _).trans (add_le_add (hhA x) (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (gaussianField_bound hvC g x) (abs_nonneg s)))
  have hHg (g) : Measurable (H g) := hH.comp (measurable_const.prodMk measurable_id)
  have hYg (g) : Measurable (gaussianField (m+1) v g) :=
    (gaussianField_measurable hv).comp (measurable_const.prodMk measurable_id)
  have hc : Integrable (fun g => gibbsReplicaMean μ (H g) 2
      (fun x => fieldCovariance (m+1) v (x 1) (x 0))) γ :=
    replicaMean_annealed_integrable μ γ hH hB hb
      (fieldCovariance_comp_measurable hv (measurable_pi_apply 1) (measurable_pi_apply 0))
      (by positivity) (fun x => fieldCovariance_bound hC hvC (x 1) (x 0))
  have he := gaussian_replica_field_ibp μ m 1 0 (G := fun _ => 1) hv hh measurable_const hC hA
    (show (0:ℝ) ≤ 1 by norm_num) hvC hhA (fun _ => by norm_num) s
  change (∫ g, gibbsReplicaMean μ (H g) 1 (fun x => gaussianField (m+1) v g (x 0)*1) ∂γ) = _ at he
  have hleft (g) : gibbsReplicaMean μ (H g) 1 (fun x => gaussianField (m+1) v g (x 0)*1) =
      tiltMean μ (H g) (gaussianField (m+1) v g) 1 := by
    simp only [mul_one]
    exact tilt_replica_coordinate μ (hHg g) (hYg g) (hB g) (hb g) 1 0 1
  have hright (g) : gibbsReplicaMean μ (H g) 1
      (fun x => ∑ l, fieldCovariance (m+1) v (x 0) (x l)) = k := by
    simp only [Fin.sum_univ_one,hdiag]
    exact replicaMean_const μ (hHg g) (hB g) (hb g) 1 k
  simp_rw [hleft] at he
  simp only [Nat.cast_one,one_mul,Fin.succ_zero_eq_one] at he
  change (∫ g, tiltMean μ (H g) (gaussianField (m+1) v g) 1 ∂γ) =
    s * ∫ g, gibbsReplicaMean μ (H g) 1 (fun x => ∑ l, fieldCovariance (m+1) v (x 0) (x l))-
      gibbsReplicaMean μ (H g) 2 (fun x => fieldCovariance (m+1) v (x 1) (x 0)) ∂γ at he
  simp_rw [hright] at he
  rw [integral_sub (integrable_const k) hc,integral_const] at he
  simpa only [Measure.real,γ,measure_univ,ENNReal.toReal_one,one_smul] using he

lemma gaussian_gg_defect_bound (m n : ℕ) (j : Fin n)
    {v : Fin (m+1) → S → ℝ} {h : S → ℝ} {G : (Fin n → S) → ℝ}
    (hv : ∀ i, Measurable (v i)) (hh : Measurable h) (hG : Measurable G)
    {C A D k s : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hvC : ∀ i x, |v i x| ≤ C) (hhA : ∀ x, |h x| ≤ A) (hGD : ∀ x, |G x| ≤ D)
    (hdiag : ∀ x, fieldCovariance (m+1) v x x = k) (hs : s ≠ 0) :
    let γ := Measure.pi (fun _ : Fin (m+1) => gaussianReal 0 1)
    let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*gaussianField (m+1) v g x
    let EG := ∫ g, gibbsReplicaMean μ (H g) n G ∂γ
    let EY := ∫ g, tiltMean μ (H g) (gaussianField (m+1) v g) 1 ∂γ
    |(∫ g, gibbsReplicaMean μ (H g) n (fun x => G x*∑ l, fieldCovariance (m+1) v (x j) (x l)) ∂γ)-
      k*EG+EG*(∫ g, gibbsReplicaMean μ (H g) 2 (fun x => fieldCovariance (m+1) v (x 1) (x 0)) ∂γ)-
      (n:ℝ)*(∫ g, gibbsReplicaMean μ (H g) (n+1)
        (fun x => G (fun l => x l.succ)*fieldCovariance (m+1) v (x j.succ) (x 0)) ∂γ)| ≤
    D*(∫ g, tiltMean μ (H g) (fun x => |gaussianField (m+1) v g x-EY|) 1 ∂γ)/|s| := by
  dsimp only
  let γ := Measure.pi (fun _ : Fin (m+1) => gaussianReal 0 1)
  let Y := gaussianField (m+1) v
  let H := fun (g : Fin (m+1) → ℝ) (x : S) => h x+s*Y g x
  let B := fun (g : Fin (m+1) → ℝ) => (∑ i, |g i|)*C
  let T := fun g => A+|s| * B g
  have hY : Measurable (Function.uncurry Y) := gaussianField_measurable hv
  have hH : Measurable (Function.uncurry H) := (hh.comp measurable_snd).add (hY.const_mul s)
  have hB (g) : 0 ≤ B g := by dsimp [B]; positivity
  have hT (g) : 0 ≤ T g := by dsimp [T]; positivity
  have hYB (g x) : |Y g x| ≤ B g := gaussianField_bound hvC g x
  have hHT (g x) : |H g x| ≤ T g := (abs_add_le _ _).trans (add_le_add (hhA x) (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hYB g x) (abs_nonneg s)))
  have hBI : Integrable B γ := by
    apply Integrable.mul_const
    exact integrable_finsetSum _ fun i _ =>
      (((measurePreserving_eval (fun _ : Fin (m+1) => gaussianReal 0 1) i).integrable_comp
        measurable_id.aestronglyMeasurable).mpr
        ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))).abs
  let U := fun x : Fin n → S => G x*∑ l, fieldCovariance (m+1) v (x j) (x l)
  let W := fun x : Fin (n+1) → S => G (fun l => x l.succ)*fieldCovariance (m+1) v (x j.succ) (x 0)
  have hcm (a b : Fin n) : Measurable (fun x : Fin n → S => fieldCovariance (m+1) v (x a) (x b)) :=
    fieldCovariance_comp_measurable hv (measurable_pi_apply a) (measurable_pi_apply b)
  have hUm : Measurable U := hG.mul (Finset.measurable_sum _ fun l _ => hcm j l)
  have hWm : Measurable W := by
    apply (hG.comp (Measurable.of_eval fun i => measurable_pi_apply i.succ)).mul
    exact fieldCovariance_comp_measurable hv (measurable_pi_apply j.succ) (measurable_pi_apply 0)
  have hUB (x) : |U x| ≤ D*((n:ℝ)*((m+1:ℕ):ℝ)*C^2) := by
    dsimp only [U]
    rw [abs_mul]
    apply mul_le_mul (hGD x) _ (abs_nonneg _) hD
    calc
      _ ≤ ∑ l : Fin n, |fieldCovariance (m+1) v (x j) (x l)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin n, ((m+1:ℕ):ℝ)*C^2 := Finset.sum_le_sum fun l _ => fieldCovariance_bound hC hvC _ _
      _ = _ := by simp; ring
  have hWB (x) : |W x| ≤ D*(((m+1:ℕ):ℝ)*C^2) := by
    dsimp only [W]
    rw [abs_mul]
    exact mul_le_mul (hGD _) (fieldCovariance_bound hC hvC _ _) (abs_nonneg _) hD
  have hUI := replicaMean_annealed_integrable μ γ hH hT hHT hUm (by positivity) hUB
  have hWI := replicaMean_annealed_integrable μ γ hH hT hHT hWm (by positivity) hWB
  let EY := ∫ g, tiltMean μ (H g) (Y g) 1 ∂γ
  have hf := annealed_replica_energy_factorization_bound μ γ hH hY hT hB hHT hYB hBI j hG hD hGD EY
  have he := gaussian_replica_field_ibp μ m n j hv hh hG hC hA hD hvC hhA hGD s
  change (∫ g, gibbsReplicaMean μ (H g) n (fun x => Y g (x j)*G x) ∂γ) =
    s*∫ g, gibbsReplicaMean μ (H g) n U-(n:ℝ)*gibbsReplicaMean μ (H g) (n+1) W ∂γ at he
  rw [integral_sub hUI (hWI.const_mul n),integral_const_mul] at he
  have hey := gaussian_field_energy_mean μ m hv hh hC hA hvC hhA hdiag s
  change EY = s*(k-∫ g, gibbsReplicaMean μ (H g) 2 (fun x => fieldCovariance (m+1) v (x 1) (x 0)) ∂γ) at hey
  rw [he] at hf
  have hab :
      |s| * |(∫ g, gibbsReplicaMean μ (H g) n U ∂γ)-k*(∫ g, gibbsReplicaMean μ (H g) n G ∂γ)+
        (∫ g, gibbsReplicaMean μ (H g) n G ∂γ)*(∫ g, gibbsReplicaMean μ (H g) 2
          (fun x => fieldCovariance (m+1) v (x 1) (x 0)) ∂γ)-
        (n:ℝ)*(∫ g, gibbsReplicaMean μ (H g) (n+1) W ∂γ)| =
      |s*((∫ g, gibbsReplicaMean μ (H g) n U ∂γ)-(n:ℝ)*(∫ g, gibbsReplicaMean μ (H g) (n+1) W ∂γ))-
        EY*(∫ g, gibbsReplicaMean μ (H g) n G ∂γ)| := by
    rw [← abs_mul,hey]; congr 1; ring
  exact (le_div_iff₀ (abs_pos.mpr hs)).mpr (by rw [mul_comm,hab]; exact hf)

end QuantitativeGaussianGG
end SphericalPerceptron

open scoped Pointwise

end
end
end

end OAI
