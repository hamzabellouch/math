import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave

theorem exp_neg_smul_perturbation {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (P R : A) (s : ℝ) :
    NormedSpace.exp ((-s) • (P + R)) = NormedSpace.exp ((-s) • P) -
      ∫ t in (0 : ℝ)..s,
        NormedSpace.exp ((t - s) • P) * R * NormedSpace.exp ((-t) • (P + R)) := by
  let f : ℝ → A := fun t =>
    NormedSpace.exp ((t - s) • P) * NormedSpace.exp ((-t) • (P + R))
  let g : ℝ → A := fun t =>
    NormedSpace.exp ((t - s) • P) * R * NormedSpace.exp ((-t) • (P + R))
  have hd : ∀ t, HasDerivAt f (-g t) t := by
    intro t
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) P (t - s)).scomp t
      ((hasDerivAt_id t).sub_const s)
    have h2 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (P + R) (-t)).scomp t
      ((hasDerivAt_id t).neg)
    have hh := h1.mul h2
    simp only [Function.comp_apply, id_eq, one_smul, neg_one_smul] at hh
    convert hh using 1
    · rfl
    · dsimp [g]
      noncomm_ring
  have hg : Continuous (fun t => -g t) := by
    have hP := (differentiable_exp_smul_const ℝ P).continuous
    have hA := (differentiable_exp_smul_const ℝ (P + R)).continuous
    exact (((hP.comp (continuous_id.sub continuous_const)).mul continuous_const).mul
      (hA.comp continuous_neg)).neg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := s) (fun t _ => hd t) (hg.intervalIntegrable 0 s)
  simp only [f, sub_self, zero_smul, NormedSpace.exp_zero, one_mul,
    neg_zero, mul_one, zero_sub, intervalIntegral.integral_neg] at hi
  change _ = _ - ∫ t in (0 : ℝ)..s, g t
  rw [neg_eq_iff_eq_neg.mp hi]
  abel

section Volterra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

noncomputable def volterra (P R : A) (f : ℝ → A) (s : ℝ) : A :=
  ∫ t in (0 : ℝ)..s, NormedSpace.exp ((t - s) • P) * R * f t

noncomputable def volterraIter (P R : A) (f : ℝ → A) : ℕ → ℝ → A
  | 0 => f
  | k + 1 => volterra P R (volterraIter P R f k)

theorem continuous_volterra_integrand (P R : A) {f : ℝ → A}
    (hf : Continuous f) :
    Continuous (fun q : ℝ × ℝ => NormedSpace.exp ((q.2 - q.1) • P) * R * f q.2) :=
  (((differentiable_exp_smul_const ℝ P).continuous.comp
    (continuous_snd.sub continuous_fst)).mul continuous_const).mul (hf.comp continuous_snd)

theorem continuous_volterra (P R : A) {f : ℝ → A} (hf : Continuous f) :
    Continuous (volterra P R f) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (continuous_volterra_integrand P R hf) continuous_id

theorem continuous_volterraIter (P R : A) {f : ℝ → A} (hf : Continuous f) (k : ℕ) :
    Continuous (volterraIter P R f k) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact continuous_volterra P R ih

theorem volterra_sub (P R : A) {f g : ℝ → A} (hf : Continuous f) (hg : Continuous g) :
    volterra P R (fun t => f t - g t) = fun s => volterra P R f s - volterra P R g s := by
  funext s
  simp only [volterra, mul_sub]
  apply intervalIntegral.integral_sub
  · exact ((continuous_volterra_integrand P R hf).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s
  · exact ((continuous_volterra_integrand P R hg).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s

theorem volterraIter_sub (P R : A) {f g : ℝ → A} (hf : Continuous f) (hg : Continuous g)
    (k : ℕ) : volterraIter P R (fun t => f t - g t) k =
      fun s => volterraIter P R f k s - volterraIter P R g k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [volterraIter, ih]
    exact volterra_sub P R (continuous_volterraIter P R hf k)
      (continuous_volterraIter P R hg k)

omit [CompleteSpace A] in
theorem volterraIter_shift (P R : A) (f : ℝ → A) (k : ℕ) :
    volterraIter P R (volterra P R f) k = volterraIter P R f (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [volterraIter, ih]

theorem perturbation_iteration (P R : A) (k : ℕ) :
    volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) k =
      fun s => volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) k s -
        volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) (k + 1) s := by
  have h0 : Continuous (fun t : ℝ => NormedSpace.exp ((-t) • P)) :=
    (differentiable_exp_smul_const ℝ P).continuous.comp continuous_neg
  have h1 : Continuous (fun t : ℝ => NormedSpace.exp ((-t) • (P + R))) :=
    (differentiable_exp_smul_const ℝ (P + R)).continuous.comp continuous_neg
  have heq : (fun t : ℝ => NormedSpace.exp ((-t) • (P + R))) =
      fun s => NormedSpace.exp ((-s) • P) -
        volterra P R (fun t => NormedSpace.exp ((-t) • (P + R))) s := by
    funext s
    exact exp_neg_smul_perturbation P R s
  conv_lhs => rw [heq]
  rw [volterraIter_sub P R h0 (continuous_volterra P R h1), volterraIter_shift]

theorem perturbation_finite_expansion (P R : A) (K : ℕ) (s : ℝ) :
    NormedSpace.exp ((-s) • (P + R)) =
      (∑ j ∈ Finset.range K, (-1 : ℝ) ^ j •
        volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) j s) +
      (-1 : ℝ) ^ K •
        volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s := by
  induction K with
  | zero => simp [volterraIter]
  | succ K ih =>
    rw [ih, Finset.sum_range_succ]
    have hi := congrFun (perturbation_iteration P R K) s
    rw [hi, smul_sub, pow_succ]
    simp only [mul_neg_one, neg_smul]
    abel

omit [CompleteSpace A] in

theorem volterraIter_norm_le (P R : A) (f : ℝ → A) (T a b : ℝ)
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • P)‖ ≤ a)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ ≤ b)
    (k : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖volterraIter P R f k s‖ ≤ (a * ‖R‖ * T) ^ k * b := by
  induction k generalizing s with
  | zero => simpa [volterraIter] using hf s hs
  | succ k ih =>
    have hn : 0 ≤ a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b) := by positivity
    have hi : ‖volterraIter P R f (k + 1) s‖ ≤
        (a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b)) * |s - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hs.1] at ht
      have hst : s - t ∈ Set.Icc (0 : ℝ) T := ⟨sub_nonneg.mpr ht.2, by linarith [ht.1, hs.2]⟩
      have htt : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.trans hs.2⟩
      have hPe : ‖NormedSpace.exp ((t - s) • P)‖ ≤ a := by
        simpa only [neg_sub] using hP (s - t) hst
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hPe (norm_nonneg R)))
        (ih t htt) (norm_nonneg _) (mul_nonneg ha (norm_nonneg R)))
    calc
      _ ≤ (a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b)) * s := by
        simpa only [sub_zero, abs_of_nonneg hs.1] using hi
      _ ≤ (a * ‖R‖ * ((a * ‖R‖ * T) ^ k * b)) * T :=
        mul_le_mul_of_nonneg_left hs.2 hn
      _ = (a * ‖R‖ * T) ^ (k + 1) * b := by rw [pow_succ]; ring

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

omit [CompleteSpace B] in
theorem continuous_algHom_map_exp (F : A →ₐ[ℝ] B) (hF : Continuous F) (x : A) :
    F (NormedSpace.exp x) = NormedSpace.exp (F x) := by
  apply NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) F hF
  rw [NormedSpace.expSeries_radius_eq_top]
  exact edist_lt_top _ _

theorem map_volterraIter (F : A →ₐ[ℝ] B) (hF : Continuous F) (P R : A)
    {f : ℝ → A} (hf : Continuous f) (k : ℕ) (s : ℝ) :
    F (volterraIter P R f k s) =
      volterraIter (F P) (F R) (fun t => F (f t)) k s := by
  let L : A →L[ℝ] B := ⟨F.toLinearMap, hF⟩
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    change L (∫ t in (0 : ℝ)..s,
      NormedSpace.exp ((t - s) • P) * R * volterraIter P R f k t) = _
    have hint : IntervalIntegrable (fun t =>
        NormedSpace.exp ((t - s) • P) * R * volterraIter P R f k t) volume 0 s :=
      ((continuous_volterra_integrand P R (continuous_volterraIter P R hf k)).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 s
    rw [← L.intervalIntegral_comp_comm hint]
    change (∫ t in (0 : ℝ)..s,
      F (NormedSpace.exp ((t - s) • P) * R * volterraIter P R f k t)) = _
    simp only [map_mul, continuous_algHom_map_exp F hF, map_smul, ih]
    rfl

theorem perturbation_mixed_norm_bound (F : A →ₐ[ℝ] B) (hF : Continuous F)
    (P R : A) (T a b N : ℝ) (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hcompare : ∀ x : A, ‖x‖ ≤ N * ‖F x‖)
    (hbase : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • P)‖ ≤ a)
    (hbase₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • F P)‖ ≤ 1)
    (hfull₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NormedSpace.exp ((-t) • (F P + F R))‖ ≤ b)
    (K : ℕ) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖NormedSpace.exp ((-s) • (P + R))‖ ≤
      (∑ j ∈ Finset.range K, (a * ‖R‖ * T) ^ j * a) +
      N * ((‖F R‖ * T) ^ K * b) := by
  have hc : Continuous (fun t : ℝ => NormedSpace.exp ((-t) • (P + R))) :=
    (differentiable_exp_smul_const ℝ (P + R)).continuous.comp continuous_neg
  have hr : ‖volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s‖ ≤
      N * ((‖F R‖ * T) ^ K * b) := by
    apply (hcompare _).trans
    apply mul_le_mul_of_nonneg_left _ hN
    rw [map_volterraIter F hF P R hc]
    simp_rw [continuous_algHom_map_exp F hF, map_smul, map_add]
    simpa only [one_mul] using
      volterraIter_norm_le (F P) (F R) (fun t => NormedSpace.exp ((-t) • (F P + F R)))
        T 1 b hT zero_le_one hb hbase₂ hfull₂ K s hs
  rw [perturbation_finite_expansion P R K s]
  calc
    _ ≤ (∑ j ∈ Finset.range K,
        ‖(-1 : ℝ) ^ j • volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) j s‖) +
        ‖(-1 : ℝ) ^ K • volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (le_refl _))
    _ = (∑ j ∈ Finset.range K,
        ‖volterraIter P R (fun t => NormedSpace.exp ((-t) • P)) j s‖) +
        ‖volterraIter P R (fun t => NormedSpace.exp ((-t) • (P + R))) K s‖ := by
      simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ _ := by
      apply add_le_add _ hr
      exact Finset.sum_le_sum fun j _ => volterraIter_norm_le P R _ T a a hT ha ha
        hbase hbase j s hs

end Volterra
end SharpTerminalLeave

end

end OAI
