import OAI.Probability.SpanningForest.InnovationGaussianProcess
import OAI.Probability.SpanningForest.InnovationMartingale
import OAI.Probability.SpanningForest.BrownianFamilyPast
import OAI.Probability.SpanningForest.GaussianSum

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336.InnovationFiniteGaussian

theorem martingale_projection {I T Ω : Type*} [Preorder T]
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (F : Filtration T mΩ)
    (M : I → T → Ω → ℝ) (hM : ∀ i, Martingale (M i) F P)
    (S : Finset I) (θ : I → ℝ) :
    Martingale (fun t ω => ∑ i ∈ S, θ i * M i t ω) F P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    convert (martingale_zero ℝ F P : Martingale (0 : T → Ω → ℝ) F P) using 1
    funext t ω
    simp
  | @insert i S hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_def, Pi.smul_def, smul_eq_mul] using
      ((hM i).smul (θ i)).add ih

theorem brownian_projection_law {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (θ : I → ℝ) (u v : ℝ≥0) :
    HasLaw (fun ω => ∑ i, θ i * (B i v ω - B i u ω))
      (gaussianReal 0 (∑ i, NNReal.mk (θ i ^ 2) (sq_nonneg _) *
        nndist (v : ℝ) (u : ℝ))) P := by
  apply independent_weighted_gaussian_sum_hasLaw
  · intro i
    exact (hB i).hasLaw_sub v u
  · exact hI.comp (fun _ f => f v - f u) (by fun_prop)

theorem brownian_finset_projection_law {I Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) (u v : ℝ≥0) :
    HasLaw (fun ω => ∑ i ∈ S, θ i * (B i v ω - B i u ω))
      (gaussianReal 0 (∑ i ∈ S, NNReal.mk (θ i ^ 2) (sq_nonneg _) *
        nndist (v : ℝ) (u : ℝ))) P := by
  classical
  have hi := brownian_projection_law (fun i : S => hB i)
    (hI.precomp (g := fun i : S => (i : I)) Subtype.val_injective)
    (fun i : S => θ i) u v
  have heq : (fun ω => ∑ i : S, θ i * (B i v ω - B i u ω)) =
      (fun ω => ∑ i ∈ S, θ i * (B i v ω - B i u ω)) := by
    funext ω
    exact Finset.sum_coe_sort S (fun i => θ i * (B i v ω - B i u ω))
  have hv := Finset.sum_coe_sort S (fun i => NNReal.mk (θ i ^ 2) (sq_nonneg _) *
    nndist (v : ℝ) (u : ℝ))
  rw [heq, hv] at hi
  exact hi

theorem brownian_projection_indep {I Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    {X : Ω → I → ℝ} (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (S : Finset I) (θ : I → ℝ) {u v : ℝ≥0} (huv : u ≤ v)
    {m : MeasurableSpace Ω}
    (hm : m ≤ MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance)
    {K : Ω → ℂ} (hK : Measurable[m] K) :
    IndepFun K (fun ω => ∑ i ∈ S, θ i * (B i v ω - B i u ω)) P := by
  let : MeasurableSpace Ω := mΩ
  have hi := BrownianFamilyPast.indepFun_weighted_increment_observation
    hB hBm hI hX hXB S θ u (v - u)
  rw [add_tsub_cancel_of_le huv] at hi
  exact (indep_of_indep_of_le_right hi (hK.comap_le.trans hm)).symm

theorem restricted_characteristic_nnInnovation
    {I Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (X : Ω → I → ℝ) (B : I → ℝ≥0 → Ω → ℝ) (b : I → ℝ → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P) (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hXrange : ∀ ω i, X ω i ∈ Set.Icc (0 : ℝ) 1)
    (hbrange : ∀ i t ω, b i t ω ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ i, Martingale (Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)) F P)
    (hF : ∀ u, F u ≤ MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance)
    (S : Finset I) (θ : I → ℝ) (s t : ℝ≥0) (τ : ℕ → ℕ → ℝ≥0)
    (hτ : ∀ n, Monotone (τ n))
    (hstart : ∀ n, τ n 0 = s) (hfinish : ∀ n, τ n (n + 1) = t)
    (duration : ℝ) (hduration : 0 ≤ duration)
    (hstep : ∀ n k, k < n + 1 →
      (τ n (k + 1) : ℝ) - (τ n k : ℝ) = duration / ((n + 1 : ℕ) : ℝ))
    {A : Set Ω} (hA : MeasurableSet[F s] A) :
    (∫ ω in A, Complex.exp (((∑ i ∈ S, θ i *
      (Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) t ω -
       Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      (Real.exp (-duration * ((∑ i ∈ S, θ i ^ 2) / 2)) : ℂ) * (P.real A : ℂ) := by
  let W := fun i => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)
  let Z := fun r ω => ∑ i ∈ S, θ i * W i r ω
  have hZ : Martingale Z F P := martingale_projection P F W hM S θ
  let Q := fun n k ω => ∑ i ∈ S, θ i * (B i (τ n (k + 1)) ω - B i (τ n k) ω)
  let R := fun n k ω => Z (τ n (k + 1)) ω - Z (τ n k) ω - Q n k ω
  let v := fun n k => ∑ i ∈ S, NNReal.mk (θ i ^ 2) (sq_nonneg _) *
    nndist (τ n (k + 1) : ℝ) (τ n k : ℝ)
  have hZsub (u v : ℝ≥0) (ω : Ω) :
      Z v ω - Z u ω = ∑ i ∈ S, θ i * (W i v ω - W i u ω) := by
    simp only [Z, mul_sub, Finset.sum_sub_distrib]
  have hmono (n k : ℕ) : τ n k ≤ τ n (k + 1) := hτ n (Nat.le_succ k)
  have hres := InnovationGaussianProcess.restricted_characteristic_of_gaussian_perturbations
    Z s t τ (fun n k => F (τ n k)) (fun n k => F.le _) (F.le s A hA)
    (fun n k => F.mono (by simpa only [hstart n] using hτ n (Nat.zero_le k)) A hA)
    (fun n k => (hZ.stronglyMeasurable s).measurable.mono
      (F.mono (by simpa only [hstart n] using hτ n (Nat.zero_le k))) le_rfl)
    (fun n k => (hZ.stronglyMeasurable _).measurable)
    hstart hfinish duration (∑ i ∈ S, θ i ^ 2) (∑ i ∈ S, |θ i|) hduration
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (Finset.sum_nonneg (fun i _ => abs_nonneg _)) Q R v
    (fun n k _ => brownian_finset_projection_law hB hI S θ _ _) ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [hZsub] using hres
  · intro n k hk
    simp only [v, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk,
      coe_nndist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (τ n k : ℝ) ≤ (τ n (k + 1) : ℝ) from hmono n k))]
    rw [hstep n k hk, ← Finset.sum_mul, mul_comm]
  · intro n k hk
    have hq : Measurable (Q n k) := by dsimp [Q]; fun_prop
    exact (((hZ.integrable _).sub (hZ.integrable _)).aestronglyMeasurable).sub
      hq.aestronglyMeasurable
  · intro n k hk
    apply Filter.Eventually.of_forall
    intro ω
    have hid : R n k ω = ∑ i ∈ S, θ i *
        (W i (τ n (k + 1)) ω - W i (τ n k) ω -
          (B i (τ n (k + 1)) ω - B i (τ n k) ω)) := by
      simp only [R, hZsub, Q, mul_sub, Finset.sum_sub_distrib]
    rw [hid, ← hstep n k hk]
    calc
      _ ≤ ∑ i ∈ S, |θ i * (W i (τ n (k + 1)) ω - W i (τ n k) ω -
          (B i (τ n (k + 1)) ω - B i (τ n k) ω))| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le S (fun i => θ i *
          (W i (τ n (k + 1)) ω - W i (τ n k) ω -
            (B i (τ n (k + 1)) ω - B i (τ n k) ω)))
      _ ≤ ∑ i ∈ S, |θ i| * ((τ n (k + 1) : ℝ) - (τ n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hi := Innovation.innovation_sub_noise_bound
          (fun ω => X ω i) (fun r => B i r.toNNReal) (hb i)
          (fun ω => hXrange ω i) (hbrange i) (τ n k) (τ n (k + 1)) ω
        simpa only [W, Innovation.nnInnovation, Real.toNNReal_coe,
          Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (show (τ n k : ℝ) ≤ (τ n (k + 1) : ℝ) from hmono n k))] using hi
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  · intro n k hk
    exact Filter.Eventually.of_forall (fun ω => by dsimp [R]; ring)
  · intro n k hk K hK
    exact brownian_projection_indep hB hBm hI hX hXB S θ (hmono n k) (hF _) hK
  · intro n k hk K hK hKbound
    exact Innovation.integral_weighted_martingale_sub_eq_zero P F hZ (hmono n k)
      hK.stronglyMeasurable (Filter.Eventually.of_forall hKbound)

end Problem336.InnovationFiniteGaussian

end

end OAI
