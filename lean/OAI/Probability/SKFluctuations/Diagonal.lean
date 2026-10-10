import Mathlib
import OAI.Probability.SKFluctuations.MarkedAttachPreserves
import OAI.Probability.SKFluctuations.ScalarWeightedJet

namespace OAI

/-! Diagonal. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem ExpNormBounded.diagonal {f : (ι → ℝ) → ℝ} (hf : ExpNormBounded f)
    (x a : ι → ℝ) : ExpNormBounded (fun z => f (x+a*z)) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  refine ⟨hf.1.comp (continuous_const.add (continuous_const.mul continuous_id)),
    C*Real.exp (c*‖x‖), c*‖a‖, by positivity, by positivity, fun z => ?_⟩
  calc
    _ ≤ C*Real.exp (c*‖x+a*z‖) := hb _
    _ ≤ C*Real.exp (c*(‖x‖+‖a‖*‖z‖)) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le a z))
    _ = _ := by rw [mul_add,Real.exp_add]; ring_nf

theorem ExpNormBounded.diagonal_integrable {f : (ι → ℝ) → ℝ} (hf : ExpNormBounded f)
    {ν : Measure (ι → ℝ)} (hν : ExponentialIncrement ν) (x a : ι → ℝ) :
    Integrable (fun z => f (x+a*z)) ν := by
  simpa only [one_smul,zero_add] using (hf.diagonal x a).affine_integrable hν 0 1

theorem ExpNormBounded.diagonal_coord_integrable {f : (ι → ℝ) → ℝ} (hf : ExpNormBounded f)
    (q : ι → ℝ≥0) (x a : ι → ℝ) (i : ι) :
    Integrable (fun z => z i*f (x+a*z)) (Measure.pi fun i => gaussianReal 0 (q i)) := by
  simpa only [one_smul,zero_add] using (hf.diagonal x a).affine_coord_integrable q 0 1 i

 

theorem standardGaussianVector_diagonal_stein {n : ℕ} (i : Fin (n+1))
    {f f₁ : (Fin (n+1) → ℝ) → ℝ} (hf : ExpNormBounded f) (hf₁ : ExpNormBounded f₁)
    (hd : ∀ x t, HasDerivAt (fun s : ℝ => f (x+s • Pi.single i 1))
      (f₁ (x+t • Pi.single i 1)) t) (x a : Fin (n+1) → ℝ) :
    (∫ z, z i*f (x+a*z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) =
      a i * ∫ z, f₁ (x+a*z) ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  have h := standardGaussianVector_stein i
    (f := fun z => f (x+a*z)) (f₁ := fun z => a i*f₁ (x+a*z))
    ?_ (hf.diagonal_integrable (exponentialIncrement_gaussian (fun _ => 1)) x a)
    ((hf₁.diagonal_integrable (exponentialIncrement_gaussian (fun _ => 1)) x a).const_mul (a i))
    (hf.diagonal_coord_integrable (fun _ => 1) x a i)
  · simpa only [integral_const_mul] using h
  · intro y t
    have he (s : ℝ) : x+a*i.insertNth s y =
        (x+a*i.insertNth 0 y)+(a i*s) • Pi.single i 1 := by
      ext j
      by_cases hj : j = i
      · subst j
        simp
      · obtain ⟨k,rfl⟩ := (Fin.eq_self_or_eq_succAbove i j).resolve_left hj
        simp
    have hd' := (hd (x+a*i.insertNth 0 y) (a i*t)).comp t
      ((hasDerivAt_id t).const_mul (a i))
    simpa only [Function.comp_def, ← he,mul_one] using hd'.congr_deriv (mul_comm _ _)

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

theorem hasDerivAt_diagonal_heat_continuation {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ} {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    {a a' : ℝ → (Fin (n+1) → ℝ)} {l r A B t m : ℝ} (ht : t ∈ Ioo l r)
    (ha : ∀ s ∈ Ioo l r, HasDerivAt a (a' s) s)
    (hA : ∀ s ∈ Ioo l r, ‖a s‖ ≤ A) (hB : ∀ s ∈ Ioo l r, ‖a' s‖ ≤ B)
    (hm : m ≠ 0) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => Real.log (∫ z, Real.exp (m*F (x+a s*z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))/m)
      (∑ i, a t i*a' t i *
        (tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+a t*z)) (fun z => H i (x+a t*z)) + m *
         tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+a t*z)) (fun z => (G i (x+a t*z))^2))) t := by
  let P := fun y => Real.exp (m*F y)
  let P₁ := fun i y => m*G i y*P y
  let P₂ := fun i y => (m*H i y + m^2*(G i y)^2)*P y
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have hP : ExpNormBounded P := ExpNormBounded.exp_lipschitz hF m
  have hB₁ (i) : BddSmooth 0 (fun y => m*G i y) := (hG i).const_mul m
  have hB₂ (i) : BddSmooth 0 (fun y => m*H i y + m^2*(G i y)^2) := by
    simpa only [pow_two] using ((hH i).const_mul m).add (((hG i).mul (hG i)).const_mul (m*m))
  have hdP (y v : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P (y+r • v)) (∑ i, v i*P₁ i (y+s • v)) s := by
    apply (((hd y v s).const_mul m).exp).congr_deriv
    dsimp [P₁,P]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdP₁ (i) (y : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P₁ i (y+r • Pi.single i 1))
        (P₂ i (y+s • Pi.single i 1)) s := by
    have hp := hdP y (Pi.single i 1) s
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hp
    apply (((hd₁ i y s).const_mul m).mul hp).congr_deriv
    dsimp [P₂,P₁]
    ring
  have hs (i) : (∫ z, z i*P₁ i (x+a t*z) ∂ν) =
      a t i*∫ z, P₂ i (x+a t*z) ∂ν :=
    standardGaussianVector_diagonal_stein i (hP.bdd_mul (hB₁ i))
      (hP.bdd_mul (hB₂ i)) (hdP₁ i) x (a t)
  have h := hasDerivAt_integral_exp_scaledSource hν hF (fun i => (hG i).continuous)
    hd ht ha hA hB m x
  have hp : 0 < ∫ z, P (x+a t*z) ∂ν := partition_pos m (hP.diagonal_integrable hν x _)
  have hGs (i) : BddSmooth 0 (fun y => (G i y)^2) := by
    simpa only [pow_two] using (hG i).mul (hG i)
  have hiH (i) : Integrable (fun z => H i (x+a t*z)*P (x+a t*z)) ν :=
    (hP.bdd_mul (hH i)).diagonal_integrable hν x _
  have hiGs (i) : Integrable (fun z => (G i (x+a t*z))^2*P (x+a t*z)) ν :=
    (hP.bdd_mul (hGs i)).diagonal_integrable hν x _
  have he (i) : (∫ z, P₂ i (x+a t*z) ∂ν) =
      m*(∫ z, H i (x+a t*z)*P (x+a t*z) ∂ν) +
      m^2*(∫ z, (G i (x+a t*z))^2*P (x+a t*z) ∂ν) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hiH i).const_mul m) ((hiGs i).const_mul (m^2))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by dsimp [P₂]; ring
  have he' : (∫ z, m*(∑ i, (a' t*z) i*G i (x+a t*z))*P (x+a t*z) ∂ν) =
      ∑ i, a' t i*(∫ z, z i*P₁ i (x+a t*z) ∂ν) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ =>
      ((hP.bdd_mul (hB₁ i)).diagonal_coord_integrable (fun _ => 1) x (a t) i).const_mul (a' t i))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [P₁]
      ring
  apply ((h.log hp.ne').div_const m).congr_deriv
  change ((∫ z, m*(∑ i, (a' t*z) i*G i (x+a t*z))*P (x+a t*z) ∂ν)/
    (∫ z, P (x+a t*z) ∂ν))/m = _
  rw [he',Finset.sum_div,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [hs,he]
  simp only [tiltedMean]
  dsimp [P,ν] at *
  field_simp

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 

theorem hasDerivAt_signed_variance_continuation {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ} {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    (q d : Fin (n+1) → ℝ) {t m : ℝ} (ht : ∀ i, 0 < q i+t*d i) (hm : m ≠ 0)
    (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => Real.log (∫ z, Real.exp (m*F (x+(fun i => Real.sqrt (q i+s*d i))*z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))/m)
      (∑ i, (d i/2) *
        (tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+(fun i => Real.sqrt (q i+t*d i))*z))
          (fun z => H i (x+(fun i => Real.sqrt (q i+t*d i))*z)) + m *
         tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+(fun i => Real.sqrt (q i+t*d i))*z))
          (fun z => (G i (x+(fun i => Real.sqrt (q i+t*d i))*z))^2))) t := by
  let a := fun s i => Real.sqrt (q i+s*d i)
  let a' := fun s i => d i/(2*Real.sqrt (q i+s*d i))
  have ha : Continuous a := continuous_pi fun i => (continuous_const.add (continuous_id.mul continuous_const)).sqrt
  have ha' : ContinuousAt a' t := continuousAt_pi.mpr fun i =>
    continuousAt_const.div (continuousAt_const.mul
      (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).sqrt)
      (mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr (ht i)))
  have hp : ∀ᶠ s in 𝓝 t, ∀ i, 0 < q i+s*d i := by
    rw [eventually_all]
    intro i
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).eventually
      (eventually_gt_nhds (ht i))
  have hA : ∀ᶠ s in 𝓝 t, ‖a s‖ ≤ ‖a t‖+1 :=
    (ha.continuousAt.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h => h.le
  have hB : ∀ᶠ s in 𝓝 t, ‖a' s‖ ≤ ‖a' t‖+1 :=
    (ha'.norm.eventually (eventually_lt_nhds (lt_add_one _))).mono fun _ h => h.le
  obtain ⟨l,r,htr,hlr⟩ := (hp.and (hA.and hB)).exists_Ioo_subset
  have haD (s) (hs : s ∈ Ioo l r) : HasDerivAt a (a' s) s := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [a, a', id_eq, one_mul] using
      (((hasDerivAt_id s).mul_const (d i)).const_add (q i)).sqrt ((hlr hs).1 i).ne'
  have hh := hasDerivAt_diagonal_heat_continuation hF hG hH hd hd₁ htr haD
    (fun s hs => (hlr hs).2.1) (fun s hs => (hlr hs).2.2) hm x
  apply hh.congr_deriv
  apply Finset.sum_congr rfl
  intro i _
  dsimp [a,a']
  rw [show Real.sqrt (q i+t*d i)*(d i/(2*Real.sqrt (q i+t*d i))) = d i/2 by
    field_simp [Real.sqrt_ne_zero'.mpr (ht i)]]

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem integral_diagonalGaussian (q : ι → ℝ≥0) {f : (ι → ℝ) → ℝ} (hf : Continuous f) :
    (∫ z, f (fun i => Real.sqrt (q i)*z i) ∂Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ z, f z ∂Measure.pi fun i => gaussianReal 0 (q i) := by
  have hh := integral_map_of_stronglyMeasurable (μ := Measure.pi fun _ : ι => gaussianReal 0 1)
    (diagonalDriver q).measurable hf.stronglyMeasurable
  change (∫ z, f z ∂linearGaussian (diagonalDriver q) 1) = _ at hh
  rw [linearGaussian_diagonal] at hh
  exact hh.symm

noncomputable def varianceContinuation (m : ℝ) (F : (ι → ℝ) → ℝ) (q : ι → ℝ) : (ι → ℝ) → ℝ :=
  shiftedContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i))) m F

noncomputable def varianceTest (m : ℝ) (F A : (ι → ℝ) → ℝ) (q : ι → ℝ) : (ι → ℝ) → ℝ :=
  shiftedMean (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i))) m F A

theorem varianceContinuation_eq {F : (ι → ℝ) → ℝ} (hF : Continuous F)
    (m : ℝ) {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (x : ι → ℝ) :
    varianceContinuation m F q x = Real.log (∫ z, Real.exp (m*F (x+(fun i => Real.sqrt (q i))*z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1)/m := by
  have hi := integral_diagonalGaussian (fun i => Real.toNNReal (q i))
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  simp only [Real.coe_toNNReal _ (hq _)] at hi
  exact congrArg (fun z => Real.log z/m) hi.symm

theorem varianceTest_eq {F A : (ι → ℝ) → ℝ} (hF : Continuous F) (hA : Continuous A)
    (m : ℝ) {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (x : ι → ℝ) :
    varianceTest m F A q x = tiltedMean (Measure.pi fun _ : ι => gaussianReal 0 1) m
      (fun z => F (x+(fun i => Real.sqrt (q i))*z)) (fun z => A (x+(fun i => Real.sqrt (q i))*z)) := by
  have hn := integral_diagonalGaussian (fun i => Real.toNNReal (q i))
    (f := fun z => A (x+z)*Real.exp (m*F (x+z))) (by fun_prop)
  have hd := integral_diagonalGaussian (fun i => Real.toNNReal (q i))
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  simp only [Real.coe_toNNReal _ (hq _)] at hn hd
  exact congrArg₂ (· / ·) hn.symm hd.symm

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

noncomputable def signedVarianceDerivative (m : ℝ) (F : (ι → ℝ) → ℝ)
    (G H : ι → (ι → ℝ) → ℝ) (d q : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, (d i/2)*(varianceTest m F (H i) q x + m*varianceTest m F (fun y => (G i y)^2) q x)

 

theorem parametric_signed_variance {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ} {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    (q d : Fin (n+1) → ℝ) {m : ℝ} (hm : 0 < m) :
    ∃ K, ∀ l r, (∀ t ∈ Ioo l r, ∀ i, 0 < q i+t*d i) →
      ParametricRegular l r K
        (fun t => varianceContinuation m F (fun i => q i+t*d i))
        (fun t => signedVarianceDerivative m F G H d (fun i => q i+t*d i)) := by
  have hGs (i) : BddSmooth 0 (fun y => (G i y)^2) := by
    simpa only [pow_two] using (hG i).mul (hG i)
  choose BH hBH bH using fun i => (hH i).bound
  choose BG hBG bG using fun i => (hGs i).bound
  let K : ℝ := ∑ i, (|d i|/2)*(BH i+m*BG i)
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ =>
    mul_nonneg (div_nonneg (abs_nonneg _) (by norm_num))
      (add_nonneg (hBH i) (mul_nonneg hm.le (hBG i)))
  have hi (t : ℝ) (x : Fin (n+1) → ℝ) :
      Integrable (fun z => Real.exp (m*F (x+z)))
        (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i+t*d i))) :=
    (exponentialIncrement_gaussian _).integrable_shift hF m x
  refine ⟨K, fun l r hq => ⟨hK, ?_, ?_, ?_, ?_⟩⟩
  · intro t _
    exact ⟨C,lipschitzWith_shiftedContinuation hF hm (hi t)⟩
  · intro t _
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_shiftedMean hF (hH i).continuous (hBH i) (bH i) (hi t)).add
        ((continuous_shiftedMean hF (hGs i).continuous (hBG i) (bG i) (hi t)).const_mul m)).const_mul (d i/2)
  · intro t _ x
    have hBH' (i) : |varianceTest m F (H i) (fun i => q i+t*d i) x| ≤ BH i :=
      abs_tiltedMean_le ((hH i).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi t x) (fun z => bH i (x+z))
    have hBG' (i) : |varianceTest m F (fun y => (G i y)^2) (fun i => q i+t*d i) x| ≤ BG i :=
      abs_tiltedMean_le ((hGs i).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi t x) (fun z => bG i (x+z))
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos hm]
    exact add_le_add (hBH' i) (mul_le_mul_of_nonneg_left (hBG' i) hm.le)
  · intro t ht x
    have hh := GaussianCalculus.hasDerivAt_signed_variance_continuation hF hG hH hd hd₁ q d
      (hq t ht) hm.ne' x
    have he : (fun s => varianceContinuation m F (fun i => q i+s*d i) x) =ᶠ[𝓝 t]
        (fun s => Real.log (∫ z, Real.exp (m*F (x+(fun i => Real.sqrt (q i+s*d i))*z))
          ∂Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)/m) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact varianceContinuation_eq hF.continuous m (fun i => (hq s hs i).le) x
    have hde : signedVarianceDerivative m F G H d (fun i => q i+t*d i) x =
        (∑ i, (d i/2)*(tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+(fun i => Real.sqrt (q i+t*d i))*z))
          (fun z => H i (x+(fun i => Real.sqrt (q i+t*d i))*z)) + m*
          tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+(fun i => Real.sqrt (q i+t*d i))*z))
          (fun z => (G i (x+(fun i => Real.sqrt (q i+t*d i))*z))^2))) := by
      simp only [signedVarianceDerivative,varianceTest_eq hF.continuous (hH _).continuous m
        (fun i => (hq t ht i).le),varianceTest_eq hF.continuous (hGs _).continuous m
        (fun i => (hq t ht i).le)]
    rw [hde]
    exact hh.congr_of_eventuallyEq he

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 
noncomputable def hierarchyAtom (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (σ : S) (x : ι → ℝ) : ℝ := by
  classical
  exact gaussianHierarchyMean w φ (fun τ => if τ = σ then 1 else 0) steps x

theorem hierarchyAtom_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (σ : S) (x : ι → ℝ) :
    0 ≤ hierarchyAtom w φ steps σ x := by
  classical
  exact gaussianHierarchyMean_nonneg hw φ (fun τ => by split_ifs <;> norm_num) steps ha x

theorem hierarchyAtom_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (σ : S) (r : ℕ) :
    BddSmooth r (hierarchyAtom w φ steps σ) :=
  gaussianHierarchyMean_smooth hw φ _ steps ha r

theorem gaussianHierarchyMean_atoms {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (A : S → ℝ) (x : ι → ℝ) :
    gaussianHierarchyMean w φ A steps x = ∑ σ, A σ*hierarchyAtom w φ steps σ x := by
  classical
  have he : A = fun τ => ∑ σ, A σ*(if τ = σ then 1 else 0) := by
    funext τ
    simp
  conv_lhs => rw [he]
  rw [gaussianHierarchyMean_sum hw φ steps ha]
  apply Finset.sum_congr rfl
  intro σ _
  exact congrFun (gaussianHierarchyMean_const_mul_ordered hw φ _ steps ha (A σ)) x

theorem hierarchyAtom_sum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    ∑ σ, hierarchyAtom w φ steps σ x = 1 := by
  have h := gaussianHierarchyMean_atoms hw φ steps ha (fun _ => 1) x
  rw [gaussianHierarchyMean_const hw φ steps ha] at h
  simpa only [one_mul] using h.symm

 

noncomputable def hierarchyPairMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (K : S → S → ℝ) (steps : List (GaussianStep ι)) (x : ι → ℝ) : ℝ :=
  ∑ σ, ∑ τ, (hierarchyAtom w φ steps σ x*hierarchyAtom w φ steps τ x)*K σ τ

theorem hierarchyPairMean_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (r : ℕ) :
    BddSmooth r (hierarchyPairMean w φ K steps) := by
  apply BddSmooth.sum Finset.univ
  intro σ _
  apply BddSmooth.sum Finset.univ
  intro τ _
  simpa only [mul_comm (K σ τ)] using
    ((hierarchyAtom_smooth hw φ steps ha σ r).mul
      (hierarchyAtom_smooth hw φ steps ha τ r)).const_mul (K σ τ)

theorem hierarchyPairMean_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (x : ι → ℝ) :
    hierarchyPairMean w φ (fun _ _ => c) steps x = c := by
  unfold hierarchyPairMean
  simp_rw [← Finset.sum_mul,← Finset.mul_sum,hierarchyAtom_sum hw φ steps ha]
  simp only [mul_one,hierarchyAtom_sum hw φ steps ha]
  ring

theorem hierarchyPairMean_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {K L : S → S → ℝ} (hKL : ∀ σ τ, K σ τ ≤ L σ τ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    hierarchyPairMean w φ K steps x ≤ hierarchyPairMean w φ L steps x := by
  apply Finset.sum_le_sum
  intro σ _
  apply Finset.sum_le_sum
  intro τ _
  exact mul_le_mul_of_nonneg_left (hKL σ τ) (mul_nonneg
    (hierarchyAtom_nonneg hw φ steps ha σ x) (hierarchyAtom_nonneg hw φ steps ha τ x))

omit [Nonempty S] in
theorem hierarchyPairMean_linear (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (K L : S → S → ℝ) (steps : List (GaussianStep ι)) (c d : ℝ) (x : ι → ℝ) :
    hierarchyPairMean w φ (fun σ τ => c*K σ τ+d*L σ τ) steps x =
      c*hierarchyPairMean w φ K steps x+d*hierarchyPairMean w φ L steps x := by
  unfold hierarchyPairMean
  simp_rw [mul_add,Finset.sum_add_distrib,← mul_assoc]
  simp_rw [mul_comm _ c,mul_comm _ d,mul_assoc,← Finset.mul_sum]

theorem hierarchyPairMean_product {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A B : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    hierarchyPairMean w φ (fun σ τ => A σ*B τ) steps x =
      gaussianHierarchyMean w φ A steps x*gaussianHierarchyMean w φ B steps x := by
  rw [gaussianHierarchyMean_atoms hw φ steps ha,gaussianHierarchyMean_atoms hw φ steps ha,
    Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

 

noncomputable def kernelPenalty (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (K : S → S → ℝ) : ℝ → List (GaussianStep ι) → (ι → ℝ) → ℝ
  | a, [] => fun x => (1-a)*hierarchyPairMean w φ K [] x
  | a, (m,q)::tail => fun x => (m-a)*hierarchyPairMean w φ K ((m,q)::tail) x+
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
        (kernelPenalty w φ K m tail) x

theorem kernelPenalty_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (r : ℕ) :
    BddSmooth r (kernelPenalty w φ K a steps) := by
  induction steps generalizing a with
  | nil => exact (hierarchyPairMean_smooth hw φ K [] ha r).const_mul (1-a)
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact ((hierarchyPairMean_smooth hw φ K ((m,q)::tail) ha r).const_mul (m-a)).add
      ((ih ha.2.2.2).shiftedMean (gaussianHierarchy_regular hw φ tail ha.2.2.2 r)
        (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q))

theorem kernelPenalty_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (x : ι → ℝ) :
    kernelPenalty w φ (fun _ _ => c) a steps x = (1-a)*c := by
  induction steps generalizing a x with
  | nil => simp only [kernelPenalty,hierarchyPairMean_const hw φ [] ha]
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    simp only [kernelPenalty,hierarchyPairMean_const hw φ ((m,q)::tail) ha]
    rw [funext (ih ha.2.2.2)]
    rw [shiftedMean_const _ (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)]
    ring

theorem kernelPenalty_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {K L : S → S → ℝ} (hKL : ∀ σ τ, K σ τ ≤ L σ τ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    kernelPenalty w φ K a steps x ≤ kernelPenalty w φ L a steps x := by
  induction steps generalizing a x with
  | nil =>
    exact mul_le_mul_of_nonneg_left (hierarchyPairMean_mono hw φ hKL [] ha x)
      (sub_nonneg.mpr ha.2)
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact add_le_add (mul_le_mul_of_nonneg_left (hierarchyPairMean_mono hw φ hKL _ ha x)
      (sub_nonneg.mpr ha.2.1))
      (shiftedMean_mono (kernelPenalty_smooth hw φ K tail ha.2.2.2 0)
        (kernelPenalty_smooth hw φ L tail ha.2.2.2 0) (fun y => ih ha.2.2.2 y)
        (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x))

theorem kernelPenalty_linear {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K L : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c d : ℝ) (x : ι → ℝ) :
    kernelPenalty w φ (fun σ τ => c*K σ τ+d*L σ τ) a steps x =
      c*kernelPenalty w φ K a steps x+d*kernelPenalty w φ L a steps x := by
  induction steps generalizing a x with
  | nil => simp only [kernelPenalty,hierarchyPairMean_linear]; ring
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    simp only [kernelPenalty,hierarchyPairMean_linear]
    rw [funext (ih ha.2.2.2)]
    rw [shiftedMean_add ((kernelPenalty_smooth hw φ K tail ha.2.2.2 0).const_mul c)
      ((kernelPenalty_smooth hw φ L tail ha.2.2.2 0).const_mul d)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x),shiftedMean_const_mul,
      shiftedMean_const_mul]
    ring

theorem kernelPenalty_rankOne {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    kernelPenalty w φ (fun σ τ => φ σ v*φ τ v) a steps x = hierarchyPenalty w φ v a steps x := by
  induction steps generalizing a x with
  | nil => simp only [kernelPenalty,hierarchyPenalty,hierarchyPairMean_product hw φ _ _ [] ha,pow_two]
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    simp only [kernelPenalty,hierarchyPenalty,hierarchyPairMean_product hw φ _ _ _ ha,pow_two]
    rw [funext (ih ha.2.2.2)]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem kernelPenalty_const_mul {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (x : ι → ℝ) :
    kernelPenalty w φ (fun σ τ => c*K σ τ) a steps x = c*kernelPenalty w φ K a steps x := by
  simpa only [zero_mul,add_zero] using kernelPenalty_linear hw φ K (fun _ _ => 0) steps ha c 0 x

theorem kernelPenalty_sum {κ : Type*} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : κ → S → S → ℝ) (is : Finset κ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    kernelPenalty w φ (fun σ τ => ∑ i ∈ is, K i σ τ) a steps x =
      ∑ i ∈ is, kernelPenalty w φ (K i) a steps x := by
  classical
  induction is using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,kernelPenalty_const hw φ steps ha,mul_zero]
  | @insert i is hi ih =>
    simp only [Finset.sum_insert hi]
    have he := kernelPenalty_linear hw φ (K i) (fun σ τ => ∑ j ∈ is, K j σ τ) steps ha 1 1 x
    simp only [one_mul] at he
    rw [he,ih]

 

theorem kernelPenalty_weighted_features {κ : Type*} [Fintype κ] {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : κ → ι → ℝ)
    (d : κ → ℝ) (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    kernelPenalty w φ (fun σ τ => ∑ i, d i*φ σ (v i)*φ τ (v i)) a steps x =
      ∑ i, d i*hierarchyPenalty w φ (v i) a steps x := by
  have he : (fun σ τ => ∑ i, d i*φ σ (v i)*φ τ (v i)) =
      fun σ τ => ∑ i, d i*(φ σ (v i)*φ τ (v i)) := by
    funext σ τ
    simp only [mul_assoc]
  rw [he,kernelPenalty_sum hw φ _ Finset.univ steps ha]
  apply Finset.sum_congr rfl
  intro i _
  rw [kernelPenalty_const_mul hw φ _ steps ha,kernelPenalty_rankOne hw φ _ steps ha]

theorem kernelPenalty_lower_bound {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a C : ℝ} (ha : OrderedSteps a steps) (hK : ∀ σ τ, -C ≤ K σ τ) (x : ι → ℝ) :
    -(1/2:ℝ)*kernelPenalty w φ K a steps x ≤ (1-a)*C/2 := by
  have hh := kernelPenalty_mono hw φ hK steps ha x
  rw [kernelPenalty_const hw φ steps ha] at hh
  linarith

 

theorem kernelPenalty_chord {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (R : S → S → ℝ) (steps : List (GaussianStep ι))
    {m a : ℝ} (hm : OrderedSteps m steps) (ha : 0 < a) (c : ℝ) (x : ι → ℝ) :
    -(1/2:ℝ)*kernelPenalty w φ (fun σ τ => a/2*(R σ τ)^2-c*R σ τ) m steps x ≤
      (1-m)*c^2/(4*a) := by
  have hK (σ τ) : -(c^2/(2*a)) ≤ a/2*(R σ τ)^2-c*R σ τ := by
    rw [← neg_div,div_le_iff₀ (show 0 < 2*a by positivity)]
    nlinarith [sq_nonneg (a*R σ τ-c)]
  have hh := kernelPenalty_lower_bound hw φ _ steps hm hK x
  convert hh using 1; ring

 
theorem prefixTest_le_const {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (front : List (GaussianStep ι))
    (ho : ∀ st ∈ front, 0 < st.1) {B : ℝ} (hb : ∀ y, A y ≤ B) (x : ι → ℝ) :
    prefixTest front F A x ≤ B := by
  have hn : ∀ y, 0 ≤ B+(-1)*A y := fun y => by linarith [hb y]
  have hh := prefixTest_nonneg hF hn front ho x
  rw [prefixTest_affine hF hA front ho B (-1) x] at hh
  linarith

theorem rootedPrefixTest_le_const {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (front : List (GaussianStep ι))
    (ho : ∀ st ∈ front, 0 < st.1) {B : ℝ} (hb : ∀ y, A y ≤ B)
    (q₀ : ι → ℝ≥0) (x : ι → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i)) (prefixTest front F A) x ≤ B := by
  have hP := prefixTest_smooth0 hF hA front ho
  have hi : Integrable (fun z => prefixTest front F A (x+z))
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) := by
    obtain ⟨D,hD,hbD⟩ := hP.bound
    exact Integrable.of_bound (hP.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      D (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hbD (x+z))
  have hh := integral_mono hi (integrable_const B) (fun z => prefixTest_le_const hF hA front ho hb (x+z))
  simpa [zeroContinuation] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators

 

theorem orderedSK_kernel_chord (n : ℕ) (hn : 0 < n) {w : Spin n → ℝ}
    (hw : ∀ σ, 0 < w σ) (steps : List (GaussianStep (OrderedFeatureIndex n)))
    {m a : ℝ} (hm : OrderedSteps m steps) (ha : 0 < a) (c : ℝ) (x : OrderedFeatureIndex n → ℝ) :
    -(1/2:ℝ)*(∑ i : OrderedFeatureIndex n, Sum.elim (fun _ => -c) (fun _ => a) i*
      hierarchyPenalty w (orderedFeature n) (Pi.single i 1) m steps x) ≤
      (n:ℝ)*(1-m)*c^2/(4*a) := by
  have he : (fun σ τ => ∑ i : OrderedFeatureIndex n, Sum.elim (fun _ => -c) (fun _ => a) i*
      orderedFeature n σ (Pi.single i 1)*orderedFeature n τ (Pi.single i 1)) =
      fun σ τ => (n:ℝ)*(a/2*(orderedOverlap n σ τ)^2-c*orderedOverlap n σ τ) := by
    funext σ τ
    simp only [orderedFeature_single]
    rw [orderedCovariance n hn]
    ring
  rw [← kernelPenalty_weighted_features hw (orderedFeature n) (fun i => Pi.single i 1) _ steps hm,he,
    kernelPenalty_const_mul hw (orderedFeature n) _ steps hm]
  have hh := mul_le_mul_of_nonneg_left (kernelPenalty_chord hw (orderedFeature n)
    (orderedOverlap n) steps hm ha c x) (Nat.cast_nonneg n)
  convert hh using 1 <;> first | rfl | ring

end SKFluctuations

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators

 

theorem orderedSK_kernel_chord_observed (n : ℕ) (hn : 0 < n) {w : Spin n → ℝ}
    (hw : ∀ σ, 0 < w σ) (steps front : List (GaussianStep (OrderedFeatureIndex n)))
    {m a : ℝ} (hm : OrderedSteps m steps) (ha : 0 < a) (c : ℝ)
    (hf : ∀ st ∈ front, 0 < st.1) (q₀ : OrderedFeatureIndex n → ℝ≥0)
    (x : OrderedFeatureIndex n → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
      (prefixTest front (gaussianHierarchy w (orderedFeature n) steps)
        (fun y => -(1/2:ℝ)*(∑ i : OrderedFeatureIndex n,
          Sum.elim (fun _ => -c) (fun _ => a) i*
          hierarchyPenalty w (orderedFeature n) (Pi.single i 1) m steps y))) x ≤
      (n:ℝ)*(1-m)*c^2/(4*a) := by
  apply rootedPrefixTest_le_const (gaussianHierarchy_regular hw (orderedFeature n) steps hm 0).1.choose_spec
    ((BddSmooth.sum Finset.univ (fun i _ =>
      (hierarchyPenalty_smooth hw (orderedFeature n) (Pi.single i 1) steps hm 0).const_mul
        (Sum.elim (fun _ => -c) (fun _ => a) i))).const_mul (-(1/2:ℝ))) front hf
  exact fun y => orderedSK_kernel_chord n hn hw steps hm ha c y

end SKFluctuations

end

end OAI
