import Mathlib
import OAI.Computability.MinUncut.Estimates.F2

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianKernel

lemma euclidean_invariant_score {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) {f : E → ℝ} (hf : Measurable f)
    (hi : ∀ x (t : ℝ), f (x+t • v) = f x) :
    (∫ x, ⟪v,x⟫ * f x ∂stdGaussian E) = 0 := by
  let R := Submodule.reflection (ℝ ∙ v)ᗮ
  have hp : MeasurePreserving R (stdGaussian E) (stdGaussian E) :=
    ⟨by fun_prop, stdGaussian_map R⟩
  have hr (x : E) : f (R x) = f x := by
    have hh : R x = x + (-2*(⟪v,x⟫/‖v‖^2)) • v := by
      simp only [R, Submodule.reflection_orthogonal_apply,
        Submodule.reflection_singleton_apply]
      module
    rw [hh, hi]
  have hs (x : E) : ⟪v,R x⟫ = -⟪v,x⟫ := by
    have hh := R.inner_map_map v (R x)
    simpa only [R, Submodule.reflection_reflection,
      Submodule.reflection_orthogonalComplement_singleton_eq_neg, inner_neg_left] using hh.symm
  have he := integral_map (μ := stdGaussian E) (f := fun x => ⟪v,x⟫ * f x)
    hp.measurable.aemeasurable
    ((measurable_const.inner measurable_id).mul hf).aestronglyMeasurable
  rw [hp.map_eq] at he
  simp_rw [hr, hs, neg_mul, integral_neg] at he
  linarith

lemma invariant_score {ι : Type*} [Fintype ι] (v : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (hi : ∀ x (t : ℝ), f (x+t • v) = f x) :
    (∫ x, (∑ i, v i*x i)*f x ∂Measure.pi (fun _ : ι => gaussianReal 0 1))=0 := by
  have h := euclidean_invariant_score (E := EuclideanSpace ℝ ι) (toLp 2 v)
    (f := fun x => f (ofLp x)) (hf.comp (by fun_prop)) (by
      intro x t
      exact hi (ofLp x) t)
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, RCLike.star_def,
    conj_trivial, Pi.star_apply, star_trivial, PiLp.toLp_apply, ofLp_toLp, mul_comm] using h

lemma coupled_score {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (i : ι) (a : κ → ℝ) {f : (ι → ℝ) × (κ → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ u, |f u| ≤ 1)
    (hi : ∀ g l (t : ℝ), f (g+t • Pi.single i 1, l-t • a) = f (g,l)) :
    (∫ g, ∫ l, g i*f (g,l) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∑ z, a z*(∫ g, ∫ l, l z*f (g,l) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let ν : Measure (κ → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  let v : ι ⊕ κ → ℝ := Sum.elim (Pi.single i (1 : ℝ) : ι → ℝ) (-a)
  have he : MeasurePreserving e.symm (μ.prod ν)
      (Measure.pi (fun _ : ι ⊕ κ => gaussianReal 0 1)) :=
    measurePreserving_sumPiEquivProdPi_symm (X := fun _ : ι ⊕ κ => ℝ)
      (fun _ => gaussianReal 0 1)
  have hh := invariant_score v (f := fun u => f (e u)) (hf.comp e.measurable)
    (by
      intro u t
      change f ((fun j => u (.inl j)+t*(Pi.single i (1 : ℝ) : ι → ℝ) j),
        fun z => u (.inr z)+t*(-a z)) = f ((fun j => u (.inl j)), fun z => u (.inr z))
      convert hi (fun j => u (.inl j)) (fun z => u (.inr z)) t using 1
      congr 1
      ext z <;> simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg])
  rw [← he.integral_comp e.symm.measurableEmbedding] at hh
  have hg : Integrable (fun u : (ι → ℝ) × (κ → ℝ) => u.1 i*f u) (μ.prod ν) :=
    ((integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable
      (by norm_num))).comp_fst ν).mul_bdd hf.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hb u)
  have hl (z : κ) : Integrable (fun u : (ι → ℝ) × (κ → ℝ) => u.2 z*f u) (μ.prod ν) :=
    ((integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable
      (by norm_num))).comp_snd μ).mul_bdd hf.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hb u)
  have hval (u : (ι → ℝ) × (κ → ℝ)) :
      (∑ j, v j * (e.symm u) j)*f (e (e.symm u)) =
        u.1 i*f u - ∑ z, a z*(u.2 z*f u) := by
    simp only [e.apply_symm_apply, Fintype.sum_sum_type, v, Sum.elim_inl, Sum.elim_inr]
    change ((∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j*u.1 j)+(∑ z, (-a z)*u.2 z))*f u = _
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, neg_mul, Finset.sum_neg_distrib]
    rw [add_mul, neg_mul, Finset.sum_mul]
    simp only [mul_assoc, sub_eq_add_neg]
  simp_rw [hval] at hh
  rw [integral_sub hg (integrable_finsetSum _ (fun z _ => (hl z).const_mul (a z))),
    integral_finsetSum _ (fun z _ => (hl z).const_mul (a z))] at hh
  simp_rw [integral_const_mul] at hh
  have hx := sub_eq_zero.mp hh
  rw [integral_prod _ hg] at hx
  simp_rw [integral_prod _ (hl _)] at hx
  exact hx


open MeasureTheory ProbabilityTheory

lemma scalar_abs_mean_le_one : (∫ t : ℝ, |t| ∂gaussianReal 0 1) ≤ 1 := by
  have h1 : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have h2 : Integrable (fun t : ℝ => t^2) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hm : (∫ t : ℝ, t^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    simpa [variance_id_gaussianReal, integral_id_gaussianReal] using h.symm
  calc
    _ ≤ ∫ t : ℝ, (t^2+1)/2 ∂gaussianReal 0 1 := by
      apply integral_mono h1.abs ((h2.add (integrable_const 1)).div_const 2)
      intro t
      change |t| ≤ (t^2+1)/2
      nlinarith [sq_nonneg (|t|-1), sq_abs t]
    _ = 1 := by rw [integral_div, integral_add h2 (integrable_const 1), hm]; norm_num

lemma bounded_scalar_score {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ t, |f t| ≤ 1) :
    |∫ t : ℝ, t*f t ∂gaussianReal 0 1| ≤ 1 := by
  have ht : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hint := ht.mul_bdd hf.aestronglyMeasurable
    (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using hb t)
  calc
    _ ≤ ∫ t : ℝ, |t*f t| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, |t| ∂gaussianReal 0 1 := by
      apply integral_mono hint.abs ht.abs
      intro t
      change |t*f t| ≤ |t|
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (abs_nonneg t)).trans_eq (mul_one _)
    _ ≤ 1 := scalar_abs_mean_le_one

end MinUncut.GaussianKernel

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
variable [Fintype A]

lemma query_shift_cancel (x : Point m n) (u : Point m n → ℝ)
    (d : Code m n → ℝ) (t : ℝ) :
    query (u + t • Pi.single x 1)
      (fun z => d z - (Real.sqrt (n^m : ℕ))⁻¹ * t * BinaryFourier.sign (z.val x)) =
      query u d := by
  classical
  funext z
  unfold query
  congr 1
  have hs : (∑ j : Point m n, (u + t • (Pi.single x (1 : ℝ) : Point m n → ℝ)) j * BinaryFourier.sign (z.val j)) =
      (∑ j : Point m n, u j * BinaryFourier.sign (z.val j)) + t*BinaryFourier.sign (z.val x) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hs]
  ring_nf

omit [Fintype A] in
lemma answer_coupled_shift (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : η ≠ 0) (c g : Point m n → ℝ) (l : Code m n → ℝ)
    (x : Point m n) (t : ℝ) :
    bitSign (f.answer (pullQuery B (c + σ • (g + t • Pi.single x 1))
      (η • (l - t • (fun z : Code m n =>
        σ * (Real.sqrt (n^m : ℕ))⁻¹ / η * BinaryFourier.sign (z.val x)))))) =
    bitSign (f.answer (pullQuery B (c+σ • g) (η • l))) := by
  have hu : c + σ • (g + t • Pi.single x 1) =
      (c+σ • g)+(σ*t) • Pi.single x 1 := by module
  have hl : η • (l - t • (fun z : Code m n =>
        σ * (Real.sqrt (n^m : ℕ))⁻¹ / η * BinaryFourier.sign (z.val x))) =
      (fun z => (η • l) z - (Real.sqrt (n^m : ℕ))⁻¹ * (σ*t) * BinaryFourier.sign (z.val x)) := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  rw [hu, hl]
  congr 1
  congr 1
  funext a
  change query _ _ (labelCode B a) = query _ _ (labelCode B a)
  rw [query_shift_cancel]

def tableCoefficient (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) (z : Code m n) : ℝ :=
  η⁻¹ * ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
    l z * bitSign (f.answer (pullQuery B (c+σ • g) (η • l)))
      ∂gauss (Code m n) ∂gauss (Point m n)

theorem gradient_table_representation (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x =
      ∑ z : Code m n, tableCoefficient f B σ η c z * BinaryFourier.sign (z.val x) := by
  have hf0 := measurable_answer f B η
  have hmap : Measurable
      (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (c+σ • p.1,p.2)) := by fun_prop
  have hf := hf0.comp hmap
  dsimp only [Function.comp_def] at hf
  have hh := GaussianKernel.coupled_score x
    (fun z : Code m n => σ * (Real.sqrt (n^m : ℕ))⁻¹ / η * BinaryFourier.sign (z.val x)) hf
    (fun u => by simp only [bitSign_abs, le_refl])
    (answer_coupled_shift f B σ hη c · · x ·)
  have hN : Real.sqrt (n^m : ℕ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast pow_pos hn m)).ne'
  rw [gradient_convolution f B hσ]
  change _ * (∫ g, ∫ l, g x * _ ∂Measure.pi (fun _ => gaussianReal 0 1)
    ∂Measure.pi (fun _ => gaussianReal 0 1)) = _
  rw [hh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp [tableCoefficient, gauss]
  field_simp

end MinUncut.Inner
namespace MinUncut.GaussianSmoothing
open MeasureTheory ProbabilityTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integral_split_other (i : ι) {f : (ι → ℝ) → ℝ} (hf : Integrable f (gamma ι)) :
    (∫ g, f g ∂gamma ι) =
    ∫ h, ∫ t, f ((split i).symm (t,h)) ∂gaussianReal 0 1 ∂gamma {j : ι // j ≠ i} := by
  let hm := (split_measurePreserving i).symm (split i)
  rw [← hm.integral_comp' f, integral_prod_symm]
  exact (hm.integrable_comp hf.aestronglyMeasurable).mpr hf
end MinUncut.GaussianSmoothing

namespace MinUncut.GaussianKernel
open MeasureTheory ProbabilityTheory GaussianSmoothing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def thresholdTable (T : ι → ℝ) (η : ℝ) (l : ι → ℝ) : ι → Bool :=
  fun z => decide (0 ≤ T z + η*l z)

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_thresholdTable (T : ι → ℝ) (η : ℝ) :
    Measurable (thresholdTable T η) := by
  apply Measurable.of_eval
  intro z
  apply measurable_to_bool
  have heq : (fun l => thresholdTable T η l z) ⁻¹' {true} = {l : ι → ℝ | 0 ≤ T z + η*l z} := by
    ext l
    simp [thresholdTable]
  rw [heq]
  exact measurableSet_le measurable_const (by fun_prop)

def tableSensitivity (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) (l : ι → ℝ) : ℝ :=
  if H (Function.update (thresholdTable T η l) z true) =
      H (Function.update (thresholdTable T η l) z false) then 0 else 1

lemma measurable_tableSensitivity (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) :
    Measurable (tableSensitivity H T η z) := by
  let D : (ι → Bool) → ℝ := fun P =>
    if H (Function.update P z true) = H (Function.update P z false) then 0 else 1
  exact (measurable_of_finite D).comp (measurable_thresholdTable T η)

omit [Fintype ι] in
lemma tableSensitivity_nonneg (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) (l : ι → ℝ) :
    0 ≤ tableSensitivity H T η z l := by unfold tableSensitivity; split <;> norm_num

omit [Fintype ι] in
lemma tableSensitivity_abs_le (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) (l : ι → ℝ) :
    |tableSensitivity H T η z l| ≤ 1 := by unfold tableSensitivity; split <;> norm_num

lemma tableSensitivity_integrable (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) :
    Integrable (tableSensitivity H T η z) (gamma ι) :=
  (integrable_const (1 : ℝ)).mono' (measurable_tableSensitivity H T η z).aestronglyMeasurable
    (ae_of_all _ fun l => by simpa only [Real.norm_eq_abs] using tableSensitivity_abs_le H T η z l)

omit [Fintype ι] in
lemma forced_threshold_split (T : ι → ℝ) (η : ℝ) (z : ι)
    (h : {j : ι // j ≠ z} → ℝ) (t : ℝ) (b : Bool) :
    Function.update (thresholdTable T η ((split z).symm (t,h))) z b =
      Function.update (thresholdTable T η ((split z).symm (0,h))) z b := by
  funext j
  by_cases hj : j = z
  · subst j; simp
  · simp [thresholdTable, split_symm_apply, hj]

omit [Fintype ι] in
lemma tableSensitivity_split (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι)
    (h : {j : ι // j ≠ z} → ℝ) (t : ℝ) :
    tableSensitivity H T η z ((split z).symm (t,h)) =
      tableSensitivity H T η z ((split z).symm (0,h)) := by
  simp only [tableSensitivity, forced_threshold_split T η z h t]

omit [Fintype ι] in
lemma equal_forced_value (H : (ι → Bool) → ℝ) (P : ι → Bool) (z : ι)
    (he : H (Function.update P z true) = H (Function.update P z false)) :
    H P = H (Function.update P z true) := by
  cases hb : P z
  · calc H P = H (Function.update P z false) := by rw [← hb, Function.update_eq_self]
         _ = _ := he.symm
  · rw [← hb, Function.update_eq_self]

lemma conditional_table_score (H : (ι → Bool) → ℝ) (hH : ∀ P, |H P| ≤ 1)
    (T : ι → ℝ) (η : ℝ) (z : ι) (h : {j : ι // j ≠ z} → ℝ) :
    |∫ t : ℝ, t*H (thresholdTable T η ((split z).symm (t,h))) ∂gaussianReal 0 1| ≤
      tableSensitivity H T η z ((split z).symm (0,h)) := by
  unfold tableSensitivity
  split_ifs with he
  · have hv (t : ℝ) : H (thresholdTable T η ((split z).symm (t,h))) =
        H (Function.update (thresholdTable T η ((split z).symm (0,h))) z true) := by
      rw [equal_forced_value H _ z (by simpa only [forced_threshold_split] using he),
        forced_threshold_split]
    simp only [hv, integral_mul_const, integral_id_gaussianReal, zero_mul, abs_zero, le_refl]
  · apply bounded_scalar_score
    · exact (measurable_of_finite H).comp ((measurable_thresholdTable T η).comp
        ((split z).symm.measurable.comp (show Measurable (fun t : ℝ => (t,h)) by fun_prop)))
    · intro t; exact hH _

theorem table_score_le (H : (ι → Bool) → ℝ) (hH : ∀ P, |H P| ≤ 1)
    (T : ι → ℝ) (η : ℝ) (z : ι) :
    |∫ l : ι → ℝ, l z * H (thresholdTable T η l) ∂gamma ι| ≤
      ∫ l : ι → ℝ, tableSensitivity H T η z l ∂gamma ι := by
  have hf : Measurable (fun l => H (thresholdTable T η l)) :=
    (measurable_of_finite H).comp (measurable_thresholdTable T η)
  have hint : Integrable (fun l : ι → ℝ => l z * H (thresholdTable T η l)) (gamma ι) :=
    (integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))).mul_bdd
      hf.aestronglyMeasurable (ae_of_all _ fun l => by simpa only [Real.norm_eq_abs] using hH _)
  have hsint := tableSensitivity_integrable H T η z
  let hm := (split_measurePreserving z).symm (split z)
  have hi := ((hm.integrable_comp hint.aestronglyMeasurable).mpr hint).integral_prod_right
  have hsi := ((hm.integrable_comp hsint.aestronglyMeasurable).mpr hsint).integral_prod_right
  dsimp only [Function.comp_def] at hi hsi
  rw [integral_split_other z hint, integral_split_other z hsint]
  simp only [split_symm_apply]
  calc
    _ ≤ ∫ h, |∫ t : ℝ, t * H (thresholdTable T η ((split z).symm (t,h)))
        ∂gaussianReal 0 1| ∂gamma {j : ι // j ≠ z} := abs_integral_le_integral_abs
    _ ≤ ∫ h, ∫ t : ℝ, tableSensitivity H T η z ((split z).symm (t,h))
        ∂gaussianReal 0 1 ∂gamma {j : ι // j ≠ z} := by
      apply integral_mono (by simpa [split_symm_apply] using hi.abs) hsi
      intro h
      simpa only [tableSensitivity_split, integral_const, probReal_univ, one_smul]
        using conditional_table_score H hH T η z h
    _ = _ := rfl
end MinUncut.GaussianKernel
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
variable [Fintype A]

@[simp] lemma bitSign_eq_iff (b c : Bool) : bitSign b = bitSign c ↔ b = c := by
  cases b <;> cases c <;> norm_num [bitSign]

def thirdFailure (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) : ℝ :=
  if f.answer (fun a => Function.update (query u (η • l)) z true (labelCode B a)) =
      f.answer (fun a => Function.update (query u (η • l)) z false (labelCode B a)) then 0 else 1

omit [Fintype A] in
lemma thirdFailure_nonneg (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    0 ≤ thirdFailure f B η u l z := by unfold thirdFailure; split <;> norm_num

omit [Fintype A] in
lemma thirdFailure_abs_le (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    |thirdFailure f B η u l z| ≤ 1 := by unfold thirdFailure; split <;> norm_num

omit [Fintype A] in
lemma measurable_thirdFailure (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ) (z : Code m n) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => thirdFailure f B η p.1 p.2 z) := by
  let D : (Code m n → Bool) → ℝ := fun P =>
    if f.answer (fun a => Function.update P z true (labelCode B a)) =
      f.answer (fun a => Function.update P z false (labelCode B a)) then 0 else 1
  have hq : Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => query p.1 (η • p.2)) := by
    apply Measurable.of_eval
    intro w
    exact (measurable_query w).comp (show Measurable
      (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (p.1, η • p.2)) by fun_prop)
  exact (measurable_of_finite D).comp hq

lemma query_eq_threshold (η : ℝ) (u : Point m n → ℝ) (l : Code m n → ℝ) :
    query u (η • l) = GaussianKernel.thresholdTable
      (fun z : Code m n => (Real.sqrt (n^m : ℕ))⁻¹ *
        ∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) η l := rfl

omit [Fintype A] in
lemma thirdFailure_eq_sensitivity (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (l : Code m n → ℝ) (z : Code m n) :
    thirdFailure f B η u l z = GaussianKernel.tableSensitivity
      (fun P : Code m n → Bool => bitSign (f.answer (fun a => P (labelCode B a))))
      (fun w : Code m n => (Real.sqrt (n^m : ℕ))⁻¹ *
        ∑ x : Point m n, u x * BinaryFourier.sign (w.val x)) η z l := by
  simp only [thirdFailure, GaussianKernel.tableSensitivity, bitSign_eq_iff, query_eq_threshold]
  rfl

omit [Fintype A] in
lemma table_score_le_thirdFailure (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) (z : Code m n) :
    |∫ l : Code m n → ℝ, l z * bitSign (f.answer (pullQuery B u (η • l))) ∂gauss (Code m n)| ≤
      ∫ l : Code m n → ℝ, thirdFailure f B η u l z ∂gauss (Code m n) := by
  change |∫ l : Code m n → ℝ, l z * bitSign (f.answer (fun a => query u (η • l) (labelCode B a))) ∂gauss (Code m n)| ≤ _
  simpa only [thirdFailure_eq_sensitivity, query_eq_threshold, gauss, GaussianSmoothing.gamma]
    using GaussianKernel.table_score_le
      (fun P : Code m n → Bool => bitSign (f.answer (fun a => P (labelCode B a))))
      (fun P => by simp only [bitSign_abs, le_refl])
      (fun w : Code m n => (Real.sqrt (n^m : ℕ))⁻¹ *
        ∑ x : Point m n, u x * BinaryFourier.sign (w.val x)) η z

lemma tableCoefficient_abs_le (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : 0 < η) (c : Point m n → ℝ) (z : Code m n) :
    |tableCoefficient f B σ η c z| ≤
      η⁻¹ * ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        thirdFailure f B η (c+σ • g) l z ∂gauss (Code m n) ∂gauss (Point m n) := by
  have hmap : Measurable
      (fun p : (Point m n → ℝ) × (Code m n → ℝ) => (c+σ • p.1,p.2)) := by fun_prop
  have hf0 := measurable_answer f B η
  have hf := hf0.comp hmap
  dsimp only [Function.comp_def] at hf
  have hs0 := measurable_thirdFailure f B η z
  have hs := hs0.comp hmap
  dsimp only [Function.comp_def] at hs
  have hi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      p.2 z * bitSign (f.answer (pullQuery B (c+σ • p.1) (η • p.2))))
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    ((integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable
      (by norm_num))).comp_snd (gauss (Point m n))).mul_bdd (c := 1) hf.aestronglyMeasurable
      (ae_of_all _ fun p => by simp only [Real.norm_eq_abs, bitSign_abs, le_refl])
  have hsi : Integrable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      thirdFailure f B η (c+σ • p.1) p.2 z)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    (integrable_const (1 : ℝ)).mono' hs.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using thirdFailure_abs_le f B η _ _ z)
  rw [tableCoefficient, abs_mul, abs_of_pos (inv_pos.mpr hη)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hη.le)
  calc
    _ ≤ ∫ g : Point m n → ℝ, |∫ l : Code m n → ℝ,
        l z * bitSign (f.answer (pullQuery B (c+σ • g) (η • l))) ∂gauss (Code m n)|
        ∂gauss (Point m n) := abs_integral_le_integral_abs
    _ ≤ _ := integral_mono hi.integral_prod_left.abs hsi.integral_prod_left
      (fun g => table_score_le_thirdFailure f B η _ z)

def tableMass (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) (c : Point m n → ℝ) : ℝ :=
  ∑ z : Code m n, |tableCoefficient f B σ η c z|

def thirdRejection (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) (c : Point m n → ℝ) : ℝ :=
  𝔼 z : Code m n, ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
    thirdFailure f B η (c+σ • g) l z ∂gauss (Code m n) ∂gauss (Point m n)

theorem tableMass_le_thirdRejection (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : 0 < η) (c : Point m n → ℝ) :
    tableMass f B σ η c ≤ (Fintype.card (Code m n) : ℝ) / η * thirdRejection f B σ η c := by
  have hc : (Fintype.card (Code m n) : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ ∑ z : Code m n, η⁻¹ * ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        thirdFailure f B η (c+σ • g) l z ∂gauss (Code m n) ∂gauss (Point m n) :=
      Finset.sum_le_sum fun z _ => tableCoefficient_abs_le f B σ hη c z
    _ = _ := by
      rw [thirdRejection, Fintype.expect_eq_sum_div_card, ← Finset.mul_sum]
      field_simp
end MinUncut.Inner

end

end OAI
