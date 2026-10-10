import OAI.Geometry.SurfaceImmersion.Primitive.CompactPeriodicAnsatzBounds
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicFiniteAnsatz

namespace OAI

/-! Compact, fixed-coefficient asymptotics of the finite periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion
open CovarianceCorrector WeightedEstimates

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The finite polynomial before the extra factor of the fast scale. -/
def phaseSum (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) (p : A) : E :=
  ∑ i ∈ Finset.range L, z^i • (U i).fastValue ℓ z p

lemma phaseSum_smooth (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) : ContDiff ℝ ∞ (phaseSum U ℓ L z) :=
  ContDiff.sum fun i _ => contDiff_const.smul ((U i).fastValue_smooth ℓ z)

lemma phaseSum_fderiv (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (L : ℕ) (z : ℝ) (p v : A) :
    fderiv ℝ (phaseSum U ℓ L z) p v =
      phaseSum (fun i => (U i).slow v) ℓ L z p +
        (ℓ v/z) • phaseSum (fun i => (U i).angle) ℓ L z p := by
  have hd (i : ℕ) := ((U i).fastValue_smooth ℓ z).differentiable (by simp) p
  change (fderiv ℝ (fun q : A => ∑ i ∈ Finset.range L,
    z^i • (U i).fastValue ℓ z q) p) v = _
  rw [fderiv_fun_sum (A := fun i (q : A) => z^i • (U i).fastValue ℓ z q)
    (u := Finset.range L) (fun i _ => (hd i).const_smul (z^i))]
  have hterm (i : ℕ) :
      fderiv ℝ (fun q : A => z^i • (U i).fastValue ℓ z q) p v =
        z^i • (((U i).slow v).fastValue ℓ z p+
          (ℓ v/z) • (U i).angle.fastValue ℓ z p) := by
    rw [fderiv_fun_const_smul (f := (U i).fastValue ℓ z) (hd i) (z^i),
      smul_apply,Family.fastValue_fderiv]
    simp only [Family.fastValue]
  simp only [sum_apply,hterm,smul_add,Finset.sum_add_distrib]
  congr 1
  rw [phaseSum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change z^i • ((ℓ v/z) • (U i).angle.fastValue ℓ z p) =
    (ℓ v/z) • (z^i • (U i).angle.fastValue ℓ z p)
  exact smul_comm _ _ _

lemma finiteAnsatz_eq_phaseSum (F : A → E) (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    finiteAnsatz F U ℓ L z = fun p => F p+z • phaseSum U ℓ L z p := by
  funext p
  simp only [finiteAnsatz,phaseSum,Finset.smul_sum,pow_succ,smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

def directionalMap (F : A → E) (v : A) : A → E := fun p => fderiv ℝ F p v

lemma directionalMap_smooth {F : A → E} (hF : ContDiff ℝ ∞ F) (v : A) :
    ContDiff ℝ ∞ (directionalMap F v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The fast angular derivative cancels exactly one power of the scale. -/
lemma finiteAnsatz_directional {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ)
    {z : ℝ} (hz : z ≠ 0) (v : A) :
    directionalMap (finiteAnsatz F U ℓ L z) v = fun p =>
      directionalMap F v p + z • phaseSum (fun i => (U i).slow v) ℓ L z p +
        ℓ v • phaseSum (fun i => (U i).angle) ℓ L z p := by
  funext p
  have hS := (phaseSum_smooth U ℓ L z).differentiable (by simp) p
  have hderiv : fderiv ℝ (fun q : A => F q+z • phaseSum U ℓ L z q) p =
      fderiv ℝ F p+z • fderiv ℝ (phaseSum U ℓ L z) p := by
    rw [fderiv_fun_add (f := F) (g := fun q : A => z • phaseSum U ℓ L z q)
      (hF.differentiable (by simp) p) (hS.const_smul z),
      fderiv_fun_const_smul (f := phaseSum U ℓ L z) hS z]
  rw [directionalMap,finiteAnsatz_eq_phaseSum,hderiv]
  simp only [add_apply,smul_apply,phaseSum_fderiv,smul_add,smul_smul]
  rw [show z*(ℓ v/z) = ℓ v by field_simp]
  simp only [directionalMap,add_assoc]

/-- Differentiation in a direction annihilated by the phase only differentiates
the slow coefficients. -/
lemma directional_phaseSum_transverse (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {v : A} (hv : ℓ v = 0) :
    directionalMap (phaseSum U ℓ L z) v =
      phaseSum (fun i => (U i).slow v) ℓ L z := by
  funext p
  simp only [directionalMap,phaseSum_fderiv,hv,zero_div,zero_smul,add_zero]

private lemma phaseSum_scale_derivative (U : ℕ → Family A E)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) {z : ℝ} (hz : z ≠ 0) (v p : A) :
    z • directionalMap (phaseSum U ℓ L z) v p =
      z • phaseSum (fun i => (U i).slow v) ℓ L z p +
        ℓ v • phaseSum (fun i => (U i).angle) ℓ L z p := by
  simp only [directionalMap,phaseSum_fderiv,smul_add,smul_smul]
  rw [show z*(ℓ v/z) = ℓ v by field_simp]

private lemma directionalMap_add {F G : A → E}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (v : A) :
    directionalMap (fun p => F p+G p) v =
      fun p => directionalMap F v p+directionalMap G v p := by
  funext p
  simp only [directionalMap,fderiv_fun_add
    (hF.differentiable (by simp) p) (hG.differentiable (by simp) p),add_apply]

private lemma directionalMap_smul {F : A → E}
    (hF : ContDiff ℝ ∞ F) (c : ℝ) (v : A) :
    directionalMap (fun p => c • F p) v =
      fun p => c • directionalMap F v p := by
  funext p
  simp only [directionalMap,fderiv_fun_const_smul
    (hF.differentiable (by simp) p),smul_apply]

private lemma directionalMap_three {F G H : A → E}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (c d : ℝ) (v : A) :
    directionalMap (fun p => F p+c • G p+d • H p) v =
      fun p => directionalMap F v p+c • directionalMap G v p+
        d • directionalMap H v p := by
  have hc : ContDiff ℝ ∞ (fun p : A => c • G p) := contDiff_const.smul hG
  have hd : ContDiff ℝ ∞ (fun p : A => d • H p) := contDiff_const.smul hH
  rw [directionalMap_add (F := fun p : A => F p+c • G p)
    (G := fun p : A => d • H p) (hF.add hc) hd,
    directionalMap_add (F := F) (G := fun p : A => c • G p) hF hc,
    directionalMap_smul hG c v,directionalMap_smul hH d v]

/-- Exact transverse and mixed second-derivative identities. -/
lemma finiteAnsatz_second_transverse {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ)
    {z : ℝ} (hz : z ≠ 0) (v : A) {w : A} (hw : ℓ w = 0) :
    directionalMap (directionalMap (finiteAnsatz F U ℓ L z) v) w = fun p =>
      directionalMap (directionalMap F v) w p +
        z • phaseSum (fun i => ((U i).slow v).slow w) ℓ L z p +
        ℓ v • phaseSum (fun i => (U i).angle.slow w) ℓ L z p := by
  rw [finiteAnsatz_directional hF U ℓ L hz v,
    directionalMap_three (directionalMap_smooth hF v)
      (phaseSum_smooth (fun i => (U i).slow v) ℓ L z)
      (phaseSum_smooth (fun i => (U i).angle) ℓ L z) z (ℓ v) w,
    directional_phaseSum_transverse _ ℓ L z hw,
    directional_phaseSum_transverse _ ℓ L z hw]

/-- After multiplication by the fast scale, the longitudinal second derivative
has a finite limit profile, namely the second angular derivative of `U 0`. -/
lemma finiteAnsatz_second_longitudinal {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ) (L : ℕ)
    {z : ℝ} (hz : z ≠ 0) {v : A} (hv : ℓ v = 1) (p : A) :
    z • directionalMap (directionalMap (finiteAnsatz F U ℓ L z) v) v p =
      z • (directionalMap (directionalMap F v) v p +
        z • phaseSum (fun i => ((U i).slow v).slow v) ℓ L z p +
        phaseSum (fun i => ((U i).slow v).angle) ℓ L z p +
        phaseSum (fun i => (U i).angle.slow v) ℓ L z p) +
        phaseSum (fun i => (U i).angle.angle) ℓ L z p := by
  rw [finiteAnsatz_directional hF U ℓ L hz v,
    directionalMap_three (directionalMap_smooth hF v)
      (phaseSum_smooth (fun i => (U i).slow v) ℓ L z)
      (phaseSum_smooth (fun i => (U i).angle) ℓ L z) z (ℓ v) v]
  simp only [hv,one_smul,smul_add]
  rw [phaseSum_scale_derivative _ ℓ L hz v p,
    phaseSum_scale_derivative _ ℓ L hz v p,hv,one_smul]
  module

lemma phaseSum_leading (U : ℕ → Family A E) (ℓ : A →L[ℝ] ℝ)
    (n : ℕ) (z : ℝ) (p : A) :
    phaseSum U ℓ (n+1) z p =
      (U 0).fastValue ℓ z p+z • phaseSum (fun i => U (i+1)) ℓ n z p := by
  rw [phaseSum,Finset.sum_range_succ']
  simp only [pow_zero,one_smul,phaseSum,Finset.smul_sum,pow_succ,smul_smul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- Fixed smooth coefficients are uniformly bounded at all fast phases. -/
lemma compact_phaseSum_bound (U : ℕ → Family A E) {Q : Set A}
    (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (L : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 ≤ z → z ≤ 1 → ∀ p ∈ Q,
      ‖phaseSum U ℓ L z p‖ ≤ C := by
  choose D hD hb using fun i => (U i).compact_lift_derivative_bound hQ 0
  refine ⟨∑ i ∈ Finset.range L, D i,
    Finset.sum_nonneg (fun i _ => hD i),?_⟩
  intro z hz hz1 p hp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hz _)]
  have hi : ‖(U i).fastValue ℓ z p‖ ≤ D i := by
    simpa only [norm_iteratedFDeriv_zero,Family.fastValue] using hb i 0 le_rfl p hp (ℓ p/z)
  exact (mul_le_mul_of_nonneg_left hi (pow_nonneg hz _)).trans
    ((mul_le_mul_of_nonneg_right (pow_le_one₀ hz hz1) (hD i)).trans_eq (one_mul _))

/-- The tail after the leading coefficient is uniformly `O(z)`. -/
lemma compact_phaseSum_tail_bound (U : ℕ → Family A E) {Q : Set A}
    (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 ≤ z → z ≤ 1 → ∀ p ∈ Q,
      ‖phaseSum U ℓ (n+1) z p-(U 0).fastValue ℓ z p‖ ≤ C*z := by
  obtain ⟨C,hC,hb⟩ := compact_phaseSum_bound (fun i => U (i+1)) hQ ℓ n
  refine ⟨C,hC,?_⟩
  intro z hz hz1 p hp
  rw [phaseSum_leading,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb z hz hz1 p hp) hz

private lemma compact_directional_bound {F : A → E} (hF : ContDiff ℝ ∞ F)
    {Q : Set A} (hQ : IsCompact Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Q, ‖F p‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound uniqueDiffOn_univ hQ
    (subset_univ _) hF.contDiffOn 0
  refine ⟨C,zero_le_one.trans hC,?_⟩
  intro p hp
  simpa only [iteratedFDerivWithin_univ,norm_iteratedFDeriv_zero] using hb 0 le_rfl p hp

private lemma compact_scaled_sum_tail_bound (U V : ℕ → Family A E)
    {Q : Set A} (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 ≤ z → z ≤ 1 → ∀ p ∈ Q,
      ‖z • phaseSum U ℓ (n+1) z p +
        (phaseSum V ℓ (n+1) z p-(V 0).fastValue ℓ z p)‖ ≤ C*z := by
  obtain ⟨C,hC,hb⟩ := compact_phaseSum_bound U hQ ℓ (n+1)
  obtain ⟨D,hD,hd⟩ := compact_phaseSum_tail_bound V hQ ℓ n
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro z hz hz1 p hp
  calc
    _ ≤ ‖z • phaseSum U ℓ (n+1) z p‖+
        ‖phaseSum V ℓ (n+1) z p-(V 0).fastValue ℓ z p‖ := norm_add_le _ _
    _ ≤ z*C+D*z := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hz]
      exact add_le_add (mul_le_mul_of_nonneg_left (hb z hz hz1 p hp) hz)
        (hd z hz hz1 p hp)
    _ = (C+D)*z := by ring

/-- The two transverse jets approach the corresponding jets of the baseline
uniformly on a compact set, with an explicit linear rate in the fast scale. -/
theorem compact_finiteAnsatz_transverse_asymptotics {F : A → E}
    (hF : ContDiff ℝ ∞ F) (U : ℕ → Family A E) {Q : Set A}
    (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (L : ℕ)
    {dy : A} (hy : ℓ dy = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ p ∈ Q,
      ‖directionalMap (finiteAnsatz F U ℓ L z) dy p-directionalMap F dy p‖ ≤ C*z ∧
      ‖directionalMap (directionalMap (finiteAnsatz F U ℓ L z) dy) dy p-
        directionalMap (directionalMap F dy) dy p‖ ≤ C*z := by
  obtain ⟨C,hC,hc⟩ := compact_phaseSum_bound (fun i => (U i).slow dy) hQ ℓ L
  obtain ⟨D,hD,hd⟩ := compact_phaseSum_bound (fun i => ((U i).slow dy).slow dy) hQ ℓ L
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro z hz hz1 p hp
  constructor
  · rw [finiteAnsatz_directional hF U ℓ L (ne_of_gt hz) dy]
    simp only [hy,zero_smul,
      add_zero,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    calc
      _ ≤ z*C := mul_le_mul_of_nonneg_left (hc z hz.le hz1 p hp) hz.le
      _ ≤ (C+D)*z := by nlinarith
  · rw [finiteAnsatz_second_transverse hF U ℓ L (ne_of_gt hz) dy hy]
    simp only [
      hy,zero_smul,add_zero,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hz]
    calc
      _ ≤ z*D := mul_le_mul_of_nonneg_left (hd z hz.le hz1 p hp) hz.le
      _ ≤ (C+D)*z := by nlinarith

/-- The longitudinal tangent and its transverse derivative have their expected
oscillating leading terms, uniformly with an `O(z)` remainder. -/
theorem compact_finiteAnsatz_longitudinal_asymptotics {F : A → E}
    (hF : ContDiff ℝ ∞ F) (U : ℕ → Family A E) {Q : Set A}
    (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (n : ℕ)
    {dx dy : A} (hx : ℓ dx = 1) (hy : ℓ dy = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ p ∈ Q,
      ‖directionalMap (finiteAnsatz F U ℓ (n+1) z) dx p-
        (directionalMap F dx p+(U 0).angle.fastValue ℓ z p)‖ ≤ C*z ∧
      ‖directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dy p-
        (directionalMap (directionalMap F dx) dy p+
          ((U 0).angle.slow dy).fastValue ℓ z p)‖ ≤ C*z := by
  obtain ⟨C,hC,hc⟩ := compact_scaled_sum_tail_bound
    (fun i => (U i).slow dx) (fun i => (U i).angle) hQ ℓ n
  obtain ⟨D,hD,hd⟩ := compact_scaled_sum_tail_bound
    (fun i => ((U i).slow dx).slow dy) (fun i => (U i).angle.slow dy) hQ ℓ n
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro z hz hz1 p hp
  constructor
  · have he : directionalMap (finiteAnsatz F U ℓ (n+1) z) dx p-
        (directionalMap F dx p+(U 0).angle.fastValue ℓ z p) =
        z • phaseSum (fun i => (U i).slow dx) ℓ (n+1) z p+
          (phaseSum (fun i => (U i).angle) ℓ (n+1) z p-
            (U 0).angle.fastValue ℓ z p) := by
      rw [finiteAnsatz_directional hF U ℓ (n+1) (ne_of_gt hz) dx]
      simp only [hx,one_smul]
      abel
    rw [he]
    exact (hc z hz.le hz1 p hp).trans (by nlinarith)
  · have he : directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dy p-
        (directionalMap (directionalMap F dx) dy p+
          ((U 0).angle.slow dy).fastValue ℓ z p) =
        z • phaseSum (fun i => ((U i).slow dx).slow dy) ℓ (n+1) z p+
          (phaseSum (fun i => (U i).angle.slow dy) ℓ (n+1) z p-
            ((U 0).angle.slow dy).fastValue ℓ z p) := by
      rw [finiteAnsatz_second_transverse hF U ℓ (n+1) (ne_of_gt hz) dx hy]
      simp only [hx,one_smul]
      abel
    rw [he]
    exact (hd z hz.le hz1 p hp).trans (by nlinarith)

/-- The rescaled second longitudinal jet converges uniformly to the second
angular derivative of the leading coefficient. No varying-map estimates enter. -/
theorem compact_finiteAnsatz_second_longitudinal_asymptotics {F : A → E}
    (hF : ContDiff ℝ ∞ F) (U : ℕ → Family A E) {Q : Set A}
    (hQ : IsCompact Q) (ℓ : A →L[ℝ] ℝ) (n : ℕ)
    {dx : A} (hx : ℓ dx = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ p ∈ Q,
      ‖z • directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dx p-
        (U 0).angle.angle.fastValue ℓ z p‖ ≤ C*z := by
  obtain ⟨B,hB,hb⟩ := compact_directional_bound
    (directionalMap_smooth (directionalMap_smooth hF dx) dx) hQ
  obtain ⟨C,hC,hc⟩ := compact_phaseSum_bound
    (fun i => ((U i).slow dx).slow dx) hQ ℓ (n+1)
  obtain ⟨D,hD,hd⟩ := compact_phaseSum_bound
    (fun i => ((U i).slow dx).angle) hQ ℓ (n+1)
  obtain ⟨E,hE,he⟩ := compact_phaseSum_bound
    (fun i => (U i).angle.slow dx) hQ ℓ (n+1)
  obtain ⟨T,hT,ht⟩ := compact_phaseSum_tail_bound
    (fun i => (U i).angle.angle) hQ ℓ n
  refine ⟨B+C+D+E+T,by positivity,?_⟩
  intro z hz hz1 p hp
  have hscaled : ‖z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p‖ ≤ C := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    exact (mul_le_mul_of_nonneg_left (hc z hz.le hz1 p hp) hz.le).trans
      ((mul_le_mul_of_nonneg_right hz1 hC).trans_eq (one_mul _))
  have hinside : ‖directionalMap (directionalMap F dx) dx p+
      z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p+
      phaseSum (fun i => ((U i).slow dx).angle) ℓ (n+1) z p+
      phaseSum (fun i => (U i).angle.slow dx) ℓ (n+1) z p‖ ≤ B+C+D+E := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (hb p hp) hscaled)) (hd z hz.le hz1 p hp)))
      (he z hz.le hz1 p hp))
  have heq : z • directionalMap (directionalMap (finiteAnsatz F U ℓ (n+1) z) dx) dx p-
      (U 0).angle.angle.fastValue ℓ z p =
      z • (directionalMap (directionalMap F dx) dx p+
        z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p+
        phaseSum (fun i => ((U i).slow dx).angle) ℓ (n+1) z p+
        phaseSum (fun i => (U i).angle.slow dx) ℓ (n+1) z p)+
      (phaseSum (fun i => (U i).angle.angle) ℓ (n+1) z p-
        (U 0).angle.angle.fastValue ℓ z p) := by
    rw [finiteAnsatz_second_longitudinal hF U ℓ (n+1) (ne_of_gt hz) hx]
    abel
  rw [heq]
  calc
    _ ≤ ‖z • (directionalMap (directionalMap F dx) dx p+
        z • phaseSum (fun i => ((U i).slow dx).slow dx) ℓ (n+1) z p+
        phaseSum (fun i => ((U i).slow dx).angle) ℓ (n+1) z p+
        phaseSum (fun i => (U i).angle.slow dx) ℓ (n+1) z p)‖+
      ‖phaseSum (fun i => (U i).angle.angle) ℓ (n+1) z p-
        (U 0).angle.angle.fastValue ℓ z p‖ := norm_add_le _ _
    _ ≤ z*(B+C+D+E)+T*z := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hz]
      exact add_le_add (mul_le_mul_of_nonneg_left hinside hz.le) (ht z hz.le hz1 p hp)
    _ = (B+C+D+E+T)*z := by ring

end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
