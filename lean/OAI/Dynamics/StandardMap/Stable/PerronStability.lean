import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Stable.LocalStable

namespace OAI

section
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma perron_defect_bound (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence)
    {B : ℝ} (hB : 0≤B) (h0 : (x 0).1=s)
    (hstep : ∀ n, ‖x (n+1)-r.step n (x n)‖≤B) :
    ‖r.perron hℓ s x-x‖≤B := by
  apply (BoundedContinuousFunction.norm_le hB).mpr
  intro n
  rw [Prod.norm_def]
  apply max_le
  · cases n with
    | zero => simpa only [BoundedContinuousFunction.sub_apply,perron_apply,Recurrence.perronValue,
        Prod.fst_sub,h0,sub_self,norm_zero] using hB
    | succ n =>
      have hh := (norm_fst_le (x (n+1)-r.step n (x n))).trans (hstep n)
      change |r.a n*(x n).1+(r.remainder n (x n)).1-(x (n+1)).1|≤B
      rw [abs_sub_comm]
      exact hh
  · have hh := (norm_snd_le (x (n+1)-r.step n (x n))).trans (hstep n)
    change |(r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)-(x n).2|≤B
    calc
      _ = |(r.b n)⁻¹| * |(x (n+1)).2-(r.b n*(x n).2+(r.remainder n (x n)).2)| := by
        rw [←abs_mul]
        congr 1
        have hb := inv_mul_cancel₀ (r.b_ne n)
        calc
          _ = (r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)-
              ((r.b n)⁻¹*r.b n)*(x n).2 := by rw [hb,one_mul]
          _ = _ := by ring
      _ ≤ (ℓ : ℝ)*B := mul_le_mul (r.inverse_bound n) hh (abs_nonneg _) ℓ.coe_nonneg
      _ ≤ B := (mul_le_mul_of_nonneg_right (show (ℓ : ℝ)≤1 from hℓ) hB).trans_eq (one_mul _)

lemma near_orbit_solution_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    {B : ℝ} (hB : 0≤B) (h0 : (x 0).1=s)
    (hstep : ∀ n, ‖x (n+1)-r.step n (x n)‖≤B) :
    ‖x-r.solution h s‖≤B/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  have hh := (perron_contracting r h (s := s)).dist_fixedPoint_le x
  rw [dist_eq_norm,dist_eq_norm] at hh
  change ‖x-r.solution h s‖≤_ at hh
  have hp := perron_defect_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)) h.le)
    s x hB h0 hstep
  rw [norm_sub_rev] at hp
  exact hh.trans (div_le_div_of_nonneg_right hp (sub_nonneg.mpr (show ((ℓ+δ : ℝ≥0) : ℝ)≤1 from h.le)))

noncomputable def LocalRecurrence.linearized (r : LocalRecurrence ℓ δ)
    (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ) : Recurrence ℓ δ where
  a := r.a
  b := r.b
  remainder n := D n
  stable_bound := r.stable_bound
  inverse_bound := r.inverse_bound
  b_ne := r.b_ne
  lipschitz n := LipschitzWith.of_dist_le_mul fun v w => by
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((D n).le_opNorm (v-w)).trans (mul_le_mul_of_nonneg_right (hD n) (norm_nonneg _))
  zero n := map_zero _

lemma linearized_step_smul (r : LocalRecurrence ℓ δ) (D : ℕ → Plane →L[ℝ] Plane)
    (hD : ∀ n, ‖D n‖≤δ) (n : ℕ) (t : ℝ) (v : Plane) :
    (r.linearized D hD).step n (t • v)=t • (r.linearized D hD).step n v := by
  apply Prod.ext <;> simp only [LocalRecurrence.linearized,Recurrence.step,Prod.smul_fst,Prod.smul_snd,
    map_smul,smul_eq_mul] <;> ring

lemma linearized_solution_smul (r : LocalRecurrence ℓ δ) (D : ℕ → Plane →L[ℝ] Plane)
    (hD : ∀ n, ‖D n‖≤δ) (h : ℓ+δ<1) (t : ℝ) :
    (r.linearized D hD).solution h t=t • (r.linearized D hD).solution h 1 := by
  symm
  apply solution_unique
  · change (t • (r.linearized D hD).solution h 1 0).1=t
    rw [Prod.smul_fst,solution_initial,smul_eq_mul,mul_one]
  · intro n
    change t • (r.linearized D hD).solution h 1 (n+1)=
      (r.linearized D hD).step n (t • (r.linearized D hD).solution h 1 n)
    rw [solution_orbit,linearized_step_smul]

lemma hasDerivAt_of_quadratic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {v : E} {x C : ℝ} (hC : 0≤C)
    (h : ∀ᶠ y in 𝓝 x, ‖f y-f x-(y-x) • v‖≤C*|y-x|^2) : HasDerivAt f v x := by
  rw [hasDerivAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  have he : 0<ε/(C+1) := div_pos hε (by linarith)
  have hsmall : ∀ᶠ y in 𝓝 x, |y-x|<ε/(C+1) := by
    filter_upwards [Metric.ball_mem_nhds x he] with y hy
    simpa only [Metric.mem_ball,Real.dist_eq] using hy
  filter_upwards [h,hsmall] with y hy hys
  rw [Real.norm_eq_abs]
  apply hy.trans
  have hb : C*|y-x|≤ε := by
    have hh := (lt_div_iff₀ (show 0<C+1 by linarith)).mp hys
    nlinarith [abs_nonneg (y-x)]
  calc
    _ = (C*|y-x|)*|y-x| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (abs_nonneg _)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma quadratic_taylor_of_derivative_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F) (hD : ∀ x, HasFDerivAt f (D x) x)
    {M : ℝ} (hM : 0≤M) (hLip : ∀ x y, ‖D x-D y‖≤M*‖x-y‖) (v w : E) :
    ‖f w-f v-D v (w-v)‖≤M*‖w-v‖^2 := by
  let g : E → F := fun x => f x-f v-D v (x-v)
  have hg (x : E) : HasFDerivAt g (D x-D v) x := by
    have hh := ((hD x).sub_const (f v)).sub ((D v).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const v))
    convert! hh using 1
  have hlocal (x : E) (hx : x∈Metric.closedBall v ‖w-v‖) : ‖D x-D v‖≤M*‖w-v‖ := by
    refine (hLip x v).trans (mul_le_mul_of_nonneg_left ?_ hM)
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
  have hh := (convex_closedBall v ‖w-v‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hg x).hasFDerivWithinAt) hlocal
    (show v∈Metric.closedBall v ‖w-v‖ by simpa only [Metric.mem_closedBall,dist_self] using norm_nonneg (w-v))
    (show w∈Metric.closedBall v ‖w-v‖ by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl])
  simpa only [g,sub_self,map_zero,sub_zero,pow_two,mul_assoc] using hh

noncomputable def flatRemainderDerivative (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v : RealPlane) : RealPlane →L[ℝ] RealPlane :=
  C.comp ((standardDerivative k (complexProjection (z+F v))-standardDerivative k (complexProjection z)).comp F)
lemma hasFDerivAt_flatRemainder (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v : RealPlane) :
    HasFDerivAt (flatRemainder k z F C) (flatRemainderDerivative k z F C v) v := by
  exact C.hasFDerivAt.comp v ((hasFDerivAt_liftRemainder k z (F v)).comp v F.hasFDerivAt)
@[simp] lemma flatRemainderDerivative_zero (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) : flatRemainderDerivative k z F C 0=0 := by
  simp only [flatRemainderDerivative,map_zero,add_zero,sub_self,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero]

lemma flatRemainderDerivative_lipschitz (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v w : RealPlane) :
    ‖flatRemainderDerivative k z F C v-flatRemainderDerivative k z F C w‖≤
      (‖C‖*derivativeVariationBound k*‖F‖^2)*‖v-w‖ := by
  have he : flatRemainderDerivative k z F C v-flatRemainderDerivative k z F C w=
      C.comp ((standardDerivative k (complexProjection (z+F v))-
        standardDerivative k (complexProjection (z+F w))).comp F) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [flatRemainderDerivative,sub_apply,ContinuousLinearMap.comp_apply,map_sub]
    abel
  have hd := standardDerivative_lift_sub_bound k (z+F v) (z+F w)
  rw [add_sub_add_left_eq_sub,←map_sub] at hd
  have hd' := hd.trans (mul_le_mul_of_nonneg_left (F.le_opNorm (v-w)) (derivativeVariationBound_nonneg k))
  rw [he]
  calc
    _ ≤ ‖C‖*‖(standardDerivative k (complexProjection (z+F v))-
      standardDerivative k (complexProjection (z+F w))).comp F‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖C‖*(‖standardDerivative k (complexProjection (z+F v))-
        standardDerivative k (complexProjection (z+F w))‖*‖F‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg C)
    _ ≤ ‖C‖*((derivativeVariationBound k*(‖F‖*‖v-w‖))*‖F‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd' (norm_nonneg F)) (norm_nonneg C)
    _ = _ := by ring

noncomputable def actualChartRemainderDerivative (k χ : ℝ) (z : ℂ) : RealPlane → RealPlane →L[ℝ] RealPlane :=
  flatRemainderDerivative k z (actualChartFrame k χ (complexProjection z))
    (actualChartInverse k χ (standardMap k (complexProjection z)))
lemma hasFDerivAt_actualChartRemainder (k χ : ℝ) (z : ℂ) (v : RealPlane) :
    HasFDerivAt (actualChartRemainder k χ z) (actualChartRemainderDerivative k χ z v) v :=
  hasFDerivAt_flatRemainder _ _ _ _ _
@[simp] lemma actualChartRemainderDerivative_zero (k χ : ℝ) (z : ℂ) : actualChartRemainderDerivative k χ z 0=0 :=
  flatRemainderDerivative_zero _ _ _ _
lemma actualChartRemainderDerivative_lipschitz (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : ℂ)
    (hz : RegularChartPoint k χ (complexProjection z))
    (hn : RegularChartPoint k χ (standardMap k (complexProjection z))) (v w : RealPlane) :
    ‖actualChartRemainderDerivative k χ z v-actualChartRemainderDerivative k χ z w‖≤
      hyperbolicChartError χ*‖v-w‖ :=
  (flatRemainderDerivative_lipschitz k z _ _ v w).trans
    (mul_le_mul_of_nonneg_right (chart_nonlinearity_coefficient k hχ _ hz hn) (norm_nonneg _))
lemma actualChartRemainderDerivative_bound (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : ℂ)
    (hz : RegularChartPoint k χ (complexProjection z))
    (hn : RegularChartPoint k χ (standardMap k (complexProjection z)))
    {v : RealPlane} (hv : ‖v‖≤1) : ‖actualChartRemainderDerivative k χ z v‖≤hyperbolicChartError χ := by
  have hh := actualChartRemainderDerivative_lipschitz k hχ z hz hn v 0
  simp only [actualChartRemainderDerivative_zero,sub_zero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hv (hyperbolicChartError_pos hχ).le).trans_eq (mul_one _))
lemma actualChartRemainder_taylor (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : ℂ)
    (hz : RegularChartPoint k χ (complexProjection z))
    (hn : RegularChartPoint k χ (standardMap k (complexProjection z))) (v w : RealPlane) :
    ‖actualChartRemainder k χ z w-actualChartRemainder k χ z v-
      actualChartRemainderDerivative k χ z v (w-v)‖≤hyperbolicChartError χ*‖w-v‖^2 :=
  quadratic_taylor_of_derivative_lipschitz _ _ (hasFDerivAt_actualChartRemainder k χ z)
    (hyperbolicChartError_pos hχ).le (actualChartRemainderDerivative_lipschitz k hχ z hz hn) v w
lemma actualChartRemainder_quadratic (k : ℝ) {χ : ℝ} (hχ : 0<χ) (z : ℂ)
    (hz : RegularChartPoint k χ (complexProjection z))
    (hn : RegularChartPoint k χ (standardMap k (complexProjection z))) (v : RealPlane) :
    ‖actualChartRemainder k χ z v‖≤hyperbolicChartError χ*‖v‖^2 := by
  simpa only [actualChartRemainder_zero,actualChartRemainderDerivative_zero,zero_apply,sub_zero] using
    actualChartRemainder_taylor k hχ z hz hn 0 v

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter Set
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma linearized_difference_residual (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ)
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    (r.extend.solution h t-r.extend.solution h s) (n+1)-
      (r.linearized D hD).step n ((r.extend.solution h t-r.extend.solution h s) n) =
      r.remainder n (r.extend.solution h t n)-r.remainder n (r.extend.solution h s n)-
        D n (r.extend.solution h t n-r.extend.solution h s n) := by
  simp only [BoundedContinuousFunction.sub_apply,local_solution_orbit r h hs,local_solution_orbit r h ht]
  apply Prod.ext <;> simp only [Prod.fst_sub,Prod.snd_sub,LocalRecurrence.step,LocalRecurrence.linearized,Recurrence.step] <;> ring

lemma solution_quadratic_approximation (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ)
    {M : ℝ} (hM : 0≤M) {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1)
    (hTaylor : ∀ n, ‖r.remainder n (r.extend.solution h t n)-r.remainder n (r.extend.solution h s n)-
        D n (r.extend.solution h t n-r.extend.solution h s n)‖≤
      M*‖r.extend.solution h t n-r.extend.solution h s n‖^2) :
    ‖r.extend.solution h t-r.extend.solution h s-(t-s) • (r.linearized D hD).solution h 1‖≤
      (M/(1-((ℓ+δ : ℝ≥0) : ℝ)))*|t-s|^2 := by
  have hstep (n : ℕ) : ‖(r.extend.solution h t-r.extend.solution h s) (n+1)-
      (r.linearized D hD).step n ((r.extend.solution h t-r.extend.solution h s) n)‖≤M*|t-s|^2 := by
    rw [linearized_difference_residual r h D hD hs ht n]
    apply (hTaylor n).trans
    apply mul_le_mul_of_nonneg_left _ hM
    exact pow_le_pow_left₀ (norm_nonneg _) ((point_sub_bound _ _ n).trans (solution_lipschitz r.extend h t s)) 2
  have h0 : ((r.extend.solution h t-r.extend.solution h s) 0).1=t-s := by
    simp only [BoundedContinuousFunction.sub_apply,Prod.fst_sub,solution_initial]
  have hh := near_orbit_solution_bound (r.linearized D hD) h (t-s) (r.extend.solution h t-r.extend.solution h s)
    (mul_nonneg hM (sq_nonneg _)) h0 hstep
  rw [linearized_solution_smul] at hh
  exact hh.trans_eq (by ring)

noncomputable def graphLinearization (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ) (s : ℝ) (hs : |s|≤1) : Sequence :=
  (r.linearized (fun n => D n (r.extend.solution h s n))
    (fun n => hD n _ (local_solution_bound r h hs n))).solution h 1

lemma solution_hasDerivAt (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    {s : ℝ} (hs : |s|<1) :
    HasDerivAt (r.extend.solution h) (graphLinearization r h D hD s hs.le) s := by
  apply hasDerivAt_of_quadratic_bound (div_nonneg hM (sub_nonneg.mpr (show ((ℓ+δ : ℝ≥0) : ℝ)≤1 from h.le)))
  have hnear : Ioo (-1 : ℝ) 1∈𝓝 s := isOpen_Ioo.mem_nhds (abs_lt.mp hs)
  filter_upwards [hnear] with t ht
  have ht' : |t|≤1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
  exact solution_quadratic_approximation r h _ _ hM hs.le ht'
    (fun n => hTaylor n _ _ (local_solution_bound r h hs.le n) (local_solution_bound r h ht' n))

noncomputable def sequenceEval (n : ℕ) : Sequence →L[ℝ] Plane :=
  ({ toFun := fun x => x n
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Sequence →ₗ[ℝ] Plane).mkContinuous 1
      (fun x => by change ‖x n‖≤1*‖x‖; simpa only [one_mul] using x.norm_coe_le_norm n)
@[simp] lemma sequenceEval_apply (n : ℕ) (x : Sequence) : sequenceEval n x=x n := rfl

lemma graph_hasDerivAt (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    {s : ℝ} (hs : |s|<1) :
    HasDerivAt (r.extend.graph h) (graphLinearization r h D hD s hs.le 0).2 s := by
  have hh := ((sequenceEval 0).hasFDerivAt.comp_hasDerivAt s (solution_hasDerivAt r h D hD hM hTaylor hs)).snd
  exact hh

lemma linearized_difference_of_fields (r : LocalRecurrence ℓ δ)
    (D E : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ) (hE : ∀ n, ‖E n‖≤δ)
    (n : ℕ) (v : Plane) :
    (r.linearized D hD).step n v-(r.linearized E hE).step n v=(D n-E n) v := by
  apply Prod.ext <;> simp only [LocalRecurrence.linearized,Recurrence.step,Prod.fst_sub,Prod.snd_sub,
    sub_apply] <;> ring

lemma linearized_solution_field_bound (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D E : ℕ → Plane →L[ℝ] Plane) (hD : ∀ n, ‖D n‖≤δ) (hE : ∀ n, ‖E n‖≤δ)
    {B : ℝ} (hB : 0≤B) (hDE : ∀ n, ‖D n-E n‖≤B) :
    ‖(r.linearized D hD).solution h 1-(r.linearized E hE).solution h 1‖≤B/(1-((ℓ+δ : ℝ≥0) : ℝ)) := by
  apply near_orbit_solution_bound _ h 1 _ hB (solution_initial _ h 1)
  intro n
  rw [solution_orbit,linearized_difference_of_fields]
  have hn : ‖(r.linearized D hD).solution h 1 n‖≤1 :=
    ((r.linearized D hD).solution h 1).norm_coe_le_norm n |>.trans (by simpa using solution_norm_bound _ h 1)
  calc
    _ ≤ ‖D n-E n‖*‖(r.linearized D hD).solution h 1 n‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ B*1 := mul_le_mul (hDE n) hn (norm_nonneg _) hB
    _ = _ := mul_one _

lemma graphLinearization_lipschitz (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hLip : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 → ‖D n v-D n w‖≤M*‖v-w‖)
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) :
    ‖graphLinearization r h D hD s hs-graphLinearization r h D hD t ht‖≤
      (M/(1-((ℓ+δ : ℝ≥0) : ℝ)))*|s-t| := by
  have hfields (n : ℕ) : ‖D n (r.extend.solution h s n)-D n (r.extend.solution h t n)‖≤M*|s-t| :=
    (hLip n _ _ (local_solution_bound r h hs n) (local_solution_bound r h ht n)).trans
      (mul_le_mul_of_nonneg_left ((point_sub_bound _ _ n).trans (solution_lipschitz _ h s t)) hM)
  exact (linearized_solution_field_bound r h _ _ _ _ (mul_nonneg hM (abs_nonneg _)) hfields).trans_eq (by ring)

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter Set
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

lemma graph_deriv_lipschitzOn (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    (hLip : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 → ‖D n v-D n w‖≤M*‖v-w‖) :
    LipschitzOnWith ⟨M/(1-((ℓ+δ : ℝ≥0) : ℝ)),
      div_nonneg hM (sub_nonneg.mpr (show ((ℓ+δ : ℝ≥0) : ℝ)≤1 by exact_mod_cast h.le))⟩
      (deriv (r.extend.graph h)) (Ioo (-1 : ℝ) 1) := by
  refine lipschitzOnWith_iff_norm_sub_le.mpr ?_
  intro s hs t ht
  have hs' : |s|<1 := abs_lt.mpr hs
  have ht' : |t|<1 := abs_lt.mpr ht
  rw [(graph_hasDerivAt r h D hD hM hTaylor hs').deriv,
    (graph_hasDerivAt r h D hD hM hTaylor ht').deriv]
  exact (norm_snd_le _).trans ((point_sub_bound _ _ 0).trans
    (graphLinearization_lipschitz r h D hD hM hLip hs'.le ht'.le))

lemma graph_contDiffOn (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    (D : ℕ → Plane → Plane →L[ℝ] Plane)
    (hD : ∀ n v, ‖v‖≤1 → ‖D n v‖≤δ)
    {M : ℝ} (hM : 0≤M)
    (hTaylor : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 →
      ‖r.remainder n w-r.remainder n v-D n v (w-v)‖≤M*‖w-v‖^2)
    (hLip : ∀ n v w, ‖v‖≤1 → ‖w‖≤1 → ‖D n v-D n w‖≤M*‖v-w‖) :
    ContDiffOn ℝ 1 (r.extend.graph h) (Ioo (-1 : ℝ) 1) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  refine ⟨fun s hs => (graph_hasDerivAt r h D hD hM hTaylor (abs_lt.mpr hs)).differentiableAt.differentiableWithinAt, ?_⟩
  exact (graph_deriv_lipschitzOn r h D hD hM hTaylor hLip).continuousOn.congr
    (fun s hs => derivWithin_of_isOpen isOpen_Ioo hs)

lemma graph_hasDerivAt_zero (r : LocalRecurrence ℓ δ) (h : ℓ+δ<1)
    {B : ℝ} (hB : 0≤B)
    (hr : ∀ n (v : Plane), ‖v‖≤1 → ‖r.remainder n v‖≤B*‖v‖^2) :
    HasDerivAt (r.extend.graph h) 0 0 := by
  apply hasDerivAt_of_quadratic_bound (div_nonneg (mul_nonneg ℓ.coe_nonneg hB)
    (sub_nonneg.mpr (linearRate_lt_one h).le))
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ)∈Ioo (-1 : ℝ) 1 by constructor <;> norm_num)] with s hs
  simpa only [graph_zero,smul_zero,sub_zero,Real.norm_eq_abs] using
    local_graph_quadratic_bound r h hB hr (le_of_lt (abs_lt.mpr hs))

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def actualStableGraph (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) : ℝ → ℝ :=
  (actualLocalRecurrence k χ hχ w hw).extend.graph (chart_rates_contract hχ)
noncomputable def actualStableCurve (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) : ℝ → ℂ :=
  fun s => w+actualChartFrame k χ (complexProjection w) (s,actualStableGraph k χ hχ w hw s)

lemma actualStableGraph_contDiffOn (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) :
    ContDiffOn ℝ 1 (actualStableGraph k χ hχ w hw) (Ioo (-1 : ℝ) 1) := by
  apply graph_contDiffOn (actualLocalRecurrence k χ hχ w hw) (chart_rates_contract hχ)
    (fun n => actualChartRemainderDerivative k χ ((standardLift k)^[n] w))
    (fun n v hv => actualChartRemainderDerivative_bound k hχ _ (hw n) (regular_lift_next k χ w hw n) hv)
    (hyperbolicChartError_pos hχ).le
  · intro n v u _ _
    exact actualChartRemainder_taylor k hχ _ (hw n) (regular_lift_next k χ w hw n) v u
  · intro n v u _ _
    exact actualChartRemainderDerivative_lipschitz k hχ _ (hw n) (regular_lift_next k χ w hw n) v u

lemma actualStableGraph_hasDerivAt_zero (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) :
    HasDerivAt (actualStableGraph k χ hχ w hw) 0 0 := by
  exact graph_hasDerivAt_zero (actualLocalRecurrence k χ hχ w hw) (chart_rates_contract hχ)
    (hyperbolicChartError_pos hχ).le
    (fun n v _ => actualChartRemainder_quadratic k hχ _ (hw n) (regular_lift_next k χ w hw n) v)

lemma actualStableCurve_contDiffOn (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) :
    ContDiffOn ℝ 1 (actualStableCurve k χ hχ w hw) (Ioo (-1 : ℝ) 1) := by
  exact contDiffOn_const.add ((actualChartFrame k χ (complexProjection w)).contDiff.comp_contDiffOn
    (contDiffOn_id.prodMk (actualStableGraph_contDiffOn k χ hχ w hw)))

lemma actualStableCurve_hasDerivAt_zero (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w))) :
    HasDerivAt (actualStableCurve k χ hχ w hw)
      (actualChartFrame k χ (complexProjection w) (1,0)) 0 :=
  HasDerivAt.const_add w ((actualChartFrame k χ (complexProjection w)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).prodMk (actualStableGraph_hasDerivAt_zero k χ hχ w hw)))

lemma actualStableCurve_regular (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|<1) : deriv (actualStableCurve k χ hχ w hw) s≠0 := by
  have hg := (actualStableGraph_contDiffOn k χ hχ w hw).differentiableOn (by norm_num)
    s (abs_lt.mp hs)
  have hg' := (hg.differentiableAt (isOpen_Ioo.mem_nhds (abs_lt.mp hs))).hasDerivAt
  have hd := HasDerivAt.const_add w ((actualChartFrame k χ (complexProjection w)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk hg'))
  have hd' : HasDerivAt (actualStableCurve k χ hχ w hw)
      (actualChartFrame k χ (complexProjection w) (1,deriv (actualStableGraph k χ hχ w hw) s)) s := hd
  rw [hd'.deriv]
  intro he
  have hw0 : RegularChartPoint k χ (complexProjection w) := hw 0
  have hi := congrArg (actualChartInverse k χ (complexProjection w)) he
  rw [actualChartInverse_frame k hχ _ hw0.1,map_zero] at hi
  have hi' := congrArg Prod.fst hi
  exact one_ne_zero hi'

lemma actualStableFrame_tangent (k χ : ℝ) (w : ℂ) :
    actualChartFrame k χ (complexProjection w) (1,0)=
      (chartSize k χ (complexProjection w)/(2*stableScale k χ (complexProjection w))) •
        stableVector k (complexProjection w) := by
  simp only [actualChartFrame,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,
    pairToComplex_apply,lyapunovFrame,planeFrame_apply,zero_smul,add_zero,smul_smul,
    div_eq_mul_inv,one_mul,zero_mul]

lemma actualStableCurve_orbit (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w)))
    {s : ℝ} (hs : |s|≤1) (n : ℕ) :
    (standardLift k)^[n] (actualStableCurve k χ hχ w hw s)=(standardLift k)^[n] w+
      actualChartFrame k χ (complexProjection ((standardLift k)^[n] w))
        ((actualLocalRecurrence k χ hχ w hw).extend.solution (chart_rates_contract hχ) s n) := by
  have hi : (actualLocalRecurrence k χ hχ w hw).extend.solution (chart_rates_contract hχ) s 0=
      (s,actualStableGraph k χ hχ w hw s) := Prod.ext (solution_initial _ _ s) rfl
  simpa only [hi,actualStableCurve] using actual_local_orbit_lift k χ hχ w hw
    ((actualLocalRecurrence k χ hχ w hw).extend.solution (chart_rates_contract hχ) s)
    (local_solution_orbit _ _ hs) n

lemma actualStableCurve_contraction (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w)))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardLift k)^[n] (actualStableCurve k χ hχ w hw s)-
      (standardLift k)^[n] (actualStableCurve k χ hχ w hw t)‖≤
      (2*hyperbolicChartScale k χ)*(hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t| := by
  rw [actualStableCurve_orbit k χ hχ w hw hs,actualStableCurve_orbit k χ hχ w hw ht,
    add_sub_add_left_eq_sub,←map_sub]
  have hn : ‖actualChartFrame k χ (complexProjection ((standardLift k)^[n] w))‖≤2*hyperbolicChartScale k χ :=
    (actualChartFrame_norm_le k hχ _).trans (mul_le_mul_of_nonneg_left (chartSize_le_scale k hχ _) (by norm_num))
  have hx := solution_exponential_contraction (actualLocalRecurrence k χ hχ w hw).extend (chart_rates_contract hχ) s t n
  exact ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hn hx (norm_nonneg _)
    (by linarith [hyperbolicChartScale_pos k hχ]))).trans_eq (by
      change (2*hyperbolicChartScale k χ)*((hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t|)=_; ring)

theorem ae_actual_stable_C1 (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0<χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ), ∀ w : ℂ, complexProjection w=z →
      ∃ γ : ℝ → ℂ, γ 0=w ∧ ContDiffOn ℝ 1 γ (Ioo (-1 : ℝ) 1) ∧
        HasDerivAt γ ((chartSize k χ z/(2*stableScale k χ z)) • stableVector k z) 0 ∧
        (∀ s : ℝ, |s|<1 → deriv γ s≠0) ∧
        (∀ s t : ℝ, |s|≤1 → |t|≤1 → ∀ n : ℕ,
          ‖(standardLift k)^[n] (γ s)-(standardLift k)^[n] (γ t)‖≤
            (2*hyperbolicChartScale k χ)*(hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t|) := by
  filter_upwards [ae_regularChartPoint_all_iterates k hk hχ] with z hz
  intro w hw
  have hr (n : ℕ) : RegularChartPoint k χ (complexProjection ((standardLift k)^[n] w)) := by
    simpa only [complexProjection_iterate,hw] using (hz n).1
  refine ⟨actualStableCurve k χ hχ w hr,?_,actualStableCurve_contDiffOn k χ hχ w hr,?_,
    fun s hs => actualStableCurve_regular k χ hχ w hr hs,fun s t hs ht n => actualStableCurve_contraction k χ hχ w hr hs ht n⟩
  · simp only [actualStableCurve,actualStableGraph,graph_zero,Prod.mk_zero_zero,map_zero,add_zero]
  · have hd := actualStableCurve_hasDerivAt_zero k χ hχ w hr
    rw [actualStableFrame_tangent] at hd
    simpa only [hw] using hd

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

@[simp] lemma standardReversal_involutive (z : Torus) : standardReversal (standardReversal z)=z := by
  apply Prod.ext <;> simp
@[simp] lemma complexProjection_tangentReversal (w : ℂ) :
    complexProjection (tangentReversal w)=standardReversal (complexProjection w) := by
  apply Prod.ext <;> simp [complexProjection]
lemma tangentReversal_inverseLift (k : ℝ) (w : ℂ) :
    tangentReversal (standardInverseLift k w)=standardLift k (tangentReversal w) := by
  apply Complex.ext <;> simp [standardInverseLift,standardLift] <;> ring
lemma tangentReversal_inverse_lift_iterate (k : ℝ) (n : ℕ) (w : ℂ) :
    tangentReversal ((standardInverseLift k)^[n] w)=(standardLift k)^[n] (tangentReversal w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',tangentReversal_inverseLift,ih,Function.iterate_succ_apply']
lemma inverse_lift_iterate_reversed (k : ℝ) (n : ℕ) (w : ℂ) :
    (standardInverseLift k)^[n] (tangentReversal w)=tangentReversal ((standardLift k)^[n] w) := by
  have hh := congrArg tangentReversal (tangentReversal_inverse_lift_iterate k n (tangentReversal w))
  simpa only [tangentReversal_involutive] using hh
lemma tangentReversal_norm_le (w : ℂ) : ‖tangentReversal w‖≤3*‖w‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (tangentReversal w)
  simp only [tangentReversal_re,tangentReversal_im,abs_neg] at hh
  have hh' := abs_sub w.re w.im
  have hr := Complex.abs_re_le_norm w
  have hi := Complex.abs_im_le_norm w
  linarith
lemma tangentReversal_ne_zero {w : ℂ} (hw : w≠0) : tangentReversal w≠0 := by
  intro he
  have hh := congrArg tangentReversal he
  exact hw (by simpa only [tangentReversal_involutive,map_zero] using hh)

lemma measurePreserving_reversal_spectralGapRegion (k : ℝ) (hk : 0≤k) (χ : ℝ) :
    MeasurePreserving standardReversal (area.restrict (spectralGapRegion k hk χ))
      (area.restrict (spectralGapRegion k hk χ)) := by
  have hh := measurePreserving_standardReversal.restrict_preimage (measurableSet_spectralGapRegion k hk χ)
  have he : standardReversal ⁻¹' spectralGapRegion k hk χ =ᵐ[area] spectralGapRegion k hk χ := by
    filter_upwards [standardLyapunov_reversal_ae k hk] with z hz
    change (χ<standardLyapunov k hk (standardReversal z))=(χ<standardLyapunov k hk z)
    rw [hz]
  rwa [Measure.restrict_congr_set he] at hh

lemma ae_stableVector_reversal_unstable (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0<standardLyapunov k hk z →
      wedge (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))=0 := by
  filter_upwards [standardLyapunov_reversal_ae k hk,ae_unstableVector_growth k hk,
    measurePreserving_standardReversal.quasiMeasurePreserving.ae (ae_stableVector_growth k hk)] with z he hu hs hp
  have hu0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardInverseDerivativeProduct_area k z) (hu hp) (by linarith)
  have hs0 := PlaneLyapunov.norm_tendsto_zero_of_negative_growth _
    (standardDerivativeProduct_area k (standardReversal z)) (hs (by rwa [he])) (by rw [he]; linarith)
  apply contracting_wedge_zero _ (standardInverseDerivativeProduct_area k z) hu0
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa only [mul_zero] using Tendsto.const_mul 3 hs0)
  rw [standardInverseDerivativeProduct_conjugate]
  simp only [ContinuousLinearMap.comp_apply,tangentReversal_involutive]
  exact tangentReversal_norm_le _

lemma ae_reversal_tangent_transverse (k : ℝ) (hk : 0≤k) :
    ∀ᵐ z ∂area, 0<standardLyapunov k hk z →
      wedge (stableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 := by
  filter_upwards [ae_stableVector_reversal_unstable k hk,ae_transverseLines k hk] with z hu hs hp
  have he := unit_collinear_eq_smul (norm_unstableVector k z) (hu hp)
  have hc : dot (unstableVector k z) (tangentReversal (stableVector k (standardReversal z)))≠0 := by
    intro hz
    rw [hz,zero_smul] at he
    exact tangentReversal_ne_zero (stableVector_ne_zero k _) he
  rw [he,wedge_smul_right]
  exact mul_ne_zero hc (hs hp)

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def actualUnstableCurve (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] (tangentReversal w)))) : ℝ → ℂ :=
  fun s => tangentReversal (actualStableCurve k χ hχ (tangentReversal w) hw s)

lemma actualUnstableCurve_contDiffOn (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] (tangentReversal w)))) :
    ContDiffOn ℝ 1 (actualUnstableCurve k χ hχ w hw) (Ioo (-1 : ℝ) 1) :=
  tangentReversal.contDiff.comp_contDiffOn (actualStableCurve_contDiffOn k χ hχ (tangentReversal w) hw)
lemma actualUnstableCurve_hasDerivAt_zero (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] (tangentReversal w)))) :
    HasDerivAt (actualUnstableCurve k χ hχ w hw)
      ((chartSize k χ (standardReversal (complexProjection w))/(2*stableScale k χ (standardReversal (complexProjection w)))) •
        tangentReversal (stableVector k (standardReversal (complexProjection w)))) 0 := by
  have hh := tangentReversal.hasFDerivAt.comp_hasDerivAt 0 (actualStableCurve_hasDerivAt_zero k χ hχ (tangentReversal w) hw)
  rw [actualStableFrame_tangent,complexProjection_tangentReversal,map_smul] at hh
  exact hh
lemma actualUnstableCurve_regular (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s : ℝ} (hs : |s|<1) : deriv (actualUnstableCurve k χ hχ w hw) s≠0 := by
  have hd := ((actualStableCurve_contDiffOn k χ hχ (tangentReversal w) hw).differentiableOn (by norm_num)
    s (abs_lt.mp hs)).differentiableAt (isOpen_Ioo.mem_nhds (abs_lt.mp hs))
  have hh : HasDerivAt (actualUnstableCurve k χ hχ w hw)
      (tangentReversal (deriv (actualStableCurve k χ hχ (tangentReversal w) hw) s)) s :=
    tangentReversal.hasFDerivAt.comp_hasDerivAt s hd.hasDerivAt
  rw [hh.deriv]
  exact tangentReversal_ne_zero (actualStableCurve_regular k χ hχ (tangentReversal w) hw hs)
lemma actualUnstableCurve_contraction (k χ : ℝ) (hχ : 0<χ) (w : ℂ)
    (hw : ∀ n : ℕ, RegularChartPoint k χ (complexProjection ((standardLift k)^[n] (tangentReversal w))))
    {s t : ℝ} (hs : |s|≤1) (ht : |t|≤1) (n : ℕ) :
    ‖(standardInverseLift k)^[n] (actualUnstableCurve k χ hχ w hw s)-
      (standardInverseLift k)^[n] (actualUnstableCurve k χ hχ w hw t)‖≤
      (6*hyperbolicChartScale k χ)*(hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t| := by
  simp only [actualUnstableCurve,inverse_lift_iterate_reversed,←map_sub]
  exact ((tangentReversal_norm_le _).trans (mul_le_mul_of_nonneg_left
    (actualStableCurve_contraction k χ hχ (tangentReversal w) hw hs ht n) (by norm_num))).trans_eq (by ring)

theorem ae_actual_unstable_C1 (k : ℝ) (hk : 0≤k) (χ : ℝ) (hχ : 0<χ) :
    ∀ᵐ z ∂area.restrict (spectralGapRegion k hk χ), ∀ w : ℂ, complexProjection w=z →
      ∃ γ : ℝ → ℂ, γ 0=w ∧ ContDiffOn ℝ 1 γ (Ioo (-1 : ℝ) 1) ∧
        HasDerivAt γ ((chartSize k χ (standardReversal z)/(2*stableScale k χ (standardReversal z))) •
          tangentReversal (stableVector k (standardReversal z))) 0 ∧
        wedge (unstableVector k z) (deriv γ 0)=0 ∧
        (∀ s : ℝ, |s|<1 → deriv γ s≠0) ∧
        (∀ s t : ℝ, |s|≤1 → |t|≤1 → ∀ n : ℕ,
          ‖(standardInverseLift k)^[n] (γ s)-(standardInverseLift k)^[n] (γ t)‖≤
            (6*hyperbolicChartScale k χ)*(hyperbolicChartRate χ+hyperbolicChartError χ)^n*|s-t|) := by
  have hr := (measurePreserving_reversal_spectralGapRegion k hk χ).quasiMeasurePreserving.ae
    (ae_regularChartPoint_all_iterates k hk hχ)
  filter_upwards [hr,(ae_stableVector_reversal_unstable k hk).filter_mono ae_restrict_le,
    ae_restrict_mem (measurableSet_spectralGapRegion k hk χ)] with z hz hline hgap
  intro w hw
  have hreg (n : ℕ) : RegularChartPoint k χ (complexProjection ((standardLift k)^[n] (tangentReversal w))) := by
    simpa only [complexProjection_iterate,complexProjection_tangentReversal,hw] using (hz n).1
  have hd := actualUnstableCurve_hasDerivAt_zero k χ hχ w hreg
  rw [hw] at hd
  refine ⟨actualUnstableCurve k χ hχ w hreg,?_,actualUnstableCurve_contDiffOn k χ hχ w hreg,hd,?_,
    fun s hs => actualUnstableCurve_regular k χ hχ w hreg hs,
    fun s t hs ht n => actualUnstableCurve_contraction k χ hχ w hreg hs ht n⟩
  · simp only [actualUnstableCurve,actualStableCurve,actualStableGraph,graph_zero,
      Prod.mk_zero_zero,map_zero,add_zero,tangentReversal_involutive]
  · rw [hd.deriv,wedge_smul_right,hline (hχ.trans hgap),mul_zero]

end StandardMapEntropy

end
end

end OAI
