import Mathlib
import OAI.MathematicalPhysics.BFSS.RellichCompactness
import OAI.MathematicalPhysics.BFSS.SmallPatches

namespace OAI

/-! Weighted tightness and compactness in local and global L2. -/

namespace BFSSRellich
noncomputable section
open MeasureTheory Set
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

def compactLp (f : EuclideanSpace ℝ ι → H) (hf : Continuous f)
    (hK : HasCompactSupport f) : Lp H 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
  (hf.memLp_of_hasCompactSupport hK).toLp f

omit [InnerProductSpace ℝ H] in
lemma compactLp_ae (f : EuclideanSpace ℝ ι → H) (hf : Continuous f)
    (hK : HasCompactSupport f) : compactLp f hf hK =ᵐ[volume] f :=
  MemLp.coeFn_toLp _

omit [InnerProductSpace ℝ H] in
lemma compactLp_congr {f g : EuclideanSpace ℝ ι → H}
    {hf : Continuous f} {hg : Continuous g}
    {hF : HasCompactSupport f} {hG : HasCompactSupport g} (h : f = g) :
    compactLp f hf hF = compactLp g hg hG := by
  subst g
  rfl

lemma compactLp_dist_square (f g : EuclideanSpace ℝ ι → H)
    (hf : Continuous f) (hg : Continuous g)
    (hF : HasCompactSupport f) (hG : HasCompactSupport g) :
    dist (compactLp f hf hF) (compactLp g hg hG)^2 = ∫ x, ‖f x-g x‖^2 := by
  rw [dist_eq_norm, ←real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (compactLp f hf hF) (compactLp g hg hG),
    compactLp_ae f hf hF,compactLp_ae g hg hG] with x hs hf hg
  rw [hs,Pi.sub_apply,hf,hg,real_inner_self_eq_norm_sq]

lemma compactLp_norm_square (f : EuclideanSpace ℝ ι → H)
    (hf : Continuous f) (hF : HasCompactSupport f) :
    ‖compactLp f hf hF‖^2 = ∫ x, ‖f x‖^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactLp_ae f hf hF] with x hx
  rw [hx,real_inner_self_eq_norm_sq]

lemma totallyBounded_range_of_dist_le {J X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : J → X) (g : J → Y) {C : ℝ} (hC : 0 < C)
    (hd : ∀ i j, dist (f i) (f j) ≤ C*dist (g i) (g j))
    (hg : TotallyBounded (range g)) : TotallyBounded (range f) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t,htr,ht,htc⟩ := Metric.finite_approx_of_totallyBounded hg (ε/C) (div_pos hε hC)
  choose a ha using (fun y : t => htr y.property)
  let : Finite t := ht.to_subtype
  refine ⟨range (fun y : t => f (a y)),finite_range _,?_⟩
  rintro _ ⟨j,rfl⟩
  obtain ⟨y,hyt,hy⟩ := mem_iUnion₂.mp (htc (mem_range_self j))
  apply mem_iUnion₂.mpr
  refine ⟨f (a ⟨y,hyt⟩),mem_range_self _,?_⟩
  change dist (f j) (f (a ⟨y,hyt⟩)) < ε
  apply (hd j (a ⟨y,hyt⟩)).trans_lt
  rw [ha]
  exact (mul_lt_mul_of_pos_left hy hC).trans_eq (mul_div_cancel₀ ε hC.ne')

lemma compactLp_bump_dist_square_le (φ : ContDiffBump (0 : EuclideanSpace ℝ ι))
    (f g : EuclideanSpace ℝ ι → H) (hf : Continuous f) (hg : Continuous g)
    (hF : HasCompactSupport f) (hG : HasCompactSupport g) :
    dist (compactLp (fun x => φ x • f x) (φ.continuous.smul hf) hF.smul_left)
      (compactLp (fun x => φ x • g x) (φ.continuous.smul hg) hG.smul_left)^2 ≤
      ∫ x in Metric.closedBall 0 φ.rOut, ‖f x-g x‖^2 := by
  rw [compactLp_dist_square]
  have hs : Function.support (fun x => ‖φ x • f x - φ x • g x‖^2) ⊆ Metric.closedBall 0 φ.rOut := by
    intro x hx
    by_contra hn
    have hz := φ.zero_of_le_dist (le_of_lt (lt_of_not_ge (show ¬dist x 0 ≤ φ.rOut from hn)))
    exact hx (by simp [hz])
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ hx => by
    by_contra hn; exact hx (hs hn))]
  apply setIntegral_mono_on
    ((((φ.continuous.smul hf).sub (φ.continuous.smul hg)).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 φ.rOut))
    (((hf.sub hg).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 φ.rOut)) Metric.isClosed_closedBall.measurableSet
  intro x _
  change ‖φ x • f x - φ x • g x‖^2 ≤ ‖f x-g x‖^2
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg φ.nonneg,mul_pow]
  have hc : (φ x)^2 ≤ 1 := by nlinarith [φ.nonneg (x := x),φ.le_one (x := x)]
  nlinarith [sq_nonneg ‖f x-g x‖]

lemma compactLp_bump_error (φ : ContDiffBump (0 : EuclideanSpace ℝ ι))
    (f : EuclideanSpace ℝ ι → H) (hf : Continuous f) (hF : HasCompactSupport f) :
    φ.rIn^2 * dist (compactLp f hf hF)
      (compactLp (fun x => φ x • f x) (φ.continuous.smul hf) hF.smul_left)^2 ≤
      ∫ x, ‖x‖^2*‖f x‖^2 := by
  rw [compactLp_dist_square, ←integral_const_mul]
  have hi := BFSSNormalMeasure.square_integrable (μ := volume) _ (hf.sub (φ.continuous.smul hf))
    (hF.sub hF.smul_left)
  have hg : Integrable (fun x => ‖x‖^2*‖f x‖^2) :=
    ((continuous_norm.pow 2).mul (hf.norm.pow 2)).integrable_of_hasCompactSupport
      (BFSSNormalMeasure.square_compact f hF).mul_left
  apply integral_mono (hi.const_mul _) hg
  intro x
  change φ.rIn^2*‖f x-φ x • f x‖^2 ≤ ‖x‖^2*‖f x‖^2
  by_cases hx : ‖x‖ ≤ φ.rIn
  · have heq := φ.one_of_mem_closedBall (by simpa using hx)
    simp [heq]
    positivity
  · have hxr : φ.rIn^2 ≤ ‖x‖^2 := pow_le_pow_left₀ φ.rIn_pos.le (le_of_not_ge hx) 2
    have he : f x-φ x • f x = (1-φ x) • f x := by rw [sub_smul,one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr φ.le_one),mul_pow]
    have hs : (1-φ x)^2 ≤ 1 := by nlinarith [φ.nonneg (x := x),φ.le_one (x := x)]
    calc
      φ.rIn^2*((1-φ x)^2*‖f x‖^2) ≤ φ.rIn^2*‖f x‖^2 := by
        gcongr; nlinarith [sq_nonneg ‖f x‖]
      _ ≤ _ := mul_le_mul_of_nonneg_right hxr (sq_nonneg _)

lemma bump_family_totallyBounded {J : Type*}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ ι))
    (f : J → EuclideanSpace ℝ ι → H) (hf : ∀ j, Continuous (f j))
    (hF : ∀ j, HasCompactSupport (f j))
    (hlocal : TotallyBounded (range (fun j => localLp
      (K := Metric.closedBall 0 φ.rOut) (f j) (hf j)))) :
    TotallyBounded (range (fun j => compactLp (fun x => φ x • f j x)
      (φ.continuous.smul (hf j)) (hF j).smul_left)) := by
  classical
  apply totallyBounded_range_of_dist_le _ _ (C := 1) zero_lt_one _ hlocal
  intro i j
  rw [one_mul]
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  rw [localLp_dist_square]
  exact compactLp_bump_dist_square_le φ (f i) (f j) (hf i) (hf j) (hF i) (hF j)
end
end BFSSRellich
namespace BFSSRellich
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]

lemma compactLp_const_smul (a : ℝ) (f : EuclideanSpace ℝ ι → H)
    (hf : Continuous f) (hF : HasCompactSupport f) :
    compactLp (fun x => a • f x) (continuous_const.smul hf) hF.smul_left =
      a • compactLp f hf hF := MemLp.toLp_const_smul a _

lemma localLp_norm_square {K : Set (EuclideanSpace ℝ ι)} [CompactSpace K]
    (f : EuclideanSpace ℝ ι → H) (hf : Continuous f) :
    ‖localLp (K := K) f hf‖^2 = ∫ x in K, ‖f x‖^2 := by
  classical
  have hz : localLp (K := K) (fun _ => (0 : H)) continuous_const = 0 := by
    change (ContinuousMap.toLp 2 _ ℝ) 0 = 0
    exact map_zero _
  have he := localLp_dist_square (K := K) f (fun _ => 0) hf continuous_const
  simpa only [hz,dist_zero_right,sub_zero] using he

lemma totallyBounded_of_tail {X : Type*} [PseudoMetricSpace X] (f : ℕ → X) (k : ℕ)
    (h : TotallyBounded (range (fun n => f (n+k)))) : TotallyBounded (range f) := by
  apply ((Set.finite_Iio k).image f).totallyBounded.union h |>.subset
  rintro _ ⟨n,rfl⟩
  by_cases hn : n < k
  · exact Or.inl ⟨n,hn,rfl⟩
  · exact Or.inr ⟨n-k,congrArg f (Nat.sub_add_cancel (le_of_not_gt hn))⟩

lemma totallyBounded_of_eventual_approximation {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X)
    (h : ∀ ε > 0, ∃ g : ℕ → X, TotallyBounded (range g) ∧
      ∀ᶠ n in atTop, dist (f n) (g n) < ε) : TotallyBounded (range f) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨g,hg,hfg⟩ := h (ε/2) (half_pos hε)
  obtain ⟨k,hk⟩ := eventually_atTop.mp hfg
  obtain ⟨s,hs,hgs⟩ := Metric.totallyBounded_iff.mp hg (ε/2) (half_pos hε)
  refine ⟨(f '' Set.Iio k) ∪ s,((Set.finite_Iio k).image f).union hs,?_⟩
  rintro _ ⟨n,rfl⟩
  by_cases hn : n < k
  · exact mem_iUnion₂.mpr ⟨f n,Or.inl ⟨n,hn,rfl⟩,by simpa using hε⟩
  · obtain ⟨y,hys,hy⟩ := mem_iUnion₂.mp (hgs (mem_range_self n))
    exact mem_iUnion₂.mpr ⟨y,Or.inr hys,(dist_triangle _ _ _).trans_lt
      (by simpa using add_lt_add (hk n (le_of_not_gt hn)) hy)⟩

lemma weighted_bump_error (φ : ContDiffBump (0 : EuclideanSpace ℝ ι))
    (w : EuclideanSpace ℝ ι → ℝ) (hw : Continuous w) (a δ : ℝ)
    (u : EuclideanSpace ℝ ι → H) (hu : Continuous u) (hU : HasCompactSupport u)
    (_hδ : 0 ≤ δ) (hwδ : ∀ x ∈ Metric.closedBall 0 φ.rOut, |w x-a| ≤ δ) :
    dist (compactLp (fun x => φ x • (w x • u x)) (φ.continuous.smul (hw.smul hu)) hU.smul_left.smul_left)
      (compactLp (fun x => φ x • (a • u x)) (φ.continuous.smul (continuous_const.smul hu)) hU.smul_left.smul_left)^2 ≤
      δ^2*(∫ x in Metric.closedBall 0 φ.rOut, ‖u x‖^2) := by
  apply (compactLp_bump_dist_square_le φ _ _ (hw.smul hu)
    (continuous_const.smul hu) hU.smul_left hU.smul_left).trans
  rw [←integral_const_mul]
  apply setIntegral_mono_on
    ((((hw.smul hu).sub (continuous_const.smul hu)).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 φ.rOut))
    ((((hu.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 φ.rOut))).const_mul _)
    Metric.isClosed_closedBall.measurableSet
  intro x hx
  change ‖w x • u x-a • u x‖^2 ≤ δ^2*‖u x‖^2
  rw [←sub_smul,norm_smul,Real.norm_eq_abs,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hwδ x hx) 2) (sq_nonneg _)

lemma continuous_weight_uniform_small (w : EuclideanSpace ℝ ι → ℝ) (hw : Continuous w)
    {δ : ℝ} (hδ : 0 < δ) : ∃ η : ℝ, 0 < η ∧
      ∀ (h R : ℝ), |h| * R < η → ∀ x ∈ Metric.closedBall 0 R,
        |w (h • x)-w 0| ≤ δ := by
  obtain ⟨η,hη,he⟩ := Metric.continuousAt_iff.mp hw.continuousAt δ hδ
  refine ⟨η,hη,?_⟩
  intro h R hh x hx
  apply le_of_lt
  change dist (w (h • x)) (w 0) < δ
  apply he
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (by simpa using hx) (abs_nonneg h)).trans_lt hh

theorem weighted_tight_compactness
    (u : ℕ → EuclideanSpace ℝ ι → H) (hu : ∀ n, Continuous (u n))
    (hU : ∀ n, HasCompactSupport (u n))
    (w : EuclideanSpace ℝ ι → ℝ) (hw : Continuous w)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (nhds 0)) (C : ℝ≥0)
    (hmoment : ∀ n, (∫ x, ‖x‖^2*‖w (h n • x) • u n x‖^2) ≤ (C : ℝ)^2)
    (hlocal : ∀ R : ℝ, 0 < R → TotallyBounded (range (fun n =>
      localLp (K := Metric.closedBall 0 R) (u n) (hu n)))) :
    TotallyBounded (range (fun n => compactLp (fun x => w (h n • x) • u n x)
      ((hw.comp ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ ι => h n)).smul continuous_id)).smul (hu n)) (hU n).smul_left)) := by
  classical
  let v : ℕ → EuclideanSpace ℝ ι → H := fun n x => w (h n • x) • u n x
  have hv (n : ℕ) : Continuous (v n) :=
    (hw.comp ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ ι => h n)).smul continuous_id)).smul (hu n)
  have hV (n : ℕ) : HasCompactSupport (v n) := (hU n).smul_left
  apply totallyBounded_of_eventual_approximation
  intro ε hε
  let R : ℝ := ((C : ℝ)+1)/(ε/2)
  have hR : 0 < R := div_pos (by positivity) (half_pos hε)
  let φ : ContDiffBump (0 : EuclideanSpace ℝ ι) := ⟨R,2*R,hR,by linarith⟩
  let g : ℕ → Lp H 2 (volume : Measure (EuclideanSpace ℝ ι)) := fun n =>
    compactLp (fun x => (w 0) • (φ x • u n x))
      (continuous_const.smul (φ.continuous.smul (hu n))) (hU n).smul_left.smul_left
  have hgb : TotallyBounded (range g) := by
    have hb := bump_family_totallyBounded φ u hu hU (hlocal φ.rOut φ.rOut_pos)
    have hb' := hb.image (uniformContinuous_const_smul (w 0))
    rw [←Set.range_comp] at hb'
    simpa only [Function.comp_def,←compactLp_const_smul] using hb'
  obtain ⟨B,hB⟩ := (hlocal φ.rOut φ.rOut_pos).isBounded.exists_norm_le
  have huB (n : ℕ) : (∫ x in Metric.closedBall 0 φ.rOut, ‖u n x‖^2) ≤ (max B 0)^2 := by
    rw [←localLp_norm_square _ (hu n)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hB _ (mem_range_self n)).trans (le_max_left _ _)) 2
  let δ : ℝ := (ε/2)/(max B 0+1)
  have hδ : 0 < δ := div_pos (half_pos hε) (by positivity)
  obtain ⟨η,hη,hwη⟩ := continuous_weight_uniform_small w hw hδ
  have hsmall : ∀ᶠ n in atTop, |h n| * φ.rOut < η :=
    (hh.abs.mul_const φ.rOut).eventually (gt_mem_nhds (by simpa using hη))
  refine ⟨g,hgb,?_⟩
  filter_upwards [hsmall] with n hn
  let b := compactLp (fun x => φ x • v n x) (φ.continuous.smul (hv n)) (hV n).smul_left
  have htail : dist (compactLp (v n) (hv n) (hV n)) b < ε/2 := by
    have he := (compactLp_bump_error φ (v n) (hv n) (hV n)).trans (hmoment n)
    change R^2*dist (compactLp (v n) (hv n) (hV n)) b^2 ≤ (C : ℝ)^2 at he
    rw [←mul_pow] at he
    have hd := (sq_le_sq₀ (mul_nonneg hR.le dist_nonneg) C.coe_nonneg).mp he
    have hre : R*(ε/2) = (C : ℝ)+1 := div_mul_cancel₀ _ (half_pos hε).ne'
    nlinarith
  have hnear : dist b (g n) < ε/2 := by
    have he := weighted_bump_error φ (fun x => w (h n • x))
      (hw.comp ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ ι => h n)).smul continuous_id)) (w 0) δ
      (u n) (hu n) (hU n) hδ.le (hwη (h n) φ.rOut hn)
    have he' : dist b (g n)^2 ≤ δ^2*(max B 0)^2 := by
      apply le_trans _ (mul_le_mul_of_nonneg_left (huB n) (sq_nonneg δ))
      have hgdef : g n = compactLp (fun x => φ x • ((w 0) • u n x))
          (φ.continuous.smul (continuous_const.smul (hu n))) (hU n).smul_left.smul_left := by
        exact compactLp_congr (funext (fun _ => smul_comm _ _ _))
      rw [hgdef]
      exact he
    rw [←mul_pow] at he'
    have hd := (sq_le_sq₀ dist_nonneg (mul_nonneg hδ.le (le_max_right _ _))).mp he'
    have hdε : δ*(max B 0+1) = ε/2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  exact (dist_triangle _ b _).trans_lt (by simpa only [add_halves] using add_lt_add htail hnear)
end
end BFSSRellich

end OAI
