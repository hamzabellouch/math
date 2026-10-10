import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.SmoothODE
open Set Metric Filter
open scoped Topology ContDiff
noncomputable section

universe u
variable {K : Type*} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def superposition (V : E → F) (hV : Continuous V) (f : C(K, E)) : C(K, F) :=
  ⟨fun x => V (f x), hV.comp f.continuous⟩

def pathLinear (a : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun x => a x (f x), a.continuous.clm_apply f.continuous⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖a‖ (by
      intro f
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro x
      exact (a x).le_opNorm (f x) |>.trans
        (mul_le_mul (a.norm_coe_le_norm x) (f.norm_coe_le_norm x)
          (norm_nonneg (f x)) (norm_nonneg a)))

@[simp] theorem pathLinear_apply (a : C(K, E →L[ℝ] F)) (f : C(K, E)) (x : K) :
    pathLinear a f x = a x (f x) := rfl

def pathLinearCLM : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
  LinearMap.mkContinuous
    { toFun := pathLinear (K := K) (E := E) (F := F)
      map_add' := by intros; ext f x; simp
      map_smul' := by intros; ext f x; simp }
    1 (by
      intro a
      simp only [one_mul]
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (fun (f : C(K, E)) =>
        (ContinuousMap.norm_le _ (by positivity)).2 (fun x =>
          (a x).le_opNorm (f x) |>.trans
            (mul_le_mul (a.norm_coe_le_norm x) (f.norm_coe_le_norm x)
              (norm_nonneg (f x)) (norm_nonneg a)))))

theorem uniform_taylor [ProperSpace E] {V : E → F} (hV : ContDiff ℝ 1 V)
    (R : ℝ) (_hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x y : E, ‖x‖ ≤ R → ‖y - x‖ < δ →
      ‖V y - V x - fderiv ℝ V x (y - x)‖ ≤ ε * ‖y - x‖ := by
  have hd := (isCompact_closedBall (0 : E) (R + 1)).uniformContinuousOn_of_continuous
    (hV.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨a, ha, hU⟩ := Metric.uniformContinuousOn_iff.mp hd ε hε
  refine ⟨min 1 a, lt_min zero_lt_one ha, fun x y hx hy => ?_⟩
  have hxc : x ∈ closedBall (0 : E) (R + 1) := by
    simpa [mem_closedBall, dist_zero_right] using (show ‖x‖ ≤ R + 1 by linarith)
  have hbase : x ∈ ball x (min 1 a) := mem_ball_self (lt_min zero_lt_one ha)
  have hyy : y ∈ ball x (min 1 a) := by simpa [mem_ball, dist_eq_norm] using hy
  have hD : ∀ z ∈ ball x (min 1 a), ‖fderiv ℝ V z - fderiv ℝ V x‖ ≤ ε := by
    intro z hz
    have hz' : ‖z - x‖ < min 1 a := by simpa [mem_ball, dist_eq_norm] using hz
    have hzc : z ∈ closedBall (0 : E) (R + 1) := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ ‖x‖ + ‖z - x‖ := norm_le_insert' z x
           _ ≤ R + 1 := by linarith [lt_of_lt_of_le hz' (min_le_left 1 a)]
    exact le_of_lt (by simpa [dist_eq_norm] using (hU z hzc x hxc
      (show dist z x < a by simpa [dist_eq_norm] using lt_of_lt_of_le hz' (min_le_right 1 a))))
  have hM := (convex_ball x (min 1 a)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => V z - fderiv ℝ V x z)
    (f' := fun z => fderiv ℝ V z - fderiv ℝ V x)
    (fun z _ => ((hV.differentiable (by norm_num) z).hasFDerivAt.sub
      ((fderiv ℝ V x).hasFDerivAt)).hasFDerivWithinAt) hD hbase hyy
  convert hM using 1
  congr 1
  rw [map_sub]
  abel

theorem hasFDerivAt_superposition [ProperSpace E] {V : E → F}
    (hV : ContDiff ℝ 1 V) (f : C(K, E)) :
    HasFDerivAt (superposition V hV.continuous)
      (pathLinear (superposition (fderiv ℝ V) (hV.continuous_fderiv (by norm_num)) f)) f := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hT⟩ := uniform_taylor hV ‖f‖ (norm_nonneg f) ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, E)) hδ] with h hh
  have hhn : ‖h‖ < δ := by simpa [mem_ball, dist_zero_right] using hh
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  change ‖V (f x + h x) - V (f x) - fderiv ℝ V (f x) (h x)‖ ≤ ε * ‖h‖
  have H := hT (f x) (f x + h x) (f.norm_coe_le_norm x)
    (by simpa using (h.norm_coe_le_norm x).trans_lt hhn)
  simpa using H.trans (mul_le_mul_of_nonneg_left (by simpa using h.norm_coe_le_norm x) hε.le)

theorem contDiff_superposition_nat [ProperSpace E] (n : ℕ) {V : E → F}
    (hV : ContDiff ℝ n V) : ContDiff ℝ n (superposition (K := K) V hV.continuous) := by
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp ⟨V, hV.continuous⟩)
  | succ n ih =>
    have h1 : ContDiff ℝ 1 V := hV.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hD : ContDiff ℝ n (fderiv ℝ V) := hV.fderiv_right (by simp)
    change ContDiff ℝ ((n : WithTop ℕ∞) + 1) (superposition V h1.continuous)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun f => pathLinear (superposition (fderiv ℝ V) hD.continuous f), ?_, ?_⟩
    · exact (pathLinearCLM (K := K) (E := E) (F := F)).contDiff.comp (ih hD)
    · intro f
      exact hasFDerivAt_superposition h1 f

theorem contDiff_superposition [ProperSpace E] {V : E → F}
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (superposition (K := K) V hV.continuous) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_superposition_nat n (hV.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)))

abbrev J := Icc (0 : ℝ) 1

def PathSpace (E : Type u) [NormedAddCommGroup E] := C(J, E)

variable [CompleteSpace E]

def extendPath (f : C(J, E)) : ℝ → E := fun s => f (projIcc 0 1 zero_le_one s)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_extendPath (f : C(J, E)) : Continuous (extendPath f) :=
  f.continuous.comp continuous_projIcc

def primitive (f : C(J, E)) : C(J, E) :=
  ⟨fun s => ∫ r in (0 : ℝ)..(s : ℝ), extendPath f r,
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_extendPath f).intervalIntegrable a b) 0).comp continuous_subtype_val⟩

omit [CompleteSpace E] in
@[simp] theorem primitive_apply (f : C(J, E)) (s : J) :
    primitive f s = ∫ r in (0 : ℝ)..(s : ℝ), extendPath f r := rfl

def primitiveCLM : C(J, E) →L[ℝ] C(J, E) :=
  LinearMap.mkContinuous
    { toFun := primitive
      map_add' := by
        intro f g; ext s
        exact intervalIntegral.integral_add
          ((continuous_extendPath f).intervalIntegrable 0 s)
          ((continuous_extendPath g).intervalIntegrable 0 s)
      map_smul' := by
        intro c f; ext s
        exact intervalIntegral.integral_smul c (extendPath f) }
    1 (by
      intro f
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
      intro s
      change ‖∫ r in (0 : ℝ)..(s : ℝ), extendPath f r‖ ≤ ‖f‖
      have H := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := (s : ℝ)) (C := ‖f‖)
        (fun r _ => f.norm_coe_le_norm (projIcc 0 1 zero_le_one r))
      apply H.trans
      simp only [sub_zero, abs_of_nonneg s.property.1]
      exact mul_le_of_le_one_right (norm_nonneg f) s.property.2)

omit [CompleteSpace E] in
@[simp] theorem primitiveCLM_apply (f : C(J, E)) : primitiveCLM f = primitive f := rfl

def constPathCLM : E →L[ℝ] C(J, E) :=
  LinearMap.mkContinuous
    { toFun := ContinuousMap.const J
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    1 (by
      intro x
      simp only [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg x)).2 (fun _ => le_rfl))

omit [CompleteSpace E] in
@[simp] theorem constPathCLM_apply (x : E) (s : J) : constPathCLM x s = x := rfl

def picardMap (V : E → E) (hV : Continuous V) (z : (ℝ × E) × C(J, E)) :
    (ℝ × E) × C(J, E) :=
  (z.1, z.2 - constPathCLM z.1.2 - z.1.1 • primitiveCLM (superposition V hV z.2))

omit [CompleteSpace E] in
theorem contDiff_picardMap [ProperSpace E] {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (picardMap V hV.continuous) := by
  unfold picardMap
  exact contDiff_fst.prodMk
    ((contDiff_snd.sub (constPathCLM.contDiff.comp (contDiff_snd.comp contDiff_fst))).sub
      ((contDiff_fst.comp contDiff_fst).smul
        (primitiveCLM.contDiff.comp ((contDiff_superposition hV).comp contDiff_snd))))

def picardLinearEquiv (b : C(J, E)) : ((ℝ × E) × C(J, E)) ≃L[ℝ] ((ℝ × E) × C(J, E)) where
  toFun := fun z => (z.1, z.2 - constPathCLM z.1.2 - z.1.1 • b)
  invFun := fun z => (z.1, z.2 + constPathCLM z.1.2 + z.1.1 • b)
  left_inv := by intro z; dsimp; congr 1; abel
  right_inv := by intro z; dsimp; congr 1; abel
  map_add' := by intros; ext <;> simp [add_smul]; abel
  map_smul' := by intros; ext <;> simp [smul_sub, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [CompleteSpace E] in
theorem hasFDerivAt_picard_zero [ProperSpace E] {V : E → E} (hV : ContDiff ℝ ∞ V) (x : E) :
    HasFDerivAt (picardMap V hV.continuous)
      (picardLinearEquiv (primitiveCLM (superposition V hV.continuous (constPathCLM x))) :
        ((ℝ × E) × C(J, E)) →L[ℝ] ((ℝ × E) × C(J, E)))
      ((0, x), constPathCLM x) := by
  let z : (ℝ × E) × C(J, E) := ((0, x), constPathCLM x)
  have hP := (contDiff_superposition (K := J) hV).differentiable (by simp)
  have hJ := primitiveCLM.hasFDerivAt.comp z ((hP (z.2)).hasFDerivAt.comp z (hasFDerivAt_snd))
  have ht := (hasFDerivAt_fst (𝕜 := ℝ) (p := z.1)).comp z hasFDerivAt_fst
  have hx := constPathCLM.hasFDerivAt.comp z
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := z.1)).comp z hasFDerivAt_fst)
  convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk
    ((hasFDerivAt_snd.sub hx).sub (ht.smul hJ)) using 1
  ext q s <;> simp [picardLinearEquiv, z]

theorem exists_smooth_local_inverse {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : G → G} (hf : ContDiff ℝ ∞ f) (a : G)
    (e₀ : G ≃L[ℝ] G) (hd : HasFDerivAt f (e₀ : G →L[ℝ] G) a) :
    ∃ e : OpenPartialHomeomorph G G, (e : G → G) = f ∧ a ∈ e.source ∧
      ∀ᶠ y in 𝓝 (f a), y ∈ e.target ∧ ContDiffAt ℝ ∞ e.symm y := by
  let e := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  have ha : a ∈ e.source := (hf.contDiffAt).mem_toOpenPartialHomeomorph_source hd (by simp)
  have hb : f a ∈ e.target := (hf.contDiffAt).image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have he : (e : G → G) = f := rfl
  have hunit : IsUnit (fderiv ℝ f a) := by
    rw [hd.fderiv]
    exact e₀.toUnit.isUnit
  have hn : ∀ᶠ x in 𝓝 a, IsUnit (fderiv ℝ f x) :=
    ((hf.continuous_fderiv (by simp)).continuousAt).preimage_mem_nhds
      (Units.isOpen.mem_nhds hunit)
  have hc : ContinuousAt e.symm (f a) := e.symm.continuousAt hb
  have hb' : e.symm (f a) = a := by rw [← he]; exact e.left_inv ha
  have hc' : Tendsto e.symm (𝓝 (f a)) (𝓝 a) := by simpa only [hb'] using hc.tendsto
  have hn' : ∀ᶠ y in 𝓝 (f a), IsUnit (fderiv ℝ f (e.symm y)) := hc' hn
  refine ⟨e, he, ha, ?_⟩
  filter_upwards [e.open_target.mem_nhds hb, hn'] with y hy hdy
  let d : G ≃L[ℝ] G := ContinuousLinearEquiv.ofUnit hdy.unit
  refine ⟨hy, e.contDiffAt_symm (f₀' := d) hy ?_ ?_⟩
  · have hd' : (d : G →L[ℝ] G) = fderiv ℝ f (e.symm y) := hdy.unit_spec
    exact (by rw [he, hd']; exact (hf.differentiable (by simp) _).hasFDerivAt)
  · rw [he]; exact hf.contDiffAt

theorem mul_mem_time {δ t s : ℝ} (ht : t ∈ Ioo (-δ) δ) (hs : s ∈ Icc 0 1) :
    t * s ∈ Ioo (-δ) δ := by
  apply abs_lt.mp
  have hs' : |t * s| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_right (abs_nonneg t) hs.2
  exact hs'.trans_lt (abs_lt.mpr ht)

def flowDomain (x₀ : E) (r δ : ℝ) : Set (ℝ × E) := Ioo (-δ) δ ×ˢ ball x₀ r

section Rescaling
variable {x₀ : E} {r δ : ℝ} {α : E × ℝ → E}
  (hc : ContinuousOn α (closedBall x₀ r ×ˢ Icc (-δ) δ))

def rescaledPath (p : flowDomain x₀ r δ) : C(J, E) :=
  ⟨fun s => α (p.val.2, p.val.1 * s.val),
    hc.comp_continuous (by fun_prop) (fun s =>
      ⟨ball_subset_closedBall p.property.2,
        Ioo_subset_Icc_self (mul_mem_time p.property.1 s.property)⟩)⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem rescaledPath_apply (p : flowDomain x₀ r δ) (s : J) :
    rescaledPath hc p s = α (p.val.2, p.val.1 * s.val) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_rescaledPath : Continuous (rescaledPath hc) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hc.comp_continuous (by fun_prop) (fun p =>
    ⟨ball_subset_closedBall p.1.property.2,
      Ioo_subset_Icc_self (mul_mem_time p.1.property.1 p.2.property)⟩)

def rescaledPaths (p : ℝ × E) : C(J, E) := by
  classical
  exact if hp : p ∈ flowDomain x₀ r δ then rescaledPath hc ⟨p, hp⟩ else 0

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem rescaledPaths_of_mem (p : ℝ × E) (hp : p ∈ flowDomain x₀ r δ) :
    rescaledPaths hc p = rescaledPath hc ⟨p, hp⟩ := by
  classical
  simp [rescaledPaths, hp]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuousOn_rescaledPaths : ContinuousOn (rescaledPaths hc) (flowDomain x₀ r δ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert continuous_rescaledPath hc using 1
  ext p s
  simp [domRestrict, rescaledPaths_of_mem]

omit [CompleteSpace E] in
theorem rescaledPaths_initial (hr : 0 < r) (hδ : 0 < δ)
    (hi : ∀ x ∈ closedBall x₀ r, α (x, 0) = x) :
    rescaledPaths hc (0, x₀) = constPathCLM x₀ := by
  have hp : (0, x₀) ∈ flowDomain x₀ r δ :=
    ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, mem_ball_self hr⟩
  rw [rescaledPaths_of_mem hc _ hp]
  ext s
  simpa using hi x₀ (mem_closedBall_self hr.le)

theorem picardMap_rescaledPaths {V : E → E} (hV : Continuous V)
    (hi : ∀ x ∈ closedBall x₀ r, α (x, 0) = x)
    (hd : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Ioo (-δ) δ,
      HasDerivAt (fun s => α (x, s)) (V (α (x, t))) t)
    (p : ℝ × E) (hp : p ∈ flowDomain x₀ r δ) :
    picardMap V hV (p, rescaledPaths hc p) = (p, 0) := by
  rw [rescaledPaths_of_mem hc _ hp]
  unfold picardMap
  congr 1
  ext s
  change α (p.2, p.1 * s.val) - p.2 - p.1 •
    (∫ u in (0 : ℝ)..(s : ℝ), V (α (p.2, p.1 * (projIcc 0 1 zero_le_one u).val))) = 0
  have hsub : uIcc (0 : ℝ) s.val ⊆ Icc 0 1 := by
    rw [uIcc_of_le s.property.1]
    exact Icc_subset_Icc le_rfl s.property.2
  have hcont : ContinuousOn (fun u : ℝ => α (p.2, p.1 * u)) (Icc 0 1) :=
    hc.comp (by fun_prop) (fun u hu =>
      ⟨ball_subset_closedBall hp.2, Ioo_subset_Icc_self (mul_mem_time hp.1 hu)⟩)
  have hint : IntervalIntegrable (fun u : ℝ => p.1 • V (α (p.2, p.1 * u)))
      MeasureTheory.volume 0 s.val :=
    (((hV.comp_continuousOn hcont).const_smul p.1).mono
      (Icc_subset_Icc le_rfl s.property.2)).intervalIntegrable_of_Icc s.property.1
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := s.val)
    (f := fun u => α (p.2, p.1 * u)) (f' := fun u => p.1 • V (α (p.2, p.1 * u)))
    (fun u hu => by
      simpa [Function.comp_def] using (hd p.2 (ball_subset_closedBall hp.2) (p.1 * u)
        (mul_mem_time hp.1 (hsub hu))).scomp u ((hasDerivAt_id u).const_mul p.1)) hint
  have hproj : (∫ u in (0 : ℝ)..(s : ℝ), V (α (p.2, p.1 * (projIcc 0 1 zero_le_one u).val))) =
      ∫ u in (0 : ℝ)..(s : ℝ), V (α (p.2, p.1 * u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [projIcc_of_mem zero_le_one (hsub hu)]
  rw [hproj, ← intervalIntegral.integral_smul]
  rw [H, mul_zero, hi p.2 (ball_subset_closedBall hp.2)]
  abel
end Rescaling

theorem smooth_flow_near_origin [ProperSpace E] {V : E → E} (hV : ContDiff ℝ ∞ V)
    {x₀ : E} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) {α : E × ℝ → E}
    (hc : ContinuousOn α (closedBall x₀ r ×ˢ Icc (-δ) δ))
    (hi : ∀ x ∈ closedBall x₀ r, α (x, 0) = x)
    (hd : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Ioo (-δ) δ,
      HasDerivAt (fun s => α (x, s)) (V (α (x, t))) t) :
    ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), ContDiffAt ℝ ∞ (fun p : ℝ × E => α (p.2, p.1)) p := by
  let a : (ℝ × E) × C(J, E) := ((0, x₀), constPathCLM x₀)
  obtain ⟨e, he, ha, hs⟩ := exists_smooth_local_inverse (contDiff_picardMap hV) a
    (picardLinearEquiv (primitiveCLM (superposition V hV.continuous (constPathCLM x₀))))
    (hasFDerivAt_picard_zero hV x₀)
  have hf0 : picardMap V hV.continuous a = (((0 : ℝ), x₀), 0) := by
    simp [picardMap, a]
  rw [hf0] at hs
  have hop : IsOpen (flowDomain x₀ r δ) := isOpen_Ioo.prod isOpen_ball
  have hp0 : ((0 : ℝ), x₀) ∈ flowDomain x₀ r δ :=
    ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, mem_ball_self hr⟩
  have hu : ContinuousAt (rescaledPaths hc) ((0 : ℝ), x₀) :=
    (continuousOn_rescaledPaths hc).continuousAt (hop.mem_nhds hp0)
  have hZ : ContinuousAt (fun p : ℝ × E => (p, rescaledPaths hc p)) ((0 : ℝ), x₀) :=
    continuousAt_id.prodMk hu
  have hZ' : Tendsto (fun p : ℝ × E => (p, rescaledPaths hc p))
      (𝓝 ((0 : ℝ), x₀)) (𝓝 a) := by
    simpa only [rescaledPaths_initial hc hr hδ hi] using hZ.tendsto
  have hsrc : ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), (p, rescaledPaths hc p) ∈ e.source :=
    hZ' (e.open_source.mem_nhds ha)
  have heb : ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), (p, 0) ∈ e.target ∧ ContDiffAt ℝ ∞ e.symm (p, 0) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto hs
  let ev : ((ℝ × E) × C(J, E)) →L[ℝ] E :=
    (ContinuousMap.evalCLM ℝ (⟨1, by constructor <;> norm_num⟩ : J)).comp
      (ContinuousLinearMap.snd ℝ (ℝ × E) C(J, E))
  have hident : (fun p : ℝ × E => α (p.2, p.1)) =ᶠ[𝓝 ((0 : ℝ), x₀)]
      (fun p => ev (e.symm (p, 0))) := by
    filter_upwards [hsrc, hop.mem_nhds hp0] with p hp hpd
    have hmap : e (p, rescaledPaths hc p) = (p, 0) := by
      rw [he]; exact picardMap_rescaledPaths hc hV.continuous hi hd p hpd
    rw [← hmap, e.left_inv hp]
    simp [ev, rescaledPaths_of_mem hc p hpd]
  filter_upwards [heb, hident.eventually_nhds] with p hp heq
  apply ContDiffAt.congr_of_eventuallyEq _ heq
  exact ev.contDiff.contDiffAt.comp p
    (hp.2.comp p (contDiffAt_id.prodMk contDiffAt_const))

theorem exists_local_smooth_flow [ProperSpace E] {V : E → E} (hV : ContDiff ℝ ∞ V) (x₀ : E) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : ℝ × E → E,
      ContDiffOn ℝ ∞ Φ (Ioo (-ε) ε ×ˢ ball x₀ r) ∧
      (∀ x ∈ ball x₀ r, Φ (0, x) = x) ∧
      ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ ball x₀ r,
        HasDerivAt (fun s => Φ (s, x)) (V (Φ (t, x))) t := by
  have h1 : ContDiffAt ℝ 1 V x₀ := (hV.of_le (by simp)).contDiffAt
  obtain ⟨δ, hδ, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one h1
  obtain ⟨α, hα, hc⟩ := (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hc' : ContinuousOn α (closedBall x₀ r ×ˢ Icc (-δ) δ) := by simpa using hc
  have hi : ∀ x ∈ closedBall x₀ r, α (x, 0) = x := fun x hx => (hα x hx).1
  have hd : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Ioo (-δ) δ,
      HasDerivAt (fun s => α (x, s)) (V (α (x, t))) t := by
    intro x hx t ht
    exact ((hα x hx).2 t (by simpa using Ioo_subset_Icc_self ht)).hasDerivAt
      (by simpa using Icc_mem_nhds ht.1 ht.2)
  have hs := smooth_flow_near_origin hV (show (0 : ℝ) < r from hr) hδ hc' hi hd
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min η r, lt_min hη hr, min η δ, lt_min hη hδ,
    fun p => α (p.2, p.1), ?_, ?_, ?_⟩
  · apply (isOpen_Ioo.prod isOpen_ball).contDiffOn_iff.mpr
    intro p hp
    apply hηs
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨?_, (show dist p.2 x₀ < min η r from hp.2).trans_le (min_le_left _ _)⟩
    simpa [Real.dist_eq] using (abs_lt.mpr hp.1).trans_le (min_le_left η δ)
  · intro x hx
    exact hi x (ball_subset_closedBall (ball_subset_ball (min_le_right η r) hx))
  · intro t ht x hx
    apply hd x (ball_subset_closedBall (ball_subset_ball (min_le_right η r) hx)) t
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right η δ)) ht.1,
      ht.2.trans_le (min_le_right η δ)⟩

def LocalSmoothFlowExistence : Prop :=
  ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
    ContDiff ℝ ∞ V → ∀ x₀,
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ),
    ∃ Φ : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContDiffOn ℝ ∞ Φ (Ioo (-ε) ε ×ˢ ball x₀ r) ∧
      (∀ x ∈ ball x₀ r, Φ (0, x) = x) ∧
      ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ ball x₀ r,
        HasDerivAt (fun s => Φ (s, x)) (V (Φ (t, x))) t

theorem localSmoothFlowExistence : LocalSmoothFlowExistence := by
  intro n V hV x₀
  exact exists_local_smooth_flow hV x₀

end
end MorseArnold.SmoothODE

end

end OAI
