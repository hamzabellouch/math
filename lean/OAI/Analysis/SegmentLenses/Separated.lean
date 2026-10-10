import OAI.Analysis.SegmentLenses.IndexedDual

namespace OAI

/-!
# Separated families and uniform positive gaps
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

section SeparatedFamilies
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]



theorem finite_head_close_pair {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (z : ℕ → FullDual V) (B : ℝ) (hz : ∀ n, ‖z n‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ i j : ℕ, i ≠ j ∧ ‖head H (z i) - head H (z j)‖ < ε := by
  have _ := locallyFiniteOrderBotV
  classical
  let E : Submodule ℝ (FullDual V) := Submodule.span ℝ (coordinate '' (H : Set V))
  have : FiniteDimensional ℝ E := FiniteDimensional.span_of_finite ℝ
    (Set.Finite.image coordinate (Finset.finite_toSet H))
  have hmem : ∀ n, head H (z n) ∈ E := by
    intro n
    apply Submodule.sum_mem
    intro v hv
    exact E.smul_mem _ (Submodule.subset_span ⟨v, hv, rfl⟩)
  let w : ℕ → E := fun n => ⟨head H (z n), hmem n⟩
  have hw : ∀ n, w n ∈ Metric.closedBall (0 : E) B := by
    intro n
    rw [Metric.mem_closedBall]
    change dist (head H (z n)) 0 ≤ B
    rw [dist_zero_right]
    exact (norm_head_le hH (z n)).trans (hz n)
  obtain ⟨a, ha, φ, hφ, ht⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε/2) (half_pos hε)
  refine ⟨φ N, φ (N+1), ne_of_lt (hφ (Nat.lt_succ_self N)), ?_⟩
  have hn := hN N le_rfl
  have hn' := hN (N+1) (Nat.le_succ N)
  have hd := dist_triangle (w (φ N)) a (w (φ (N+1)))
  rw [dist_comm a] at hd
  change ‖head H (z (φ N)) - head H (z (φ (N+1)))‖ < ε
  have he : dist (w (φ N)) (w (φ (N+1))) =
      ‖head H (z (φ N)) - head H (z (φ (N+1)))‖ := by
    change dist (head H (z (φ N))) (head H (z (φ (N+1)))) = _
    exact dist_eq_norm _ _
  rw [he] at hd
  dsimp only [Function.comp_apply] at hn hn'
  linarith

theorem separated_predual_family {D : ℝ} (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : CoordinatePredual V) (z : ℕ → CoordinatePredual V),
      1 ≤ ‖x‖ → ‖x‖ ≤ D → (∀ i, ‖z i‖ ≤ 2*D) →
      (∀ i j, i ≠ j → 1 ≤ ‖z i - z j‖) →
      ∃ i, ‖x‖ + c < max ‖x+z i‖ ‖x-z i‖ := by
  let c : ℝ := 1 / (4096 * (D+1))
  have hD0 : 0 ≤ D := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1/4096 := by
    dsimp [c]
    apply (div_le_iff₀ (by positivity : 0 < 4096*(D+1))).mpr
    nlinarith
  have hcD : D*c ≤ 1/4096 := by
    dsimp [c]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 4096*(D+1))).mpr
    nlinarith
  refine ⟨c, hc, ?_⟩
  intro x z hx1 hxD hz hsep
  by_contra! hbad
  obtain ⟨H, hH, u, hu, he⟩ := predual_finite_approx x hc
  let R := ‖x‖ + 2*c
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have huNorm : ‖x‖-c ≤ ‖u‖ := by
    have hn := norm_sub_norm_le x.val u
    change ‖x.val-u‖ < c at he
    change ‖x.val‖-c ≤ ‖u‖
    linarith
  have htails : ∀ i, ‖tail H (z i).val‖ ≤ 1/4 := by
    intro i
    have hp : ‖u+(z i).val‖ ≤ R := by
      have ht : ‖u+(z i).val‖ ≤ ‖x.val+(z i).val‖ + ‖x.val-u‖ := by
        have heq : u+(z i).val = (x.val+(z i).val)+(u-x.val) := by module
        rw [heq]
        exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev u x.val])
      have hb := (le_max_left ‖x+z i‖ ‖x-z i‖).trans (hbad i)
      change ‖x.val+(z i).val‖ ≤ ‖x.val‖ + c at hb
      dsimp [R]
      change ‖x.val-u‖ < c at he
      linarith
    have hm : ‖u-(z i).val‖ ≤ R := by
      have ht : ‖u-(z i).val‖ ≤ ‖x.val-(z i).val‖ + ‖x.val-u‖ := by
        have heq : u-(z i).val = (x.val-(z i).val)+(u-x.val) := by module
        rw [heq]
        exact (norm_add_le _ _).trans_eq (by rw [norm_sub_rev u x.val])
      have hb := (le_max_right ‖x+z i‖ ‖x-z i‖).trans (hbad i)
      change ‖x.val-(z i).val‖ ≤ ‖x.val‖ + c at hb
      dsimp [R]
      change ‖x.val-u‖ < c at he
      linarith
    have ht := completed_main_tail hH u (z i).val hu R hR hp hm
    have hq : R^2-‖u‖^2 ≤ 1/64 := by
      have hu0 : 0 ≤ ‖x‖-c := by linarith
      have husq : (‖x‖-c)^2 ≤ ‖u‖^2 := sq_le_sq₀ hu0 (norm_nonneg u) |>.mpr huNorm
      have hxc : ‖x‖*c ≤ D*c := mul_le_mul_of_nonneg_right hxD hc.le
      have hcc : c^2 ≤ c := by nlinarith
      change (‖x‖+2*c)^2-‖u‖^2 ≤ 1/64
      nlinarith
    have hs : Real.sqrt (R^2-‖u‖^2) ≤ 1/8 := by
      exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
    linarith
  obtain ⟨i, j, hij, hh⟩ := finite_head_close_pair hH (fun i => (z i).val) (2*D) hz (by norm_num : (0:ℝ)<1/2)
  have ht : ‖(z i).val-(z j).val‖ ≤
      ‖head H (z i).val-head H (z j).val‖ + ‖tail H (z i).val‖ + ‖tail H (z j).val‖ := by
    have heq : (z i).val-(z j).val =
        (head H (z i).val-head H (z j).val)+tail H (z i).val-tail H (z j).val := by
      simp only [tail]; module
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hlow := hsep i j hij
  change 1 ≤ ‖(z i).val-(z j).val‖ at hlow
  linarith [htails i, htails j]

end SeparatedFamilies


section LargerDirections
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev CofiniteLargeSphere (F : CofiniteSubspace E) := {y : E // y ∈ F.space ∧ 1 ≤ ‖y‖}

def averagedLargeOn (x : SphereOne E) (t : ℝ) (F : CofiniteSubspace E) : ℝ :=
  ⨅ y : CofiniteLargeSphere E F, (‖x.val+t•y.val‖+‖x.val-t•y.val‖)/2-1

def averagedLargeAt (x : SphereOne E) (t : ℝ) : ℝ :=
  ⨆ F : CofiniteSubspace E, averagedLargeOn E x t F

def averagedLargeModulus (t : ℝ) : ℝ := ⨅ x : SphereOne E, averagedLargeAt E x t

variable {E}

theorem average_nonneg_all (x y : E) (hx : ‖x‖ = 1) (t : ℝ) :
    0 ≤ (‖x+t•y‖+‖x-t•y‖)/2-1 := by
  have he : (x+t•y)+(x-t•y) = (2:ℝ)•x := by module
  have h := norm_add_le (x+t•y) (x-t•y)
  rw [he, norm_smul, hx, mul_one] at h
  norm_num at h
  linarith

theorem averagedLargeOn_bounds (hE : ¬ FiniteDimensional ℝ E) (x : SphereOne E)
    {t : ℝ} (ht : 0 ≤ t) (F : CofiniteSubspace E) :
    0 ≤ averagedLargeOn E x t F ∧ averagedLargeOn E x t F ≤ t := by
  let u : CofiniteSphere E F := Classical.choice (F.sphere_nonempty hE)
  let y : CofiniteLargeSphere E F := ⟨u.val, u.property.1, u.property.2.ge⟩
  let : Nonempty (CofiniteLargeSphere E F) := ⟨y⟩
  have hb : BddBelow (Set.range (fun y : CofiniteLargeSphere E F =>
      (‖x.val+t•y.val‖+‖x.val-t•y.val‖)/2-1)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v,rfl⟩
    exact average_nonneg_all x.val v.val x.property t
  exact ⟨le_ciInf (fun v => average_nonneg_all x.val v.val x.property t),
    (ciInf_le hb y).trans (average_bounds x.val u.val x.property u.property.2 ht).2⟩

theorem averagedLargeModulus_lower (hE : ¬ FiniteDimensional ℝ E) {t c : ℝ} (ht : 0 ≤ t)
    (hw : ∀ x : SphereOne E, ∀ ε : ℝ, 0 < ε → ∃ F : CofiniteSubspace E,
      ∀ y : CofiniteLargeSphere E F,
        c - ε ≤ (‖x.val+t•y.val‖+‖x.val-t•y.val‖)/2-1) :
    c ≤ averagedLargeModulus E t := by
  have := sphereOne_nonempty hE
  apply le_ciInf
  intro x
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F,hF⟩ := hw x ε hε
  have hb : BddAbove (Set.range (fun F : CofiniteSubspace E => averagedLargeOn E x t F)) := by
    refine ⟨t, ?_⟩
    rintro _ ⟨G,rfl⟩
    exact (averagedLargeOn_bounds hE x ht G).2
  let u : CofiniteSphere E F := Classical.choice (F.sphere_nonempty hE)
  let : Nonempty (CofiniteLargeSphere E F) := ⟨⟨u.val,u.property.1,u.property.2.ge⟩⟩
  have he : c-ε ≤ averagedLargeOn E x t F := le_ciInf hF
  have h := he.trans (le_ciSup hb F)
  change c - ε ≤ averagedLargeAt E x t at h
  linarith

end LargerDirections

section AveragedRefinementConsequences
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

theorem predual_strong_large_average [Infinite V] {t : ℝ} (ht : 0 < t) :
    Real.sqrt (1+t^2/4)-1 ≤ averagedLargeModulus (CoordinatePredual V) t := by
  apply averagedLargeModulus_lower predual_not_finite ht.le
  intro x ε hε
  obtain ⟨H,hH,hw⟩ := strong_predual_averaged_witness x.val x.property ht hε
  refine ⟨CofiniteSubspace.ofMap (predualHeadValues H), ?_⟩
  intro y
  exact hw y.val (predualHeadValues_zero H y.val y.property.1) y.property.2

theorem clipping_scalar {t : ℝ} : Real.sqrt (1+t^2/12)-1 ≤ Real.sqrt (1+t^2/4)-1 := by
  apply sub_le_sub_right
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg t]


theorem infinite_paired_clipping {t : ℝ} (ht : 0 < t) :
    Real.sqrt (1+t^2/12)-1 ≤ averagedModulus BInfinite t := by
  classical
  exact clipping_scalar.trans (strong_predual_all_radius_average (infiniteV := inferInstance) ht)


theorem forest_paired_clipping {t : ℝ} (ht : 0 < t) :
    Real.sqrt (1+t^2/12)-1 ≤ averagedModulus X t := by
  classical
  exact clipping_scalar.trans (strong_fullDual_all_radius_average_of_reflexive (infiniteV := inferInstance) forest_primal_reflexive ht)

def radialConstant : ℝ := Real.sqrt 2 + Real.sqrt 6

theorem radialConstant_ge : 2 ≤ radialConstant := by
  have h2 : 1 ≤ Real.sqrt 2 := by exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h6 : 1 ≤ Real.sqrt 6 := by exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  dsimp [radialConstant]
  linarith

def originalOmega (t : ℝ) : ℝ := (Real.sqrt (1+4*(t/radialConstant)^2)-1)/2

theorem originalOmega_positive {t : ℝ} (ht : 0 < t) : 0 < originalOmega t := by
  have hc : 0 < radialConstant := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) radialConstant_ge
  have hq : 0 < (t/radialConstant)^2 := sq_pos_of_pos (div_pos ht hc)
  have hs : 1 < Real.sqrt (1+4*(t/radialConstant)^2) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    nlinarith
  dsimp [originalOmega]
  linarith

theorem originalOmega_comparison {t : ℝ} (ht : 0 < t) :
    originalOmega t / 2 ≤ Real.sqrt (1+t^2/4)-1 := by
  have hc : 0 < radialConstant := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) radialConstant_ge
  have hratio : t/radialConstant ≤ t/2 := by
    apply (div_le_iff₀ hc).mpr
    have h := mul_le_mul_of_nonneg_left radialConstant_ge ht.le
    nlinarith
  have hratio0 : 0 ≤ t/radialConstant := (div_pos ht hc).le
  let a := Real.sqrt (1+t^2/4)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha : 1 ≤ a := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [sq_nonneg t]
  have hasq : a^2 = 1+t^2/4 := Real.sq_sqrt (by positivity)
  have hs : Real.sqrt (1+4*(t/radialConstant)^2) ≤ 4*a-3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by linarith, ?_⟩
    nlinarith [sq_nonneg (a-1)]
  dsimp [originalOmega]
  change (Real.sqrt (1+4*(t/radialConstant)^2)-1)/2/2 ≤ a-1
  linarith



theorem infinite_original_modulus {t : ℝ} (ht : 0 < t) :
    0 < originalOmega t/2 ∧ originalOmega t/2 ≤ averagedModulus BInfinite t ∧
      originalOmega t/2 ≤ averagedLargeModulus BInfinite t := by
  classical
  exact ⟨half_pos (originalOmega_positive ht),
    (originalOmega_comparison ht).trans (strong_predual_all_radius_average (infiniteV := inferInstance) ht),
    (originalOmega_comparison ht).trans (predual_strong_large_average ht)⟩

end AveragedRefinementConsequences



end SegmentLenses

end

end OAI
