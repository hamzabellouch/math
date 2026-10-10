import OAI.Geometry.QuadricBundles.DualForms

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Matrix Complex Filter Topology BigOperators Set Metric MeasureTheory
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
lemma norm_matrix_pair_le {n : Type u1} [Fintype n]
    (H : Matrix n n ℂ) (v w : n → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i j, ‖H i j‖ ≤ C) :
    ‖star v ⬝ᵥ H *ᵥ w‖ ≤ (Fintype.card n : ℝ)^2 * C * ‖v‖ * ‖w‖ := by
  change ‖∑ i, star (v i) * ∑ j, H i j * w j‖ ≤ _
  simp_rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, ‖star (v i) * (H i j * w j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _i : n, ∑ _j : n, ‖v‖ * (C * ‖w‖) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul, norm_star, norm_mul]
      exact mul_le_mul (norm_le_pi_norm v i)
        (mul_le_mul (hb i j) (norm_le_pi_norm w j) (norm_nonneg _) hC)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by simp [pow_two]; ring

lemma quadraticValue_sub_bound {n : Type u2} [Fintype n]
    (H : Matrix n n ℂ) (v w : n → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i j, ‖H i j‖ ≤ C) :
    |quadraticValue H v - quadraticValue H w| ≤
      (Fintype.card n : ℝ)^2 * C * ‖v-w‖ * (‖v‖+‖w‖) := by
  have he : star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w =
      star (v-w) ⬝ᵥ H *ᵥ v + star w ⬝ᵥ H *ᵥ (v-w) := by
    simp only [star_sub, sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub]
    ring
  calc
    _ = |(star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w).re| := by
      simp [quadraticValue]
    _ ≤ ‖star v ⬝ᵥ H *ᵥ v - star w ⬝ᵥ H *ᵥ w‖ := Complex.abs_re_le_norm _
    _ ≤ ‖star (v-w) ⬝ᵥ H *ᵥ v‖ + ‖star w ⬝ᵥ H *ᵥ (v-w)‖ := by
      rw [he]; exact norm_add_le _ _
    _ ≤ (Fintype.card n : ℝ)^2 * C * ‖v-w‖ * ‖v‖ +
        (Fintype.card n : ℝ)^2 * C * ‖w‖ * ‖v-w‖ :=
      add_le_add (norm_matrix_pair_le H _ _ hC hb) (norm_matrix_pair_le H _ _ hC hb)
    _ = _ := by ring

theorem quadraticValue_moving_vector {n : Type u3} [Fintype n]
    (H : ℕ → Matrix n n ℂ) {v : ℕ → n → ℂ} {w : n → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ k i j, ‖H k i j‖ ≤ C)
    (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun k ↦ quadraticValue (H k) (v k) - quadraticValue (H k) w)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun k ↦ (Fintype.card n : ℝ)^2 * C * ‖v k-w‖ * (‖v k‖+‖w‖))
      atTop (𝓝 0) := by
    have hs : Tendsto (fun k ↦ ‖v k-w‖) atTop (𝓝 ‖w-w‖) :=
      (hv.sub tendsto_const_nhds).norm
    have hh : Tendsto (fun k ↦ (Fintype.card n : ℝ)^2 * C * ‖v k-w‖ * (‖v k‖+‖w‖))
        atTop (𝓝 ((Fintype.card n : ℝ)^2 * C * ‖w-w‖ * (‖w‖+‖w‖))) :=
      (tendsto_const_nhds.mul hs).mul (hv.norm.add tendsto_const_nhds)
    simpa using hh
  apply squeeze_zero_norm
    (fun k ↦ by simpa only [Real.norm_eq_abs] using
      quadraticValue_sub_bound (H k) (v k) w hC (hb k)) ht

lemma nonnegative_usc_integrableOn_ball {Ω : Set (ℂ × ℂ)} {q : ℂ × ℂ → ℝ}
    (hq : UpperSemicontinuousOn q Ω) (hpos : ∀ x ∈ Ω, 0 ≤ q x)
    {x : ℂ × ℂ} {r : ℝ} (hb : closedBall x r ⊆ Ω) :
    IntegrableOn q (ball x r) := by
  obtain ⟨C,hC⟩ := (hq.mono hb).bddAbove_of_isCompact (isCompact_closedBall x r)
  have hmeas : AEStronglyMeasurable q (volume.restrict (ball x r)) :=
    (aemeasurable_restrict_of_measurable_subtype measurableSet_ball
      (upperSemicontinuousOn_iff_restrict.mpr
        (hq.mono (ball_subset_closedBall.trans hb))).measurable).aestronglyMeasurable
  exact (integrableOn_const (C := C)
      (measure_ne_top_of_subset ball_subset_closedBall
        (isCompact_closedBall x r).measure_ne_top)).mono' hmeas
    ((ae_restrict_mem measurableSet_ball).mono fun y hy ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos y (hb (ball_subset_closedBall hy)))]
      exact hC (mem_image_of_mem _ (ball_subset_closedBall hy)))

local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

theorem moving_points_force_nonzero_limit
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {u : ℕ → (ℂ × ℂ) → ℝ} {q : (ℂ × ℂ) → ℝ}
    (hu : ∀ k, DiskPshOn Ω (u k)) (hpos : ∀ k x, x ∈ Ω → 0 ≤ u k x)
    {xm : ℕ → ℂ × ℂ} {x : ℂ × ℂ} {r : ℝ} (hr : 0 < r)
    (hb : closedBall x (3*r) ⊆ Ω)
    (hx : Tendsto xm atTop (𝓝 x))
    (hn : Tendsto (fun k ↦ u k (xm k)) atTop (𝓝 1))
    (hl : Tendsto (fun k ↦ ⨍ y in ball x (2*r), u k y) atTop
      (𝓝 (⨍ y in ball x (2*r), q y))) :
    ∃ y ∈ ball x (2*r), q y ≠ 0 := by
  have hb2 : closedBall x (2*r) ⊆ Ω :=
    (closedBall_subset_closedBall (by linarith)).trans hb
  have hv (c : ℂ × ℂ) {s : ℝ} (hs : 0 < s) : 0 < (volume (ball c s)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume c hs))
      (measure_ne_top_of_subset ball_subset_closedBall (isCompact_closedBall c s).measure_ne_top)
  have hV := hv x (show 0 < 2*r by positivity)
  have hW := hv (0 : ℂ × ℂ) hr
  let a : ℝ := (volume (ball x (2*r))).toReal⁻¹ *
    ((volume (ball (0 : ℂ × ℂ) r)).toReal * (1/2))
  apply nonzero_of_average_limit measurableSet_ball (a := a)
    (mul_pos (inv_pos.mpr hV) (mul_pos hW (by norm_num))) hl
  have hxe : ∀ᶠ k in atTop, dist (xm k) x < r :=
    hx.eventually (ball_mem_nhds x hr)
  have hne : ∀ᶠ k in atTop, (1/2 : ℝ) ≤ u k (xm k) :=
    ((tendsto_order.mp hn).1 (1/2) (by norm_num)).mono fun _ h ↦ h.le
  filter_upwards [hxe,hne] with k hk hn'
  have hi := nonnegative_usc_integrableOn_ball (hu k).1 (hpos k) hb2
  have hm := (hu k).moving_base_mass hΩ hr hk hb
    (fun y hy ↦ hpos k y (hb2 (ball_subset_closedBall hy))) hi hn'
  simpa [a, setAverage_eq, smul_eq_mul, measureReal_def] using
    mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hV.le)

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace ExtractedTrace
variable {D : EqualizerData} {ex : ℕ → ℕ} {P : ∀ k, TwistedPshForm D (ex k)}
    (X : ExtractedTrace ex P)

lemma averages_globalValue (i : StandardChart) (n : ℕ) (x : BaseCoordinates) (r : ℝ)
    (v : FiberCoordinates) (hb : ball x r ⊆ traceInterior (i,n)) :
    Tendsto (fun k ↦ ⨍ y in ball x r, (P (X.subsequence k)).value i (y,v)) atTop
      (𝓝 (⨍ y in ball x r, X.globalValue i (y,v))) := by
  have he (k : ℕ) : (⨍ y in ball x r, quadraticValue (cutoffTrace (P (X.subsequence k)) (i,n) y) v)=
      ⨍ y in ball x r, (P (X.subsequence k)).value i (y,v) := by
    apply setAverage_congr_fun measurableSet_ball
    apply Eventually.of_forall
    intro y hy
    rw [cutoffTrace_eq _ _ (traceDomain_subset_support (i,n) (traceInterior_subset_domain (i,n) (hb hy)))]
    rfl
  have hq : (⨍ y in ball x r, quadraticValue (X.matrix (i,n) y) v)=
      ⨍ y in ball x r, X.globalValue i (y,v) := by
    apply setAverage_congr_fun measurableSet_ball
    apply Eventually.of_forall
    intro y hy
    exact (X.globalValue_eq_value i n (p := (y,v)) (hb hy)).symm
  simpa only [he,hq] using X.averages (i,n) x r v hb

lemma globalValue_nonzero_of_sequence
    (i : StandardChart) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (z : ℕ → BaseCoordinates) (v : ℕ → FiberCoordinates)
    (x : BaseCoordinates) (w : FiberCoordinates)
    (hxlim : Tendsto z atTop (𝓝 x)) (hvlim : Tendsto v atTop (𝓝 w))
    (hxn : dist x 0 ≤ 1)
    (hbnd : ∀ k t, (P (X.subsequence (φ k))).value i (z k,t) ≤ ‖t‖^2)
    (hnorm : Tendsto (fun k ↦ (P (X.subsequence (φ k))).value i (z k,v k)) atTop (𝓝 1)) :
    ∃ y, X.globalValue i (y,w) ≠ 0 := by
  let seq (k : ℕ) := X.subsequence (φ k)
  have hcoeff (k : ℕ) (b c : Fin 2) : ‖(P (seq k)).matrix i (z k) b c‖ ≤ 4 := by
    have hm : ‖(P (seq k)).matrix i (z k)‖ ≤ 4 * 1 :=
      norm_matrix_of_quadratic_bound ((P (seq k)).positive i _).posSemidef
        (C := 1) (by norm_num)
        (fun t ↦ by simpa only [one_mul, TwistedPshForm.value] using hbnd k t)
    calc
      _ ≤ ‖(P (seq k)).matrix i (z k) b‖ := norm_le_pi_norm _ c
      _ ≤ ‖(P (seq k)).matrix i (z k)‖ := norm_le_pi_norm _ b
      _ ≤ 4 := by simpa only [mul_one] using hm
  have hdiff := quadraticValue_moving_vector (fun k ↦ (P (seq k)).matrix i (z k))
    (by norm_num : (0:ℝ)≤4) hcoeff hvlim
  have hfixed : Tendsto (fun k ↦ (P (seq k)).value i (z k,w)) atTop (𝓝 1) := by
    have h := hnorm.sub hdiff
    simpa only [TwistedPshForm.value,seq,sub_sub_cancel,sub_zero] using h
  have hball : closedBall x (3*(1/4:ℝ)) ⊆ traceInterior (i,0) := by
    apply closedBall_subset_ball'
    simp only [Nat.cast_zero, zero_add]
    linarith
  have hb : ball x (2*(1/4:ℝ)) ⊆ traceInterior (i,0) :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall (by norm_num)).trans hball)
  have hav := (X.averages_globalValue i 0 x (2*(1/4:ℝ)) w hb).comp hφ.tendsto_atTop
  have hp (k : ℕ) : DiskPshOn (traceInterior (i,0))
      (fun y : BaseCoordinates ↦ (P (seq k)).value i (y,w)) :=
    ((P (seq k)).psh i).comp (f := fun y : BaseCoordinates ↦ (y,w))
      (by fun_prop) (mapsTo_univ _ _)
  obtain ⟨y,_,hy⟩ := moving_points_force_nonzero_limit (Ω := traceInterior (i,0)) isOpen_ball hp
    (fun k y _ ↦ (P (seq k)).value_nonneg i y w)
    (by norm_num : (0:ℝ)<1/4) hball hxlim hfixed hav
  exact ⟨y,hy⟩

theorem globalValue_nonzero
    (hP : ∀ k i z, ‖z‖≤1 → ∀ v, (P k).value i (z,v)≤‖v‖^2)
    (hN : ∀ k, ∃ i z v, ‖z‖≤1 ∧ ‖v‖≤1 ∧ (P k).value i (z,v)=1) :
    ∃ i z v, X.globalValue i (z,v)≠0 := by
  choose chart z v hz hv hn using hN
  let S := StandardChart × (BaseCoordinates × FiberCoordinates)
  let p (k : ℕ) : S := (chart (X.subsequence k),(z (X.subsequence k),v (X.subsequence k)))
  let K : Set S := univ ×ˢ (closedBall 0 1 ×ˢ closedBall 0 1)
  have hK : IsCompact K := isCompact_univ.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hp (k : ℕ) : p k∈K := by
    exact ⟨mem_univ _,by simpa only [mem_closedBall,dist_zero_right] using hz (X.subsequence k),
      by simpa only [mem_closedBall,dist_zero_right] using hv (X.subsequence k)⟩
  obtain ⟨a,ha,φ,hφ,hlim⟩ := hK.isSeqCompact.subseq_of_frequently_in (x := p) (Frequently.of_forall hp)
  let i : StandardChart := a.1
  let x : BaseCoordinates := a.2.1
  let w : FiberCoordinates := a.2.2
  let seq (k : ℕ) := X.subsequence (φ k)
  have hxlim : Tendsto (fun k ↦ z (seq k)) atTop (𝓝 x) :=
    ((continuous_fst.comp continuous_snd).tendsto a).comp hlim
  have hvlim : Tendsto (fun k ↦ v (seq k)) atTop (𝓝 w) :=
    ((continuous_snd.comp continuous_snd).tendsto a).comp hlim
  have hilim : ∀ᶠ k in atTop, chart (seq k)=i := by
    have hi : Tendsto (fun k ↦ chart (seq k)) atTop (𝓝 i) :=
      (continuous_fst.tendsto a).comp hlim
    exact hi.eventually ((isOpen_discrete {i}).mem_nhds (mem_singleton i))
  have hnorm : Tendsto (fun k ↦ (P (seq k)).value i (z (seq k),v (seq k))) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hilim] with k hk
    rw [← hk,hn]
  obtain ⟨y,hy⟩ := X.globalValue_nonzero_of_sequence i φ hφ
    (fun k ↦ z (seq k)) (fun k ↦ v (seq k)) x w hxlim hvlim ha.2.1
    (fun k t ↦ hP (seq k) i _ (hz (seq k)) t) hnorm
  exact ⟨i,y,w,hy⟩
end ExtractedTrace
end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
noncomputable section

def ExtractedTrace.pshDualForm {D : EqualizerData} {ex : ℕ → ℕ}
    {P : ∀ k, TwistedPshForm D (ex k)} (X : ExtractedTrace ex P)
    (hex : Tendsto ex atTop atTop) : D.PshDualForm where
  value := X.globalValue
  quadratic i z := ⟨X.globalMatrix i z,X.globalMatrix_positive i z,fun _ ↦ rfl⟩
  psh := X.globalValue_psh
  compatible i j _ hz v := X.globalValue_change hex i j hz v

theorem no_unbounded_positive_metrics (ex : ℕ → ℕ) (hex : ∀ k, 0 < ex k)
    (hlim : Tendsto ex atTop atTop)
    (hmetric : ∀ k, ∃ h : SmoothHermitianMetric
      (powerPullbackTwist sourceGraphScalars.equalizerData.bundle (ex k) (hex k)),
      h.StrictlyGriffithsPositive) : False := by
  choose h hp using hmetric
  have hn (k : ℕ) := ((h k).tracedForm (hex k) (hp k)).exists_normalized
  choose P hP hN using hn
  obtain ⟨X⟩ := exists_extractedTrace hex P hP
  obtain ⟨i,z,v,hv⟩ := X.globalValue_nonzero hP hN
  exact hv ((X.pshDualForm hlim).source_value_zero i z v)

theorem source_eventually_no_positive_metric :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m (hm : 0 < m), m₀ ≤ m →
      ¬ ∃ h : SmoothHermitianMetric
        (powerPullbackTwist sourceGraphScalars.equalizerData.bundle m hm),
        h.StrictlyGriffithsPositive := by
  by_contra hh
  push Not at hh
  have hseq (k : ℕ) := hh (k+1) (by omega)
  choose ex hex hbound hm using hseq
  have hlim : Tendsto ex atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ ↦ k)
    · intro k; exact (Nat.le_succ k).trans (hbound k)
    · exact tendsto_id
  exact no_unbounded_positive_metrics ex hex hlim hm
end
end QuadricCounterexample

end

end OAI
