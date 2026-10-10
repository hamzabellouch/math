import OAI.Analysis.FourierLLogL.Dyadic.Grid
/-! # Reduction to the finite grid -/

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Dyadic
open Period Node
noncomputable section

lemma expU_mono {M : ℕ} {f g : Grid M → ℝ} (h : ∀ y, f y ≤ g y) :
    expU f ≤ expU g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => h y)) (side_pos _).le

lemma avg_mono {M : ℕ} (p : Node) {f g : Grid M → ℝ} (h : ∀ y ∈ p.block M, f y ≤ g y) :
    p.avg f ≤ p.avg g := by
  apply mul_le_mul_of_nonneg_left (expU_mono ?_) (inv_pos.mpr p.len_pos).le
  intro y
  by_cases hy : y ∈ p.block M
  · simpa [hy] using h y hy
  · simp [hy]

lemma atom_volume_real {M : ℕ} (x : Grid M) : volume.real (atom x) = side M := by
  rw [measureReal_def, atom_volume, ENNReal.toReal_ofReal (side_pos M).le]

section E
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cell averages from the real model. -/
def liftGrid (M : ℕ) (f : ℝ → E) (y : Grid M) : E :=
  (side M)⁻¹ • ∫ x in atom y, f x

lemma expU_liftGrid (M : ℕ) (f : ℝ → E) (hf : Integrable f μ₁) :
    expU (liftGrid M f) = ∫ x, f x ∂μ₁ := by
  have hi : IntegrableOn f (⋃ y : Grid M, atom y) := by rw [← atom_partition]; exact hf
  unfold expU liftGrid μ₁
  rw [atom_partition M, integral_iUnion atom_measurable atom_disjoint hi, tsum_fintype]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, mul_inv_cancel₀ (side_pos M).ne', one_smul]

lemma liftGrid_ind {M : ℕ} (p : Node) (h : p.lev ≤ M) (f : ℝ → E) :
    liftGrid M (p.cells.indicator f) = (p.block M).indicator (liftGrid M f) := by
  ext y
  by_cases hy : y ∈ p.block M
  · rw [indicator_of_mem hy]
    unfold liftGrid
    congr 1
    exact setIntegral_congr_fun (atom_measurable y)
      (fun x hx => indicator_of_mem ((atom_iff_coarse p h hx).mpr hy) f)
  · rw [indicator_of_notMem hy, liftGrid, setIntegral_eq_zero_of_forall_eq_zero]
    · exact smul_zero _
    · exact fun x hx => indicator_of_notMem (mt (atom_iff_coarse p h hx).mp hy) f

lemma avg_liftGrid {M : ℕ} (f : ℝ → E) (hf : Integrable f μ₁)
    {p : Node} (hp : p.valid) (h : p.lev ≤ M) :
    p.avg (liftGrid M f) = p.len⁻¹ • ∫ x in p.cells, f x := by
  rw [avg, ← liftGrid_ind p h, expU_liftGrid, μ₁, setIntegral_indicator
    (show MeasurableSet p.cells from measurableSet_Ico), inter_eq_right.mpr (cells_sub hp)]
  exact hf.indicator measurableSet_Ico

lemma avg_smulHi_lift {M : ℕ} (f : ℝ → E) {p : Node} (hp : p.valid) (h : p.lev+1 ≤ M)
    (hF : Integrable (fun x => p.Hi x • f x) μ₁) :
    p.avg (fun y => p.Hi (pos y) • liftGrid M f y) =
      ∫ x, haarH x • f (p.a+p.len*x) ∂μ₁ := by
  have heq : (fun y => p.Hi (pos y) • liftGrid M f y) =
      liftGrid M (fun x => p.Hi x • f x) := by
    ext y
    unfold liftGrid
    rw [smul_comm, ← integral_smul]
    congr 1
    exact setIntegral_congr_fun (atom_measurable _) fun x hx =>
      congrArg (fun c : ℝ => c • f x) (Hi_const (p:=p) (q:=vertex y) h (pos_mem y) hx)
  rw [heq, avg_liftGrid _ hF hp (by omega),
    cells, box, ← mean_translate_scale (fun x => p.Hi x • f x) p.a p.len_pos]
  congr 1
  funext x
  rw [show p.Hi (p.a+p.len*x) = haarH x from congrArg haarH (by
    unfold normarg; field_simp [p.len_pos.ne']; ring)]

lemma norm_expU_le {M : ℕ} (f : Grid M → E) : ‖expU f‖ ≤ expU (fun x => ‖f x‖) := by
  unfold expU
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (side_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (side_pos _).le

lemma norm_avg_le {M : ℕ} (p : Node) (f : Grid M → E) :
    ‖p.avg f‖ ≤ p.avg (fun x => ‖f x‖) := by
  unfold avg
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr p.len_pos)]
  refine mul_le_mul_of_nonneg_left ((norm_expU_le _).trans ?_) (inv_pos.mpr p.len_pos).le
  apply expU_mono
  intro y; by_cases hy : y ∈ block p M <;> simp [hy]

lemma avg_sub {M : ℕ} (p : Node) (f g : Grid M → E) :
    p.avg (fun y => f y - g y) = p.avg f - p.avg g := by
  unfold avg expU
  simp_rw [indicator_sub, Finset.sum_sub_distrib, smul_sub]

variable [CompleteSpace E]

lemma liftGrid_const {M : ℕ} (c : E) (y : Grid M) :
    liftGrid M (fun _ => c) y = c := by
  rw [liftGrid, setIntegral_const, atom_volume_real, smul_smul,
    inv_mul_cancel₀ (side_pos _).ne', one_smul]


lemma avg_const {M : ℕ} {p : Node} (hp : p.valid) (h : p.lev ≤ M) (c : E) :
    p.avg (fun _ : Grid M => c) = c := by
  have heq := funext (liftGrid_const (M:=M) c)
  rw [← heq, avg_liftGrid (fun _ : ℝ => c) (integrable_const _) hp h, setIntegral_const]
  have hh : volume.real p.cells = p.len := by
    rw [cells,box, Real.volume_real_Ico_of_le (by linarith [p.len_pos])]
    ring
  rw [hh, smul_smul, inv_mul_cancel₀ p.len_pos.ne', one_smul]

end E

lemma lift_bounds {M : ℕ} {ρ : ℝ → ℝ} (hρ : Integrable ρ μ₁) (h0 : ∀ x, 0 ≤ ρ x)
    (B : ℝ) (hb : ∀ x, ρ x ≤ B) (y : Grid M) :
    0 ≤ liftGrid M ρ y ∧ liftGrid M ρ y ≤ B := by
  have hi : IntegrableOn ρ (atom y) := (show IntegrableOn ρ unitInt volume from hρ).mono_set (atom_sub y)
  have : IsFiniteMeasure (volume.restrict (atom y)) :=
    show IsFiniteMeasure (volume.restrict (Ico (pos y) (pos y+side M))) from inferInstance
  constructor
  · exact mul_nonneg (inv_pos.mpr (side_pos _)).le (integral_nonneg h0)
  · have H : (∫ x in atom y, ρ x) ≤ ∫ x in atom y, B :=
      integral_mono hi (integrable_const _) hb
    exact le_trans (mul_le_mul_of_nonneg_left H (inv_pos.mpr (side_pos _)).le)
      (liftGrid_const B y).le

lemma lift_shift {M : ℕ} (J : ℕ) (hJ : J+1 ≤ M) (f : ℝ → ℂ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ x, ‖f x‖ ≤ B) {y : Grid M} {x : ℝ} (hx : x ∈ atom y) :
    FinShift J (liftGrid M f) y = shift f 0 1 J x := by
  unfold FinShift shift haarLayer
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun k hk => ?_
  let p : Node := ⟨n,k⟩
  have hl : p.lev+2 ≤ M := by dsimp [p]; rw [Finset.mem_range] at hn; omega
  have hB' (x : ℝ) := H_bound (p.normarg x)
  have Hm : Measurable (p.Hi) := measurableH.comp (by unfold normarg; fun_prop)
  have Hi : Integrable (fun x => p.Hi x • f x) μ₁ :=
    Integrable.of_bound (Hm.smul hf).aestronglyMeasurable B (ae_of_all _ (fun x => by
      change ‖p.Hi x • f x‖ ≤ _
      rw [norm_smul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (show ‖p.Hi x‖ ≤ 1 from hB' x)).trans (hb x)))
  rw [show lft 0 1 n k = p.a by simp [lft,p,a,len], one_mul]
  change FinJump p _ y = p.Gi x • _
  rw [FinJump, Gi_const (q:=vertex y) hl (pos_mem y) hx,
    avg_smulHi_lift f (Finset.mem_range.mp hk) (by omega) Hi]
  rfl


lemma lift_mod_error (M : ℕ) {ρ : ℝ → ℝ} (hρ : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (B : ℝ) (hb : ∀ x, ρ x ≤ B) (n : ℤ) (y : Grid M) :
    ‖liftGrid M (modρ ρ (n:ℝ)) y - finMod (liftGrid M ρ) (n:Grid M) y‖ ≤
      (B * |(n:ℝ)| * (2*π)) * side M := by
  rw [finMod, chi_cast]
  have : IsFiniteMeasure (volume.restrict (atom y)) :=
    show IsFiniteMeasure (volume.restrict (Ico (pos y) (pos y+side M))) from inferInstance
  let u : ℝ := n
  let q (x : ℝ) := (ρ x:ℂ) * phase u (pos y)
  let F := modρ ρ u
  let C := (B * |u| *(2*π))*side M
  have heq : (↑(liftGrid M ρ y) : ℂ) * phase u (pos y) = liftGrid M q y := by
    unfold liftGrid q
    rw [integral_mul_const, integral_complex_ofReal]
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
  change ‖liftGrid M F y - _ * phase u (pos y)‖ ≤ C
  rw [heq]
  have HiF : IntegrableOn F (atom y) := Integrable.of_bound (measurable_mod hρ _).aestronglyMeasurable B
    (ae_of_all _ fun x => by rw [norm_mod h0]; exact hb x)
  have Hiq : IntegrableOn q (atom y) :=
    Integrable.of_bound (((Complex.continuous_ofReal.measurable.comp hρ).mul measurable_const).aestronglyMeasurable) B (ae_of_all _ fun x => by
        change ‖q x‖ ≤ _
        unfold q
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x),
          phase_unimod, mul_one] using hb x)
  have hh (x : ℝ) (hx : x ∈ atom y) : ‖F x - q x‖ ≤ C := by
    unfold F modρ q C
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 _)]
    have hk : |x-pos y| ≤ side M := by
      change pos y ≤ x ∧ x < pos y+side M at hx
      rw [abs_le]; constructor <;> linarith [hx.1,hx.2,side_pos M]
    calc
      _ ≤ B*(|u| *(2*π*side M)) := mul_le_mul (hb x)
        ((norm_phase_sub u x _).trans (by gcongr)) (norm_nonneg _) ((h0 x).trans (hb x))
      _ = _ := by ring
  rw [liftGrid, liftGrid, ← smul_sub, ← integral_sub HiF Hiq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (side_pos M))]
  have H : ‖∫ x in atom y, F x - q x‖ ≤ ∫ _ in atom y, C :=
    (norm_integral_le_integral_norm _).trans (integral_mono_ae (HiF.sub Hiq).norm
      (integrable_const _) ((ae_restrict_mem (atom_measurable y)).mono hh))
  refine (mul_le_mul_of_nonneg_left H (inv_pos.mpr (side_pos M)).le).trans ?_
  rw [setIntegral_const, atom_volume_real, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (side_pos M).ne', one_mul]

lemma FinJump_error {M : ℕ} {f g : Grid M → ℂ} (B : ℝ)
    (h : ∀ x, ‖f x - g x‖ ≤ B) {p : Node} (hp : p.valid) (hl : p.lev ≤ M) (x : Grid M) :
    ‖FinJump p f x - FinJump p g x‖ ≤ B := by
  rw [FinJump, FinJump, ← smul_sub, ← avg_sub, norm_smul, Real.norm_eq_abs]
  refine (mul_le_of_le_one_left (norm_nonneg _) (G_bound _)).trans
    ((norm_avg_le _ _).trans ?_)
  refine (avg_mono p (g:=fun _ => B) fun y _ => ?_).trans (avg_const hp hl B).le
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) (H_bound _)).trans (h _)

lemma FinShift_error {M : ℕ} {f g : Grid M → ℂ} (B : ℝ)
    (h : ∀ x, ‖f x - g x‖ ≤ B) {J : ℕ} (hJ : J ≤ M) (x : Grid M) :
    ‖FinShift J f x - FinShift J g x‖ ≤ (∑ n ∈ Finset.range J, (2:ℝ)^n)*B := by
  unfold FinShift
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  apply le_trans (b:=∑ k ∈ Finset.range (2^n), B)
  · exact Finset.sum_le_sum (fun k hk => FinJump_error B h (Finset.mem_range.mp hk)
      ((Finset.mem_range.mp hn).le.trans hJ) _)
  simp


lemma usable_transfer {ρ : ℝ → ℝ} (hf : Integrable ρ μ₁) (D : ℝ)
    {M J : ℕ} (h : J ≤ M) {x : ℝ} (hx : usable ρ 0 1 J D x)
    {y : Grid M} (hy : x ∈ atom y) :
    finGood D J (liftGrid M ρ) y := by
  intro p hp hl hpy
  rw [avg_liftGrid ρ hf hp (hl.le.trans h)]
  have hx' : x ∈ p.cells := (atom_iff_coarse p (hl.le.trans h) hy).mpr hpy
  have H1 : lft 0 1 p.lev p.ix = p.a := by simp [lft,a,len]
  have H2 : 1*side p.lev = p.len := one_mul _
  have H := hx p.lev hl p.ix hp (by rwa [H1,H2])
  rw [H1,H2,density,mean_translate_scale _ _ p.len_pos] at H
  exact H

lemma expU_add_one (M : ℕ) (W : Grid M → ℝ) :
    expU (fun y => W y + 1) = expU W + 1 := by
  simp only [expU, Finset.sum_add_distrib, smul_eq_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, mul_add, Grid, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_comm (side M) ((2:ℝ)^M), pow_mul_side]

theorem GridBound.unitTreeBound (hgrid : GridBound) : UnitTreeBound := by
  obtain ⟨C,hC,h⟩ := hgrid
  refine ⟨C+1, by positivity,?_⟩
  filter_upwards [h] with j hj
  intro ρ hρ h0 hm hb J G hG hGu hD
  let B := Real.exp ((2:ℝ)^j)
  have hB : 0 ≤ B := Real.exp_nonneg _
  have hbi : Integrable ρ μ₁ := Integrable.of_bound hρ.aestronglyMeasurable B
    (ae_of_all _ (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using hb x))
  let Y (n : ℤ) (x : ℝ) := ENNReal.ofReal ‖shift (modρ ρ n) 0 1 J x‖
  let Z (n : ℕ) (x : ℝ) := ⨆ i : ℤ, ⨆ (_h : i.natAbs ≤ n), Y i x
  have hYm (n : ℤ) : Measurable (Y n) :=
    (show Measurable (fun x => shift (modρ ρ n) 0 1 J x)
      from measurable_shift_comp (measurable_mod hρ _) measurable_const measurable_const measurable_id J)
      |>.norm.ennreal_ofReal
  have hZm (n : ℕ) : Measurable (Z n) :=
    Measurable.iSup fun i => Measurable.iSup fun (_ : i.natAbs ≤ n) => hYm i
  have hZo : Monotone Z := fun n m h x => iSup_le fun i => iSup_le fun hi =>
    le_iSup₂ (f := fun i (_h : i.natAbs ≤ m) => Y i x) i (le_trans hi h)
  have hZ (x : ℝ) : maxShift ρ 0 1 J x ≤ ⨆ n, Z n x := by
    refine iSup_le fun i =>
      (le_iSup₂ (f := fun l : ℤ => fun (_ : l.natAbs ≤ i.natAbs) => Y l x) i le_rfl).trans
        (le_iSup (fun n => Z n x) i.natAbs)
  refine (lintegral_mono hZ).trans ?_
  rw [lintegral_iSup hZm hZo]
  refine iSup_le fun n => ?_
  let S := ∑ m ∈ Finset.range J, (2:ℝ)^m
  have ht : Tendsto (fun M => S*(B*(n:ℝ)*(2*π))*side M) atTop (𝓝 0) := by
    have hs : Tendsto side atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num) (by norm_num)
    simpa only [mul_zero] using hs.const_mul (S*(B*(n:ℝ)*(2*π)))
  obtain ⟨M,hM,hMJ,hMt⟩ := ((hj J).and
    ((eventually_ge_atTop (J+1)).and (ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))))).exists
  change _ < (1:ℝ) at hMt
  obtain ⟨W,hW,hWm,hWe⟩ :=
    hM (liftGrid M ρ) (fun y => (lift_bounds hbi h0 B hb y).1) (by rwa [expU_liftGrid M ρ hbi])
      (fun y => (lift_bounds hbi h0 B hb y).2)
  have Hx (y : Grid M) (x : ℝ) (hx : x ∈ atom y) (hxg : x ∈ G) :
      Z n x ≤ ENNReal.ofReal (W y + 1) := by
    refine iSup_le fun (i : ℤ) => iSup_le fun hi => ?_
    have hw := hWe y (usable_transfer hbi _ (by omega) (hD x hxg) hx) (i:Grid M)
    let f := liftGrid M (modρ ρ (i:ℝ))
    have hh := FinShift_error (B*|(i:ℝ)| * (2*π)*side M) (lift_mod_error M hρ h0 B hb i)
      (show J ≤ M by omega) y
    change ‖FinShift J f y - _‖ ≤ S*_ at hh
    have Hlem : |(i:ℝ)| ≤ (n:ℝ) := by rw [abs_le]; constructor <;> exact_mod_cast (by omega)
    have hlim : S*(B*|(i:ℝ)| * (2*π)*side M) ≤ 1 := by
      calc
        _ ≤ S*(B*(n:ℝ)*(2*π)*side M) := by
          have h := side_pos M
          have : 0 ≤ S := Finset.sum_nonneg (fun _ _ => by positivity)
          gcongr
        _ ≤ 1 := by linarith
    change ENNReal.ofReal _ ≤ _
    apply ENNReal.ofReal_le_ofReal
    have hfi (x : ℝ) : ‖modρ ρ i x‖ ≤ B := by rw [norm_mod h0]; exact hb _
    rw [← lift_shift J hMJ _ (measurable_mod hρ _) B hfi hx]
    have HE := norm_sub_norm_le (FinShift J f y) (FinShift J (finMod (liftGrid M ρ) (i:Grid M)) y)

    change ‖FinShift J f y‖ ≤ W y + 1
    linarith
  let V := G.indicator (Z n)
  have HV : (∫⁻ x in G, Z n x) = ∫⁻ x in unitInt, V x := by
    unfold V
    rw [lintegral_indicator hG, Measure.restrict_restrict hG, inter_eq_left.mpr hGu]
  rw [HV, atom_partition M, lintegral_iUnion atom_measurable atom_disjoint, tsum_fintype]
  have Hv (y : Grid M) :
      (∫⁻ x in atom y, V x) ≤ ENNReal.ofReal ((W y+1)*side M) := by
    calc
      _ ≤ ∫⁻ _ in atom y, ENNReal.ofReal (W y+1) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (atom_measurable y)] with x hx
        by_cases H : x ∈ G
        · simpa [V,H] using Hx y x hx H
        · simp [V,H]
      _ = _ := by rw [setLIntegral_const, atom_volume,
                       ENNReal.ofReal_mul (by linarith [hW y] : 0 ≤ W y+1)]
  refine (Finset.sum_le_sum (fun y _ => Hv y)).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · apply ENNReal.ofReal_le_ofReal
    calc
      ∑ y, _ = expU (fun y => W y + 1) := by simp only [expU,smul_eq_mul,← Finset.sum_mul]; ring
      _ ≤ C*(2:ℝ)^j+1 := by rw [expU_add_one M W]; linarith
      _ ≤ _ := by linarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j)]
  · intro y _; have := side_pos M; have := hW y; positivity

end
end FourierLLogL.Dyadic

end OAI
