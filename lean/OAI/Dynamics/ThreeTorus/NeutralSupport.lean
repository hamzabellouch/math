import OAI.Dynamics.ThreeTorus.Transmission

namespace OAI

/-! Neutral lattice sampling, retained support, and stationary image separation. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma cell_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a : ℝ) :
    |f a - ∫ x in a..a+1, f x| ≤ ∫ x in a..a+1, |deriv f x| := by
  have hc : Continuous (fun x => |deriv f x|) := (hf.continuous_deriv (by norm_num)).abs
  have hbound (x : ℝ) (hx : x ∈ Icc a (a+1)) :
      |f a-f x| ≤ ∫ t in a..a+1, |deriv f t| := by
    have hFTC := intervalIntegral.integral_deriv_eq_sub
      (fun t _ => hf.differentiable (by norm_num) t)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable (a := a) (b := x))
    calc
      _ = |∫ t in a..x, deriv f t| := by rw [hFTC, abs_sub_comm]
      _ ≤ ∫ t in a..x, |deriv f t| := by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm hx.1 (f := deriv f)
      _ ≤ ∫ t in a..a+1, |deriv f t| := by
        exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
          (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (hc.intervalIntegrable _ _)
  calc
    _ = |∫ x in a..a+1, (f a-f x)| := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.continuous.intervalIntegrable _ _)]
      simp
    _ ≤ ∫ x in a..a+1, |f a-f x| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (by linarith : a ≤ a+1)
        (f := fun x => f a-f x)
    _ ≤ ∫ _ in a..a+1, (∫ t in a..a+1, |deriv f t|) :=
      intervalIntegral.integral_mono_on (by linarith) ((continuous_const.sub hf.continuous).abs.intervalIntegrable _ _)
        intervalIntegrable_const hbound
    _ = _ := by simp

/-- Arbitrary-offset unit lattice estimate, before scaling to the neutral refresh mesh. -/
lemma lattice_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|)) (a : ℝ) :
    Summable (fun j : ℤ => f (a+j)) ∧
      |(∑' j : ℤ, f (a+j)) - ∫ x, f x| ≤ ∫ x, |deriv f x| := by
  let c (j : ℤ) := ∫ x in (a+j)..(a+j+1), f x
  let b (j : ℤ) := ∫ x in (a+j)..(a+j+1), |deriv f x|
  let e (j : ℤ) := f (a+j)-c j
  have hc : HasSum c (∫ x, f x) := hi.hasSum_intervalIntegral a
  have hb : HasSum b (∫ x, |deriv f x|) := hdi.hasSum_intervalIntegral a
  have heB (j : ℤ) : ‖e j‖ ≤ b j := by
    exact cell_sample_error hf (a+j)
  have he : Summable e := hb.summable.of_norm_bounded heB
  have hid (j : ℤ) : e j+c j = f (a+j) := by dsimp [e,c]; ring
  have hsum : HasSum (fun j : ℤ => f (a+j)) ((∑' j, e j)+(∫ x, f x)) :=
    (he.hasSum.add hc).congr_fun (fun j => (hid j).symm)
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, add_sub_cancel_right]
  calc
    _ ≤ ∑' j, ‖e j‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm he.norm
    _ ≤ ∑' j, b j := he.norm.tsum_le_tsum heB hb.summable
    _ = _ := hb.tsum_eq

/-- The mesh version of the arbitrary-offset Riemann estimate in neutral refresh. -/
lemma mesh_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|))
    {h : ℝ} (hh : 0 < h) (a : ℝ) :
    Summable (fun j : ℤ => f (a+h*j)) ∧
      |h*(∑' j : ℤ, f (a+h*j)) - ∫ x, f x| ≤ h*∫ x, |deriv f x| := by
  let g : ℝ → ℝ := fun x => f (h*x)
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_const.mul contDiff_id)
  have hgi : Integrable g := hi.comp_mul_left' hh.ne'
  have hd (x : ℝ) : deriv g x = deriv f (h*x)*h := by
    simpa only [g, Function.comp_def, mul_one] using (((hf.differentiable (by norm_num) (h*x)).hasDerivAt).comp x
      ((hasDerivAt_id x).const_mul h)).deriv
  have hdgi : Integrable (fun x => |deriv g x|) := by
    simp_rw [hd, abs_mul, abs_of_pos hh]
    exact (hdi.comp_mul_left' hh.ne').mul_const h
  have hid (j : ℤ) : g (a/h+j) = f (a+h*j) := by
    dsimp [g]; congr 1; field_simp
  obtain ⟨hs,hb⟩ := lattice_sample_error hg hgi hdgi (a/h)
  simp_rw [hid] at hs hb
  refine ⟨hs, ?_⟩
  have hgint : (∫ x, g x) = h⁻¹*(∫ x, f x) := by
    exact (Measure.integral_comp_mul_left f h).trans (by rw [abs_of_pos (inv_pos.mpr hh)]; rfl)
  have hdint : (∫ x, |deriv g x|) = ∫ x, |deriv f x| := by
    simp_rw [hd, abs_mul, abs_of_pos hh]
    rw [integral_mul_const, Measure.integral_comp_mul_left (fun x => |deriv f x|) h]
    rw [abs_of_pos (inv_pos.mpr hh)]
    simp only [smul_eq_mul]
    field_simp
  rw [hgint, hdint] at hb
  calc
    _ = |h*((∑' j : ℤ, f (a+h*j)) - h⁻¹*(∫ x, f x))| := by
      congr 1
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    _ = h*|(∑' j : ℤ, f (a+h*j)) - h⁻¹*(∫ x, f x)| := by
      rw [abs_mul, abs_of_pos hh]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hh.le

/-- Exact normalization for a residue class of the neutral refresh lattice. -/
lemma neutral_residue_riemann_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|))
    {P s L : ℝ} (hP : 0 < P) (hs : 0 < s) (hL : 0 < L) (a : ℝ) :
    |(s*L)⁻¹*(∑' j : ℤ, f (a+P/(s*L)*j)) - P⁻¹*(∫ x, f x)|
      ≤ (s*L)⁻¹*(∫ x, |deriv f x|) := by
  have hh : 0 < P/(s*L) := by positivity
  have hb := (mesh_sample_error hf hi hdi hh a).2
  calc
    _ = |P⁻¹*((P/(s*L))*(∑' j : ℤ, f (a+P/(s*L)*j)) - ∫ x, f x)| := by
      congr 1
      field_simp
    _ = P⁻¹*|(P/(s*L))*(∑' j : ℤ, f (a+P/(s*L)*j)) - ∫ x, f x| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hP)]
    _ ≤ P⁻¹*((P/(s*L))*(∫ x, |deriv f x|)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

/-- Mesh reversal uses the actual integer negation bijection; negative old
angular indices have the same arbitrary-offset Riemann estimate. -/
lemma signed_mesh_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|))
    {h : ℝ} (hh : h ≠ 0) (a : ℝ) :
    Summable (fun j : ℤ => f (a+h*j)) ∧
      |(|h| *(∑' j : ℤ, f (a+h*j))) - ∫ x, f x| ≤ |h| *∫ x, |deriv f x| := by
  rcases lt_or_gt_of_ne hh with hh | hh
  · obtain ⟨hs,hb⟩ := mesh_sample_error hf hi hdi (h := -h) (by linarith) a
    have he (j : ℤ) : f (a+h*j) = f (a+(-h)*(-j:ℤ)) := by
      push_cast; congr 1; ring
    have ht : (∑' j : ℤ, f (a+h*j)) = ∑' j : ℤ, f (a+(-h)*j) := by
      simp_rw [he]
      exact (Equiv.neg ℤ).tsum_eq (fun j : ℤ => f (a+(-h)*j))
    refine ⟨?_,?_⟩
    · simpa only [Function.comp_def, he] using hs.comp_injective (neg_injective : Injective (Neg.neg : ℤ → ℤ))
    · rw [abs_of_neg hh,ht]
      exact hb
  · simpa only [abs_of_pos hh] using mesh_sample_error hf hi hdi hh a

/-- Exact signed normalization, with arbitrary offset and arbitrary positive
integer residue spacing. This is source (neutral-riemann-error). -/
lemma signed_neutral_residue_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|))
    {P s L : ℝ} (hP : 0 < P) (hs : s ≠ 0) (hL : 0 < L) (y β : ℝ) :
    Summable (fun j : ℤ => (|s| *L)⁻¹*f (((y+j*P)/s-β)/L)) ∧
      |(∑' j : ℤ, (|s| *L)⁻¹*f (((y+j*P)/s-β)/L))-
          P⁻¹*(∫ a, f a)| ≤ (|s| *L)⁻¹*(∫ a, |deriv f a|) := by
  have hh : P/(s*L) ≠ 0 := div_ne_zero hP.ne' (mul_ne_zero hs hL.ne')
  obtain ⟨hsum,hb⟩ := signed_mesh_sample_error hf hi hdi hh ((y/s-β)/L)
  have hi' (j : ℤ) : (y/s-β)/L+(P/(s*L))*j = ((y+j*P)/s-β)/L := by ring
  simp_rw [hi'] at hsum hb
  have hab : |P/(s*L)| = P/(|s| *L) := by rw [abs_div,abs_mul,abs_of_pos hP,abs_of_pos hL]
  rw [hab] at hb
  refine ⟨hsum.mul_left _,?_⟩
  rw [tsum_mul_left]
  calc
    _ = |P⁻¹*((P/(|s| *L))*(∑' j : ℤ, f (((y+j*P)/s-β)/L)) - ∫ a, f a)| := by
      generalize (∑' j : ℤ, f (((y+j*P)/s-β)/L)) = S
      congr 1; field_simp
    _ = P⁻¹*|(P/(|s| *L))*(∑' j : ℤ, f (((y+j*P)/s-β)/L)) - ∫ a, f a| := by
      rw [abs_mul,abs_of_pos (inv_pos.mpr hP)]
    _ ≤ P⁻¹*((P/(|s| *L))*(∫ a, |deriv f a|)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

lemma fine_affine_neutral_error {F : ℝ × ℝ → ℝ} {P n : ℕ} {h : ℤ} {L s : ℝ}
    (hP : 0 < P) (hs : s ≠ 0) (hL : 0 < L) (β : ℝ)
    (hF : ContDiff ℝ 1 (fun a => F (s,a)))
    (hi : Integrable (fun a => F (s,a)))
    (hd : Integrable (fun a => |deriv (fun a => F (s,a)) a|)) :
    |fineResidueKernel (affineKernel F L β) P h n s-
      (P:ℝ)⁻¹*(∫ a, F (s,a))| ≤
      (|s| *L)⁻¹*(∫ a, |deriv (fun a => F (s,a)) a|) := by
  have hh := (signed_neutral_residue_error (P := (P:ℝ)) hF hi hd (by exact_mod_cast hP) hs hL
    ((n:ℝ)*s-h) β).2
  have he : fineResidueKernel (affineKernel F L β) P h n s =
      ∑' j : ℤ, (|s| *L)⁻¹*F (s,((((n:ℝ)*s-h)+j*P)/s-β)/L) := by
    unfold fineResidueKernel affineKernel
    have ht := (Equiv.neg ℤ).tsum_eq
      (fun j : ℤ => (|s| *L)⁻¹*F (s,((((n:ℝ)*s-h)+j*P)/s-β)/L))
    convert ht using 1
    apply tsum_congr
    intro j
    simp only [Equiv.neg_apply,Int.cast_neg]
    congr 3; ring
  rw [he]
  exact hh

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma compact_slice_tsupport {F : ℝ × ℝ → ℝ} {D : ℝ}
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (s : ℝ) :
    tsupport (fun a => F (s,a)) ⊆ Icc (-D) D := by
  apply closure_minimal _ isClosed_Icc
  intro a ha
  by_contra hn
  exact ha (hFa s a (lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hn)))

lemma compact_slice_support {F : ℝ × ℝ → ℝ} {D : ℝ}
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (s : ℝ) :
    HasCompactSupport (fun a => F (s,a)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (compact_slice_tsupport hFa s)

lemma compact_slice_derivative_bound {F : ℝ × ℝ → ℝ} {D : ℝ} {C : ℝ≥0}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (hD : 0 ≤ D)
    (hC : LipschitzWith C F) (s : ℝ) :
    Integrable (fun a => F (s,a)) ∧
    Integrable (fun a => |deriv (fun a => F (s,a)) a|) ∧
    (∫ a, |deriv (fun a => F (s,a)) a|) ≤ 2*D*C := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => F (s,a)) :=
    hF.comp ((contDiff_const (c := s)).prodMk contDiff_id)
  have hc := compact_slice_support hFa s
  have hfd : Continuous (deriv (fun a => F (s,a))) := hf.continuous_deriv (by simp)
  have hdi : Integrable (fun a => |deriv (fun a => F (s,a)) a|) :=
    hfd.abs.integrable_of_hasCompactSupport (hc.deriv.comp_left (abs_zero))
  have hl : LipschitzWith C (fun a => F (s,a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hC.dist_le_mul (s,a) (s,b)
  refine ⟨hf.continuous.integrable_of_hasCompactSupport hc,hdi,?_⟩
  have hzero (a : ℝ) (ha : a ∉ Icc (-D) D) : deriv (fun a => F (s,a)) a = 0 := by
    by_contra hn
    exact ha (compact_slice_tsupport hFa s (support_deriv_subset hn))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-D) D)
    (f := fun a => |deriv (fun a => F (s,a)) a|) (fun a ha => by rw [hzero a ha,abs_zero])]
  calc
    _ ≤ ∫ _ in Icc (-D) D, (C:ℝ) :=
      setIntegral_mono_on hdi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        (fun a _ => by simpa only [← Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := a) hl)
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -D ≤ D)]
      simp only [smul_eq_mul]
      ring

lemma compact_slice_integral_continuous {F : ℝ × ℝ → ℝ} {D : ℝ}
    (hF : Continuous F) (hFa : ∀ s a, D < |a| → F (s,a) = 0) :
    Continuous (fun s => ∫ a, F (s,a)) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := Icc (-D) D) isCompact_Icc
  · exact hF.continuousOn
  · intro s a _ ha
    exact hFa s a (lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using ha))

lemma fine_affine_neutral_uniform {F : ℝ × ℝ → ℝ} {P n : ℕ} {h : ℤ}
    {D ε L : ℝ} {C : ℝ≥0}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (hD : 0 ≤ D)
    (hC : LipschitzWith C F) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    (hP : 0 < P) (hL : 0 < L) (β s : ℝ) :
    |fineResidueKernel (affineKernel F L β) P h n s-
      (P:ℝ)⁻¹*(∫ a, F (s,a))| ≤ (ε*L)⁻¹*(2*D*C) := by
  by_cases hs : |s| < ε
  · have he : (∫ a, F (s,a)) = 0 := by simp [hz s _ hs]
    have hk : fineResidueKernel (affineKernel F L β) P h n s = 0 := by
      unfold fineResidueKernel affineKernel
      simp [hz s _ hs]
    rw [hk,he,mul_zero,sub_self,abs_zero]
    positivity
  · have hsε : ε ≤ |s| := le_of_not_gt hs
    have hs0 : s ≠ 0 := by intro hh; simp [hh] at hsε; linarith
    obtain ⟨hi,hd,hb⟩ := compact_slice_derivative_bound hF hFa hD hC s
    calc
      _ ≤ (|s| *L)⁻¹*(∫ a, |deriv (fun a => F (s,a)) a|) :=
        fine_affine_neutral_error hP hs0 hL β
          ((hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) hi hd
      _ ≤ (|s| *L)⁻¹*(2*D*C) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hsε hL.le)) (by positivity)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma fine_affine_neutral_l1_error {F : ℝ × ℝ → ℝ} {P n : ℕ} {h : ℤ}
    {A D ε L : ℝ} {C : ℝ≥0}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0) (hA : 0 ≤ A)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (hD : 0 ≤ D)
    (hC : LipschitzWith C F) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    (hn : 0 < n) (hP : 0 < P) (hL : 0 < L) (β : ℝ) :
    (∫ s, |fineResidueKernel (affineKernel F L β) P h n s-
      (P:ℝ)⁻¹*(∫ a, F (s,a))|) ≤ (2*A)*((ε*L)⁻¹*(2*D*C)) := by
  obtain ⟨M,hM⟩ := exists_nat_ge (A*(L*D+|β|))
  have hk := fineResidueKernel_regular (h := h) (n := n)
    (affineKernel_smooth (L := L) (β := β) hF hε hz).continuous
    (show 0 < max A 1 from lt_max_of_lt_right zero_lt_one)
    (fun s y hh => affineKernel_eq_zero_s hFs (lt_of_le_of_lt (le_max_left _ _) hh))
    (fun s y hh => affineKernel_eq_zero_y hL hA hD hFs hFa (lt_of_le_of_lt hM hh)) hn hP
  have hZ := compact_slice_integral_continuous hF.continuous hFa
  have hcZ : HasCompactSupport (fun s => ∫ a, F (s,a)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
    intro s hs
    have hab : A < |s| := lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hs)
    simp [hFs s _ hab]
  have hi := (hk.2.sub ((hZ.integrable_of_hasCompactSupport hcZ).const_mul (P:ℝ)⁻¹)).abs
  have hzero (s : ℝ) (hs : s ∉ Icc (-A) A) :
      |fineResidueKernel (affineKernel F L β) P h n s-(P:ℝ)⁻¹*(∫ a, F (s,a))| = 0 := by
    have hab : A < |s| := lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hs)
    rw [fineResidueKernel_eq_zero (fun s y hh => affineKernel_eq_zero_s hFs hh) hab]
    simp [hFs s _ hab]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-A) A) hzero]
  calc
    _ ≤ ∫ _ in Icc (-A) A, (ε*L)⁻¹*(2*D*C) :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        (fun s _ => fine_affine_neutral_uniform hF hFa hD hC hε hz hP hL β s)
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -A ≤ A)]
      simp only [smul_eq_mul]
      ring

lemma compact_rect_bounds {F : ℝ × ℝ → ℝ} (hc : HasCompactSupport F) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      (∀ s a, A < |s| → F (s,a) = 0) ∧ (∀ s a, D < |a| → F (s,a) = 0) := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R 0,max R 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hh' : |s| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_left ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hh'.trans (le_max_left _ _))) hs
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hh' : |a| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_right ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hh'.trans (le_max_left _ _))) hs

/-- Uniform residue equalization for actual compact smooth stationary weight.
One slope is chosen before the passage integer, with all lattice phases,
all residues, and both signs controlled. -/
lemma neutral_fine_l1_bound {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ s a, |s| < ε → F (s,a) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P n : ℕ}, 0 < P → 0 < n → ∀ h : ℤ, ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      (∫ s, |fineResidueKernel (affineKernel F L β) P h n s-
        (P:ℝ)⁻¹*(∫ a, F (s,a))|) ≤ C/L := by
  obtain ⟨A,D,hA,hD,hFs,hFa⟩ := compact_rect_bounds hcF
  obtain ⟨C,hC⟩ := compact_smooth_lipschitz hF hcF
  refine ⟨(2*A)*(2*D*C)/ε,by positivity,?_⟩
  intro P n hP hn h L hL β
  have hb := fine_affine_neutral_l1_error (h := h) hF hFs hA hFa hD hC hε hz hn hP hL β
  convert hb using 1; ring

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma deriv_affine_on {I : Set ℝ} {J : ℝ → ℝ} {L β : ℝ}
    (hIo : IsOpen I) (he : ∀ a ∈ I, J a = L*a+β) {a : ℝ} (ha : a ∈ I) :
    deriv J a = L := by
  have hev : J =ᶠ[𝓝 a] (fun x => L*x+β) := by
    filter_upwards [hIo.mem_nhds ha] with x hx using he x hx
  rw [hev.deriv_eq]
  simp

/-- The branch is the actual inverse of the affine jitter on the good arc.
Off that image both sides vanish because the old stationary weight is cut off. -/
lemma branchKernel_affine_on {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × ℝ → ℝ} {L β : ℝ}
    (hIo : IsOpen I) (hL : 0 < L) (he : ∀ a ∈ I, J a = L*a+β)
    (hs : tsupport F ⊆ I ×ˢ univ) (y s : ℝ) :
    branchKernel I J F (y,s) = L⁻¹*F ((y-β)/L,s) := by
  classical
  have hinj : InjOn J I := by
    intro a ha b hb hab
    rw [he a ha,he b hb] at hab
    nlinarith
  by_cases hy : y ∈ J '' I
  · obtain ⟨a,ha,rfl⟩ := hy
    have hg := hinj.leftInvOn_invFunOn ha
    have ht : (J a-β)/L = a := by rw [he a ha]; field_simp; ring
    rw [branchKernel,ite_eq_left (mem_image_of_mem J ha),hg,deriv_affine_on hIo he ha,
      abs_of_pos hL,ht]
    ring
  · have ha : (y-β)/L ∉ I := by
      intro hh
      apply hy
      refine ⟨(y-β)/L,hh,?_⟩
      rw [he _ hh]
      field_simp
      ring
    have hz : F ((y-β)/L,s) = 0 := by
      by_contra hn
      exact ha (hs (subset_tsupport _ hn)).1
    rw [branchKernel,ite_eq_right hy,hz,mul_zero]

lemma passageBranchKernel_affine_on {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × ℝ → ℝ} {L β : ℝ}
    (hIo : IsOpen I) (hL : 0 < L) (he : ∀ a ∈ I, J a = L*a+β)
    (hs : tsupport F ⊆ I ×ˢ univ) :
    passageBranchKernel I J F = affineKernel (F ∘ Prod.swap) L β := by
  funext s y
  rw [passageBranchKernel_formula,branchKernel_affine_on hIo hL he hs]
  simp only [affineKernel,Function.comp_apply,Prod.swap_prod_mk,mul_inv_rev]
  ring

lemma compact_slice_integral_regular {F : ℝ × ℝ → ℝ}
    (hF : Continuous F) (hcF : HasCompactSupport F) :
    Continuous (fun s => ∫ a, F (s,a)) ∧ Integrable (fun s => ∫ a, F (s,a)) := by
  obtain ⟨A,D,_,_,hFs,hFa⟩ := compact_rect_bounds hcF
  have hZ := compact_slice_integral_continuous hF hFa
  refine ⟨hZ,hZ.integrable_of_hasCompactSupport ?_⟩
  apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
  intro s hs
  have hab : A < |s| := lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hs)
  simp [hFs s _ hab]

lemma affine_fine_regular {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    {P n : ℕ} (hP : 0 < P) (hn : 0 < n) (h : ℤ) {L : ℝ} (hL : 0 < L) (β : ℝ) :
    Continuous (fineResidueKernel (affineKernel F L β) P h n) ∧
      Integrable (fineResidueKernel (affineKernel F L β) P h n) := by
  obtain ⟨A,D,hA,hD,hFs,hFa⟩ := compact_rect_bounds hcF
  obtain ⟨M,hM⟩ := exists_nat_ge (A*(L*D+|β|))
  apply fineResidueKernel_regular
    (affineKernel_smooth (L := L) (β := β) hF hε hz).continuous
    (show 0 < max A 1 from lt_max_of_lt_right zero_lt_one)
    (fun s y hh => affineKernel_eq_zero_s hFs (lt_of_le_of_lt (le_max_left _ _) hh))
    (fun s y hh => affineKernel_eq_zero_y hL hA hD hFs hFa (lt_of_le_of_lt hM hh)) hn hP

/-- The neutral equalization estimate on the actual temporal circle, uniformly
in the large preparation integer, residues, offsets and affine good-arc jitter.
The constant is fixed using only the old cut-off stationary weight. -/
lemma neutral_branch_circle_l1_bound {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {I : Set ℝ} {J : ℝ → ℝ} {P n : ℕ},
      IsOpen I → tsupport F ⊆ I ×ˢ univ → 0 < P → 0 < n →
      ∀ h : ℤ, ∀ L : ℝ, 0 < L → ∀ β : ℝ, (∀ a ∈ I, J a = L*a+β) →
      (∫ z, |foldCircleDensity (fineResidueKernel (passageBranchKernel I J F) P h n) z-
        foldCircleDensity (fun s => (P:ℝ)⁻¹*(∫ a, F (a,s))) z| ∂AddCircle.haarAddCircle) ≤ C/L := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ Prod.swap) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hc : HasCompactSupport (F ∘ Prod.swap) := hcF.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have hzf : ∀ s a, |s| < ε → (F ∘ Prod.swap) (s,a) = 0 := fun s a hs => hz a s hs
  obtain ⟨C,hC,hb⟩ := neutral_fine_l1_bound hf hc hε hzf
  refine ⟨C,hC,?_⟩
  intro I J P n hIo hsF hP hn h L hL β he
  rw [passageBranchKernel_affine_on hIo hL he hsF]
  have hq := affine_fine_regular hf hc hε hzf hP hn h hL β
  have hr := compact_slice_integral_regular hf.continuous hc
  calc
    _ ≤ ∫ s, |fineResidueKernel (affineKernel (F ∘ Prod.swap) L β) P h n s-
        (P:ℝ)⁻¹*(∫ a, F (a,s))| :=
      foldCircleDensity_l1_difference hq.1.measurable hq.2
        (measurable_const.mul hr.1.measurable) (hr.2.const_mul _)
    _ ≤ _ := hb hP hn h L hL β

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

/-- The broad slope is chosen after the cutoff weight and before the periodic jitter is fixed;
the final passage integer is only subject to a lower bound. The displayed
reference density is exactly the old cutoff stationary marginal, folded to
the temporal circle and divided by the residue modulus. -/
lemma exact_neutral_circle_spectral_estimate
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {o' : ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (hIo : IsOpen I)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
    (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
    (hzχ : ∀ a, χ 0 a = 0)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      ∀ (J₀ : ℝ → ℝ) (J : UnitAddCircle → ℝ),
      (∀ a ∈ I, J₀ a = L*a+β) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀ → Measurable J →
      (∀ x ∈ I, J (x : UnitAddCircle) = J₀ x) →
      ∃ S : ℕ → Finset ℤ,
        (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
        (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          (∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
            unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
              (circleDensityLift o' (retainedCircleWeight ψ χ
                (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
              n ((h+k*(Q:ℤ):ℤ):ℝ) t) a-
            foldCircleDensity (fun s => (Q:ℝ)⁻¹*(∫ a, F (a,s))) a|
            ∂AddCircle.haarAddCircle) < C/L+η := by
  let B : ℝ × ℝ → ℂ := fun p => A₀ (p.2 : UnitAddCircle) p.1
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) B ψ₀
  change ∃ C, _
  obtain ⟨hF,hcF,ε,hε,hz⟩ := exact_cutoff_weight_regular hm hR hV hdV hAr
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hψ₀ hcψ₀ h0
  have hKA : ∀ p : ℝ × ℝ, B p ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => Ioc_subset_Icc_self (hsupp _ hp)
  have hsF : tsupport F ⊆ I ×ˢ univ := by
    intro p hp
    exact ⟨(hsψ₀ (stationaryCutoffLift_support (continuous_const.mul hV.continuous)
      isCompact_Icc hKA hp).1).2,mem_univ _⟩
  obtain ⟨C,hC,hBound⟩ := neutral_branch_circle_l1_bound hF hcF hε hz
  refine ⟨C,hC,?_⟩
  intro L hL β J₀ J he hJ hj hJe
  have hinj : InjOn J₀ I := by
    intro a ha b hb hab
    rw [he a ha,he b hb] at hab
    nlinarith
  have hd : ∀ x ∈ I, deriv J₀ x ≠ 0 := fun x hx => by
    rw [deriv_affine_on hIo he hx]
    exact hL.ne'
  obtain ⟨S,hSN,hST,ht⟩ := exact_passage_circle_spectral_limit hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hδt hJ hIo hinj hd hj hJe
    hψ₀ hcψ₀ hsψ₀ heψ hψc hχc hcχ hzχ hψ hχ hχW hQ h
  refine ⟨S,hSN,hST,?_⟩
  intro η hη
  have hηt := ht.eventually (gt_mem_nhds hη)
  have hu (n : ℕ) (hn : 0 < n) :
      Integrable (foldCircleDensity (fun t => ∑ k ∈ S n,
        unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o' (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
          n ((h+k*(Q:ℤ):ℤ):ℝ) t)) AddCircle.haarAddCircle := by
    apply integrable_foldCircleDensity
    · exact (S n).measurable_fun_sum (fun k hk => (retained_unfolded_regular hJ hIo hinj hd
        hψc hχc (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
        o' hn (hSN n hn k hk)).1)
    · exact integrable_finsetSum _ (fun k hk => (retained_unfolded_regular hJ hIo hinj hd
        hψc hχc (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
        o' hn (hSN n hn k hk)).2)
  obtain ⟨hK,AK,hAK,MK,hsK,hyK⟩ := passageBranchKernel_regular hJ hIo hinj hd hF hcF hsF hε hz
  have hv (n : ℕ) (hn : 0 < n) := fineResidueKernel_regular (h := h) hK hAK hsK hyK hn hQ
  have hw := compact_slice_integral_regular ((hF.comp (contDiff_snd.prodMk contDiff_fst)).continuous)
    (hcF.comp_homeomorph (Homeomorph.prodComm ℝ ℝ))
  have hwi : Integrable (foldCircleDensity (fun s => (Q:ℝ)⁻¹*(∫ a, F (a,s))))
      AddCircle.haarAddCircle :=
    integrable_foldCircleDensity (measurable_const.mul hw.1.measurable) (hw.2.const_mul _)
  filter_upwards [hηt,eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hbn := hBound hIo hsF hQ hn0 h L hL β he
  exact (integral_abs_sub_triangle (hu n hn0)
    (integrable_foldCircleDensity (hv n hn0).1.measurable (hv n hn0).2) hwi).trans_lt
    (by linarith)

end ThreeTorus
end
end

section

/-! The two exact support separations in the passage and stage construction.
No spectral or asymptotic separation is substituted for actual disjoint sets. -/
noncomputable section
open Set Function
open scoped Topology
namespace ThreeTorus

/-- One integral shift separates the speed ranges for all distinct integer
angular indices in a finite list. It also keeps every range away from zero. -/
theorem exists_integral_speed_separation {ι X : Type*} [Finite ι]
    [TopologicalSpace X] [CompactSpace X] (m : ι → ℤ) (φ : X → ℝ)
    (hm : ∀ i, m i ≠ 0) (hφ : Continuous φ) :
    ∃ c : ℕ, 0 < c ∧
      (∀ i x, (m i : ℝ) * ((c:ℝ) + φ x) ≠ 0) ∧
      (∀ i j x y, (m i : ℝ) * ((c:ℝ) + φ x) =
        (m j : ℝ) * ((c:ℝ) + φ y) → m i = m j) := by
  obtain ⟨R,hR⟩ := (isCompact_range hφ).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (Set.finite_range (fun i => (m i : ℝ))).isCompact.isBounded.exists_norm_le
  let B := max R 0
  let M := max D 0
  have hB : 0 ≤ B := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hφB x : |φ x| ≤ B := (hR _ (mem_range_self x)).trans (le_max_left _ _)
  have hmM i : |(m i : ℝ)| ≤ M := (hD _ (mem_range_self i)).trans (le_max_left _ _)
  obtain ⟨c,hc⟩ := exists_nat_gt (2*M*B+B+1)
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hcB : B < (c:ℝ) := by nlinarith
  have hcp : (0:ℝ) < c := hB.trans_lt hcB
  refine ⟨c,by exact_mod_cast hcp,?_,?_⟩
  · intro i x
    apply mul_ne_zero (by exact_mod_cast hm i)
    have ht := (abs_le.mp (hφB x)).1
    linarith
  · intro i j x y he
    by_contra hij
    have hd : 1 ≤ |((m i-m j : ℤ):ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
    have he' : ((m i:ℝ)-(m j:ℝ))*(c:ℝ) = (m j:ℝ)*φ y-(m i:ℝ)*φ x := by
      nlinarith [he]
    have hh : |(m j:ℝ)*φ y-(m i:ℝ)*φ x| ≤ 2*M*B := calc
      _ ≤ |(m j:ℝ)*φ y|+|(m i:ℝ)*φ x| := abs_sub _ _
      _ = |(m j:ℝ)| *|φ y|+|(m i:ℝ)| *|φ x| := by rw [abs_mul,abs_mul]
      _ ≤ M*B+M*B := add_le_add
        (mul_le_mul (hmM j) (hφB y) (abs_nonneg _) hM)
        (mul_le_mul (hmM i) (hφB x) (abs_nonneg _) hM)
      _ = 2*M*B := by ring
    rw [← he',abs_mul,abs_of_pos hcp] at hh
    simp only [Int.cast_sub] at hd
    nlinarith

/-- A stationary image of an amplitude support. The pair records frequency
and the unchanged slow coordinate. -/
def stationaryImage (m : ℤ) (V : ℝ → ℝ) (K : Set (ℝ × UnitAddCircle)) :
    Set (ℝ × UnitAddCircle) :=
  (fun p : ℝ × UnitAddCircle => ((m:ℝ)*V p.1,p.2)) '' K

lemma stationaryImage_compact {m : ℤ} {V : ℝ → ℝ} {K : Set (ℝ × UnitAddCircle)}
    (hV : Continuous V) (hK : IsCompact K) : IsCompact (stationaryImage m V K) :=
  hK.image ((continuous_const.mul (hV.comp continuous_fst)).prodMk continuous_snd)

/-- For equal angular indices, branch injectivity preserves the exact gaps
between disjoint coefficient supports. -/
lemma stationaryImage_disjoint_same {m : ℤ} (hm : m ≠ 0) {V : ℝ → ℝ} {I : Set ℝ}
    (hV : InjOn V I) {K L : Set (ℝ × UnitAddCircle)}
    (hK : K ⊆ I ×ˢ univ) (hL : L ⊆ I ×ˢ univ) (hd : Disjoint K L) :
    Disjoint (stationaryImage m V K) (stationaryImage m V L) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p,hp,rfl⟩ ⟨q,hq,he⟩
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  have heV : V q.1 = V p.1 := mul_left_cancel₀ (by exact_mod_cast hm) he1
  have hep : q = p := Prod.ext (hV (hL hq).1 (hK hp).1 heV) he2
  exact Set.disjoint_left.mp hd hp (hep ▸ hq)

/-- Different angular indices are separated by their frequency ranges. -/
lemma stationaryImage_disjoint_distinct {m n : ℤ} {V : ℝ → ℝ}
    {K L : Set (ℝ × UnitAddCircle)}
    (hsep : ∀ p ∈ K, ∀ q ∈ L, (m:ℝ)*V p.1 ≠ (n:ℝ)*V q.1) :
    Disjoint (stationaryImage m V K) (stationaryImage n V L) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p,hp,rfl⟩ ⟨q,hq,he⟩
  exact hsep p hp q hq (congrArg Prod.fst he).symm

end ThreeTorus
end
end

end OAI
