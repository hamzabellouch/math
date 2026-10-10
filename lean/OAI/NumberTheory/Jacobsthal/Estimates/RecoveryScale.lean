import OAI.NumberTheory.Jacobsthal.Analysis.RieszMajorantIntegrals

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Set _root_.Filter

theorem exists_uniform_riesz_right_tails :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ X sigma T : ℝ, 0 < X → 1 < sigma → 0 < T →
      ‖∫ t in Iic (-T), characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        4*((sigma-1)⁻¹+C)*X^sigma/T ∧
      ‖∫ t in Ici T, characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        4*((sigma-1)⁻¹+C)*X^sigma/T := by
  obtain ⟨C,hC,hbound⟩ := uniform_log_derivative_right
  refine ⟨C,hC,?_⟩
  intro q _ chi hchi X sigma T hX hs hT
  let B : ℝ := (sigma-1)⁻¹+C
  let D : ℝ := B*X^sigma
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hpoint (t:ℝ) : ‖characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      D*((4:ℝ)/(1+t^2)) := by
    have hre : ((sigma:ℂ)+(t:ℂ)*Complex.I).re = sigma := by simp
    have hb : ‖logDeriv (DirichletCharacter.LFunction chi) ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B := by
      simpa only [logDeriv_apply,hre,B] using
        hbound q chi ((sigma:ℂ)+(t:ℂ)*Complex.I) (by simpa only [hre] using hs)
    rw [norm_characterRieszIntegrand chi hX,hre]
    calc
      _ ≤ B*‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖*X^sigma := by gcongr
      _ = D*‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ := by dsimp only [D]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (rieszKernel_norm_bound (by linarith) t) hD
  have hf := integrable_characterRiesz_right chi hchi hs hX
  have hg := rieszMajorant_integrable.const_mul D
  have htail (S:Set ℝ) (hbudget : (∫ t in S, (4:ℝ)/(1+t^2)) ≤ 4/T) :
      ‖∫ t in S, characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        4*((sigma-1)⁻¹+C)*X^sigma/T := by
    calc
      _ ≤ ∫ t in S, ‖characterRieszIntegrand chi X ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t in S, D*((4:ℝ)/(1+t^2)) :=
        integral_mono (μ := volume.restrict S) hf.norm.integrableOn hg.integrableOn hpoint
      _ = D*(∫ t in S, (4:ℝ)/(1+t^2)) := integral_const_mul _ _
      _ ≤ D*(4/T) := mul_le_mul_of_nonneg_left hbudget hD
      _ = _ := by dsimp only [D,B]; ring
  exact ⟨htail (Iic (-T)) (rieszMajorant_lower_tail hT),
    htail (Ici T) (rieszMajorant_upper_tail hT)⟩

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex _root_.MeasureTheory
open scoped Interval

lemma riesz_left_edge_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X left right T C : ℝ} (hX : 0 < X) (hl : 1/2 ≤ left) (hlr : left ≤ right)
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc left right ×ℂ Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3)
    (hf : _root_.Erdos970.HolomorphicOn (characterRieszIntegrand chi X) (Icc left right ×ℂ Icc (-T) T)) :
    ‖_root_.Erdos970.VIntegral (characterRieszIntegrand chi X) left (-T) T‖ ≤
      4*Real.pi*C*(modulusHeight q T)^3*X^left := by
  let B : ℝ := C*(modulusHeight q T)^3*X^left
  have hH := modulusHeight_ge_one q T
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hTT : -T ≤ T := by linarith
  have hmaps : MapsTo (fun t:ℝ => (left:ℂ)+(t:ℂ)*Complex.I) (Icc (-T) T)
      (Icc left right ×ℂ Icc (-T) T) := by
    intro t ht
    simp only [Complex.mem_reProdIm,show ((left:ℂ)+(t:ℂ)*Complex.I).re = left by simp,
      show ((left:ℂ)+(t:ℂ)*Complex.I).im = t by simp]
    exact ⟨⟨le_rfl,hlr⟩,ht⟩
  have hc : ContinuousOn (fun t:ℝ => characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I))
      (Icc (-T) T) := hf.continuousOn.comp (by fun_prop) hmaps
  have hfi : IntervalIntegrable (fun t:ℝ => characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I))
      volume (-T) T := (show ContinuousOn _ (uIcc (-T) T) by simpa only [uIcc_of_le hTT] using hc).intervalIntegrable
  have hg := (rieszMajorant_integrable.const_mul B).intervalIntegrable (a := -T) (b := T)
  have hpoint : ∀ t ∈ Icc (-T) T,
      ‖characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I)‖ ≤ B*((4:ℝ)/(1+t^2)) := by
    intro t ht
    have hlog := hb _ (hmaps ht)
    rw [norm_characterRieszIntegrand chi hX,show ((left:ℂ)+(t:ℂ)*Complex.I).re = left by simp]
    calc
      _ ≤ (C*(modulusHeight q T)^3)*‖rieszKernel ((left:ℂ)+(t:ℂ)*Complex.I)‖*X^left := by gcongr
      _ = B*‖rieszKernel ((left:ℂ)+(t:ℂ)*Complex.I)‖ := by dsimp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (rieszKernel_norm_bound hl t) hB
  have hcomp := intervalIntegral.integral_mono_on hTT hfi.norm hg hpoint
  rw [intervalIntegral.integral_const_mul] at hcomp
  have hmajor := mul_le_mul_of_nonneg_left (rieszMajorant_interval_le T) hB
  rw [norm_VIntegral_eq]
  calc
    _ ≤ ∫ t in (-T)..T, ‖characterRieszIntegrand chi X ((left:ℂ)+(t:ℂ)*Complex.I)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hTT
    _ ≤ B*(4*Real.pi) := hcomp.trans hmajor
    _ = _ := by dsimp only [B]; ring

lemma riesz_horizontal_edge_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X left right T height C : ℝ} (hX : 1 ≤ X) (hl : 1/2 ≤ left) (hlr : left ≤ right)
    (hr : right ≤ 2) (_hT : 0 ≤ T) (hy : |height| = T) (hC : 0 ≤ C)
    (hb : ∀ s ∈ Icc left right ×ℂ Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3)
    (hf : _root_.Erdos970.HolomorphicOn (characterRieszIntegrand chi X) (Icc left right ×ℂ Icc (-T) T)) :
    ‖_root_.Erdos970.HIntegral (characterRieszIntegrand chi X) left right height‖ ≤
      8*C*(modulusHeight q T)^3*X^right/(1+T^2) := by
  have hXp : 0 < X := by linarith
  let B : ℝ := C*(modulusHeight q T)^3*X^right*((4:ℝ)/(1+T^2))
  have hH := modulusHeight_ge_one q T
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hmaps : MapsTo (fun x:ℝ => (x:ℂ)+(height:ℂ)*Complex.I) (Icc left right)
      (Icc left right ×ℂ Icc (-T) T) := by
    intro x hx
    simp only [Complex.mem_reProdIm,show ((x:ℂ)+(height:ℂ)*Complex.I).re = x by simp,
      show ((x:ℂ)+(height:ℂ)*Complex.I).im = height by simp]
    exact ⟨hx,abs_le.mp hy.le⟩
  have hc : ContinuousOn (fun x:ℝ => characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I))
      (Icc left right) := hf.continuousOn.comp (by fun_prop) hmaps
  have hfi : IntervalIntegrable (fun x:ℝ => characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I))
      volume left right := (show ContinuousOn _ (uIcc left right) by simpa only [uIcc_of_le hlr] using hc).intervalIntegrable
  have hpoint : ∀ x ∈ Icc left right,
      ‖characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I)‖ ≤ B := by
    intro x hx
    have hlog := hb _ (hmaps hx)
    have hkernel := rieszKernel_norm_bound (hl.trans hx.1) height
    have hsq : height^2 = T^2 := by rw [← sq_abs height,hy]
    rw [hsq] at hkernel
    have hpow := Real.rpow_le_rpow_of_exponent_le hX hx.2
    rw [norm_characterRieszIntegrand chi hXp,show ((x:ℂ)+(height:ℂ)*Complex.I).re = x by simp]
    calc
      _ ≤ (C*(modulusHeight q T)^3)*((4:ℝ)/(1+T^2))*X^right := by gcongr
      _ = B := by dsimp only [B]; ring
  have hcomp := intervalIntegral.integral_mono_on hlr hfi.norm (intervalIntegrable_const (c := B)) hpoint
  rw [intervalIntegral.integral_const] at hcomp
  have hwidth : right-left ≤ 2 := by linarith
  have hwidthB := mul_le_mul_of_nonneg_right hwidth hB
  unfold _root_.Erdos970.HIntegral
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x:ℝ => characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I)) hlr
  have hbound : ‖∫ x in left..right, characterRieszIntegrand chi X ((x:ℂ)+(height:ℂ)*Complex.I)‖ ≤ 2*B := by
    simp only [smul_eq_mul] at hcomp
    linarith
  apply hbound.trans_eq
  dsimp only [B]
  ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Set _root_.Complex _root_.MeasureTheory

lemma norm_mellinFactor : ‖mellinFactor‖ = 1/(2*Real.pi) := by
  unfold mellinFactor
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]

theorem exists_uniform_riesz_contour_bound :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q), chi ≠ 1 →
      ∀ X sigma T : ℝ, 1 ≤ X → 1 < sigma → sigma ≤ 2 → 0 < T →
      ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        (1/(2*Real.pi)) *
          (4*Real.pi*C*(modulusHeight q T)^3*X^(rieszContourLeft a q T) +
            16*C*(modulusHeight q T)^3*X^sigma/(1+T^2) +
            8*((sigma-1)⁻¹+B)*X^sigma/T) := by
  obtain ⟨a,ha,ha100,C,hC,hrect⟩ := exists_uniform_riesz_rectangle
  obtain ⟨B,hB,htails⟩ := exists_uniform_riesz_right_tails
  refine ⟨a,ha,ha100,C,hC,B,hB,?_⟩
  intro q _ chi hchi X sigma T hX hs hs2 hT
  have hXp : 0 < X := by linarith
  obtain ⟨hl,hzero,hhol⟩ := hrect q chi hchi X sigma T hXp hs hs2 hT
  let left : ℝ := rieszContourLeft a q T
  have hlr : left ≤ sigma := by
    have hdiv : 0 ≤ a/(modulusHeight q T)^2 := div_nonneg ha.le (sq_nonneg _)
    dsimp only [left,rieszContourLeft]
    linarith
  have hlog : ∀ s ∈ Icc left sigma ×ℂ Icc (-T) T,
      ‖logDeriv (DirichletCharacter.LFunction chi) s‖ ≤ C*(modulusHeight q T)^3 :=
    fun s hmem => (hzero s hmem).2
  have hleft := riesz_left_edge_bound chi hXp hl hlr hT.le hC.le hlog hhol
  have hdown := riesz_horizontal_edge_bound chi (height := -T) hX hl hlr hs2 hT.le
    (by rw [abs_neg,abs_of_nonneg hT.le]) hC.le hlog hhol
  have hup := riesz_horizontal_edge_bound chi (height := T) hX hl hlr hs2 hT.le
    (abs_of_nonneg hT.le) hC.le hlog hhol
  obtain ⟨htlo,hthi⟩ := htails q chi hchi X sigma T hXp hs hT
  have hshift := norm_full_vertical_shift_le (characterRieszIntegrand chi X) left sigma T hlr hT.le
    hhol (integrable_characterRiesz_right chi hchi hs hXp)
  let E : ℝ := 4*Real.pi*C*(modulusHeight q T)^3*X^left +
    16*C*(modulusHeight q T)^3*X^sigma/(1+T^2) + 8*((sigma-1)⁻¹+B)*X^sigma/T
  have hfull : ‖_root_.Erdos970.VerticalIntegral (characterRieszIntegrand chi X) sigma‖ ≤ E := by
    have hp := add_le_add (add_le_add (add_le_add (add_le_add htlo hleft) hdown) hup) hthi
    apply (hshift.trans hp).trans_eq
    dsimp only [E,left]
    ring
  rw [finite_riesz_eq_integrand chi hs hXp,norm_mul,norm_mellinFactor,
    ← norm_verticalIntegral_eq (characterRieszIntegrand chi X) sigma]
  exact mul_le_mul_of_nonneg_left hfull (by positivity)

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_log_cube_le (K b : ℝ) (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, 3 ≤ L ∧ K*(Real.log L)^3 ≤ b*L := by
  have hbase := Real.tendsto_pow_log_div_mul_add_atTop (1:ℝ) 0 3 one_ne_zero
  have hlim : Tendsto (fun L:ℝ => K*(Real.log L)^3/L) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero,mul_zero,mul_div_assoc] using hbase.const_mul K
  filter_upwards [eventually_ge_atTop (3:ℝ),hlim.eventually (gt_mem_nhds hb)] with L hL hsmall
  refine ⟨hL,?_⟩
  exact (div_le_iff₀ (by linarith : 0 < L)).mp hsmall.le

lemma polylog_height_bound (A D : ℝ) (hD : 0 ≤ D) {L : ℝ} (hL : 3 ≤ L)
    (q : ℕ) [NeZero q] (hq : (q:ℝ) ≤ L^A) :
    modulusHeight q (L^D) ≤ (A+D+Real.log 7)*Real.log L := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hT : 1 ≤ L^D := Real.one_le_rpow hL1 hD
  have hTp : 0 < L^D := Real.rpow_pos_of_pos hLp _
  have hlogL : 1 < Real.log L :=
    (Real.lt_log_iff_exp_lt hLp).mpr (Real.exp_one_lt_three.trans_le hL)
  have hqpos : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hlogq := Real.log_le_log hqpos hq
  rw [Real.log_rpow hLp] at hlogq
  have hlogT : Real.log (L^D+6) ≤ Real.log (7*(L^D)) :=
    Real.log_le_log (by positivity) (by nlinarith only [hT])
  rw [Real.log_mul (by norm_num : (7:ℝ) ≠ 0) hTp.ne',Real.log_rpow hLp] at hlogT
  have hlog7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have h7 := mul_le_mul_of_nonneg_left hlogL.le hlog7
  unfold modulusHeight
  rw [abs_of_nonneg hTp.le]
  nlinarith only [hlogq,hlogT,h7]

lemma div_rpow_add_one {L : ℝ} (hL : 0 < L) (R : ℝ) : L/L^(R+1) = L^(-R) := by
  have hn := (Real.rpow_pos_of_pos hL R).ne'
  rw [Real.rpow_add hL,Real.rpow_one,Real.rpow_neg hL.le]
  field_simp

theorem eventually_polylog_contour_savings (a A R : ℝ) (ha : 0 < a) (hA : 0 < A) (hR : 0 < R) :
    ∀ᶠ X : ℝ in atTop, 3 ≤ X ∧ ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ (Real.log X)^A →
      let L : ℝ := Real.log X
      let T : ℝ := L^(R+2)
      3 ≤ L ∧ 1 ≤ T ∧
        (modulusHeight q T)^3*Real.exp (-a*L/(modulusHeight q T)^2) ≤ L^(-R) ∧
        (modulusHeight q T)^3/(1+T^2) ≤ L^(-R) ∧ L/T ≤ L^(-R) := by
  let K : ℝ := A+(R+2)+Real.log 7
  have h7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by dsimp only [K]; linarith
  have he1 := Real.tendsto_log_atTop.eventually (eventually_log_cube_le (K^3) 1 zero_lt_one)
  have he2 := Real.tendsto_log_atTop.eventually (eventually_log_cube_le ((R+2)*K^2) a ha)
  filter_upwards [eventually_ge_atTop (3:ℝ),he1,he2] with X hX h1 h2
  refine ⟨hX,?_⟩
  intro q _ hq
  let L : ℝ := Real.log X
  let T : ℝ := L^(R+2)
  let H : ℝ := modulusHeight q T
  have hL : 3 ≤ L := h1.1
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  have hT : 1 ≤ T := Real.one_le_rpow hL1 (by linarith)
  have hTp : 0 < T := by linarith
  have hH : 1 ≤ H := modulusHeight_ge_one q T
  have hHp : 0 < H := by linarith
  have hheight : H ≤ K*Real.log L := polylog_height_bound A (R+2) (by linarith) hL q hq
  have hH3 : H^3 ≤ L := by
    calc
      _ ≤ (K*Real.log L)^3 := by gcongr
      _ = K^3*(Real.log L)^3 := by ring
      _ ≤ L := by simpa only [one_mul] using h1.2
  have hH2 : H^2 ≤ K^2*(Real.log L)^2 := by
    calc
      _ ≤ (K*Real.log L)^2 := by gcongr
      _ = _ := by ring
  have hguard : (R+2)*Real.log L*H^2 ≤ a*L := by
    calc
      _ ≤ (R+2)*Real.log L*(K^2*(Real.log L)^2) := by gcongr
      _ = ((R+2)*K^2)*(Real.log L)^3 := by ring
      _ ≤ a*L := h2.2
  have hsave : (R+2)*Real.log L ≤ a*L/H^2 := (le_div_iff₀ (by positivity)).mpr hguard
  have hexp : Real.exp (-a*L/H^2) ≤ L^(-(R+2)) := by
    rw [Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    calc
      _ = -(a*L/H^2) := by ring
      _ ≤ -((R+2)*Real.log L) := neg_le_neg hsave
      _ = _ := by ring
  have hratio : L/T ≤ L^(-R) := by
    calc
      _ ≤ L/L^(R+1) := div_le_div_of_nonneg_left hLp.le (Real.rpow_pos_of_pos hLp _)
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
      _ = _ := div_rpow_add_one hLp R
  change 3 ≤ L ∧ 1 ≤ T ∧ H^3*Real.exp (-a*L/H^2) ≤ L^(-R) ∧ H^3/(1+T^2) ≤ L^(-R) ∧ L/T ≤ L^(-R)
  refine ⟨hL,hT,?_,?_,hratio⟩
  · calc
      _ ≤ L*L^(-(R+2)) := mul_le_mul hH3 hexp (Real.exp_nonneg _) hLp.le
      _ = L/T := by dsimp only [T]; rw [Real.rpow_neg hLp.le,div_eq_mul_inv]
      _ ≤ _ := hratio
  · calc
      _ ≤ L/(1+T^2) := div_le_div_of_nonneg_right hH3 (by positivity)
      _ ≤ L/T := div_le_div_of_nonneg_left hLp.le hTp (by nlinarith only [hT])
      _ ≤ _ := hratio

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma rpow_perron_sigma {X : ℝ} (hX : 1 < X) :
    X^(1+(Real.log X)⁻¹) = X*Real.exp 1 := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < X),mul_add,mul_one,
    mul_inv_cancel₀ (Real.log_pos hX).ne',Real.exp_add,Real.exp_log (by linarith : 0 < X)]

lemma rpow_rieszContourLeft {X : ℝ} (hX : 0 < X) (a : ℝ) (q : ℕ) (T : ℝ) :
    X^(rieszContourLeft a q T) = X*Real.exp (-a*Real.log X/(modulusHeight q T)^2) := by
  rw [Real.rpow_def_of_pos hX]
  have he : Real.log X*rieszContourLeft a q T =
      Real.log X+(-a*Real.log X/(modulusHeight q T)^2) := by unfold rieszContourLeft; ring
  rw [he,Real.exp_add,Real.exp_log hX]

theorem riesz_character_log_power (A R : ℝ) (hA : 0 < A) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), chi ≠ 1 → (q:ℝ) ≤ (Real.log X)^A →
      ‖rieszSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤ K*X/(Real.log X)^R := by
  obtain ⟨a,ha,_ha100,C,hC,B,hB,hcontour⟩ := exists_uniform_riesz_contour_bound
  let P : ℝ := 4*Real.pi*C+16*C*Real.exp 1+8*(B+1)*Real.exp 1
  let K : ℝ := (1/(2*Real.pi))*P
  have hP : 0 < P := by dsimp only [P]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_polylog_contour_savings a A R ha hA hR] with X hX
  intro q _ chi hchi hq
  obtain ⟨hX3,hSavings⟩ := hX
  obtain ⟨hL3,hT1,hleft,hhor,hratio⟩ := hSavings q hq
  let L : ℝ := Real.log X
  let T : ℝ := L^(R+2)
  let H : ℝ := modulusHeight q T
  let sigma : ℝ := 1+L⁻¹
  have hXp : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hLp : 0 < L := by linarith
  have hTp : 0 < T := by linarith
  have hs1 : 1 < sigma := by
    have hi : 0 < L⁻¹ := inv_pos.mpr hLp
    dsimp only [sigma]
    linarith
  have hs2 : sigma ≤ 2 := by
    have hinv : L⁻¹ ≤ 1 := by rw [← one_div]; exact (div_le_iff₀ hLp).mpr (by linarith)
    dsimp only [sigma]
    linarith
  have h := hcontour q chi hchi X sigma T (by linarith) hs1 hs2 hTp
  have hrightpow : X^sigma = X*Real.exp 1 := rpow_perron_sigma hX1
  have hleftpow : X^(rieszContourLeft a q T) = X*Real.exp (-a*L/H^2) := rpow_rieszContourLeft hXp a q T
  have hinv : (sigma-1)⁻¹ = L := by dsimp only [sigma]; rw [add_sub_cancel_left,inv_inv]
  rw [hrightpow,hleftpow,hinv] at h
  change H^3*Real.exp (-a*L/H^2) ≤ L^(-R) at hleft
  change H^3/(1+T^2) ≤ L^(-R) at hhor
  change L/T ≤ L^(-R) at hratio
  have hBL := mul_le_mul_of_nonneg_left (show 1 ≤ L by linarith) hB
  have hLB : L+B ≤ (B+1)*L := by nlinarith only [hBL]
  have htail : (L+B)/T ≤ (B+1)*L^(-R) := by
    calc
      _ ≤ ((B+1)*L)/T := div_le_div_of_nonneg_right hLB hTp.le
      _ = (B+1)*(L/T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hleft (show 0 ≤ 4*Real.pi*C*X by positivity)
  have h2 := mul_le_mul_of_nonneg_left hhor (show 0 ≤ 16*C*Real.exp 1*X by positivity)
  have h3 := mul_le_mul_of_nonneg_left htail (show 0 ≤ 8*Real.exp 1*X by positivity)
  have he : 4*Real.pi*C*H^3*(X*Real.exp (-a*L/H^2)) +
      16*C*H^3*(X*Real.exp 1)/(1+T^2)+8*(L+B)*(X*Real.exp 1)/T ≤ P*X*L^(-R) := by
    calc
      _ = (4*Real.pi*C*X)*(H^3*Real.exp (-a*L/H^2)) +
          (16*C*Real.exp 1*X)*(H^3/(1+T^2))+(8*Real.exp 1*X)*((L+B)/T) := by ring
      _ ≤ (4*Real.pi*C*X)*L^(-R)+(16*C*Real.exp 1*X)*L^(-R)+
          (8*Real.exp 1*X)*((B+1)*L^(-R)) := add_le_add (add_le_add h1 h2) h3
      _ = _ := by dsimp only [P]; ring
  apply h.trans
  calc
    _ ≤ (1/(2*Real.pi))*(P*X*L^(-R)) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = K*X/(Real.log X)^R := by dsimp only [K]; rw [Real.rpow_neg hLp.le]; ring

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz

noncomputable def rieszDifferenceWeight (delta u : ℝ) : ℝ :=
  (max (1+delta-u) 0-max (1-u) 0)/delta

lemma rieszWeight_scaled {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    (1+delta)*rieszWeight (u/(1+delta)) = max (1+delta-u) 0 := by
  have hp : 0 < 1+delta := by linarith
  by_cases hu : u ≤ 1+delta
  · have hratio : u/(1+delta) ≤ 1 := (div_le_iff₀ hp).mpr (by linarith)
    simp only [rieszWeight,max_eq_left (sub_nonneg.mpr hratio),max_eq_left (sub_nonneg.mpr hu)]
    field_simp
  · have hratio : 1 ≤ u/(1+delta) := (le_div_iff₀ hp).mpr (by linarith)
    simp only [rieszWeight,max_eq_right (sub_nonpos.mpr hratio),
      max_eq_right (show 1+delta-u ≤ 0 by linarith),mul_zero]

lemma rieszDifferenceWeight_eq {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    rieszDifferenceWeight delta u =
      ((1+delta)*rieszWeight (u/(1+delta))-rieszWeight u)/delta := by
  rw [rieszWeight_scaled hd]
  rfl

lemma rieszDifferenceWeight_nonneg {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    0 ≤ rieszDifferenceWeight delta u := by
  unfold rieszDifferenceWeight
  apply div_nonneg _ hd.le
  exact sub_nonneg.mpr (max_le_max (by linarith) le_rfl)

lemma rieszDifferenceWeight_le_one {delta : ℝ} (hd : 0 < delta) (u : ℝ) :
    rieszDifferenceWeight delta u ≤ 1 := by
  have hm : max (1+delta-u) 0 ≤ max (1-u) 0+delta := by
    apply max_le
    · have h := le_max_left (1-u) 0
      linarith
    · have h := le_max_right (1-u) 0
      linarith
  unfold rieszDifferenceWeight
  exact (div_le_iff₀ hd).mpr (by linarith)

lemma rieszDifferenceWeight_eq_one {delta u : ℝ} (hd : 0 < delta) (hu : u ≤ 1) :
    rieszDifferenceWeight delta u = 1 := by
  unfold rieszDifferenceWeight
  rw [max_eq_left (show 0 ≤ 1+delta-u by linarith),max_eq_left (show 0 ≤ 1-u by linarith)]
  have he : 1+delta-u-(1-u) = delta := by ring
  rw [he,div_self hd.ne']

lemma rieszDifferenceWeight_eq_zero {delta u : ℝ} (hd : 0 < delta) (hu : 1+delta ≤ u) :
    rieszDifferenceWeight delta u = 0 := by
  simp only [rieszDifferenceWeight,max_eq_right (show 1+delta-u ≤ 0 by linarith),
    max_eq_right (show 1-u ≤ 0 by linarith),sub_self,zero_div]

lemma riesz_rescaled_difference {delta X : ℝ} (hd : 0 < delta) (_hX : 0 < X) (n : ℝ) :
    ((1+delta)*rieszWeight (n/((1+delta)*X))-rieszWeight (n/X))/delta =
      rieszDifferenceWeight delta (n/X) := by
  rw [rieszDifferenceWeight_eq hd]
  have he : n/((1+delta)*X) = (n/X)/(1+delta) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]




open scoped BigOperators

noncomputable def sharpSum (f : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), f n
noncomputable def rieszRecovery (f : ℕ → ℂ) (X delta : ℝ) : ℂ :=
  (((1+delta:ℝ):ℂ)*rieszSum f ((1+delta)*X)-rieszSum f X)/(delta:ℂ)

lemma rieszSum_extend (f : ℕ → ℂ) {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    rieszSum f X = ∑ n ∈ Finset.range (⌊Y⌋₊+1), f n*(rieszWeight ((n:ℝ)/X):ℂ) := by
  rw [← tsum_riesz_eq_finite f hX]
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌊Y⌋₊ < n := by simp only [Finset.mem_range] at hn; omega
  have hYn : Y < (n:ℝ) := (Nat.floor_lt (hX.le.trans hXY)).mp hn'
  have hw := rieszWeight_eq_zero (x := (n:ℝ)/X) ((le_div_iff₀ hX).mpr (by linarith))
  rw [hw,Complex.ofReal_zero,mul_zero]

lemma rieszRecovery_eq_sum (f : ℕ → ℂ) {X delta : ℝ} (hX : 0 < X) (hd : 0 < delta) :
    rieszRecovery f X delta =
      ∑ n ∈ Finset.range (⌊(1+delta)*X⌋₊+1), f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ) := by
  have hXY : X ≤ (1+delta)*X := by nlinarith [mul_pos hd hX]
  unfold rieszRecovery
  rw [rieszSum_extend f hX hXY]
  unfold rieszSum
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  have hw := congrArg Complex.ofReal (riesz_rescaled_difference hd hX (n:ℝ))
  push_cast at hw
  calc
    _ = f n * ((((1+delta:ℝ):ℂ)*(rieszWeight ((n:ℝ)/((1+delta)*X)):ℂ)-
        (rieszWeight ((n:ℝ)/X):ℂ))/(delta:ℂ)) := by ring
    _ = _ := by push_cast; rw [hw]

lemma rieszRecovery_sub_sharp (f : ℕ → ℂ) {X delta : ℝ} (hX : 0 < X) (hd : 0 < delta) :
    rieszRecovery f X delta-sharpSum f X =
      ∑ n ∈ Finset.Ico (⌊X⌋₊+1) (⌊(1+delta)*X⌋₊+1),
        f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ) := by
  have hXY : X ≤ (1+delta)*X := by nlinarith [mul_pos hd hX]
  have hfloor : ⌊X⌋₊+1 ≤ ⌊(1+delta)*X⌋₊+1 := Nat.add_le_add_right (Nat.floor_mono hXY) 1
  have hprefix : (∑ n ∈ Finset.range (⌊X⌋₊+1),
      f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)) = sharpSum f X := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n ≤ ⌊X⌋₊ := by simp only [Finset.mem_range] at hn; omega
    have hnX : (n:ℝ) ≤ X := (show (n:ℝ) ≤ (⌊X⌋₊:ℝ) by exact_mod_cast hn').trans (Nat.floor_le hX.le)
    rw [rieszDifferenceWeight_eq_one hd ((div_le_iff₀ hX).mpr (by linarith)),Complex.ofReal_one,mul_one]
  have hs := Finset.sum_range_add_sum_Ico (fun n:ℕ => f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)) hfloor
  rw [hprefix] at hs
  rw [rieszRecovery_eq_sum f hX hd,← hs,add_sub_cancel_left]

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

theorem norm_rieszRecovery_sub_sharp (f : ℕ → ℂ)
    (hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ))
    {X delta : ℝ} (hX : 1 ≤ X) (hd : 0 < delta) :
    ‖rieszRecovery f X delta-sharpSum f X‖ ≤ (delta*X+1)*Real.log ((1+delta)*X) := by
  have hXp : 0 < X := by linarith
  let Y : ℝ := (1+delta)*X
  have hXY : X ≤ Y := by dsimp only [Y]; nlinarith [mul_pos hd hXp]
  have hY1 : 1 ≤ Y := hX.trans hXY
  have hYp : 0 < Y := by linarith
  have hfloor : ⌊X⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hXY
  let S := Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1)
  have hcard : (S.card:ℝ) ≤ delta*X+1 := by
    dsimp only [S]
    rw [Nat.card_Ico,Nat.cast_sub (Nat.add_le_add_right hfloor 1)]
    push_cast
    have hy := Nat.floor_le hYp.le
    have hx := Nat.lt_floor_add_one X
    dsimp only [Y] at hy
    nlinarith
  have hpoint (n:ℕ) (hn : n ∈ S) :
      ‖f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ ≤ Real.log Y := by
    have hn' := Finset.mem_Ico.mp hn
    have hnp : 0 < n := by omega
    have hnf : n ≤ ⌊Y⌋₊ := by omega
    have hnY : (n:ℝ) ≤ Y := (show (n:ℝ) ≤ (⌊Y⌋₊:ℝ) by exact_mod_cast hnf).trans (Nat.floor_le hYp.le)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (rieszDifferenceWeight_nonneg hd _)]
    calc
      _ ≤ ‖f n‖ := by
        have h := mul_le_mul_of_nonneg_left (rieszDifferenceWeight_le_one hd ((n:ℝ)/X)) (norm_nonneg (f n))
        simpa only [mul_one] using h
      _ ≤ Real.log (n:ℝ) := hcoeff n hnp
      _ ≤ Real.log Y := Real.log_le_log (by exact_mod_cast hnp) hnY
  rw [rieszRecovery_sub_sharp f hXp hd]
  change ‖∑ n ∈ S, f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ ≤ (delta*X+1)*Real.log Y
  calc
    _ ≤ ∑ n ∈ S, ‖f n*(rieszDifferenceWeight delta ((n:ℝ)/X):ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, Real.log Y := Finset.sum_le_sum hpoint
    _ = (S.card:ℝ)*Real.log Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.log_nonneg hY1)

lemma norm_rieszRecovery_le (f : ℕ → ℂ) (X : ℝ) {delta : ℝ} (hd : 0 < delta) :
    ‖rieszRecovery f X delta‖ ≤
      ((1+delta)*‖rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖)/delta := by
  unfold rieszRecovery
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ ‖((1+delta:ℝ):ℂ)*rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < 1+delta)]

theorem sharpSum_norm_le_riesz (f : ℕ → ℂ)
    (hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ))
    {X delta : ℝ} (hX : 1 ≤ X) (hd : 0 < delta) :
    ‖sharpSum f X‖ ≤
      ((1+delta)*‖rieszSum f ((1+delta)*X)‖+‖rieszSum f X‖)/delta +
        (delta*X+1)*Real.log ((1+delta)*X) := by
  have he := norm_rieszRecovery_sub_sharp f hcoeff hX hd
  have hr := norm_rieszRecovery_le f X hd
  have ht := norm_add_le (sharpSum f X-rieszRecovery f X delta) (rieszRecovery f X delta)
  rw [sub_add_cancel,norm_sub_rev] at ht
  linarith

end Erdos970Dependency.SiegelWalfisz



namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

lemma eventually_log_rpow_le_self (k : ℝ) :
    ∀ᶠ X : ℝ in atTop, 3 ≤ X ∧ (Real.log X)^k ≤ X := by
  let N : ℕ := ⌈k⌉₊
  have hkN : k ≤ (N:ℝ) := Nat.le_ceil k
  have hbase := Real.tendsto_pow_log_div_mul_add_atTop (1:ℝ) 0 N one_ne_zero
  have hlim : Tendsto (fun X:ℝ => (Real.log X)^N/X) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero] using hbase
  filter_upwards [eventually_ge_atTop (3:ℝ),hlim.eventually (gt_mem_nhds zero_lt_one)] with X hX hsmall
  have hXp : 0 < X := by linarith
  have hlog : 1 ≤ Real.log X := ((Real.lt_log_iff_exp_lt hXp).mpr (Real.exp_one_lt_three.trans_le hX)).le
  have hnat : (Real.log X)^N ≤ X := by
    have h := (div_le_iff₀ hXp).mp hsmall.le
    simpa only [one_mul] using h
  refine ⟨hX,?_⟩
  calc
    _ ≤ (Real.log X)^(N:ℝ) := Real.rpow_le_rpow_of_exponent_le hlog hkN
    _ = (Real.log X)^N := Real.rpow_natCast _ _
    _ ≤ X := hnat

lemma character_vonMangoldt_norm_le {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (n : ℕ) :
    ‖chi n*(ArithmeticFunction.vonMangoldt n:ℂ)‖ ≤ Real.log (n:ℝ) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (chi.norm_le_one n)
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    _ ≤ _ := ArithmeticFunction.vonMangoldt_le_log

lemma recovery_scale_bounds (k : ℝ) (hk : 0 < k) {X : ℝ}
    (hX : 3 ≤ X) (hpow : (Real.log X)^k ≤ X) :
    let delta : ℝ := (Real.log X)^(-k)
    let Y : ℝ := (1+delta)*X
    0 < delta ∧ delta ≤ 1 ∧ 1 ≤ delta*X ∧ X ≤ Y ∧ Y ≤ 2*X ∧
      Real.log X ≤ Real.log Y ∧ Real.log Y ≤ 2*Real.log X := by
  let L : ℝ := Real.log X
  let delta : ℝ := L^(-k)
  let Y : ℝ := (1+delta)*X
  have hXp : 0 < X := by linarith
  have hL : 1 ≤ L := ((Real.lt_log_iff_exp_lt hXp).mpr (Real.exp_one_lt_three.trans_le hX)).le
  have hLp : 0 < L := by linarith
  have hp : 0 < L^k := Real.rpow_pos_of_pos hLp _
  have hp1 : 1 ≤ L^k := Real.one_le_rpow hL hk.le
  have hd : 0 < delta := Real.rpow_pos_of_pos hLp _
  have hd1 : delta ≤ 1 := by
    dsimp only [delta]
    rw [Real.rpow_neg hLp.le,← one_div]
    exact (div_le_iff₀ hp).mpr (by linarith)
  have hprod : delta*L^k = 1 := by
    dsimp only [delta]
    rw [Real.rpow_neg hLp.le,inv_mul_cancel₀ hp.ne']
  have hdX : 1 ≤ delta*X := by
    have h := mul_le_mul_of_nonneg_left hpow hd.le
    change delta*L^k ≤ delta*X at h
    rwa [hprod] at h
  have hXY : X ≤ Y := by dsimp only [Y]; nlinarith
  have hY2 : Y ≤ 2*X := by
    have h := mul_le_mul_of_nonneg_right hd1 hXp.le
    dsimp only [Y]
    nlinarith
  have hYp : 0 < Y := hXp.trans_le hXY
  have hlogs : Real.log X ≤ Real.log Y := Real.log_le_log hXp hXY
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
  have hlogY : Real.log Y ≤ 2*Real.log X := by
    have h := Real.log_le_log hYp hY2
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hXp.ne'] at h
    linarith
  exact ⟨hd,hd1,hdX,hXY,hY2,hlogs,hlogY⟩

lemma recovery_power_product {L : ℝ} (hL : 0 < L) (k : ℝ) :
    L^(-k)*L^(2*k) = L^k := by
  rw [← Real.rpow_add hL]
  congr 1
  ring

lemma recovery_power_times_log {L : ℝ} (hL : 0 < L) (M : ℝ) :
    L^(-(M+1))*L = L^(-M) := by
  calc
    _ = L^(-(M+1))*L^(1:ℝ) := by rw [Real.rpow_one]
    _ = L^(-(M+1)+1) := (Real.rpow_add hL _ _).symm
    _ = _ := by congr 1; ring

end Erdos970Dependency.SiegelWalfisz


end Erdos970

end OAI
