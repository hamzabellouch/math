import OAI.Geometry.LatticeCovering.GaussianSmoothing

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

lemma integral_RV_zero (f : RV 0 → ℝ) : (∫ x, f x)=f 0 := by
  rw [Measure.volume_pi_eq_dirac (0 : RV 0), integral_dirac]

lemma cons_weighted {d : ℕ} (a b x y : ℝ) (u v : RV d) :
    Fin.cons (a*x+b*y) (a•u+b•v) = a•Fin.cons x u+b•Fin.cons y v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl




theorem gaussian_dominated_integral (d : ℕ) {f g h : RV d → ℝ}
    (fc : Continuous f) (gc : Continuous g) (hc : Continuous h)
    (fp : ∀ x, 0 < f x) (gp : ∀ x, 0 < g x) (hp : ∀ x, 0 < h x)
    (fb : GaussianBound f) (gb : GaussianBound g) (hb : GaussianBound h)
    {a b : ℝ} (ha : 0 < a) (hb' : 0 < b) (hab : a+b=1)
    (hfg : ∀ x y, f x^a*g y^b ≤ h (a•x+b•y)) :
    (∫ x, f x)^a*(∫ y, g y)^b ≤ ∫ z, h z := by
  induction d with
  | zero =>
    simp only [integral_RV_zero]
    have H := hfg 0 0
    simpa only [smul_zero,add_zero] using H
  | succ d ih =>
    have hm : ∀ y z : RV d,
        (marginalOne f y)^a*(marginalOne g z)^b ≤ marginalOne h (a•y+b•z) := by
      intro y z
      apply positive_integral
        (fc.comp (show Continuous (fun t : ℝ => Fin.cons t y) by fun_prop))
        (gc.comp (show Continuous (fun t : ℝ => Fin.cons t z) by fun_prop))
        (fun t => fp (Fin.cons t y)) (fun t => gp (Fin.cons t z))
        (fb.integrable_slice fc _) (gb.integrable_slice gc _) (hb.integrable_slice hc _)
        (fun t => (hp _).le) ha hb' hab
      intro t u
      simpa only [cons_weighted,Function.comp_def,id_eq] using hfg (Fin.cons t y) (Fin.cons u z)
    have H := ih (fb.continuous_marginalOne fc) (gb.continuous_marginalOne gc)
      (hb.continuous_marginalOne hc) (marginalOne_positive fb fc fp)
      (marginalOne_positive gb gc gp) (marginalOne_positive hb hc hp)
      (fb.for_marginalOne fc) (gb.for_marginalOne gc) (hb.for_marginalOne hc) hm
    simpa only [integral_marginalOne (fb.integrable fc),integral_marginalOne (gb.integrable gc),
      integral_marginalOne (hb.integrable hc)] using H


end SingleLatticeCovering.Prekopa

noncomputable section
namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BigOperators

lemma sum_sq_le_norm_sq (d : ℕ) (x : RV d) :
    (∑ i, (x i)^2) ≤ (d : ℝ)*‖x‖^2 := by
  calc
    _ ≤ ∑ _ : Fin d, ‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_le_pi_norm x i
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (x i)) hi 2
    _ = _ := by simp

def softIndicator {d : ℕ} (K : Set (RV d)) (t : ℝ) (x : RV d) : ℝ :=
  Real.exp (-t*(infDist x K)^2)

lemma softIndicator_positive {d : ℕ} (K : Set (RV d)) (t : ℝ) (x : RV d) :
    0 < softIndicator K t x := Real.exp_pos _

lemma continuous_softIndicator {d : ℕ} (K : Set (RV d)) (t : ℝ) :
    Continuous (softIndicator K t) := by
  unfold softIndicator
  exact Real.continuous_exp.comp (continuous_const.mul ((continuous_infDist_pt K).pow 2))

lemma softIndicator_gaussianBound {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (hne : K.Nonempty) {t : ℝ} (ht : 0 < t) : GaussianBound (softIndicator K t) := by
  obtain ⟨R,hR,hb⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨Real.exp (t*R^2),t/(2*((d : ℝ)+1)),Real.exp_pos _,by positivity,?_⟩
  intro x
  obtain ⟨u,hu,he⟩ := hK.exists_infDist_eq_dist hne x
  have hn : ‖x‖ ≤ infDist x K+R := by
    calc
      ‖x‖ ≤ ‖x-u‖+‖u‖ := by simpa only [add_comm] using norm_le_insert' x u
      _ ≤ infDist x K+R := by rw [he,dist_eq_norm]; exact add_le_add_right (hb u hu) _
  have hs : ‖x‖^2 ≤ 2*((infDist x K)^2+R^2) := by
    have hn' := pow_le_pow_left₀ (norm_nonneg x) hn 2
    nlinarith [sq_nonneg (infDist x K-R)]
  have hs' : (∑ i, (x i)^2) ≤ 2*((d : ℝ)+1)*((infDist x K)^2+R^2) := by
    calc
      _ ≤ (d : ℝ)*‖x‖^2 := sum_sq_le_norm_sq d x
      _ ≤ (d : ℝ)*(2*((infDist x K)^2+R^2)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (infDist x K),sq_nonneg R]
  rw [abs_of_pos (softIndicator_positive K t x),softIndicator,gaussianKernel,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2*((d : ℝ)+1) := by positivity
  have hm := mul_le_mul_of_nonneg_left hs' (div_nonneg ht.le hd.le)
  field_simp at hm ⊢
  nlinarith

lemma infDist_weighted {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) (x y : RV d) :
    infDist (a•x+b•y) C ≤ a*infDist x A+b*infDist y B := by
  obtain ⟨u,hu,heu⟩ := hA.exists_infDist_eq_dist hneA x
  obtain ⟨v,hv,hev⟩ := hB.exists_infDist_eq_dist hneB y
  calc
    _ ≤ dist (a•x+b•y) (a•u+b•v) := infDist_le_dist_of_mem (hABC u hu v hv)
    _ = ‖a•(x-u)+b•(y-v)‖ := by rw [dist_eq_norm]; congr 1; module
    _ ≤ ‖a•(x-u)‖+‖b•(y-v)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg ha,abs_of_nonneg hb,heu,hev,dist_eq_norm,dist_eq_norm]

lemma softIndicator_weighted {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (ht : 0 ≤ t)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) (x y : RV d) :
    (softIndicator A t x)^a*(softIndicator B t y)^b ≤ softIndicator C t (a•x+b•y) := by
  have H := infDist_weighted hA hB hneA hneB ha hb hABC x y
  have hsq : (infDist (a•x+b•y) C)^2 ≤ a*(infDist x A)^2+b*(infDist y B)^2 := by
    have HH := pow_le_pow_left₀ (infDist_nonneg : 0 ≤ infDist (a•x+b•y) C) H 2
    have hm := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (infDist x A-infDist y B))
    nlinarith [sq_nonneg (a*infDist x A+b*infDist y B),sq_nonneg (infDist x A),sq_nonneg (infDist y B)]
  simp only [softIndicator,←Real.exp_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hsq)]



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BigOperators

lemma softIndicator_tendsto {d : ℕ} {K : Set (RV d)} (hK : IsClosed K)
    (hne : K.Nonempty) (x : RV d) :
    Tendsto (fun n : ℕ => softIndicator K ((n : ℝ)+1) x) atTop
      (𝓝 (K.indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : x ∈ K
  · simp only [softIndicator,infDist_zero_of_mem hx,zero_pow (by omega : 2 ≠ 0),
      mul_zero,Real.exp_zero,Set.indicator_of_mem hx]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem hx]
    have hd : 0 < (infDist x K)^2 := sq_pos_of_pos ((hK.notMem_iff_infDist_pos hne).mp hx)
    have hq : Real.exp (-(infDist x K)^2)<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd)
    have H := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-(infDist x K)^2)).le hq).mul_const
      (Real.exp (-(infDist x K)^2))
    simp only [zero_mul] at H
    convert H using 1
    ext n
    rw [softIndicator,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring

lemma softIndicator_antitone {d : ℕ} (K : Set (RV d)) (x : RV d) :
    Antitone (fun t : ℝ => softIndicator K t x) := by
  intro t u htu
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg htu) (sq_nonneg _)

lemma softIndicator_integral_tendsto {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (hne : K.Nonempty) :
    Tendsto (fun n : ℕ => ∫ x, softIndicator K ((n : ℝ)+1) x) atTop
      (𝓝 (volume K).toReal) := by
  have H := tendsto_integral_of_dominated_convergence (softIndicator K 1)
    (fun n => (continuous_softIndicator K ((n : ℝ)+1)).aestronglyMeasurable)
    ((softIndicator_gaussianBound hK hne zero_lt_one).integrable (continuous_softIndicator K 1))
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (softIndicator_positive K _ x)]
      exact softIndicator_antitone K x (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : (1:ℝ) ≤ (n : ℝ)+1)))
    (Filter.Eventually.of_forall (softIndicator_tendsto hK.isClosed hne))
  simpa only [integral_indicator hK.measurableSet,integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] using H




theorem compact_volume {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) :
    ((volume A).toReal)^a*((volume B).toReal)^b ≤ (volume C).toReal := by
  rcases A.eq_empty_or_nonempty with rfl | hneA
  · simp only [measure_empty,ENNReal.toReal_zero,Real.zero_rpow (ne_of_gt ha),zero_mul]
    exact ENNReal.toReal_nonneg
  rcases B.eq_empty_or_nonempty with rfl | hneB
  · simp only [measure_empty,ENNReal.toReal_zero,Real.zero_rpow (ne_of_gt hb),mul_zero]
    exact ENNReal.toReal_nonneg
  have hneC : C.Nonempty := by
    obtain ⟨u,hu⟩ := hneA
    obtain ⟨v,hv⟩ := hneB
    exact ⟨a•u+b•v,hABC u hu v hv⟩
  have hpoint : ∀ n : ℕ,
      (∫ x, softIndicator A ((n : ℝ)+1) x)^a*
      (∫ x, softIndicator B ((n : ℝ)+1) x)^b ≤ ∫ x, softIndicator C ((n : ℝ)+1) x := by
    intro n
    have hn : 0 < (n : ℝ)+1 := by positivity
    apply gaussian_dominated_integral d (continuous_softIndicator _ _) (continuous_softIndicator _ _)
      (continuous_softIndicator _ _) (softIndicator_positive _ _) (softIndicator_positive _ _)
      (softIndicator_positive _ _) (softIndicator_gaussianBound hA hneA hn)
      (softIndicator_gaussianBound hB hneB hn) (softIndicator_gaussianBound hC hneC hn) ha hb hab
    exact softIndicator_weighted hA hB hneA hneB ha.le hb.le hab hn.le hABC
  exact le_of_tendsto_of_tendsto
    (((Real.continuous_rpow_const ha.le).tendsto _).comp (softIndicator_integral_tendsto hA hneA) |>.mul
      (((Real.continuous_rpow_const hb.le).tendsto _).comp (softIndicator_integral_tendsto hB hneB)))
    (softIndicator_integral_tendsto hC hneC) (Filter.Eventually.of_forall hpoint)


end SingleLatticeCovering.Prekopa




namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric Sections Isotropization
open scoped ENNReal Topology BigOperators




theorem logConcave_section_volume {m D : ℕ} {K : Set (RV m × E D)}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    LogConcave (fun y => (volume (fiber K y)).toReal) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg,fun x y a b ha hb hab => ?_⟩
  apply compact_volume (fiber_compact hK x) (fiber_compact hK y)
    (fiber_compact hK (a•x+b•y)) ha hb hab
  intro u hu v hv
  have H := hconv hu hv ha.le hb.le hab
  exact H

lemma LogConcave.const_mul {D : ℕ} {f : E D → ℝ} (hf : LogConcave f)
    {c : ℝ} (hc : 0 ≤ c) : LogConcave (fun x => c*f x) := by
  refine ⟨fun x => mul_nonneg hc (hf.1 x),fun x y a b ha hb hab => ?_⟩
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul,Real.zero_rpow (ne_of_gt ha),Real.zero_rpow (ne_of_gt hb),le_refl]
  · rw [Real.mul_rpow hc.le (hf.1 x),Real.mul_rpow hc.le (hf.1 y)]
    calc
      c^a*f x^a*(c^b*f y^b) = (c^a*c^b)*(f x^a*f y^b) := by ring
      _ = c*(f x^a*f y^b) := by rw [←Real.rpow_add hc,hab,Real.rpow_one]
      _ ≤ c*f (a•x+b•y) := mul_le_mul_of_nonneg_left (hf.2 x y a b ha hb hab) hc.le



theorem logConcave_canonical_density {m D : ℕ} {K : Set (RV m × E D)}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    LogConcave (fun y => ((volume K)⁻¹).toReal*(volume (fiber K y)).toReal) :=
  LogConcave.const_mul (logConcave_section_volume hK hconv) ENNReal.toReal_nonneg



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology

def ScalarLogConcave (f : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ f t) ∧ ∀ u v a b : ℝ, 0 < a → 0 < b → a+b=1 →
    f u^a*f v^b ≤ f (a*u+b*v)

def linearCap {d : ℕ} (K : Set (RV d)) (L : RV d →L[ℝ] ℝ) (t : ℝ) : Set (RV d) :=
  K ∩ {x | t ≤ L x}

lemma linearCap_compact {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (L : RV d →L[ℝ] ℝ) (t : ℝ) : IsCompact (linearCap K L t) :=
  hK.inter_right (isClosed_le continuous_const L.continuous)

theorem scalarLogConcave_cap_volume {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (L : RV d →L[ℝ] ℝ) :
    ScalarLogConcave (fun t => (volume (linearCap K L t)).toReal) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg,fun u v a b ha hb hab => ?_⟩
  apply compact_volume (linearCap_compact hK L u) (linearCap_compact hK L v)
    (linearCap_compact hK L (a*u+b*v)) ha hb hab
  intro x hx y hy
  refine ⟨hconv hx.1 hy.1 ha.le hb.le hab,?_⟩
  change a*u+b*v ≤ L (a•x+b•y)
  simp only [map_add,map_smul,smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx.2 ha.le) (mul_le_mul_of_nonneg_left hy.2 hb.le)

lemma ScalarLogConcave.const_mul {f : ℝ → ℝ} (hf : ScalarLogConcave f)
    {c : ℝ} (hc : 0 ≤ c) : ScalarLogConcave (fun t => c*f t) := by
  refine ⟨fun t => mul_nonneg hc (hf.1 t),fun u v a b ha hb hab => ?_⟩
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul,Real.zero_rpow (ne_of_gt ha),Real.zero_rpow (ne_of_gt hb),le_refl]
  rw [Real.mul_rpow hc.le (hf.1 u),Real.mul_rpow hc.le (hf.1 v)]
  calc
    c^a*f u^a*(c^b*f v^b) = (c^a*c^b)*(f u^a*f v^b) := by ring
    _ = c*(f u^a*f v^b) := by rw [←Real.rpow_add hc,hab,Real.rpow_one]
    _ ≤ c*f (a*u+b*v) := mul_le_mul_of_nonneg_left (hf.2 u v a b ha hb hab) hc.le

lemma ScalarLogConcave.log_interpolation {f : ℝ → ℝ} (hf : ScalarLogConcave f)
    {u v a b : ℝ} (hu : 0 < f u) (hv : 0 < f v)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    a*Real.log (f u)+b*Real.log (f v) ≤ Real.log (f (a*u+b*v)) := by
  have hp : 0 < f u^a*f v^b := mul_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)
  have H := Real.log_le_log hp (hf.2 u v a b ha hb hab)
  rwa [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hu _)) (ne_of_gt (Real.rpow_pos_of_pos hv _)),
    Real.log_rpow hu,Real.log_rpow hv] at H



theorem ScalarLogConcave.exponential_tail {f : ℝ → ℝ} (hf : ScalarLogConcave f)
    (hle : ∀ t, f t ≤ 1) (hleft : (3:ℝ)/4 ≤ f (-2)) (hright : f 2 ≤ (1:ℝ)/4)
    {t : ℝ} (ht : 0 ≤ t) : f t ≤ Real.exp (1-t/16) := by
  have _ := ht
  by_cases ht2 : t ≤ 2
  · exact (hle t).trans (Real.one_le_exp (by linarith))
  have ht2 : 2 < t := lt_of_not_ge ht2
  rcases (hf.1 t).eq_or_lt with hzero | hpos
  · rw [←hzero]; exact (Real.exp_pos _).le
  have hleftpos : 0 < f (-2) := by linarith
  let a := (t-2)/(t+2)
  let b := 4/(t+2)
  have htp : 0 < t+2 := by linarith
  have ha : 0 < a := div_pos (by linarith) htp
  have hb : 0 < b := div_pos (by norm_num) htp
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have hinter : a*(-2)+b*t=2 := by dsimp [a,b]; field_simp; ring
  have H := hf.log_interpolation hleftpos hpos ha hb hab
  rw [hinter] at H
  have hl : -(1:ℝ)/2 ≤ Real.log (f (-2)) := by
    have A := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 3/4 by norm_num)
    have B := Real.log_le_log (show (0:ℝ) < 3/4 by norm_num) hleft
    norm_num at A
    linarith
  have h2pos : 0 < f 2 := by
    have HH := hf.2 (-2) t a b ha hb hab
    rw [hinter] at HH
    exact (mul_pos (Real.rpow_pos_of_pos hleftpos _) (Real.rpow_pos_of_pos hpos _)).trans_le HH
  have hr : Real.log (f 2) ≤ -(3:ℝ)/4 := by
    have A := Real.log_le_log h2pos hright
    have B := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/4 by norm_num)
    linarith
  have H' : a*(-(1:ℝ)/2)+b*Real.log (f t) ≤ -(3:ℝ)/4 := by
    have A := mul_le_mul_of_nonneg_left hl ha.le
    linarith
  have H'' := mul_le_mul_of_nonneg_right H' htp.le
  have haeq : a*(t+2)=t-2 := div_mul_cancel₀ _ (ne_of_gt htp)
  have hbeq : b*(t+2)=4 := div_mul_cancel₀ _ (ne_of_gt htp)
  have hcalc : (a*(-(1:ℝ)/2)+b*Real.log (f t))*(t+2)=
      (t-2)*(-(1:ℝ)/2)+4*Real.log (f t) := by
    calc
      _ = (a*(t+2))*(-(1:ℝ)/2)+(b*(t+2))*Real.log (f t) := by ring
      _ = _ := by rw [haeq,hbeq]
  rw [hcalc] at H''
  have hlog : Real.log (f t) ≤ 1-t/16 := by linarith
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped Topology

lemma right_derivative_nonpos_of_max {F : ℝ → ℝ} {A : ℝ}
    (hF : HasDerivAt F A 0) (hmax : ∀ t ∈ Ioo (0:ℝ) 1, F t ≤ F 0) : A ≤ 0 := by
  apply le_of_tendsto hF.tendsto_slope_zero_right
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin,hnear] with t ht ht1
  simp only [zero_add,smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht)) (sub_nonpos.mpr (hmax t ⟨ht,ht1⟩))



theorem ScalarLogConcave.log_bound_at_weighted_mode {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : 0 < r)
    (hφ₀ : 0 < φ r₀) (hφr : 0 < φ r)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀) :
    Real.log (φ r)-Real.log (φ r₀) ≤ -(m:ℝ)*(r-r₀)/r₀ := by
  let F : ℝ → ℝ := fun t => (m:ℝ)*Real.log ((1-t)*r₀+t*r)+
    (1-t)*Real.log (φ r₀)+t*Real.log (φ r)
  have hdlin : HasDerivAt (fun t : ℝ => (1-t)*r₀+t*r) (r-r₀) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ))).mul_const r₀).add
      ((hasDerivAt_id (0:ℝ)).mul_const r) using 1 ;       simp only [zero_sub,neg_one_mul,one_mul] ; ring
  have hdlog := hdlin.log (by simpa using ne_of_gt hr₀)
  have hd : HasDerivAt F ((m:ℝ)*(r-r₀)/r₀-Real.log (φ r₀)+Real.log (φ r)) 0 := by
    convert! ((hdlog.const_mul (m:ℝ)).add
      (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ))).mul_const (Real.log (φ r₀)))).add
      ((hasDerivAt_id (0:ℝ)).mul_const (Real.log (φ r))) using 1 ;       simp only [sub_zero,one_mul,zero_mul,add_zero,zero_sub,neg_one_mul] ; ring
  have hFmax : ∀ t ∈ Ioo (0:ℝ) 1, F t ≤ F 0 := by
    intro t ht
    let z := (1-t)*r₀+t*r
    have hz : 0 < z := add_pos (mul_pos (by linarith [ht.2]) hr₀) (mul_pos ht.1 hr)
    have hinter := hφ.log_interpolation hφ₀ hφr (show 0 < 1-t by linarith [ht.2]) ht.1 (by ring)
    change (1-t)*Real.log (φ r₀)+t*Real.log (φ r) ≤ Real.log (φ z) at hinter
    have hφz : 0 < φ z := by
      have H := hφ.2 r₀ r (1-t) t (by linarith [ht.2]) ht.1 (by ring)
      exact (mul_pos (Real.rpow_pos_of_pos hφ₀ _) (Real.rpow_pos_of_pos hφr _)).trans_le H
    have H := Real.log_le_log (mul_pos (pow_pos hz _) hφz) (hmax z hz)
    rw [Real.log_mul (ne_of_gt (pow_pos hz _)) (ne_of_gt hφz),
      Real.log_mul (ne_of_gt (pow_pos hr₀ _)) (ne_of_gt hφ₀),Real.log_pow,Real.log_pow] at H
    dsimp [F]
    simp only [sub_zero,one_mul,zero_mul,add_zero]
    change (m:ℝ)*Real.log z+((1-t)*Real.log (φ r₀))+t*Real.log (φ r) ≤ _
    linarith
  have H := right_derivative_nonpos_of_max hd hFmax
  rw [neg_mul,neg_div]
  linarith

def shellRate (u : ℝ) : ℝ := u-1-Real.log u



theorem ScalarLogConcave.weighted_mode_envelope {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : 0 < r)
    (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀) :
    r^m*φ r ≤ (r₀^m*φ r₀)*Real.exp (-(m:ℝ)*shellRate (r/r₀)) := by
  rcases (hφ.1 r).eq_or_lt with hz | hp
  · rw [←hz,mul_zero]; positivity
  have H := hφ.log_bound_at_weighted_mode hr₀ hr hφ₀ hp hmax
  have hlog : Real.log (r^m*φ r) ≤ Real.log (r₀^m*φ r₀)-(m:ℝ)*shellRate (r/r₀) := by
    rw [Real.log_mul (ne_of_gt (pow_pos hr _)) (ne_of_gt hp),
      Real.log_mul (ne_of_gt (pow_pos hr₀ _)) (ne_of_gt hφ₀),Real.log_pow,Real.log_pow]
    rw [shellRate,Real.log_div (ne_of_gt hr) (ne_of_gt hr₀)]
    have he : (r-r₀)/r₀=r/r₀-1 := by field_simp
    rw [neg_mul,neg_div,mul_div_assoc,he] at H
    nlinarith
  have HE := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (mul_pos (pow_pos hr _) hp),Real.exp_sub,
    Real.exp_log (mul_pos (pow_pos hr₀ _) hφ₀),div_eq_mul_inv,←Real.exp_neg] at HE
  simpa only [neg_mul] using HE


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped Topology

lemma shellRate_ge_sqrt_sq {u : ℝ} (hu : 0 < u) : (Real.sqrt u-1)^2 ≤ shellRate u := by
  have H := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu)
  rw [Real.log_sqrt hu.le] at H
  dsimp [shellRate]
  nlinarith [Real.sq_sqrt hu.le]

lemma shellRate_ge_sq_div_nine {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) :
    (u-1)^2/9 ≤ shellRate u := by
  have hs := Real.sqrt_nonneg u
  have hs2 : Real.sqrt u ≤ 2 := by nlinarith [Real.sq_sqrt hu.le]
  have he : (u-1)^2=(Real.sqrt u-1)^2*(Real.sqrt u+1)^2 := by
    calc
      _ = ((Real.sqrt u)^2-1)^2 := by rw [Real.sq_sqrt hu.le]
      _ = _ := by ring
  have hsq : (Real.sqrt u+1)^2 ≤ 9 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.sqrt u-1))
  rw [←he] at hm
  nlinarith [shellRate_ge_sqrt_sq hu]

lemma shellRate_support {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    shellRate a+(1-a⁻¹)*(u-a) ≤ shellRate u := by
  have H := Real.log_le_sub_one_of_pos (div_pos hu ha)
  rw [Real.log_div (ne_of_gt hu) (ne_of_gt ha)] at H
  have he : (1-a⁻¹)*(u-a)=u-a-u/a+1 := by field_simp; ring
  rw [he]
  dsimp [shellRate]
  linarith

lemma shellRate_upper_tail {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 1+ε ≤ u) :
    ε^2/9+(ε/2)*(u-(1+ε)) ≤ shellRate u := by
  have ha : 0 < 1+ε := by linarith
  have hs := shellRate_support (show 0 < u by linarith) ha
  have hb := shellRate_ge_sq_div_nine ha (show 1+ε ≤ 2 by linarith)
  have hc : ε/2 ≤ 1-(1+ε)⁻¹ := by
    have he : (1-(1+ε)⁻¹)*(1+ε)=ε := by
      rw [sub_mul,one_mul,inv_mul_cancel₀ (ne_of_gt ha)]
      ring
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hu)
  nlinarith

lemma shellRate_lower_tail {ε u : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hu : 0 < u) (hu1 : u ≤ 1-ε) :
    ε^2/9+(ε/2)*((1-ε)-u) ≤ shellRate u := by
  have ha : 0 < 1-ε := by linarith
  have hs := shellRate_support hu ha
  have hb := shellRate_ge_sq_div_nine ha (show 1-ε ≤ 2 by linarith)
  have hc : 1-(1-ε)⁻¹ ≤ -ε/2 := by
    have he : (1-(1-ε)⁻¹)*(1-ε) = -ε := by
      rw [sub_mul,one_mul,inv_mul_cancel₀ (ne_of_gt ha)]
      ring
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith
  have hm := mul_le_mul_of_nonpos_right hc (sub_nonpos.mpr hu1)
  nlinarith



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped Topology

lemma integral_exp_shift_Ioi {a : ℝ} (ha : 0 < a) (c : ℝ) :
    (∫ r : ℝ in Ioi c, Real.exp (-a*(r-c)))=a⁻¹ := by
  have he (r : ℝ) : Real.exp (-a*(r-c))=Real.exp (a*c)*Real.exp (-a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith)]
  rw [neg_div_neg_eq,div_eq_mul_inv,←mul_assoc,←Real.exp_add]
  simp

lemma integral_exp_shift_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    (∫ r : ℝ in Iic c, Real.exp (a*(r-c)))=a⁻¹ := by
  have he (r : ℝ) : Real.exp (a*(r-c))=Real.exp (-a*c)*Real.exp (a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [integral_const_mul,integral_exp_mul_Iic ha]
  rw [div_eq_mul_inv,←mul_assoc,←Real.exp_add]
  simp

lemma integrableOn_exp_shift_Ioi {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun r : ℝ => Real.exp (-a*(r-c))) (Ioi c) volume := by
  have he (r : ℝ) : Real.exp (-a*(r-c))=Real.exp (a*c)*Real.exp (-a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  exact (integrableOn_exp_mul_Ioi (by linarith) c).const_mul _

lemma integrableOn_exp_shift_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun r : ℝ => Real.exp (a*(r-c))) (Iic c) volume := by
  have he (r : ℝ) : Real.exp (a*(r-c))=Real.exp (-a*c)*Real.exp (a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  exact (integrableOn_exp_mul_Iic ha c).const_mul _

lemma ScalarLogConcave.upper_shell_envelope {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ ε r : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hr : (1+ε)*r₀ ≤ r) :
    r^m*φ r ≤ (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*
      Real.exp (-((m:ℝ)*ε/(2*r₀))*(r-(1+ε)*r₀)) := by
  have hrp : 0 < r := (mul_pos (by linarith) hr₀).trans_le hr
  have hu : 1+ε ≤ r/r₀ := (le_div_iff₀ hr₀).mpr hr
  have H := mul_le_mul_of_nonpos_left (shellRate_upper_tail hε hε1 hu)
    (neg_nonpos.mpr (Nat.cast_nonneg m))
  have E := hφ.weighted_mode_envelope hr₀ hrp hφ₀ hmax
  apply E.trans
  rw [mul_assoc (r₀^m*φ r₀),←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hr₀.le _) hφ₀.le)
  apply Real.exp_le_exp.mpr
  exact H.trans_eq (by field_simp; ring)

lemma ScalarLogConcave.lower_shell_envelope {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ ε r : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hr : 0 < r) (hr1 : r ≤ (1-ε)*r₀) :
    r^m*φ r ≤ (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*
      Real.exp (((m:ℝ)*ε/(2*r₀))*(r-(1-ε)*r₀)) := by
  have hu : r/r₀ ≤ 1-ε := (div_le_iff₀ hr₀).mpr hr1
  have H := mul_le_mul_of_nonpos_left (shellRate_lower_tail hε hε1 (div_pos hr hr₀) hu)
    (neg_nonpos.mpr (Nat.cast_nonneg m))
  have E := hφ.weighted_mode_envelope hr₀ hr hφ₀ hmax
  apply E.trans
  rw [mul_assoc (r₀^m*φ r₀),←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hr₀.le _) hφ₀.le)
  apply Real.exp_le_exp.mpr
  exact H.trans_eq (by field_simp; ring)

lemma ScalarLogConcave.upper_shell_integral {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} (hm : 0 < m) {r₀ ε : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    (∫ r in Ioi ((1+ε)*r₀), r^m*φ r) ≤
      (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹ := by
  have ha : 0 < (m:ℝ)*ε/(2*r₀) := by positivity
  calc
    _ ≤ ∫ r in Ioi ((1+ε)*r₀),
        (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*Real.exp (-((m:ℝ)*ε/(2*r₀))*(r-(1+ε)*r₀)) := by
      have hs : Ioi ((1+ε)*r₀) ⊆ Ioi 0 := by
        intro r hr
        exact ((mul_pos (by linarith) hr₀).trans hr)
      apply integral_mono_ae (hi.mono_set hs) ((integrableOn_exp_shift_Ioi ha _).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hφ.upper_shell_envelope hr₀ hε hε1 hφ₀ hmax (le_of_lt hr)
    _ = _ := by rw [integral_const_mul,integral_exp_shift_Ioi ha]


lemma ScalarLogConcave.lower_shell_integral {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} (hm : 0 < m) {r₀ ε : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    (∫ r in Ioc 0 ((1-ε)*r₀), r^m*φ r) ≤
      (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹ := by
  have ha : 0 < (m:ℝ)*ε/(2*r₀) := by positivity
  let F : ℝ → ℝ := fun r => (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*
    Real.exp (((m:ℝ)*ε/(2*r₀))*(r-(1-ε)*r₀))
  have hF : IntegrableOn F (Iic ((1-ε)*r₀)) volume :=
    (integrableOn_exp_shift_Iic ha _).const_mul _
  calc
    _ ≤ ∫ r in Ioc 0 ((1-ε)*r₀), F r := by
      apply integral_mono_ae (hi.mono_set Ioc_subset_Ioi_self) (hF.mono_set Ioc_subset_Iic_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hφ.lower_shell_envelope hr₀ hε hε1 hφ₀ hmax hr.1 hr.2
    _ ≤ ∫ r in Iic ((1-ε)*r₀), F r := by
      apply setIntegral_mono_set hF
      · exact Filter.Eventually.of_forall (fun r => by dsimp [F]; positivity)
      · exact Filter.Eventually.of_forall Ioc_subset_Iic_self
    _ = _ := by dsimp [F]; rw [integral_const_mul,integral_exp_shift_Iic ha]

lemma radial_integral_lower {φ : ℝ → ℝ} {m : ℕ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hφ : ∀ r, 0 ≤ φ r)
    (hmono : ∀ r ∈ Ioc 0 r₀, φ r₀ ≤ φ r)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    r₀^m*φ r₀*r₀/(m+1:ℝ) ≤ ∫ r in Ioi 0, r^m*φ r := by
  have hpoly : IntegrableOn (fun r : ℝ => r^m*φ r₀) (Ioc 0 r₀) volume :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
  have hcalc : (∫ r in Ioc 0 r₀, r^m*φ r₀)=r₀^m*φ r₀*r₀/(m+1:ℝ) := by
    rw [←intervalIntegral.integral_of_le hr₀.le,intervalIntegral.integral_mul_const,integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero m),sub_zero,pow_succ]
    ring
  rw [←hcalc]
  calc
    _ ≤ ∫ r in Ioc 0 r₀, r^m*φ r := by
      apply integral_mono_ae hpoly (hi.mono_set Ioc_subset_Ioi_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact mul_le_mul_of_nonneg_left (hmono r hr) (pow_nonneg hr.1.le _)
    _ ≤ _ := by
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact mul_nonneg (pow_nonneg hr.le _) (hφ r)
      · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self


theorem ScalarLogConcave.shell_integral_bound {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} (hm : 0 < m) {r₀ ε : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hmono : ∀ r ∈ Ioc 0 r₀, φ r₀ ≤ φ r)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    (∫ r in Ioc 0 ((1-ε)*r₀), r^m*φ r)+
      (∫ r in Ioi ((1+ε)*r₀), r^m*φ r) ≤
      (4*((m:ℝ)+1)/((m:ℝ)*ε)*Real.exp (-(m:ℝ)*ε^2/9))*(∫ r in Ioi 0, r^m*φ r) := by
  have HL := hφ.lower_shell_integral hm hr₀ hε hε1 hφ₀ hmax hi
  have HU := hφ.upper_shell_integral hm hr₀ hε hε1.le hφ₀ hmax hi
  have HN := radial_integral_lower hr₀ hφ.1 hmono hi
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have HN' : r₀^m*φ r₀*r₀ ≤ ((m:ℝ)+1)*(∫ r in Ioi 0, r^m*φ r) := by
    have H := (div_le_iff₀ (show 0 < (m:ℝ)+1 by positivity)).mp HN
    linarith
  have he : 2*((r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹)=
      (4/((m:ℝ)*ε)*Real.exp (-(m:ℝ)*ε^2/9))*(r₀^m*φ r₀*r₀) := by field_simp; ring
  have HE := mul_le_mul_of_nonneg_left HN' (show 0 ≤ 4/((m:ℝ)*ε)*Real.exp (-(m:ℝ)*ε^2/9) by positivity)
  calc
    _ ≤ 2*((r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹) := by linarith
    _ = _ := he
    _ ≤ _ := HE
    _ = _ := by ring

lemma exists_weighted_mode {φ : ℝ → ℝ} {m : ℕ} (hm : 0 < m)
    (hc : Continuous φ) (hp : 0 < φ 1)
    (ht : Tendsto (fun r : ℝ => r^m*φ r) atTop (𝓝 0)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ 0 < φ r₀ ∧
      ∀ r : ℝ, 0 < r → r^m*φ r ≤ r₀^m*φ r₀ := by
  have hev : ∀ᶠ r : ℝ in atTop, r^m*φ r < φ 1 := ht (Iio_mem_nhds hp)
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  let B := max R 1
  have hB : (1:ℝ) ≤ B := le_max_right _ _
  have hcont : Continuous (fun r : ℝ => r^m*φ r) := by fun_prop
  obtain ⟨r₀,hr₀,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by linarith : (0:ℝ) ≤ B)) hcont.continuousOn
  have hbase : φ 1 ≤ r₀^m*φ r₀ := by
    simpa only [Set.mem_ofPred_eq,one_pow,one_mul] using hmax (show (1:ℝ) ∈ Icc 0 B from ⟨by norm_num,hB⟩)
  have hpos : 0 < r₀ := by
    rcases hr₀.1.eq_or_lt with hz | hz
    · subst r₀
      simp only [zero_pow (Nat.ne_of_gt hm),zero_mul] at hbase
      linarith
    · exact hz
  have hφpos : 0 < φ r₀ := (mul_pos_iff_of_pos_left (pow_pos hpos m)).mp (hp.trans_le hbase)
  refine ⟨r₀,hpos,hφpos,fun r hr => ?_⟩
  by_cases hrB : r ≤ B
  · exact hmax ⟨hr.le,hrB⟩
  · exact (hR r ((le_max_left R 1).trans (le_of_not_ge hrB))).le.trans hbase







end SingleLatticeCovering.Prekopa


end
end
end
end
end

end OAI
