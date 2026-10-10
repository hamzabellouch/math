import Mathlib
import OAI.Probability.SLELocalization.DyadicKernels

namespace OAI


/-! Conformal localization and Rectangle Energy estimates. -/

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem dyadic_weighted_energy {Q : ℕ → Set α} (hQ : ∀ j, MeasurableSet (Q j))
    {g : α → ℝ} (hg : MemLp g 2 μ) {V : ℝ} (n : ℕ)
    (harea : ∀ j < n, ((2:ℝ)^j)^2*μ.real (Q j) ≤ V) :
    (∫ x, dyadicKernel Q n x*g x ∂μ)^2 ≤
      3*(n:ℝ)*V*(∫ x, (g x)^2 ∂μ) := by
  exact (integral_mul_square_le (dyadicKernel_memLp hQ n) hg).trans
    (mul_le_mul_of_nonneg_right (dyadicKernel_square_energy hQ n harea)
      (integral_nonneg (fun x => sq_nonneg _)))

omit [IsFiniteMeasure μ] in
lemma dyadicKernel_integral_mul {Q : ℕ → Set α} (hQ : ∀ j, MeasurableSet (Q j))
    {g : α → ℝ} (hg : Integrable g μ) (n : ℕ) :
    (∫ x, dyadicKernel Q n x*g x ∂μ) =
      ∑ j ∈ Finset.range n, (2:ℝ)^j*(∫ x in Q j, g x ∂μ) := by
  have he : (fun x => dyadicKernel Q n x*g x) =
      fun x => ∑ j ∈ Finset.range n, (Q j).indicator (fun x => (2:ℝ)^j*g x) x := by
    funext x
    rw [dyadicKernel,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hx : x ∈ Q j <;> simp [hx]
  rw [he,integral_finsetSum _ (fun j hj => (hg.const_mul _).indicator (hQ j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_indicator (hQ j),integral_const_mul]

omit [IsFiniteMeasure μ] in
lemma dyadic_L1_telescoping {Q : ℕ → Set α} {g : α → ℝ} {v : ℕ → ℝ}
    {C : ℝ} (hstep : ∀ j, |v (j+1)-v j| ≤ C*(2:ℝ)^j*(∫ x in Q j, g x ∂μ))
    (n : ℕ) : |v n-v 0| ≤ C*∑ j ∈ Finset.range n, (2:ℝ)^j*(∫ x in Q j, g x ∂μ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ |v (n+1)-v n|+|v n-v 0| := abs_sub_le _ _ _
      _ ≤ C*(2:ℝ)^n*(∫ x in Q n, g x ∂μ)+
          C*∑ j ∈ Finset.range n, (2:ℝ)^j*(∫ x in Q j, g x ∂μ) := add_le_add (hstep n) ih
      _ = _ := by rw [Finset.sum_range_succ]; ring

theorem critical_means_from_L1 {Q : ℕ → Set α} (hQ : ∀ j, MeasurableSet (Q j))
    {g : α → ℝ} (hg : MemLp g 2 μ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    {v : ℕ → ℝ} {C V : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ j, |v (j+1)-v j| ≤ C*(2:ℝ)^j*(∫ x in Q j, g x ∂μ))
    (n : ℕ) (harea : ∀ j < n, ((2:ℝ)^j)^2*μ.real (Q j) ≤ V) :
    (v n-v 0)^2 ≤ 3*C^2*(n:ℝ)*V*(∫ x, (g x)^2 ∂μ) := by
  have hi := hg.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hb := dyadic_L1_telescoping hstep n
  rw [← dyadicKernel_integral_mul hQ hi n] at hb
  have hn : 0 ≤ ∫ x, dyadicKernel Q n x*g x ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hg0] with x hx
    apply mul_nonneg _ hx
    apply Finset.sum_nonneg
    intro j hj
    exact indicator_nonneg (fun x hx => by positivity) x
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC hn)).2 hb
  rw [sq_abs,mul_pow] at hs
  calc
    _ ≤ C^2*(∫ x, dyadicKernel Q n x*g x ∂μ)^2 := hs
    _ ≤ C^2*(3*(n:ℝ)*V*(∫ x, (g x)^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left (dyadic_weighted_energy hQ hg n harea) (sq_nonneg _)
    _ = _ := by ring

end Measure

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

lemma rectangle_measure_restrict {a b c d a' b' c' d' : ℝ}
    (haa : a ≤ a') (hbb : b' ≤ b) (hcc : c ≤ c') (hdd : d' ≤ d) :
    ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))).restrict
      ((Ioc a' b').prod (Ioc c' d')) =
      (volume.restrict (Ioc a' b')).prod (volume.restrict (Ioc c' d')) := by
  rw [Measure.prod_restrict,Measure.prod_restrict]
  have hs : (Ioc a' b').prod (Ioc c' d') ⊆ (Ioc a b).prod (Ioc c d) := by
    rintro p ⟨hx,hy⟩
    exact ⟨⟨haa.trans_lt hx.1,hx.2.trans hbb⟩,⟨hcc.trans_lt hy.1,hy.2.trans hdd⟩⟩
  exact Measure.restrict_restrict_of_subset hs

lemma rectangle_measure_real {a b c d a' b' c' d' : ℝ}
    (hab : a' ≤ b') (hcd : c' ≤ d')
    (haa : a ≤ a') (hbb : b' ≤ b) (hcc : c ≤ c') (hdd : d' ≤ d) :
    ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))).real
      ((Ioc a' b').prod (Ioc c' d')) = (b'-a')*(d'-c') := by
  rw [Measure.real]
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ)
    (rectangle_measure_restrict haa hbb hcc hdd)
  simp only [Measure.restrict_apply_univ] at he
  rw [he,← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ,Real.volume_Ioc,ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (sub_nonneg.2 hab),ENNReal.toReal_ofReal (sub_nonneg.2 hcd)]

theorem strip_nested_means {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    (a b c d : ℕ → ℝ) (hab : ∀ j, a j < b j) (hcd : ∀ j, c j < d j)
    (hlo : 0 ≤ c 0) (hhi : d 0 ≤ Real.pi)
    (haa : ∀ j, a j ≤ a (j+1)) (hbb : ∀ j, b (j+1) ≤ b j)
    (hcc : ∀ j, c j ≤ c (j+1)) (hdd : ∀ j, d (j+1) ≤ d j)
    (hw : ∀ j, b j-a j = (b 0-a 0)/(2:ℝ)^j)
    (hh : ∀ j, d j-c j = (d 0-c 0)/(2:ℝ)^j) (n : ℕ) :
    ((∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb (a n) (b n)).prod (intervalProb (c n) (d n)))-
      (∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb (a 0) (b 0)).prod (intervalProb (c 0) (d 0))))^2 ≤
      3*(2/(d 0-c 0)+1/(b 0-a 0))^2*(n:ℝ)*(b 0-a 0)*(d 0-c 0)*
        (∫ p : ℝ × ℝ, ‖fderiv ℝ (stripPotential H q r Fbar)
          ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2
          ∂(volume.restrict (Ioc (a 0) (b 0))).prod (volume.restrict (Ioc (c 0) (d 0)))) := by
  let μ := (volume.restrict (Ioc (a 0) (b 0))).prod (volume.restrict (Ioc (c 0) (d 0)))
  let Q := fun j => (Ioc (a j) (b j)).prod (Ioc (c j) (d j))
  let g := fun p : ℝ × ℝ => ‖fderiv ℝ (stripPotential H q r Fbar) ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖
  let v := fun j => ∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
    ∂(intervalProb (a j) (b j)).prod (intervalProb (c j) (d j))
  let C := 2/(d 0-c 0)+1/(b 0-a 0)
  have ha0 (j : ℕ) : a 0 ≤ a j := (monotone_nat_of_le_succ haa) (Nat.zero_le j)
  have hb0 (j : ℕ) : b j ≤ b 0 := (antitone_nat_of_succ_le hbb) (Nat.zero_le j)
  have hc0 (j : ℕ) : c 0 ≤ c j := (monotone_nat_of_le_succ hcc) (Nat.zero_le j)
  have hd0 (j : ℕ) : d j ≤ d 0 := (antitone_nat_of_succ_le hdd) (Nat.zero_le j)
  have hC : 0 ≤ C := by
    have hw0 := sub_pos.2 (hab 0)
    have hh0 := sub_pos.2 (hcd 0)
    dsimp [C]; positivity
  have hstep (j : ℕ) : |v (j+1)-v j| ≤ C*(2:ℝ)^j*(∫ p in Q j, g p ∂μ) := by
    have hlen : d j-c j ≤ 2*(d (j+1)-c (j+1)) := by rw [hh j,hh (j+1),pow_succ]; exact le_of_eq (by ring)
    have ht := strip_rectangle_poincare hF hinj hext hcont hH hr q
      (hab j) (hcd j) (hab (j+1)) (hcd (j+1)) (hlo.trans (hc0 j)) ((hd0 j).trans hhi)
      (haa j) (hbb j) (hcc j) (hdd j) (show (0:ℝ) ≤ 2 by norm_num) hlen
    change |v (j+1)-v j| ≤ _ at ht
    have he : 2/(d j-c j)+1/(b j-a j) = C*(2:ℝ)^j := by
      rw [hw j,hh j]
      dsimp [C]
      field_simp
    rw [he] at ht
    simpa only [Q,μ,rectangle_measure_restrict (ha0 j) (hb0 j) (hc0 j) (hd0 j)] using ht
  have harea (j : ℕ) (hj : j < n) : ((2:ℝ)^j)^2*μ.real (Q j) ≤ (b 0-a 0)*(d 0-c 0) := by
    rw [rectangle_measure_real (hab j).le (hcd j).le (ha0 j) (hb0 j) (hc0 j) (hd0 j)]
    rw [hw j,hh j]
    exact le_of_eq (by field_simp)
  have ht := critical_means_from_L1 (μ := μ) (Q := Q)
    (fun j => measurableSet_Ioc.prod measurableSet_Ioc)
    (strip_gradient_rect_memLp hF hinj hext hH hr q (a 0) (b 0) hlo hhi)
    (ae_of_all _ (fun p => norm_nonneg _)) hC hstep n harea
  dsimp only [v,C,g] at ht
  convert ht using 1
  ring

lemma rectangle_measure_total {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))).real univ =
      (b-a)*(d-c) := by
  rw [Measure.real,← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.restrict_apply_univ,Real.volume_Ioc,ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (sub_nonneg.2 hab),ENNReal.toReal_ofReal (sub_nonneg.2 hcd)]

theorem strip_parent_energy {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {a b c d a' b' c' d' : ℝ}
    (hab : a < b) (hcd : c < d) (hab' : a' < b') (hcd' : c' < d')
    (hlo : 0 ≤ c) (hhi : d ≤ Real.pi)
    (haa : a ≤ a') (hbb : b' ≤ b) (hcc : c ≤ c') (hdd : d' ≤ d)
    (hlen : d-c ≤ 2*(d'-c')) :
    ((∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb a' b').prod (intervalProb c' d'))-
      (∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb a b).prod (intervalProb c d)))^2 ≤
      (2/(d-c)+1/(b-a))^2*(b-a)*(d-c)*
        (∫ p : ℝ × ℝ, ‖fderiv ℝ (stripPotential H q r Fbar) ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2
          ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  have hp := strip_rectangle_poincare hF hinj hext hcont hH hr q hab hcd hab' hcd'
    hlo hhi haa hbb hcc hdd (show (0:ℝ) ≤ 2 by norm_num) hlen
  have hcoef : 0 ≤ 2/(d-c)+1/(b-a) := by
    have hb := sub_pos.2 hab
    have hd := sub_pos.2 hcd
    positivity
  have hE := strip_gradient_rect_memLp hF hinj hext hH hr q a b hlo hhi
  have hi : 0 ≤ ∫ p : ℝ × ℝ, ‖fderiv ℝ (stripPotential H q r Fbar) ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖
      ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d)) := integral_nonneg (fun _ => norm_nonneg _)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hcoef hi)).2 hp
  rw [sq_abs,mul_pow] at hs
  have hc := integral_mul_square_le (memLp_const (1:ℝ)) hE
  simp only [one_mul,one_pow,integral_const,smul_eq_mul,mul_one,
    rectangle_measure_total hab.le hcd.le] at hc
  exact hs.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc (sq_nonneg (2/(d-c)+1/(b-a))))

lemma rectangleProb_integral {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ × ℝ → ℝ) :
    (∫ p, f p ∂(intervalProb a b).prod (intervalProb c d)) =
      ((b-a)*(d-c))⁻¹*(∫ p, f p ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  rw [intervalProb,intervalProb,Measure.prod_smul_left,Measure.prod_smul_right,
    integral_smul_measure,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sub_nonneg.2 hab),ENNReal.toReal_ofReal (sub_nonneg.2 hcd)]
  simp only [smul_eq_mul,mul_inv_rev]
  ring

theorem strip_negative_mean {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {η : ℝ → ℂ} (hη : ContinuousOn η (Icc 0 1)) (hη0 : η 0 = 0)
    (hη1 : ‖η 1‖ = 1) (hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
    (haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
      (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0) :
    (∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
      ∂(intervalProb a b).prod (intervalProb 0 Real.pi))^2 ≤
      (Real.pi/(b-a))*(∫ p : ℝ × ℝ, ‖fderiv ℝ (stripPotential H q r Fbar)
        ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2
          ∂(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (0:ℝ) Real.pi))) := by
  let u := fun p : ℝ × ℝ => stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
  let G := fun p : ℝ × ℝ => ‖fderiv ℝ (stripPotential H q r Fbar) ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2
  let μ := intervalProb a b
  let ν := intervalProb 0 Real.pi
  let : IsProbabilityMeasure μ := intervalProb_isProbability hab
  let : IsProbabilityMeasure ν := intervalProb_isProbability Real.pi_pos
  have hu := strip_potential_mean_integrable hcont hH.le hr q hab Real.pi_pos le_rfl le_rfl
  have hu2 : MemLp u 2 (μ.prod ν) := MemLp.of_bound hu.aestronglyMeasurable H (ae_of_all _ (fun p => by
    have hh := sphereTruncation_bounds hH.le hr q (Fbar (Complex.exp ((p.1:ℂ)+(p.2:ℂ)*Complex.I)))
    change ‖stripPotential H q r Fbar _‖ ≤ H
    rw [Real.norm_eq_abs,stripPotential,abs_of_nonneg hh.1]
    exact hh.2))
  have hG := (strip_gradient_rect_memLp hF hinj hext hH hr q a b le_rfl le_rfl).integrable_sq
  have hR := hG.integral_prod_left
  have hRμ : Integrable (fun v => ∫ φ in Ioc (0:ℝ) Real.pi, G (v,φ)) μ :=
    integrable_intervalProb hab hR
  have hbound : ∀ᵐ p ∂μ.prod ν, u p^2 ≤
      Real.pi*(∫ φ in Ioc (0:ℝ) Real.pi, G (p.1,φ)) := by
    have hn := strip_negative_section_energy hF hinj hext hcont hH hr q hη hη0 hη1 hηH haccess
    have hv : ∀ᵐ v ∂μ, ∀ φ ∈ Ioc (0:ℝ) Real.pi, u (v,φ)^2 ≤
        Real.pi*(∫ ψ in Ioc (0:ℝ) Real.pi, G (v,ψ)) := by
      apply intervalProb_ae.mpr
      filter_upwards [ae_restrict_of_ae hn,
        ae_restrict_mem measurableSet_Ioc,show ∀ᵐ v ∂volume.restrict (Ioc a b), v ≠ (0:ℝ) from
          ae_restrict_of_ae (volume.ae_ne 0)] with v hv hvab hv0
      intro φ hφ
      have hvneg : v < 0 := lt_of_le_of_ne (hvab.2.trans hb) hv0
      have hh := hv hvneg φ ⟨hφ.1.le,hφ.2⟩
      rw [intervalIntegral.integral_of_le Real.pi_pos.le] at hh
      exact hh
    have hφ : ∀ᵐ φ ∂ν, φ ∈ Ioc (0:ℝ) Real.pi := intervalProb_ae.mpr (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hv,
      Measure.quasiMeasurePreserving_snd.ae hφ] with p hp hpφ
    exact hp p.2 hpφ
  have hmono := integral_mono_ae hu2.integrable_sq ((hRμ.comp_fst ν).const_mul Real.pi) hbound
  have hj := integral_mul_square_le (memLp_const (1:ℝ)) hu2
  simp only [one_mul,one_pow,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,
    smul_eq_mul,mul_one,one_mul] at hj
  refine hj.trans (hmono.trans_eq ?_)
  rw [integral_const_mul]
  rw [integral_fun_fst (fun v => ∫ φ in Ioc (0:ℝ) Real.pi, G (v,φ))]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  rw [integral_intervalProb hab.le,intervalIntegral.integral_of_le hab.le]
  rw [← integral_prod _ hG]
  simp only [div_eq_mul_inv,mul_assoc]

structure DRect where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  hab : a < b
  hcd : c < d

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
namespace DRect

def closed (Q : DRect) : Set (ℝ × ℝ) := (Icc Q.a Q.b).prod (Icc Q.c Q.d)

def cells (Q : DRect) : Set (ℝ × ℝ) := (Ioc Q.a Q.b).prod (Ioc Q.c Q.d)

def measure (Q : DRect) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc Q.a Q.b)).prod (volume.restrict (Ioc Q.c Q.d))

def halfLo (l r : ℝ) (s : Bool) : ℝ := if s then (l+r)/2 else l

def halfHi (l r : ℝ) (s : Bool) : ℝ := if s then r else (l+r)/2

lemma half_bounds {l r : ℝ} (h : l < r) (s : Bool) :
    l ≤ halfLo l r s ∧ halfLo l r s < halfHi l r s ∧ halfHi l r s ≤ r := by
  cases s
  · change l ≤ l ∧ l < (l+r)/2 ∧ (l+r)/2 ≤ r
    refine ⟨le_rfl,?_,?_⟩ <;> linarith
  · change l ≤ (l+r)/2 ∧ (l+r)/2 < r ∧ r ≤ r
    refine ⟨?_,?_,le_rfl⟩ <;> linarith

lemma half_length (l r : ℝ) (s : Bool) : halfHi l r s-halfLo l r s = (r-l)/2 := by
  cases s <;> simp [halfLo,halfHi] <;> ring

def child (Q : DRect) (s : Bool × Bool) : DRect where
  a := halfLo Q.a Q.b s.1
  b := halfHi Q.a Q.b s.1
  c := halfLo Q.c Q.d s.2
  d := halfHi Q.c Q.d s.2
  hab := (half_bounds Q.hab s.1).2.1
  hcd := (half_bounds Q.hcd s.2).2.1

lemma child_bounds (Q : DRect) (s : Bool × Bool) :
    Q.a ≤ (Q.child s).a ∧ (Q.child s).b ≤ Q.b ∧
    Q.c ≤ (Q.child s).c ∧ (Q.child s).d ≤ Q.d :=
  ⟨(half_bounds Q.hab s.1).1,(half_bounds Q.hab s.1).2.2,
    (half_bounds Q.hcd s.2).1,(half_bounds Q.hcd s.2).2.2⟩

lemma child_width (Q : DRect) (s : Bool × Bool) : (Q.child s).b-(Q.child s).a = (Q.b-Q.a)/2 := half_length _ _ _

lemma child_height (Q : DRect) (s : Bool × Bool) : (Q.child s).d-(Q.child s).c = (Q.d-Q.c)/2 := half_length _ _ _

lemma child_closed_subset (Q : DRect) (s : Bool × Bool) : (Q.child s).closed ⊆ Q.closed := by
  rintro p ⟨hx,hy⟩
  obtain ⟨ha,hb,hc,hd⟩ := Q.child_bounds s
  exact ⟨⟨ha.trans hx.1,hx.2.trans hb⟩,⟨hc.trans hy.1,hy.2.trans hd⟩⟩

def chooseSide (l r x : ℝ) : Bool := decide ((l+r)/2 < x)

lemma mem_chosen_half {l r x : ℝ} (hx : x ∈ Icc l r) :
    x ∈ Icc (halfLo l r (chooseSide l r x)) (halfHi l r (chooseSide l r x)) := by
  by_cases h : (l+r)/2 < x
  · simp [chooseSide,h,halfLo,halfHi,h.le,hx.2]
  · have hm : x ≤ (l+r)/2 := le_of_not_gt h
    simp [chooseSide,h,halfLo,halfHi,hx.1,hm]

def chooseChild (Q : DRect) (x : ℝ × ℝ) : Bool × Bool :=
  (chooseSide Q.a Q.b x.1,chooseSide Q.c Q.d x.2)

lemma mem_chosen_child {Q : DRect} {x : ℝ × ℝ} (hx : x ∈ Q.closed) :
    x ∈ (Q.child (Q.chooseChild x)).closed :=
  ⟨mem_chosen_half hx.1,mem_chosen_half hx.2⟩

end DRect

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

def DIndex : ℕ → Type
  | 0 => Unit
  | n+1 => DIndex n × (Bool × Bool)

instance dIndex_fintype (n : ℕ) : Fintype (DIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (DIndex n × (Bool × Bool)))

def dyadicRect (Q : DRect) : (n : ℕ) → DIndex n → DRect
  | 0, _ => Q
  | n+1, i => (dyadicRect Q n i.1).child i.2

def dParent (n : ℕ) (i : DIndex (n+1)) : DIndex n := i.1

def dFromBits (β : ℕ → Bool × Bool) : (n : ℕ) → DIndex n
  | 0 => ()
  | n+1 => (dFromBits β n,β n)

lemma dFromBits_congr {β β' : ℕ → Bool × Bool} (n : ℕ) (h : ∀ k < n, β k = β' k) :
    dFromBits β n = dFromBits β' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (dFromBits β n,β n) = (dFromBits β' n,β' n)
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),h n (Nat.lt_succ_self n)]

def dExtendBits : (n : ℕ) → DIndex n → (ℕ → Bool × Bool)
  | 0, _ => fun _ => (false,false)
  | n+1, i => Function.update (dExtendBits n i.1) n i.2

lemma dFromBits_extend (n : ℕ) (i : DIndex n) : dFromBits (dExtendBits n i) n = i := by
  induction n with
  | zero => cases i; rfl
  | succ n ih =>
    change (dFromBits (Function.update (dExtendBits n i.1) n i.2) n,
      Function.update (dExtendBits n i.1) n i.2 n) = i
    rw [Function.update_self]
    have he := dFromBits_congr n (β := Function.update (dExtendBits n i.1) n i.2)
      (β' := dExtendBits n i.1) (fun k hk => Function.update_of_ne (Nat.ne_of_lt hk) _ _)
    rw [he,ih i.1]
    rfl

lemma dyadicRect_width (Q : DRect) (n : ℕ) (i : DIndex n) :
    (dyadicRect Q n i).b-(dyadicRect Q n i).a = (Q.b-Q.a)/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadicRect]
  | succ n ih => rw [dyadicRect,DRect.child_width,ih,pow_succ]; ring

lemma dyadicRect_height (Q : DRect) (n : ℕ) (i : DIndex n) :
    (dyadicRect Q n i).d-(dyadicRect Q n i).c = (Q.d-Q.c)/(2:ℝ)^n := by
  induction n with
  | zero => simp [dyadicRect]
  | succ n ih => rw [dyadicRect,DRect.child_height,ih,pow_succ]; ring

lemma dyadicRect_bounds (Q : DRect) (n : ℕ) (i : DIndex n) :
    Q.a ≤ (dyadicRect Q n i).a ∧ (dyadicRect Q n i).b ≤ Q.b ∧
    Q.c ≤ (dyadicRect Q n i).c ∧ (dyadicRect Q n i).d ≤ Q.d := by
  induction n with
  | zero => exact ⟨le_rfl,le_rfl,le_rfl,le_rfl⟩
  | succ n ih =>
    obtain ⟨ha,hb,hc,hd⟩ := ih i.1
    obtain ⟨ha',hb',hc',hd'⟩ := (dyadicRect Q n i.1).child_bounds i.2
    exact ⟨ha.trans ha',hb'.trans hb,hc.trans hc',hd'.trans hd⟩

def dPointBranch (Q : DRect) (x : ℝ × ℝ) : (n : ℕ) → DIndex n
  | 0 => ()
  | n+1 => (dPointBranch Q x n,(dyadicRect Q n (dPointBranch Q x n)).chooseChild x)

lemma dPointBranch_parent (Q : DRect) (x : ℝ × ℝ) (n : ℕ) :
    dParent n (dPointBranch Q x (n+1)) = dPointBranch Q x n := rfl

lemma dPointBranch_mem {Q : DRect} {x : ℝ × ℝ} (hx : x ∈ Q.closed) (n : ℕ) :
    x ∈ (dyadicRect Q n (dPointBranch Q x n)).closed := by
  induction n with
  | zero => exact hx
  | succ n ih => exact DRect.mem_chosen_child ih

lemma probability_means_tendsto {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    {u : α → ℝ} {S : Set α} {x : α} (hc : ContinuousWithinAt u S x)
    (ν : ℕ → Measure α) [∀ n, IsProbabilityMeasure (ν n)]
    (hi : ∀ n, Integrable u (ν n)) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hs : ∀ n, ∀ᵐ p ∂ν n, p ∈ S ∧ dist p x ≤ e n) :
    Tendsto (fun n => ∫ p, u p ∂ν n) atTop (𝓝 (u x)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ,hδ,hδ'⟩ := Metric.continuousWithinAt_iff.1 hc (ε/2) (half_pos hε)
  filter_upwards [he.eventually (gt_mem_nhds hδ)] with n hn
  have hb : ∀ᵐ p ∂ν n, ‖u p-u x‖ ≤ ε/2 := by
    filter_upwards [hs n] with p hp
    simpa only [dist_eq_norm] using (hδ' hp.1 (hp.2.trans_lt hn)).le
  have hm := norm_integral_le_of_norm_le_const hb
  rw [integral_sub (hi n) (integrable_const _)] at hm
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul,mul_one] at hm
  have hh : dist (∫ p, u p ∂ν n) (u x) ≤ ε/2 := by simpa only [dist_eq_norm] using hm
  exact hh.trans_lt (by linarith)

lemma rectangle_point_dist {a b c d : ℝ} {p x : ℝ × ℝ}
    (hp : p ∈ (Icc a b).prod (Icc c d)) (hx : x ∈ (Icc a b).prod (Icc c d)) :
    dist p x ≤ max (b-a) (d-c) := by
  rw [Prod.dist_eq]
  apply max_le_max
  · rw [Real.dist_eq,abs_le]
    constructor <;> linarith [hp.1.1,hp.1.2,hx.1.1,hx.1.2]
  · rw [Real.dist_eq,abs_le]
    constructor <;> linarith [hp.2.1,hp.2.2,hx.2.1,hx.2.2]

theorem strip_rectangle_means_tendsto {Fbar : ℂ → OnePoint ℂ}
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 ≤ H) (hr : 0 < r) (q : ℂ)
    (a b c d : ℕ → ℝ) (hab : ∀ n, a n < b n) (hcd : ∀ n, c n < d n)
    (hlo : ∀ n, 0 ≤ c n) (hhi : ∀ n, d n ≤ Real.pi)
    {x : ℝ × ℝ} (hx : ∀ n, x ∈ (Icc (a n) (b n)).prod (Icc (c n) (d n)))
    (he : Tendsto (fun n => max (b n-a n) (d n-c n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
      ∂(intervalProb (a n) (b n)).prod (intervalProb (c n) (d n))) atTop
      (𝓝 (stripPotential H q r Fbar ((x.1:ℂ)+(x.2:ℂ)*Complex.I))) := by
  let ν := fun n => (intervalProb (a n) (b n)).prod (intervalProb (c n) (d n))
  have (n : ℕ) : IsProbabilityMeasure (intervalProb (a n) (b n)) := intervalProb_isProbability (hab n)
  have (n : ℕ) : IsProbabilityMeasure (intervalProb (c n) (d n)) := intervalProb_isProbability (hcd n)
  let S := {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ Real.pi}
  have hu : ContinuousOn (fun p : ℝ × ℝ => stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)) S :=
    (stripPotential_continuous hH hr q hcont).comp
      ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul_const _)).continuousOn
      (by intro p hp; simpa [closedStrip,S] using hp)
  have hxs : x ∈ S := ⟨(hlo 0).trans (hx 0).2.1,(hx 0).2.2.trans (hhi 0)⟩
  apply probability_means_tendsto (hu x hxs) ν
    (fun n => strip_potential_mean_integrable hcont hH hr q (hab n) (hcd n) (hlo n) (hhi n)) he
  intro n
  have hmem {l r : ℝ} : ∀ᵐ y : ℝ ∂intervalProb l r, y ∈ Icc l r :=
    intervalProb_ae.2 ((ae_restrict_mem measurableSet_Ioc).mono (fun y hy => Ioc_subset_Icc_self hy))
  have hX := (Measure.quasiMeasurePreserving_fst (μ := intervalProb (a n) (b n))
    (ν := intervalProb (c n) (d n))).tendsto_ae.eventually hmem
  have hY := (Measure.quasiMeasurePreserving_snd (μ := intervalProb (a n) (b n))
    (ν := intervalProb (c n) (d n))).tendsto_ae.eventually hmem
  filter_upwards [hX,hY] with p hpx hpy
  exact ⟨⟨(hlo n).trans hpy.1,hpy.2.trans (hhi n)⟩,rectangle_point_dist ⟨hpx,hpy⟩ (hx n)⟩

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
variable (H : ℝ) (q : ℂ) (r : ℝ) (Fbar : ℂ → OnePoint ℂ)

def stripMean (Q : DRect) : ℝ :=
  ∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
    ∂(intervalProb Q.a Q.b).prod (intervalProb Q.c Q.d)

def stripEnergy (Q : DRect) : ℝ :=
  ∫ p : ℝ × ℝ, ‖fderiv ℝ (stripPotential H q r Fbar) ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2 ∂Q.measure

def rectCoefficient (Q : DRect) : ℝ := (2/(Q.d-Q.c)+1/(Q.b-Q.a))^2*(Q.b-Q.a)*(Q.d-Q.c)

lemma rectCoefficient_pos (Q : DRect) : 0 < rectCoefficient Q := by
  have hw := sub_pos.2 Q.hab
  have hh := sub_pos.2 Q.hcd
  unfold rectCoefficient
  positivity

lemma dyadicRect_coefficient (Q : DRect) (n : ℕ) (i : DIndex n) :
    rectCoefficient (dyadicRect Q n i) = rectCoefficient Q := by
  unfold rectCoefficient
  rw [dyadicRect_width,dyadicRect_height]
  have h2 : (2:ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hw : Q.b-Q.a ≠ 0 := (sub_pos.2 Q.hab).ne'
  have hh : Q.d-Q.c ≠ 0 := (sub_pos.2 Q.hcd).ne'
  field_simp

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy
variable (H : ℝ) (q : ℂ) (r : ℝ) (Fbar : ℂ → OnePoint ℂ)
variable {H q r Fbar}

theorem strip_dyadic_mean_critical {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im})
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (hH : 0 < H) (hr : 0 < r) (Q : DRect) (hlo : 0 ≤ Q.c) (hhi : Q.d ≤ Real.pi)
    (n : ℕ) (i : DIndex n) :
    (stripMean H q r Fbar (dyadicRect Q n i)-stripMean H q r Fbar Q)^2 ≤
      3*rectCoefficient Q*(n:ℝ)*stripEnergy H q r Fbar Q := by
  let β := dExtendBits n i
  let R := fun j => dyadicRect Q j (dFromBits β j)
  have hR0 : R 0 = Q := rfl
  have hRn : R n = dyadicRect Q n i := by dsimp [R,β]; rw [dFromBits_extend]
  have hRstep (j : ℕ) : R (j+1) = (R j).child (β j) := rfl
  have hb (j : ℕ) := (R j).child_bounds (β j)
  have ht := strip_nested_means hF hinj hext hcont hH hr q
    (fun j => (R j).a) (fun j => (R j).b) (fun j => (R j).c) (fun j => (R j).d)
    (fun j => (R j).hab) (fun j => (R j).hcd) hlo hhi
    (fun j => (hb j).1) (fun j => (hb j).2.1) (fun j => (hb j).2.2.1) (fun j => (hb j).2.2.2)
    (fun j => dyadicRect_width Q j (dFromBits β j))
    (fun j => dyadicRect_height Q j (dFromBits β j)) n
  change (stripMean H q r Fbar (R n)-stripMean H q r Fbar (R 0))^2 ≤ _ at ht
  rw [hR0,hRn] at ht
  unfold stripEnergy rectCoefficient DRect.measure
  convert ht using 1
  ring

theorem strip_dyadic_mean_step {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im})
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (hH : 0 < H) (hr : 0 < r) (Q : DRect) (hlo : 0 ≤ Q.c) (hhi : Q.d ≤ Real.pi)
    (n : ℕ) (i : DIndex (n+1)) :
    (stripMean H q r Fbar (dyadicRect Q (n+1) i)-stripMean H q r Fbar (dyadicRect Q n (dParent n i)))^2 ≤
      rectCoefficient Q*stripEnergy H q r Fbar (dyadicRect Q n (dParent n i)) := by
  let R := dyadicRect Q n i.1
  obtain ⟨ha,hb,hc,hd⟩ := dyadicRect_bounds Q n i.1
  obtain ⟨ha',hb',hc',hd'⟩ := R.child_bounds i.2
  have hl : R.d-R.c ≤ 2*((R.child i.2).d-(R.child i.2).c) := by rw [DRect.child_height]; linarith
  have ht := strip_parent_energy hF hinj hext hcont hH hr q R.hab R.hcd
    (R.child i.2).hab (R.child i.2).hcd (hlo.trans hc) (hd.trans hhi) ha' hb' hc' hd' hl
  change (stripMean H q r Fbar (R.child i.2)-stripMean H q r Fbar R)^2 ≤
    rectCoefficient R*stripEnergy H q r Fbar R at ht
  rw [dyadicRect_coefficient] at ht
  exact ht

theorem strip_dyadic_mean_limit
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    (hH : 0 ≤ H) (hr : 0 < r) (Q : DRect) (hlo : 0 ≤ Q.c) (hhi : Q.d ≤ Real.pi)
    {x : ℝ × ℝ} (hx : x ∈ Q.closed) :
    Tendsto (fun n => stripMean H q r Fbar (dyadicRect Q n (dPointBranch Q x n))) atTop
      (𝓝 (stripPotential H q r Fbar ((x.1:ℂ)+(x.2:ℂ)*Complex.I))) := by
  let R := fun n => dyadicRect Q n (dPointBranch Q x n)
  have hb (n : ℕ) := dyadicRect_bounds Q n (dPointBranch Q x n)
  apply strip_rectangle_means_tendsto hcont hH hr q
    (fun n => (R n).a) (fun n => (R n).b) (fun n => (R n).c) (fun n => (R n).d)
    (fun n => (R n).hab) (fun n => (R n).hcd)
    (fun n => hlo.trans (hb n).2.2.1) (fun n => (hb n).2.2.2.trans hhi)
    (fun n => dPointBranch_mem hx n)
  have h2 := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  have hw : Tendsto (fun n => (R n).b-(R n).a) atTop (𝓝 0) := by
    simpa only [R,dyadicRect_width,div_eq_mul_inv,mul_zero,Function.comp_def] using tendsto_const_nhds.mul h2
  have hh : Tendsto (fun n => (R n).d-(R n).c) atTop (𝓝 0) := by
    simpa only [R,dyadicRect_height,div_eq_mul_inv,mul_zero,Function.comp_def] using tendsto_const_nhds.mul h2
  simpa only [max_self] using hw.max hh

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.RectangleEnergy

def totalStripEnergy (H : ℝ) (q : ℂ) (r : ℝ) (Fbar : ℂ → OnePoint ℂ) : ℝ :=
  ∫ p : ℝ × ℝ, ‖fderiv ℝ (stripPotential H q r Fbar) ((p.1:ℂ)+(p.2:ℂ)*Complex.I)‖^2
    ∂volume.prod (volume.restrict (Ioc (0:ℝ) Real.pi))

lemma totalStripEnergy_nonneg (H : ℝ) (q : ℂ) (r : ℝ) (Fbar : ℂ → OnePoint ℂ) :
    0 ≤ totalStripEnergy H q r Fbar := integral_nonneg (fun _ => sq_nonneg _)

lemma totalStripEnergy_eq (H : ℝ) (q : ℂ) (r : ℝ) (Fbar : ℂ → OnePoint ℂ) :
    totalStripEnergy H q r Fbar = ∫ z in openStrip, ‖fderiv ℝ (stripPotential H q r Fbar) z‖^2 := by
  have he := (Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding
    (fun z => ‖fderiv ℝ (stripPotential H q r Fbar) z‖^2) openStrip
  have hs : Complex.measurableEquivRealProd.symm ⁻¹' openStrip =
      (univ : Set ℝ).prod (Ioo (0:ℝ) Real.pi) := by
    ext p
    change (0 < p.2 ∧ p.2 < Real.pi) ↔ True ∧ (0 < p.2 ∧ p.2 < Real.pi)
    simp
  rw [hs] at he
  change (∫ p : ℝ × ℝ, _ ∂(volume.prod volume).restrict ((univ : Set ℝ) ×ˢ Ioo (0:ℝ) Real.pi)) = _ at he
  rw [← Measure.prod_restrict,Measure.restrict_univ,restrict_Ioo_eq_restrict_Ioc] at he
  refine Eq.trans ?_ he
  unfold totalStripEnergy
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    have hp : (p.1:ℂ)+(p.2:ℂ)*Complex.I = Complex.measurableEquivRealProd.symm p := by
      apply Complex.ext <;> simp
    dsimp only
    rw [hp])

 theorem totalStripEnergy_bound {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ) :
    totalStripEnergy H q r Fbar ≤ 2*Real.pi*H := by
  have hi := strip_energy_integrable hF hinj hext hH hr q
  have hb := strip_potential_energy hF hinj hext hH hr q
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z => sq_nonneg _))] at hb
  rw [totalStripEnergy_eq]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

lemma stripEnergy_le_total {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    (Q : DRect) (hlo : 0 ≤ Q.c) (hhi : Q.d ≤ Real.pi) :
    stripEnergy H q r Fbar Q ≤ totalStripEnergy H q r Fbar := by
  have hi := strip_energy_integrable_prod hF hinj hext hH hr q
  rw [restrict_Ioo_eq_restrict_Ioc] at hi
  apply integral_mono_measure _ (ae_of_all _ (fun _ => sq_nonneg _)) hi
  exact Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono_set _
    (fun y hy => ⟨hlo.trans_lt hy.1,hy.2.trans hhi⟩))

def unitSlab (j : ℝ) : DRect := ⟨j,j+1,0,Real.pi,by linarith,Real.pi_pos⟩

def longSlab (j : ℝ) (hj : 0 ≤ j) : DRect := ⟨-1,j+1,0,Real.pi,by linarith,Real.pi_pos⟩

def slabMeanCoefficient : ℝ := 3*(2*(2/Real.pi+1)^2*Real.pi+Real.pi)

lemma slabMeanCoefficient_pos : 0 < slabMeanCoefficient := by
  unfold slabMeanCoefficient
  positivity

lemma longSlab_coefficient (j : ℝ) (hj : 0 ≤ j) :
    rectCoefficient (longSlab j hj) ≤ (2/Real.pi+1)^2*Real.pi*(j+2) := by
  have hw : 1 ≤ j+2 := by linarith
  have hi : 1/(j+2) ≤ 1 := (div_le_one (by linarith)).2 hw
  unfold rectCoefficient longSlab
  dsimp only
  rw [sub_zero,show j+1-(-1)=j+2 by ring]
  calc
    _ ≤ (2/Real.pi+1)^2*(j+2)*Real.pi := by gcongr
    _ = _ := by ring

theorem negative_unitSlab_mean {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {η : ℝ → ℂ} (hη : ContinuousOn η (Icc 0 1)) (hη0 : η 0 = 0)
    (hη1 : ‖η 1‖ = 1) (hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
    (haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
      (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r)
    (j : ℝ) (hj : j ≤ -1) :
    (stripMean H q r Fbar (unitSlab j))^2 ≤ Real.pi*totalStripEnergy H q r Fbar := by
  have hh := strip_negative_mean hF hinj hext hcont hH hr q hη hη0 hη1 hηH haccess
    (a := j) (b := j+1) (by linarith) (by linarith)
  change (stripMean H q r Fbar (unitSlab j))^2 ≤
    (Real.pi/(j+1-j))*stripEnergy H q r Fbar (unitSlab j) at hh
  rw [show j+1-j=1 by ring,div_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (stripEnergy_le_total hF hinj hext hH hr q (unitSlab j) le_rfl le_rfl) Real.pi_pos.le)

theorem positive_unitSlab_mean {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im})
    (hinj : InjOn F {z : ℂ | 0 < z.im}) {Fbar : ℂ → OnePoint ℂ}
    (hext : ∀ z, 0 < z.im → Fbar z = (F z : OnePoint ℂ))
    (hcont : ContinuousOn Fbar {z : ℂ | 0 ≤ z.im})
    {H r : ℝ} (hH : 0 < H) (hr : 0 < r) (q : ℂ)
    {η : ℝ → ℂ} (hη : ContinuousOn η (Icc 0 1)) (hη0 : η 0 = 0)
    (hη1 : ‖η 1‖ = 1) (hηH : ∀ t ∈ Icc 0 1, 0 ≤ (η t).im)
    (haccess : ∀ t ∈ Icc 0 1, Fbar (η t) ∈
      (fun w : ℂ => (w : OnePoint ℂ)) '' closedBall q r)
    (j : ℝ) (hj : 0 ≤ j) :
    (stripMean H q r Fbar (unitSlab j))^2 ≤
      slabMeanCoefficient*(j+2)*totalStripEnergy H q r Fbar := by
  let A := stripMean H q r Fbar (unitSlab j)
  let B := stripMean H q r Fbar (unitSlab (-1))
  let M := stripMean H q r Fbar (longSlab j hj)
  let E := totalStripEnergy H q r Fbar
  let K := (2/Real.pi+1)^2*Real.pi
  have hE : 0 ≤ E := totalStripEnergy_nonneg _ _ _ _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEB := stripEnergy_le_total hF hinj hext hH hr q (longSlab j hj) le_rfl le_rfl
  have hp (a' b' : ℝ) (hab' : a' < b') (haa : -1 ≤ a') (hbb : b' ≤ j+1) :
      ((∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb a' b').prod (intervalProb 0 Real.pi))-M)^2 ≤ K*(j+2)*E := by
    have hh := strip_parent_energy hF hinj hext hcont hH hr q
      (a := -1) (b := j+1) (c := 0) (d := Real.pi) (a' := a') (b' := b') (c' := 0) (d' := Real.pi)
      (by linarith) Real.pi_pos hab' Real.pi_pos le_rfl le_rfl haa hbb le_rfl le_rfl
      (by linarith [Real.pi_pos])
    change (_-M)^2 ≤ rectCoefficient (longSlab j hj)*stripEnergy H q r Fbar (longSlab j hj) at hh
    exact hh.trans (mul_le_mul (longSlab_coefficient j hj) hEB
      (integral_nonneg (fun _ => sq_nonneg _)) (by positivity))
  have hA : (A-M)^2 ≤ K*(j+2)*E := hp j (j+1) (by linarith) (by linarith) le_rfl
  have hB : (M-B)^2 ≤ K*(j+2)*E := by
    have hh := hp (-1) 0 (by norm_num) le_rfl (by linarith)
    have heB : B = ∫ p : ℝ × ℝ, stripPotential H q r Fbar ((p.1:ℂ)+(p.2:ℂ)*Complex.I)
        ∂(intervalProb (-1) 0).prod (intervalProb 0 Real.pi) := by simp [B,stripMean,unitSlab]
    rw [← heB] at hh
    nlinarith
  have hb : B^2 ≤ Real.pi*E := negative_unitSlab_mean hF hinj hext hcont hH hr q
    hη hη0 hη1 hηH haccess (-1) le_rfl
  have hb' : B^2 ≤ Real.pi*(j+2)*E := hb.trans (by nlinarith [mul_nonneg hE (mul_nonneg Real.pi_pos.le (show 0 ≤ j+1 by linarith))])
  have hsum : A^2 ≤ 3*((A-M)^2+(M-B)^2+B^2) := by
    nlinarith [sq_nonneg ((A-M)-(M-B)),sq_nonneg ((A-M)-B),sq_nonneg ((M-B)-B)]
  change A^2 ≤ slabMeanCoefficient*(j+2)*E
  calc
    _ ≤ 3*((A-M)^2+(M-B)^2+B^2) := hsum
    _ ≤ 3*(K*(j+2)*E+K*(j+2)*E+Real.pi*(j+2)*E) := by gcongr
    _ = _ := by dsimp [K,slabMeanCoefficient]; ring

lemma complex_rectangle_diff_norm (Q : DRect) {x : ℝ × ℝ} (hx : x ∈ Q.closed) :
    ‖((x.1:ℂ)+(x.2:ℂ)*Complex.I)-((Q.a:ℂ)+(Q.c:ℂ)*Complex.I)‖ ≤
      (Q.b-Q.a)+(Q.d-Q.c) := by
  have hh := Complex.norm_le_abs_re_add_abs_im
    (((x.1:ℂ)+(x.2:ℂ)*Complex.I)-((Q.a:ℂ)+(Q.c:ℂ)*Complex.I))
  change x.1 ∈ Icc Q.a Q.b ∧ x.2 ∈ Icc Q.c Q.d at hx
  simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_add,add_zero] at hh
  rw [abs_of_nonneg (sub_nonneg.2 hx.1.1),abs_of_nonneg (sub_nonneg.2 hx.2.1)] at hh
  linarith [hx.1.2,hx.2.2]

lemma exp_difference_small {z w : ℂ} (hzw : ‖z-w‖ ≤ 1) :
    ‖Complex.exp z-Complex.exp w‖ ≤ 2*‖z-w‖*Real.exp w.re := by
  have he : Complex.exp z-Complex.exp w = (Complex.exp (z-w)-1)*Complex.exp w := by
    rw [sub_mul,one_mul,← Complex.exp_add,sub_add_cancel]
  rw [he,norm_mul,Complex.norm_exp]
  exact mul_le_mul_of_nonneg_right (Complex.norm_exp_sub_one_le hzw) (Real.exp_pos _).le

def expCellScale : ℝ := 4*(1+Real.pi)*Real.exp 1

lemma expCellScale_pos : 0 < expCellScale := by unfold expCellScale; positivity

lemma expCellScale_ge : 1+Real.pi ≤ expCellScale := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.2 (by norm_num)
  unfold expCellScale
  nlinarith [Real.pi_pos]

lemma dyadicCell_exp_geometry (j : ℝ) (n : ℕ) (i : DIndex n)
    (hsmall : expCellScale/(2:ℝ)^n < 1/16) :
    let Q := dyadicRect (unitSlab j) n i
    let v := Complex.exp ((Q.a:ℂ)+(Q.c:ℂ)*Complex.I)
    0 ≤ v.im ∧ Real.exp j/2 ≤ ‖v‖ ∧
    ∀ x ∈ Q.closed, dist v (Complex.exp ((x.1:ℂ)+(x.2:ℂ)*Complex.I)) <
      Real.exp j*(expCellScale/(2:ℝ)^n) := by
  let Q := dyadicRect (unitSlab j) n i
  have hb := dyadicRect_bounds (unitSlab j) n i
  change j ≤ Q.a ∧ Q.b ≤ j+1 ∧ 0 ≤ Q.c ∧ Q.d ≤ Real.pi at hb
  have hl : (Q.b-Q.a)+(Q.d-Q.c) = (1+Real.pi)/(2:ℝ)^n := by
    rw [dyadicRect_width,dyadicRect_height]
    simp only [unitSlab]
    ring
  have hc : Q.c ≤ Real.pi := Q.hcd.le.trans hb.2.2.2
  have hre : (((Q.a:ℂ)+(Q.c:ℂ)*Complex.I):ℂ).re = Q.a := by simp
  have him : (((Q.a:ℂ)+(Q.c:ℂ)*Complex.I):ℂ).im = Q.c := by simp
  dsimp only
  change 0 ≤ (Complex.exp ((Q.a:ℂ)+(Q.c:ℂ)*Complex.I)).im ∧ _
  refine ⟨?_,?_,?_⟩
  · rw [Complex.exp_im,hre,him]
    exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_mem_Icc ⟨hb.2.2.1,hc⟩)
  · rw [Complex.norm_exp,hre]
    have hh := Real.exp_le_exp.mpr hb.1
    linarith [Real.exp_pos j]
  · intro x hx
    have hd := complex_rectangle_diff_norm Q hx
    rw [hl] at hd
    have hge : (1+Real.pi)/(2:ℝ)^n ≤ expCellScale/(2:ℝ)^n := by
      exact div_le_div_of_nonneg_right expCellScale_ge (by positivity)
    have hdn : ‖((x.1:ℂ)+(x.2:ℂ)*Complex.I)-((Q.a:ℂ)+(Q.c:ℂ)*Complex.I)‖ ≤ 1 := by
      linarith [hd.trans hge]
    rw [dist_comm,dist_eq_norm]
    have he := exp_difference_small hdn
    rw [hre] at he
    have hea : Real.exp Q.a ≤ Real.exp (j+1) := Real.exp_le_exp.mpr (Q.hab.le.trans hb.2.1)
    calc
      _ ≤ 2*‖((x.1:ℂ)+(x.2:ℂ)*Complex.I)-((Q.a:ℂ)+(Q.c:ℂ)*Complex.I)‖*Real.exp Q.a := he
      _ ≤ 2*((1+Real.pi)/(2:ℝ)^n)*Real.exp (j+1) := by gcongr
      _ < Real.exp j*(expCellScale/(2:ℝ)^n) := by
        rw [Real.exp_add,expCellScale]
        have hp : 0 < (1+Real.pi)/(2:ℝ)^n*Real.exp j*Real.exp 1 := by positivity
        convert (show 2*((1+Real.pi)/(2:ℝ)^n*Real.exp j*Real.exp 1) <
          4*((1+Real.pi)/(2:ℝ)^n*Real.exp j*Real.exp 1) by linarith) using 1 <;> ring

end SLEExactGauge.RectangleEnergy

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.BoundaryCutoff

def clamp (σ ε : ℝ) (w : ℂ) : ℂ := ⟨σ*max (σ*w.re) ε,w.im⟩

def velocity (σ ε u : ℝ) (w : ℂ) : ℂ := 2/clamp σ ε (w-(u:ℂ))

lemma side_sq {σ : ℝ} (hσ : |σ| = 1) : σ*σ = 1 := by
  have hh := sq_abs σ
  rw [hσ] at hh
  nlinarith

lemma clamp_eq {σ ε : ℝ} (hσ : |σ| = 1) {w : ℂ} (hw : ε ≤ σ*w.re) :
    clamp σ ε w = w := by
  apply Complex.ext
  · change σ*max (σ*w.re) ε = w.re
    rw [max_eq_left hw,← mul_assoc,side_sq hσ,one_mul]
  · rfl

lemma clamp_norm {σ ε : ℝ} (hσ : |σ| = 1) (hε : 0 < ε) (w : ℂ) : ε ≤ ‖clamp σ ε w‖ := by
  have hh : ε ≤ |(clamp σ ε w).re| := by
    change ε ≤ |σ*max (σ*w.re) ε|
    rw [abs_mul,hσ,one_mul,abs_of_nonneg (hε.le.trans (le_max_right _ _))]
    exact le_max_right _ _
  exact hh.trans (Complex.abs_re_le_norm _)

lemma clamp_ne_zero {σ ε : ℝ} (hσ : |σ| = 1) (hε : 0 < ε) (w : ℂ) : clamp σ ε w ≠ 0 :=
  norm_pos_iff.1 (hε.trans_le (clamp_norm hσ hε w))

lemma clamp_norm_sub {σ ε : ℝ} (hσ : |σ| = 1) (z w : ℂ) :
    ‖clamp σ ε z-clamp σ ε w‖ ≤ 2*‖z-w‖ := by
  have hm : |max (σ*z.re) ε-max (σ*w.re) ε| ≤ |σ*z.re-σ*w.re| := by
    simpa only [sub_self,abs_zero,max_eq_left (abs_nonneg (σ*z.re-σ*w.re))] using
      abs_max_sub_max_le_max (σ*z.re) ε (σ*w.re) ε
  have hr : |(clamp σ ε z-clamp σ ε w).re| ≤ ‖z-w‖ := by
    change |σ*max (σ*z.re) ε-σ*max (σ*w.re) ε| ≤ ‖z-w‖
    rw [← mul_sub,abs_mul,hσ,one_mul]
    have he : |σ*z.re-σ*w.re| = |z.re-w.re| := by rw [← mul_sub,abs_mul,hσ,one_mul]
    rw [he] at hm
    exact hm.trans (by simpa using Complex.abs_re_le_norm (z-w))
  have hi : |(clamp σ ε z-clamp σ ε w).im| ≤ ‖z-w‖ := by
    simpa [clamp] using Complex.abs_im_le_norm (z-w)
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

lemma velocity_eq {σ ε u : ℝ} (hσ : |σ| = 1) {w : ℂ} (hw : ε ≤ σ*(w.re-u)) :
    velocity σ ε u w = 2/(w-(u:ℂ)) := by
  unfold velocity
  rw [clamp_eq hσ (by simpa using hw)]

lemma norm_velocity_le {σ ε : ℝ} (hσ : |σ| = 1) (hε : 0 < ε) (u : ℝ) (w : ℂ) :
    ‖velocity σ ε u w‖ ≤ 2/ε := by
  rw [velocity,norm_div,Complex.norm_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hε (clamp_norm hσ hε _)

end SLEExactGauge.BoundaryCutoff

end

end

end OAI
