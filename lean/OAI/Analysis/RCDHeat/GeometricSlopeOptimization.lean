import Mathlib
import OAI.Analysis.RCDHeat.VariableHeatQuadratic

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: GeometricSlopeOptimization, GeometricSignedOptimization, DimensionalScaledParameter, DimensionalScaledGradient, DimensionalLocalGradient. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X]

theorem localSlope_sq_le_geometric_quadratic {V : X → ℝ} (x : X)
    {A B C r : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hr0 : 0 < r) (hr1 : r < 1) (J : ℕ)
    (h : ∀ j, J ≤ j → ∀ y,
      |V x-V y| ≤ C*r^j*A/2+B*dist x y^2/(2*(C*r^j))) :
    (localSlope V x).toReal^2 ≤ B*A/r^2 := by
  let c := Real.sqrt (B/A)
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos hB hA)
  have hc2 : c^2*A = B := by
    rw [show c^2 = B/A from Real.sq_sqrt (div_nonneg hB.le hA.le)]
    field_simp
  let S := C*r^J
  have hS : 0 < S := mul_pos hC (pow_pos hr0 J)
  have hslope : localSlope V x ≤ ENNReal.ofReal (A*c/r) := by
    refine (iInf_le_of_le (S/c) (iInf_le_of_le (div_pos hS hc) ?_)).trans le_rfl
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hne
    have hd : 0 < dist x y := dist_pos.mpr (Ne.symm hne)
    have hdS : c*dist x y < S := by
      have hh := (lt_div_iff₀ hc).mp hy
      nlinarith only [hh]
    obtain ⟨j,hjl,hju⟩ := exists_nat_pow_near_of_lt_one
      (div_pos (mul_pos hc hd) hS) ((div_le_one hS).mpr hdS.le) hr0 hr1
    let s := C*r^(J+j)
    have hse : s = S*r^j := by dsimp [s,S]; rw [pow_add]; ring
    have hsp : 0 < s := mul_pos hC (pow_pos hr0 _)
    have hsd : c*dist x y ≤ s := by
      have hh := (div_le_iff₀ hS).mp hju
      rw [hse]; nlinarith only [hh]
    have hsr : s*r < c*dist x y := by
      have hh := (lt_div_iff₀ hS).mp hjl
      rw [pow_succ] at hh
      rw [hse]; nlinarith only [hh]
    have he1 : s*A/2 ≤ A*c/r*dist x y/2 := by
      have hh := (lt_div_iff₀ hr0).mpr hsr
      calc
        _ ≤ (c*dist x y/r)*A/2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh.le hA.le) (by norm_num)
        _ = _ := by ring
    have he2 : B*dist x y^2/(2*s) ≤ A*c*dist x y/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2*s)).mpr
      rw [←hc2]
      nlinarith [mul_nonneg (show 0 ≤ A*c*dist x y by positivity) (sub_nonneg.mpr hsd)]
    have he3 : A*c*dist x y/2 ≤ A*c/r*dist x y/2 := by
      have hn : A*c ≤ A*c/r := (le_div_iff₀ hr0).mpr (by nlinarith [mul_nonneg (mul_pos hA hc).le (sub_nonneg.mpr hr1.le)])
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ dist x y/2)
    have hh := h (J+j) (Nat.le_add_right _ _) y
    change |V x-V y| ≤ s*A/2+B*dist x y^2/(2*s) at hh
    have hb : |V x-V y| ≤ A*c/r*dist x y := by linarith
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hd).mpr
    simpa only [abs_sub_comm] using hb
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hslope
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ A*c/r)] at ht
  have hh := pow_le_pow_left₀ ENNReal.toReal_nonneg ht 2
  have he : (A*c/r)^2 = B*A/r^2 := by rw [←hc2]; ring
  rwa [he] at hh

theorem localSlope_sq_le_geometric_limit {V : X → ℝ} (x : X)
    {A B C r : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hr0 : 0 < r) (hr1 : r < 1) (a b : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (h : ∀ᶠ j in atTop, ∀ y,
      |V x-V y| ≤ C*r^j*a j/2+b j*dist x y^2/(2*(C*r^j))) :
    (localSlope V x).toReal^2 ≤ B*A/r^2 := by
  have hA : 0 ≤ A := by
    apply ge_of_tendsto ha
    filter_upwards [h] with j hj
    have hh := hj x
    simp only [sub_self,abs_zero,dist_self,zero_pow (by norm_num : 2 ≠ 0),
      mul_zero,zero_div,add_zero] at hh
    have hp : 0 < C*r^j := mul_pos hC (pow_pos hr0 j)
    exact nonneg_of_mul_nonneg_right (by linarith : 0 ≤ C*r^j*a j) hp
  have hver (ε : ℝ) (hε : 0 < ε) :
      (localSlope V x).toReal^2 ≤ (B+ε)*(A+ε)/r^2 := by
    have hsmall : ∀ᶠ j in atTop, a j ≤ A+ε ∧ b j ≤ B+ε ∧ ∀ y,
        |V x-V y| ≤ C*r^j*a j/2+b j*dist x y^2/(2*(C*r^j)) := by
      filter_upwards [ha.eventually (Iio_mem_nhds (by linarith : A < A+ε)),
        hb.eventually (Iio_mem_nhds (by linarith : B < B+ε)),h] with j hj hk hh
      exact ⟨hj.le,hk.le,hh⟩
    obtain ⟨J,hJ⟩ := eventually_atTop.mp hsmall
    apply localSlope_sq_le_geometric_quadratic x (by linarith : 0 < A+ε)
      (by linarith : 0 < B+ε) hC hr0 hr1 J
    intro j hj y
    have hp : 0 < C*r^j := mul_pos hC (pow_pos hr0 j)
    apply (hJ j hj).2.2 y |>.trans
    apply add_le_add
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hJ j hj).1 hp.le) (by norm_num)
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hJ j hj).2.1 (sq_nonneg _)) (by positivity)
  have ht : Tendsto (fun ε : ℝ => (B+ε)*(A+ε)/r^2) (𝓝[>] 0) (𝓝 (B*A/r^2)) := by
    have hc : Continuous (fun ε : ℝ => (B+ε)*(A+ε)/r^2) := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with ε hε using hver ε hε)


 
theorem geometric_signed_slope_bound {V : X → ℝ} (x : X)
    {A B r : ℝ} (hB : 0 < B) (hr0 : 0 < r) (hr1 : r < 1)
    (ap bp am bm : ℕ → ℝ)
    (hap : Tendsto ap atTop (𝓝 A)) (hbp : Tendsto bp atTop (𝓝 B))
    (ham : Tendsto am atTop (𝓝 A)) (hbm : Tendsto bm atTop (𝓝 B))
    (hp : ∀ᶠ j in atTop, ∀ y, V x-V y ≤ r^j*ap j/2+bp j*dist x y^2/(2*r^j))
    (hm : ∀ᶠ j in atTop, ∀ y, -V x-(-V y) ≤ r^j*am j/2+bm j*dist x y^2/(2*r^j)) :
    (localSlope V x).toReal^2 ≤ B*A/r^2 := by
  apply localSlope_sq_le_geometric_limit x hB zero_lt_one hr0 hr1
    (fun j => max (ap j) (am j)) (fun j => max (bp j) (bm j))
    (by simpa using hap.max ham) (by simpa using hbp.max hbm)
  filter_upwards [hp,hm] with j hp hm y
  simp only [one_mul]
  apply abs_le.mpr
  have hb (a b : ℝ) (ha : a ≤ max (ap j) (am j)) (hb : b ≤ max (bp j) (bm j)) :
      r^j*a/2+b*dist x y^2/(2*r^j) ≤
        r^j*max (ap j) (am j)/2+max (bp j) (bm j)*dist x y^2/(2*r^j) := by
    apply add_le_add
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha (pow_pos hr0 j).le) (by norm_num)
    · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (sq_nonneg _)) (by positivity)
  constructor
  · have hh := (hm y).trans (hb _ _ (le_max_right _ _) (le_max_right _ _))
    linarith
  · exact (hp y).trans (hb _ _ (le_max_left _ _) (le_max_left _ _))

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_scaled_parameter_ratio
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {l : ℝ} (hl : 0 < l)
    (hH : (fun x => (slopeAtScale φ l x).toReal^2) =ᵐ[hausdorff n X] H)
    (N : ℝ) (hN : (n:ℝ) ≤ N) {t : ℝ} (ht : 0 < t)
    (q r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ V : X → ℝ, Continuous V →
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ᵐ x ∂hausdorff n X,
        (localSlope V x).toReal^2 ≤ Real.exp (-2*K*t)*
          (heatAt (hausdorff n X) hX.quadratic t H x+
          4*t*q*heatGeneratorAt (hausdorff n X) hX.quadratic t f x+2*N*q^2*heatKernelIntegral K 1 1 t)/r^2 := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro V hV heV
  have hfneg : (-φ) =ᵐ[μ] (-f : Lp ℝ 2 μ) := by
    filter_upwards [hf,Lp.coeFn_neg f] with x hx hy
    simp only [hy,Pi.neg_apply,hx]
  have heVneg : (heatAt μ hX.quadratic t (-f) : X → ℝ) =ᵐ[μ] -V := by
    rw [map_neg]
    filter_upwards [heV,Lp.coeFn_neg (heatAt μ hX.quadratic t f)] with x hx hy
    simpa only [hy,Pi.neg_apply] using congrArg Neg.neg hx
  have hHneg : (fun x => (slopeAtScale (-φ) l x).toReal^2) =ᵐ[μ] H := by
    simpa only [slopeAtScale_neg_eq] using hH
  have hp := hX.variable_geometric_increment K n hn hφ p R hsupp f H hf hl hH N hN ht q r hr0 hr1 V hV heV
  have hm := hX.variable_geometric_increment K n hn hφ.neg p R
    (fun x hx => by simp only [Pi.neg_apply,hsupp x hx,neg_zero]) (-f) H hfneg hl hHneg N hN ht (-q) r hr0 hr1 (-V) hV.neg heVneg
  have hgen : (heatGeneratorAt μ hX.quadratic t (-f) : X → ℝ) =ᵐ[μ]
      fun x => -heatGeneratorAt μ hX.quadratic t f x := by
    rw [map_neg]; exact Lp.coeFn_neg _
  filter_upwards [hp,hm,hgen] with x hp hm hg
  obtain ⟨ap,bp,hap,hbp,hp⟩ := hp
  obtain ⟨am,bm,ham,hbm,hm⟩ := hm
  rw [hg] at ham
  have he : heatAt μ hX.quadratic t H x+4*t*(-q)*(-heatGeneratorAt μ hX.quadratic t f x)+
      2*N*(-q)^2*heatKernelIntegral K 1 1 t =
      heatAt μ hX.quadratic t H x+4*t*q*heatGeneratorAt μ hX.quadratic t f x+
      2*N*q^2*heatKernelIntegral K 1 1 t := by ring
  rw [he] at ham
  exact geometric_signed_slope_bound x (Real.exp_pos _) hr0 hr1 ap bp am bm hap hbp ham hbm hp hm

theorem NoncollapsedRCD.dimensional_scaled_parameter
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {l : ℝ} (hl : 0 < l)
    (hH : (fun x => (slopeAtScale φ l x).toReal^2) =ᵐ[hausdorff n X] H)
    (N : ℝ) (hN : (n:ℝ) ≤ N) {t : ℝ} (ht : 0 < t) (q : ℝ) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ V : X → ℝ, Continuous V →
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ᵐ x ∂hausdorff n X,
        (localSlope V x).toReal^2 ≤ Real.exp (-2*K*t)*
          (heatAt (hausdorff n X) hX.quadratic t H x+
          4*t*q*heatGeneratorAt (hausdorff n X) hX.quadratic t f x+2*N*q^2*heatKernelIntegral K 1 1 t) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro V hV heV
  let r : ℕ → ℝ := fun j => 1-1/((j:ℝ)+2)
  have hr0 (j : ℕ) : 0 < r j := by
    dsimp [r]; have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hh : 1/((j:ℝ)+2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have hr1 (j : ℕ) : r j < 1 := by
    dsimp [r]
    have hh : (0:ℝ) < 1/((j:ℝ)+2) := by positivity
    linarith
  have hr : Tendsto r atTop (𝓝 1) := by
    have hh : Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 (0:ℝ)) := by
      have hh := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
      convert! hh using 1
      ext j
      simp [Nat.cast_add]
    simpa [r] using hh.const_sub 1
  have hb (j : ℕ) := hX.dimensional_scaled_parameter_ratio K n hn hφ p R hsupp f H hf hl hH N hN ht q (r j) (hr0 j) (hr1 j) V hV heV
  filter_upwards [ae_all_iff.mpr hb] with x hx
  have ht' : Tendsto (fun j => Real.exp (-2*K*t)*(heatAt μ hX.quadratic t H x+
      4*t*q*heatGeneratorAt μ hX.quadratic t f x+2*N*q^2*heatKernelIntegral K 1 1 t)/(r j)^2)
      atTop (𝓝 (Real.exp (-2*K*t)*(heatAt μ hX.quadratic t H x+
      4*t*q*heatGeneratorAt μ hX.quadratic t f x+2*N*q^2*heatKernelIntegral K 1 1 t))) := by
    convert! (tendsto_const_nhds.div (hr.pow 2) (by norm_num : (1:ℝ)^2 ≠ 0)) using 1; simp
  exact ge_of_tendsto ht' (Eventually.of_forall hx)

end

 
section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

noncomputable def heatDimensionCoefficient (K N t : ℝ) : ℝ :=
  2*t^2*Real.exp (-2*K*t)/(N*heatKernelIntegral K 1 1 t)

theorem heatKernelIntegral_pos (K : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < heatKernelIntegral K 1 1 t := by
  rw [heatKernelIntegral_one]
  exact intervalIntegral.integral_pos ht (by fun_prop) (fun _ _ => (Real.exp_pos _).le)
    ⟨0,⟨le_rfl,ht.le⟩,Real.exp_pos _⟩

theorem heatDimensionCoefficient_nonneg (K : ℝ) {N t : ℝ} (hN : 0 < N) (ht : 0 < t) :
    0 ≤ heatDimensionCoefficient K N t := by
  unfold heatDimensionCoefficient
  exact div_nonneg (by positivity) (mul_pos hN (heatKernelIntegral_pos K ht)).le

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_scaled_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {l : ℝ} (hl : 0 < l)
    (hH : (fun x => (slopeAtScale φ l x).toReal^2) =ᵐ[hausdorff n X] H)
    (N : ℝ) (hN : (n:ℝ) ≤ N) {t : ℝ} (ht : 0 < t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ V : X → ℝ, Continuous V →
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ᵐ x ∂hausdorff n X,
        (localSlope V x).toReal^2 + heatDimensionCoefficient K N t *
          (heatGeneratorAt (hausdorff n X) hX.quadratic t f x)^2 ≤
          Real.exp (-2*K*t)*heatAt (hausdorff n X) hX.quadratic t H x := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro V hV heV
  have hb (q : ℚ) := hX.dimensional_scaled_parameter K n hn hφ p R hsupp f H hf hl hH N hN ht (q:ℝ) V hV heV
  have hN0 : 0 < N := by
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hJ := heatKernelIntegral_pos K ht
  filter_upwards [ae_all_iff.mpr hb] with x hx
  have ha (q : ℝ) : (localSlope V x).toReal^2 ≤ Real.exp (-2*K*t)*
      (heatAt μ hX.quadratic t H x + 4*t*q*heatGeneratorAt μ hX.quadratic t f x +
        2*N*q^2*heatKernelIntegral K 1 1 t) := by
    obtain ⟨a,_,_,ha⟩ := Real.exists_seq_rat_strictMono_tendsto q
    have hc : Continuous (fun q : ℝ => Real.exp (-2*K*t)*
      (heatAt μ hX.quadratic t H x + 4*t*q*heatGeneratorAt μ hX.quadratic t f x +
        2*N*q^2*heatKernelIntegral K 1 1 t)) := by fun_prop
    exact ge_of_tendsto (hc.continuousAt.tendsto.comp ha) (Eventually.of_forall fun j => hx (a j))
  have h := ha (-t*heatGeneratorAt μ hX.quadratic t f x/(N*heatKernelIntegral K 1 1 t))
  have he : Real.exp (-2*K*t)*
      (heatAt μ hX.quadratic t H x +
        4*t*(-t*heatGeneratorAt μ hX.quadratic t f x/(N*heatKernelIntegral K 1 1 t))*
          heatGeneratorAt μ hX.quadratic t f x +
        2*N*(-t*heatGeneratorAt μ hX.quadratic t f x/(N*heatKernelIntegral K 1 1 t))^2*
          heatKernelIntegral K 1 1 t) =
      Real.exp (-2*K*t)*heatAt μ hX.quadratic t H x -
        heatDimensionCoefficient K N t*(heatGeneratorAt μ hX.quadratic t f x)^2 := by
    unfold heatDimensionCoefficient
    field_simp [hN0.ne',hJ.ne']
    ring
  rw [he] at h
  linarith

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_local_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    (hH : (fun x => (localSlope φ x).toReal^2) =ᵐ[hausdorff n X] H)
    (N : ℝ) (hN : (n:ℝ) ≤ N) {t : ℝ} (ht : 0 < t) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ V : X → ℝ, Continuous V →
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ᵐ x ∂hausdorff n X,
        (localSlope V x).toReal^2+heatDimensionCoefficient K N t *
          (heatGeneratorAt (hausdorff n X) hX.quadratic t f x)^2 ≤
          Real.exp (-2*K*t)*heatAt (hausdorff n X) hX.quadratic t H x := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro V hV heV
  let Hj : ℕ → Lp ℝ 2 μ := fun j =>
    (slopeAtScale_sq_memLp μ hφ p R hsupp (by positivity : 0 ≤ 1/(j+1:ℝ))).toLp
      (fun x => (slopeAtScale φ (1/(j+1:ℝ)) x).toReal^2)
  have hHeq : (localSlope_sq_compact_memLp μ hφ p R hsupp).toLp
      (fun x => (localSlope φ x).toReal^2) = H := by
    apply Lp.ext
    exact (localSlope_sq_compact_memLp μ hφ p R hsupp).coeFn_toLp.trans hH
  have hc : Tendsto Hj atTop (𝓝 H) := by
    simpa only [hHeq] using slopeSq_toLp_tendsto μ hφ p R hsupp
  have hheat : Tendsto (fun j => heatAt μ hX.quadratic t (Hj j)) atTop
      (𝓝 (heatAt μ hX.quadratic t H)) := ((heatAt μ hX.quadratic t).continuous.tendsto H).comp hc
  obtain ⟨a,ha,hseq⟩ := (tendstoInMeasure_of_tendsto_Lp hheat).exists_seq_tendsto_ae
  have hb (j : ℕ) : ∀ᵐ x ∂μ,
      (localSlope V x).toReal^2+heatDimensionCoefficient K N t *
          (heatGeneratorAt μ hX.quadratic t f x)^2 ≤
      Real.exp (-2*K*t)*heatAt μ hX.quadratic t (Hj j) x := by
    apply hX.dimensional_scaled_gradient K n hn hφ p R hsupp f (Hj j) hf
      (by positivity : 0 < 1/(j+1:ℝ)) _ N hN ht V hV heV
    exact (slopeAtScale_sq_memLp μ hφ p R hsupp (by positivity : 0 ≤ 1/(j+1:ℝ))).coeFn_toLp.symm
  filter_upwards [hseq,ae_all_iff.mpr hb] with x hx hxb
  exact ge_of_tendsto (hx.const_mul (Real.exp (-2*K*t)))
    (Eventually.of_forall fun j => hxb (a j))


end RegularPointCoordinates

end OAI
