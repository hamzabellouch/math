import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Estimates.CellBallMassFromLevel
import OAI.MeasureTheory.FalconerCompletion.Fourier.HalfDimensionalFourierWithCutoff
import OAI.MeasureTheory.FalconerCompletion.Shells.WeightedMaskTransform

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
namespace GraphLiteralSupport.CurrentFalconer.Exceptional
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def scaleAbout (a : ℝ) (c x : V) : V := a • (x-c)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma scaleAbout_ball_preimage {a : ℝ} (ha : 0 < a) (c x : V) (r : ℝ) :
    scaleAbout a c ⁻¹' ball x r = ball (a⁻¹ • x+c) (r/a) := by
  ext y
  simp only [mem_preimage,mem_ball,scaleAbout,dist_eq_norm]
  have he : a • (y-c)-x = a • (y-(a⁻¹ • x+c)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  rw [lt_div_iff₀ ha]
  rw [mul_comm]

lemma projectionCollision_scale (μ : Measure V) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) (c : V) (ε : ℝ) (w : V) :
    projectionCollision (μ.map (scaleAbout a c)) (a*ε) w = projectionCollision μ ε w := by
  rw [projectionCollision,measureReal_def,Measure.map_prod_map μ μ (by unfold scaleAbout; fun_prop)
    (by unfold scaleAbout; fun_prop),Measure.map_apply (by unfold scaleAbout; fun_prop) (by measurability)]
  change ((μ.prod μ) _).toReal = ((μ.prod μ) _).toReal
  congr 2
  ext z
  change |inner ℝ (a • (z.1-c)-a • (z.2-c)) w| ≤ a*ε ↔ |inner ℝ (z.1-z.2) w| ≤ ε
  rw [←smul_sub,show (z.1-c)-(z.2-c)=z.1-z.2 by abel,real_inner_smul_left,abs_mul,abs_of_pos ha]
  exact mul_le_mul_iff_right₀ ha
end GraphLiteralSupport.CurrentFalconer.Exceptional

namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Exceptional
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

noncomputable def rescaledConditional (ρ : Measure (EuclideanSpace ℝ (Fin d))) (P : CellPath d) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (classConditional ρ P).map (scaleAbout ((2:ℝ)^P.length) (treeCenter P))

lemma rescaledConditional_probability (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) (hP : 0 < ρ (treeCell P)) :
    IsProbabilityMeasure (rescaledConditional ρ P) := by
  let := classConditional_probability ρ P hP
  unfold rescaledConditional
  infer_instance

lemma rescaledConditional_support (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) :
    ∀ᵐ x ∂rescaledConditional ρ P, dist x 0 ≤ d+1 := by
  rw [rescaledConditional]
  apply (ae_map_iff (by unfold scaleAbout; fun_prop) (by measurability)).mpr
  have hm : ∀ᵐ y ∂classConditional ρ P, y ∈ treeCell P := by
    exact classConditional_ae_mem ρ P
  filter_upwards [hm] with y hy
  have hh := ambientGridCell_dist_le (treeCenter_mem P) hy
  change dist y (treeCenter P) ≤ (d+1:ℝ)/(2:ℝ)^P.length at hh
  simp only [scaleAbout,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2:ℝ)^P.length)]
  rw [dist_eq_norm] at hh
  simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < (2:ℝ)^P.length)).mp hh

lemma rescaledConditional_dyadic_ball (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {m : ℝ → ℝ} {N B : ℕ} {s sig : ℝ}
    (hr : RegularizedProfileData ρ N B s sig m) {p j : ℕ}
    (hpN : p+j ≤ N) (P : CellPath d) (hP : P.length=p)
    (hpos : 0 < ρ (treeCell P)) (x : EuclideanSpace ℝ (Fin d)) :
    (rescaledConditional ρ P).real (ball x ((2:ℝ)^j)⁻¹) ≤
      (2*(d:ℝ)+9)^d*((2:ℝ)^N)^(m p-m (p+j)+2*(d+1:ℝ)*sig) := by
  let := hr.probability
  have he : ((2:ℝ)^j)⁻¹/(2:ℝ)^p = ((2:ℝ)^(p+j))⁻¹ := by rw [pow_add]; field_simp
  rw [measureReal_def,rescaledConditional,Measure.map_apply (by unfold scaleAbout; fun_prop)
    measurableSet_ball,scaleAbout_ball_preimage (by positivity),hP,he]
  simpa only [Nat.cast_add,measureReal_def] using conditional_ball_from_profile ρ hr (by omega) hpN P hP hpos (((2:ℝ)^p)⁻¹ • x+treeCenter P)
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Exceptional
open scoped ENNReal
variable {d : ℕ}

lemma profile_power_dyadic (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N) (p j : ℕ) (e : ℝ) :
    ((2:ℝ)^N)^(m p-m (p+j)+e) =
      (((2:ℝ)^j)⁻¹)^((d:ℝ)/2)*
        ((2:ℝ)^N)^(adjustedProfile (d:=d) m N p-adjustedProfile (d:=d) m N (p+j)+e) := by
  have hNp : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [Real.inv_rpow (by positivity),←Real.rpow_natCast_mul (by norm_num),
    ←Real.rpow_neg (by norm_num),←Real.rpow_natCast_mul (by norm_num),
    ←Real.rpow_natCast_mul (by norm_num),←Real.rpow_add (by norm_num)]
  congr 1
  unfold adjustedProfile
  push_cast
  field_simp
  ring

lemma rescaledConditional_ball_bound (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {m : ℝ → ℝ} {N B : ℕ} {s sig : ℝ} (hN : 0 < N)
    (hr : RegularizedProfileData ρ N B s sig m) {p t : ℕ}
    (hpt : p ≤ t) (htN : t ≤ N) (P : CellPath d) (hP : P.length=p)
    (hpos : 0 < ρ (treeCell P)) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ)
    (hr0 : ((2:ℝ)^(t-p))⁻¹ ≤ r) (hr1 : r ≤ 1) :
    (rescaledConditional ρ P).real (ball x r) ≤
      ((2*(d:ℝ)+9)^d*(2:ℝ)^((d:ℝ)/2))*
      ((2:ℝ)^N)^(adjustedProfile (d:=d) m N p-
        intervalMin (adjustedProfile (d:=d) m N) p t+2*(d+1:ℝ)*sig)*r^((d:ℝ)/2) := by
  let := hr.probability
  let := rescaledConditional_probability ρ P hpos
  have hrp : 0 < r := lt_of_lt_of_le (by positivity) hr0
  obtain ⟨j,hjlo,hjhi⟩ := exists_nat_pow_near_of_lt_one hrp hr1
    (by norm_num : 0 < (2:ℝ)⁻¹) (by norm_num : (2:ℝ)⁻¹ < 1)
  simp only [inv_pow] at hjlo hjhi
  have hjt : j ≤ t-p := by
    by_contra hc
    have hj : t-p < j := by omega
    have hh : ((2:ℝ)^j)⁻¹ < ((2:ℝ)^(t-p))⁻¹ :=
      inv_lt_inv₀ (by positivity) (by positivity) |>.mpr (pow_lt_pow_right₀ (by norm_num) hj)
    exact (not_lt_of_ge hr0) (hjhi.trans_lt hh)
  have hb := rescaledConditional_dyadic_ball ρ hr (by omega : p+j ≤ N) P hP hpos x
  rw [profile_power_dyadic (d:=d) m hN] at hb
  have hmin := intervalMin_le (adjustedProfile (d:=d) m N) (by omega : p ≤ p+j) (by omega : p+j ≤ t)
  have he : ((2:ℝ)^N)^(adjustedProfile (d:=d) m N p-adjustedProfile (d:=d) m N (p+j)+2*(d+1:ℝ)*sig) ≤
      ((2:ℝ)^N)^(adjustedProfile (d:=d) m N p-intervalMin (adjustedProfile (d:=d) m N) p t+2*(d+1:ℝ)*sig) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  have hjr : ((2:ℝ)^j)⁻¹ ≤ 2*r := by
    rw [pow_succ,mul_inv_rev] at hjlo
    norm_num at hjlo
    linarith
  have hs : (((2:ℝ)^j)⁻¹)^((d:ℝ)/2) ≤ (2:ℝ)^((d:ℝ)/2)*r^((d:ℝ)/2) := by
    rw [←Real.mul_rpow (by norm_num) hrp.le]
    exact Real.rpow_le_rpow (by positivity) hjr (by positivity)
  calc
    _ ≤ (rescaledConditional ρ P).real (ball x ((2:ℝ)^j)⁻¹) := measureReal_mono (ball_subset_ball hjhi)
    _ ≤ _ := hb
    _ ≤ (2*(d:ℝ)+9)^d*((2:ℝ)^((d:ℝ)/2)*r^((d:ℝ)/2))*
        ((2:ℝ)^N)^(adjustedProfile (d:=d) m N p-intervalMin (adjustedProfile (d:=d) m N) p t+2*(d+1:ℝ)*sig) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hs he (by positivity) (by positivity)) (by positivity : 0 ≤ (2*(d:ℝ)+9)^d)
    _ = _ := by ring
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.Exceptional
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem critical_projection_collision_mean (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ξ : Measure V), IsProbabilityMeasure μ →
      IsFiniteMeasure ξ → (∃ z : V, ∀ᵐ x ∂μ, dist x z ≤ T) →
      ∀ (K L H R ε : ℝ), 1 ≤ K → 1 ≤ L → 1 ≤ H → H ≤ R →
      0 < ε → 100/ε ≤ H →
      (∀ (x : V) (r : ℝ), H⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (K*r^((Module.finrank ℝ V:ℝ)/2))) →
      ξ univ ≤ 1 → (∀ᵐ w ∂ξ, ‖w‖=1) →
      (∀ (w : V), ‖w‖=1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
        ξ (ball w r) ≤ ENNReal.ofReal (L*r^((Module.finrank ℝ V:ℝ)/2))) →
      (∫ w, projectionCollision μ ε w ∂ξ) ≤ C*ε*L*K*(1+Real.log H) := by
  obtain ⟨C₁,hC₁,hmean⟩ := CriticalFourierSupport.CurrentFalconer.halfDimensional_fourier (V:=V) T
  obtain ⟨C₂,hC₂,hpoint⟩ := projection_collision_frequency_bound (V:=V)
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro μ ξ hμ hξ hsupp K L H R ε hK hL hH hHR hε hεH hball hmass hsphere hcap
  let := hμ
  let := hξ
  have hi : Integrable (fun z : V × ℝ => ‖charFun μ (z.2 • z.1)‖^2)
      (ξ.prod (volume.restrict (Icc (-H) H))) := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
  have hp := integral_mono (projectionCollision_integrable μ ξ ε)
    (hi.integral_prod_left.const_mul (C₂*ε))
    (fun w => hpoint μ ε H hε (by linarith) hεH w)
  rw [integral_const_mul,integral_integral_swap hi] at hp
  have hm := hmean μ ξ hμ hξ hsupp K L H R hK hL hH hHR hball hmass hsphere hcap
  simp only [CriticalFourierSupport.CurrentFalconer.manuscriptFourier,charFun_neg,
    Complex.norm_conj] at hm
  apply hp.trans
  have hh := mul_le_mul_of_nonneg_left hm (mul_pos hC₂ hε).le
  convert hh using 1
  ring

end GraphLiteralSupport.CurrentFalconer.Exceptional
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Exceptional
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

lemma testWidth_zero (N J t : ℕ) (sig : ℝ) :
    testWidth N J 0 t sig = 2*((2:ℝ)^t)⁻¹*((2:ℝ)^N)^(500*sig) := by
  simp only [testWidth,Nat.cast_zero,zero_div,sub_zero,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]

lemma scaled_testWidth_zero (N J p t : ℕ) (hpt : p ≤ t) (sig : ℝ) :
    (2:ℝ)^p*testWidth N J 0 t sig =
      2*((2:ℝ)^(t-p))⁻¹*((2:ℝ)^N)^(500*sig) := by
  rw [testWidth_zero,show (2:ℝ)^t=(2:ℝ)^(t-p)*(2:ℝ)^p by rw [←pow_add,Nat.sub_add_cancel hpt]]
  field_simp

theorem actual_projection_collision_mean (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N B : ℕ) (s sig : ℝ) (ρ : Measure (EuclideanSpace ℝ (Fin d)))
      (m : ℝ → ℝ), 0 < N → 0 < sig → RegularizedProfileData ρ N B s sig m →
      50 ≤ ((2:ℝ)^N)^(500*sig) →
      ∀ (ξ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ξ → ξ univ ≤ 1 →
      (∀ᵐ w ∂ξ, ‖w‖=1) →
      (∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 → ∀ r : ℝ,
        ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 → ξ (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ∀ p t : ℕ, p ≤ t → t ≤ N → ∀ P : CellPath d, P.length=p → 0 < ρ (treeCell P) → ∀ J : ℕ,
      (∫ w, (fullProjectionCollision ρ P (testWidth N J 0 t sig) w).toReal ∂ξ) ≤
        C*(N+1:ℝ)*((2:ℝ)^(t-p))⁻¹*
          ((2:ℝ)^N)^(adjustedProfile (d:=d) m N p-intervalMin (adjustedProfile (d:=d) m N) p t+
            (501+2*(d+1:ℝ))*sig) := by
  obtain ⟨C,hC,hmean⟩ := critical_projection_collision_mean (V:=EuclideanSpace ℝ (Fin d)) (d+1)
  let D : ℝ := (2*(d:ℝ)+9)^d*(2:ℝ)^((d:ℝ)/2)
  have hD : 1 ≤ D := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_pow₀; have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _; linarith
    · exact Real.one_le_rpow (by norm_num) (by positivity)
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨2*C*D,by positivity,?_⟩
  intro N B s sig ρ m hN hsig hr hbig ξ hξ hmass hsphere hcap p t hpt htN P hP hpos J
  let := hr.probability
  let := hξ
  let := rescaledConditional_probability ρ P hpos
  let R : ℝ := (2:ℝ)^N
  let H : ℝ := (2:ℝ)^(t-p)
  let Δ : ℝ := adjustedProfile (d:=d) m N p-intervalMin (adjustedProfile (d:=d) m N) p t
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr (intervalMin_le _ le_rfl hpt)
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := by positivity
  have hH : 1 ≤ H := one_le_pow₀ (by norm_num)
  have hHp : 0 < H := by positivity
  have hHR : H ≤ R := pow_le_pow_right₀ (by norm_num) (by omega)
  have hK : 1 ≤ D*R^(Δ+2*(d+1:ℝ)*sig) := one_le_mul_of_one_le_of_one_le hD
    (Real.one_le_rpow hR (by positivity))
  have hball : ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), H⁻¹ ≤ r → r ≤ 1 →
      rescaledConditional ρ P (ball x r) ≤ ENNReal.ofReal (D*R^(Δ+2*(d+1:ℝ)*sig)*r^((d:ℝ)/2)) := by
    intro x r hr0 hr1
    have hrp : 0 < r := lt_of_lt_of_le (by positivity) hr0
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
      (rescaledConditional_ball_bound ρ hN hr hpt htN P hP hpos x r hr0 hr1)
  let ε : ℝ := 2*H⁻¹*R^(500*sig)
  have hε : 0 < ε := by positivity
  have hεH : 100/ε ≤ H := by
    rw [div_le_iff₀ hε]
    dsimp [ε]
    have he : H*(2*H⁻¹*R^(500*sig))=2*R^(500*sig) := by field_simp
    rw [he]
    linarith
  have hm := hmean (rescaledConditional ρ P) ξ inferInstance hξ
    ⟨0,rescaledConditional_support ρ P⟩ (D*R^(Δ+2*(d+1:ℝ)*sig)) (R^sig) H R ε hK
    (Real.one_le_rpow hR hsig.le) hH hHR hε hεH
    (by simpa using hball) hmass hsphere (by simpa using hcap)
  have he : ∀ w, projectionCollision (rescaledConditional ρ P) ε w =
      (fullProjectionCollision ρ P (testWidth N J 0 t sig) w).toReal := by
    intro w
    have hεeq : ε=(2:ℝ)^P.length*testWidth N J 0 t sig := by
      rw [hP,scaled_testWidth_zero _ _ _ _ hpt]
    rw [hεeq,rescaledConditional,projectionCollision_scale _ (by positivity)]
    rfl
  simp_rw [he] at hm
  have hlog : 1+Real.log H ≤ N+1 := by
    dsimp [H]
    rw [Real.log_pow]
    have hln : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg (α:=ℝ) (t-p))
    have hn : (t-p:ℕ) ≤ N := by omega
    have hn' : (t-p:ℕ) ≤ (N:ℝ) := by exact_mod_cast hn
    linarith
  apply hm.trans
  have hlog' := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C*ε*R^sig*(D*R^(Δ+2*(d+1:ℝ)*sig)) by positivity)
  apply hlog'.trans_eq
  change C*(2*H⁻¹*R^(500*sig))*R^sig*(D*R^(Δ+2*(d+1:ℝ)*sig))*(N+1) =
    (2*C*D)*(N+1)*H⁻¹*R^(Δ+(501+2*(d+1:ℝ))*sig)
  have hfac : R^(500*sig)*R^sig*R^(Δ+2*(d+1:ℝ)*sig) = R^(Δ+(501+2*(d+1:ℝ))*sig) := by
    rw [←Real.rpow_add hRp,←Real.rpow_add hRp]
    congr 1; ring
  calc
    _ = (2*C*D)*(N+1)*H⁻¹*(R^(500*sig)*R^sig*R^(Δ+2*(d+1:ℝ)*sig)) := by ring
    _ = _ := by rw [hfac]
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.Exceptional
open Set MeasureTheory
open scoped ENNReal
lemma exceptional_of_mean {V : Type*} [MeasurableSpace V] (ξ : Measure V)
    [IsFiniteMeasure ξ] {f : V → ℝ} {S : Set V} {T B : ℝ}
    (hf : Integrable f ξ) (hf0 : ∀ᵐ w ∂ξ, 0 ≤ f w) (hS : ∀ᵐ w ∂ξ, w ∈ S)
    (hT : 0 < T) (hB : 0 ≤ B) (hmean : (∫ w, f w ∂ξ) ≤ T*B) :
    ξ {w | w ∈ S ∧ f w ≤ T}ᶜ ≤ ENNReal.ofReal B := by
  have hm := mul_meas_ge_le_integral_of_nonneg hf0 hf T
  have hr : ξ.real {w | T ≤ f w} ≤ B :=
    le_of_mul_le_mul_left (hm.trans hmean) hT
  apply (measure_mono_ae ?_).trans ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).mpr hr)
  filter_upwards [hS] with w hw
  intro hb
  have hh : ¬(w ∈ S ∧ f w ≤ T) := hb
  exact (lt_of_not_ge (fun h => hh ⟨hw,h⟩)).le
end GraphLiteralSupport.CurrentFalconer.Exceptional
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Exceptional Filter
open scoped ENNReal Topology

theorem uniform_actual_projection_exceptional (d : ℕ) (sig : ℝ) (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (B : ℕ) (s : ℝ),
      RegularizedProfileData ρ N B s sig m →
      ∀ (ξ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ξ → ξ univ ≤ 1 →
      (∀ᵐ w ∂ξ, ‖w‖=1) →
      (∀ w : EuclideanSpace ℝ (Fin d), ‖w‖=1 → ∀ r : ℝ,
        ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        ξ (ball w r) ≤ ENNReal.ofReal (((2:ℝ)^N)^sig*r^((d:ℝ)/2))) →
      ∀ J p t : ℕ, p ≤ t → t ≤ N → ∀ P : CellPath d, P.length=p →
        0 < ρ (treeCell P) →
        ξ (descriptorGood ρ m N sig (1000*(d+1:ℝ)) J 0 P (.projection p t))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-sig)) := by
  obtain ⟨C,hC,hmean⟩ := actual_projection_collision_mean d
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (by positivity : 0 < 500*sig) 50
  obtain ⟨N₂,h₂⟩ := eventually_atTop.mp (shell_polynomial_subpowerND 1 (2*C) sig hsig)
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro N hN ρ m B s hr ξ hξ hmass hsphere hcap J p t hpt htN P hP hpos
  have hNp : 0 < N := by omega
  have hN₁ : N₁ ≤ N := by omega
  have hN₂ : N₂ ≤ N := by omega
  let := hr.probability
  let := hξ
  let := classConditional_probability ρ P hpos
  let R : ℝ := (2:ℝ)^N
  let Δ : ℝ := adjustedProfile (d:=d) m N p-intervalMin (adjustedProfile (d:=d) m N) p t
  let H : ℝ := (2:ℝ)^(t-p)
  let T : ℝ := H⁻¹*R^(Δ+(1000*(d+1:ℝ))*sig)
  have hRp : 0 < R := by positivity
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hT : 0 < T := by positivity
  have hm := hmean N B s sig ρ m hNp hsig hr (h₁ N hN₁) ξ hξ hmass hsphere hcap
    p t hpt htN P hP hpos J
  have hc : C*(N+1:ℝ) ≤ R^sig := by
    have hh := h₂ N hN₂
    simp only [pow_one] at hh
    have hn : (1:ℝ) ≤ N := by exact_mod_cast hNp
    exact (show C*(N+1:ℝ) ≤ 2*C*N by nlinarith).trans hh
  have hm' : (∫ w, (fullProjectionCollision ρ P (testWidth N J 0 t sig) w).toReal ∂ξ) ≤ T*R^(-sig) := by
    apply hm.trans
    calc
      _ ≤ R^sig*H⁻¹*R^(Δ+(501+2*(d+1:ℝ))*sig) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
      _ = H⁻¹*R^(Δ+(502+2*(d+1:ℝ))*sig) := by
        calc
          _ = H⁻¹*(R^sig*R^(Δ+(501+2*(d+1:ℝ))*sig)) := by ring
          _ = _ := by rw [←Real.rpow_add hRp]; congr 2; ring
      _ ≤ H⁻¹*R^(Δ+(1000*(d+1:ℝ)-1)*sig) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hR
        have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith
      _ = T*R^(-sig) := by
        dsimp [T]
        rw [mul_assoc,←Real.rpow_add hRp]
        congr 2; ring
  have hi : Integrable (fun w => (fullProjectionCollision ρ P (testWidth N J 0 t sig) w).toReal) ξ := by
    exact projectionCollision_integrable (classConditional ρ P) ξ (testWidth N J 0 t sig)
  have hmark := exceptional_of_mean ξ hi (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    (S:={w | ‖w‖=1}) hsphere hT (show 0 ≤ R^(-sig) by positivity) hm'
  have hscale : (2:ℝ)^(-((t:ℝ)-p))=H⁻¹ := by
    dsimp [H]
    rw [←Nat.cast_sub hpt,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  have he : descriptorGood ρ m N sig (1000*(d+1:ℝ)) J 0 P (.projection p t) =
      {w | ‖w‖=1 ∧ (fullProjectionCollision ρ P (testWidth N J 0 t sig) w).toReal ≤ T} := by
    ext w
    simp only [descriptorGood,mem_ofPred_eq,hscale]
    exact and_congr_right (fun _ => ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hT.le)
  simpa only [he,R,Set.mem_ofPred_eq] using hmark
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
