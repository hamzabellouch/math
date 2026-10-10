import Mathlib
import OAI.Probability.SKFluctuations.InvariantPropagation

namespace OAI

/-! Centered Monotone Integral. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Scalar
open MeasureTheory Filter Set
open scoped Topology

theorem halfLine_integral_pos {f : ℝ → ℝ} (hc : Continuous f)
    (hi : IntegrableOn f (Ioi 0)) (hn : ∀ x, 0 < x → 0 ≤ f x)
    {x : ℝ} (hx : 0 < x) (hp : 0 < f x) : 0 < ∫ y in Ioi 0, f y := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; exact hn y hy) hi).mpr
  have ho : IsOpen ({y | 0 < f y} ∩ Ioi 0) := (isOpen_lt continuous_const hc).inter isOpen_Ioi
  apply (ho.measure_pos volume ⟨x,hp,hx⟩).trans_le
  apply measure_mono
  intro y hy
  exact ⟨ne_of_gt hy.1,hy.2⟩

theorem onePeak_nonneg {g w L : ℝ → ℝ}
    (hc : ContinuousOn g (Ici 0)) (hd : ∀ x, 0 < x → HasDerivAt g (w x*L x) x)
    (hw : ∀ x, 0 < x → 0 ≤ w x) (hL : AntitoneOn L (Ioi 0))
    (hzero : g 0 = 0) (htop : Tendsto g atTop (𝓝 0)) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g x := by
  rcases hx.eq_or_lt with rfl|hx
  · exact hzero.ge
  by_cases hsign : 0 ≤ L x
  · have hm : MonotoneOn g (Icc 0 x) := monotoneOn_of_deriv_nonneg (convex_Icc ..)
      (hc.mono (Icc_subset_Ici_self)) (by
        intro y hy
        rw [interior_Icc] at hy
        exact (hd y hy.1).differentiableAt.differentiableWithinAt) (by
        intro y hy
        rw [interior_Icc] at hy
        rw [(hd y hy.1).deriv]
        exact mul_nonneg (hw y hy.1) (hsign.trans (hL hy.1 hx hy.2.le)))
    simpa only [hzero] using hm ⟨le_rfl,hx.le⟩ ⟨hx.le,le_rfl⟩ hx.le
  · have hm : AntitoneOn g (Ici x) := antitoneOn_of_deriv_nonpos (convex_Ici _)
      (hc.mono (Ici_subset_Ici.mpr hx.le)) (by
        intro y hy
        rw [interior_Ici] at hy
        exact (hd y (hx.trans hy)).differentiableAt.differentiableWithinAt) (by
        intro y hy
        rw [interior_Ici] at hy
        rw [(hd y (hx.trans hy)).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (hw y (hx.trans hy))
          ((hL hx (hx.trans hy) hy.le).trans (lt_of_not_ge hsign).le))
    apply le_of_tendsto htop
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hm (show x ∈ Ici x from Set.mem_Ici.mpr (le_refl x)) hy hy

theorem centered_weight_exists_zero {w φ : ℝ → ℝ}
    (hwc : Continuous w) (hφc : Continuous φ) (hw : ∀ x, 0 < x → 0 < w x)
    (hφ0 : φ 0 < 0) (hi : IntegrableOn (fun x => w x*φ x) (Ioi 0))
    (hcenter : ∫ x in Ioi 0, w x*φ x = 0) : ∃ a, 0 < a ∧ φ a = 0 := by
  have hex : ∃ b, 0 < b ∧ 0 < φ b := by
    by_contra! h
    have hn : ∀ x, 0 < x → 0 ≤ -(w x*φ x) := fun x hx =>
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hw x hx).le (h x hx))
    have he : ∀ᶠ x in nhdsWithin 0 (Ioi 0), φ x < 0 ∧ 0 < x :=
      ((hφc.continuousAt.eventually (Iio_mem_nhds hφ0)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨x,hxφ,hx⟩ := he.exists
    have hp := halfLine_integral_pos ((hwc.mul hφc).neg) hi.neg hn hx
      (neg_pos.mpr (mul_neg_of_pos_of_neg (hw x hx) hxφ))
    change 0 < ∫ y in Ioi 0, -(w y*φ y) at hp
    rw [integral_neg,hcenter,neg_zero] at hp
    exact (lt_irrefl 0 hp)
  obtain ⟨b,hb,hφb⟩ := hex
  obtain ⟨a,ha,he⟩ := intermediate_value_Icc hb.le hφc.continuousOn ⟨hφ0.le,hφb.le⟩
  refine ⟨a,lt_of_le_of_ne ha.1 ?_,he⟩
  intro h
  subst a
  exact hφ0.ne he

theorem centered_weight_mul_nonneg {w φ v : ℝ → ℝ}
    (hw : ∀ x, 0 < x → 0 ≤ w x) (hφ : MonotoneOn φ (Ici 0))
    (hv : MonotoneOn v (Ici 0)) {a : ℝ} (ha : 0 ≤ a) (hφa : φ a = 0)
    (hi : IntegrableOn (fun x => w x*φ x) (Ioi 0))
    (hiv : IntegrableOn (fun x => w x*φ x*v x) (Ioi 0))
    (hcenter : ∫ x in Ioi 0, w x*φ x = 0) :
    0 ≤ ∫ x in Ioi 0, w x*φ x*v x := by
  have hn : ∀ x, 0 < x → 0 ≤ w x*φ x*(v x-v a) := by
    intro x hx
    rcases le_total x a with hxa|hax
    · have h1 : φ x ≤ 0 := by simpa only [hφa] using hφ hx.le ha hxa
      have h2 : v x-v a ≤ 0 := sub_nonpos.mpr (hv hx.le ha hxa)
      exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hw x hx) h1) h2
    · have h1 : 0 ≤ φ x := by simpa only [hφa] using hφ ha hx.le hax
      exact mul_nonneg (mul_nonneg (hw x hx) h1) (sub_nonneg.mpr (hv ha hx.le hax))
  have hh := setIntegral_nonneg (μ := volume) measurableSet_Ioi (fun x hx => hn x hx)
  simp_rw [mul_sub] at hh
  rw [integral_sub hiv (hi.mul_const (v a)),integral_mul_const,hcenter,zero_mul,sub_zero] at hh
  exact hh

theorem centered_weight_mul_pos {w φ v : ℝ → ℝ}
    (hwc : Continuous w) (hφc : Continuous φ) (hvc : Continuous v)
    (hw : ∀ x, 0 < x → 0 < w x) (hφ : StrictMonoOn φ (Ici 0))
    (hv : StrictMonoOn v (Ici 0)) {a : ℝ} (ha : 0 ≤ a) (hφa : φ a = 0)
    (hi : IntegrableOn (fun x => w x*φ x) (Ioi 0))
    (hiv : IntegrableOn (fun x => w x*φ x*v x) (Ioi 0))
    (hcenter : ∫ x in Ioi 0, w x*φ x = 0) :
    0 < ∫ x in Ioi 0, w x*φ x*v x := by
  have hn : ∀ x, 0 < x → 0 ≤ w x*φ x*(v x-v a) := by
    intro x hx
    rcases le_total x a with hxa|hax
    · have h1 : φ x ≤ 0 := by simpa only [hφa] using hφ.monotoneOn hx.le ha hxa
      exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hw x hx).le h1)
        (sub_nonpos.mpr (hv.monotoneOn hx.le ha hxa))
    · have h1 : 0 ≤ φ x := by simpa only [hφa] using hφ.monotoneOn ha hx.le hax
      exact mul_nonneg (mul_nonneg (hw x hx).le h1) (sub_nonneg.mpr (hv.monotoneOn ha hx.le hax))
  have hint : IntegrableOn (fun x => w x*φ x*(v x-v a)) (Ioi 0) := by
    convert hiv.sub (hi.mul_const (v a)) using 1
    ext x
    simp only [Pi.sub_apply,mul_sub]
  have hx : 0 < a+1 := by linarith
  have hp1 : 0 < φ (a+1) := by simpa only [hφa] using hφ ha hx.le (by linarith : a < a+1)
  have hp2 : 0 < v (a+1)-v a := sub_pos.mpr (hv ha hx.le (by linarith))
  have hh := halfLine_integral_pos ((hwc.mul hφc).mul (hvc.sub continuous_const))
    hint hn hx (mul_pos (mul_pos (hw _ hx) hp1) hp2)
  change 0 < ∫ y in Ioi 0, w y*φ y*(v y-v a) at hh
  simp_rw [mul_sub] at hh
  rw [integral_sub hiv (hi.mul_const (v a)),integral_mul_const,hcenter,zero_mul,sub_zero] at hh
  exact hh

end SKFluctuations.Scalar

 

 
namespace SKFluctuations.Scalar
open Set Filter MeasureTheory
open scoped Topology

structure PhysicalSlopeSlice (m : ℝ) where
  B : ℝ → ℝ
  C : ℝ → ℝ
  z : ℝ → ℝ
  κ : ℝ → ℝ
  lam : ℝ → ℝ
  dB : ∀ x, HasDerivAt B (C x) x
  dC : ∀ x, HasDerivAt C (-2*C x*z x) x
  dz : ∀ x, HasDerivAt z (m*C x+κ x) x
  dκ : ∀ x, HasDerivAt κ (lam x-2*z x*κ x) x
  Cpos : ∀ x, 0 < C x
  κnonneg : ∀ x, 0 ≤ x → 0 ≤ κ x
  lamnonneg : ∀ x, 0 ≤ x → 0 ≤ lam x
  cone : ∀ x, 0 ≤ x → lam x ≤ 3*z x*κ x
  Bzero : B 0 = 0
  zzero : z 0 = 0

namespace PhysicalSlopeSlice
variable {m : ℝ} (S : PhysicalSlopeSlice m)

noncomputable def A (x : ℝ) := S.z x-m*S.B x
noncomputable def Φ (x : ℝ) := 2*(S.z x)^2-m*S.C x
noncomputable def L (s x : ℝ) := S.κ x-S.z x*(x/s+S.A x+S.z x)
noncomputable def R₀ (x : ℝ) := 2*S.κ x-m*S.C x/2-(S.z x)^2/2
noncomputable def R₁ (s x : ℝ) := S.A x*x/s+(S.A x)^2/2
noncomputable def G (x : ℝ) := 2*S.z x*(3*S.z x*S.κ x-S.lam x)

theorem continuous_B : Continuous S.B := continuous_iff_continuousAt.mpr fun x => (S.dB x).continuousAt
theorem continuous_C : Continuous S.C := continuous_iff_continuousAt.mpr fun x => (S.dC x).continuousAt
theorem continuous_z : Continuous S.z := continuous_iff_continuousAt.mpr fun x => (S.dz x).continuousAt
theorem continuous_κ : Continuous S.κ := continuous_iff_continuousAt.mpr fun x => (S.dκ x).continuousAt

theorem dA (x : ℝ) : HasDerivAt S.A (S.κ x) x := by
  convert (S.dz x).sub ((S.dB x).const_mul m) using 1 <;> first | rfl | ring

theorem continuous_A : Continuous S.A := continuous_iff_continuousAt.mpr fun x => (S.dA x).continuousAt

theorem A_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ S.A x := by
  have hm : MonotoneOn S.A (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici _)
    S.continuous_A.continuousOn (fun y _ => (S.dA y).differentiableAt.differentiableWithinAt) (by
      intro y hy
      rw [interior_Ici] at hy
      rw [(S.dA y).deriv]
      exact S.κnonneg y hy.le)
  have h := hm (show (0:ℝ) ∈ Ici 0 from Set.mem_Ici.mpr (le_refl 0)) hx hx
  simpa only [A,S.zzero,S.Bzero,mul_zero,sub_zero] using h

theorem z_strictMono (hm : 0 < m) : StrictMonoOn S.z (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) S.continuous_z.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(S.dz x).deriv]
  exact add_pos_of_pos_of_nonneg (mul_pos hm (S.Cpos x)) (S.κnonneg x hx.le)

theorem z_pos (hm : 0 < m) {x : ℝ} (hx : 0 < x) : 0 < S.z x := by
  simpa only [S.zzero] using S.z_strictMono hm (show (0:ℝ) ∈ Ici 0 from Set.mem_Ici.mpr (le_refl 0)) hx.le hx

theorem z_nonneg (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ S.z x := by
  rcases hx.eq_or_lt with rfl|hx
  · exact S.zzero.ge
  · exact (S.z_pos hm hx).le

theorem dΦ (x : ℝ) : HasDerivAt S.Φ (2*S.z x*(2*S.κ x+3*m*S.C x)) x := by
  convert ((S.dz x).pow 2 |>.const_mul 2).sub ((S.dC x).const_mul m) using 1 <;> first | rfl | ring

theorem continuous_Φ : Continuous S.Φ := continuous_iff_continuousAt.mpr fun x => (S.dΦ x).continuousAt

theorem Φ_strictMono (hm : 0 < m) : StrictMonoOn S.Φ (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) S.continuous_Φ.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(S.dΦ x).deriv]
  positivity [S.z_pos hm hx,S.κnonneg x hx.le,S.Cpos x]

theorem Φ_zero_neg (hm : 0 < m) : S.Φ 0 < 0 := by
  dsimp only [Φ]
  rw [S.zzero]
  nlinarith [S.Cpos 0]

theorem dL (s x : ℝ) : HasDerivAt (S.L s)
    (S.lam x-5*S.z x*S.κ x-2*m*S.C x*S.z x-
      (m*S.C x+S.κ x)*(x/s+S.A x)-S.z x/s) x := by
  have h := (S.dκ x).sub ((S.dz x).mul (((hasDerivAt_id x).div_const s |>.add (S.dA x)).add (S.dz x)))
  convert h using 1 <;> first | rfl | (simp only [id_eq,Pi.add_apply]; ring)

theorem L_strictAnti (hm : 0 < m) {s : ℝ} (hs : 0 < s) : StrictAntiOn (S.L s) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
    (continuous_iff_continuousAt.mpr fun x => (S.dL s x).continuousAt).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(S.dL s x).deriv]
  have h1 : 0 ≤ S.z x*S.κ x := mul_nonneg (S.z_pos hm hx).le (S.κnonneg x hx.le)
  have h2 : 0 ≤ 2*m*S.C x*S.z x := by positivity [S.Cpos x,S.z_pos hm hx]
  have h3 : 0 ≤ (m*S.C x+S.κ x)*(x/s+S.A x) := by positivity [S.Cpos x,S.κnonneg x hx.le,S.A_nonneg hx.le]
  have h4 : 0 < S.z x/s := div_pos (S.z_pos hm hx) hs
  nlinarith [S.cone x hx.le]

theorem dR₀ (x : ℝ) : HasDerivAt S.R₀ (2*S.lam x-5*S.z x*S.κ x) x := by
  convert (((S.dκ x).const_mul 2).sub ((S.dC x).const_mul m |>.div_const 2)).sub
    ((S.dz x).pow 2 |>.div_const 2) using 1 <;> first | rfl | ring

theorem dR₁ (s x : ℝ) : HasDerivAt (S.R₁ s)
    (S.κ x*x/s+S.A x/s+S.A x*S.κ x) x := by
  convert ((S.dA x).mul (hasDerivAt_id x) |>.div_const s).add
    ((S.dA x).pow 2 |>.div_const 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)

theorem R₁_monotone {s : ℝ} (hs : 0 < s) : MonotoneOn (S.R₁ s) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (continuous_iff_continuousAt.mpr fun x => (S.dR₁ s x).continuousAt).continuousOn
    (fun x _ => (S.dR₁ s x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  change 0 < x at hx
  rw [(S.dR₁ s x).deriv]
  positivity [S.κnonneg x hx.le,S.A_nonneg hx.le]

theorem weighted_tail_bounds (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    {w F : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-x/s-S.A x-3*S.z x)) x)
    (hF : ∀ x, HasDerivAt F (-w x*S.Φ x) x)
    (hF0 : F 0 = 0) (hFt : Tendsto F atTop (𝓝 0))
    (hwzt : Tendsto (fun x => w x*S.z x) atTop (𝓝 0))
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  constructor
  · exact onePeak_nonneg hFc.continuousOn (by
      intro y _
      simpa only [neg_mul,mul_neg] using hF y) (fun y _ => hw y)
      (S.Φ_strictMono hm |>.monotoneOn.mono Ioi_subset_Ici_self |>.neg) hF0 hFt hx
  · have hd : ∀ y, HasDerivAt (fun y => w y*S.z y-F y) (w y*S.L s y) y := by
      intro y
      convert ((hdw y).mul (S.dz y)).sub (hF y) using 1; first | rfl | (dsimp only [L,Φ]; ring)
    have hh := onePeak_nonneg
      ((continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt).continuousOn)
      (fun y _ => hd y) (fun y _ => hw y)
      (S.L_strictAnti hm hs |>.antitoneOn.mono Ioi_subset_Ici_self)
      (by simp only [S.zzero,mul_zero,hF0,sub_zero]) (by simpa only [sub_zero] using hwzt.sub hFt) hx
    exact sub_nonneg.mp hh

end PhysicalSlopeSlice
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar

noncomputable def physicalSlopeOfJets {m : ℝ} (j : ℕ → ℝ → ℝ)
    (hd : ∀ k x, HasDerivAt (j k) (j (k+1) x) x)
    (hp : ∀ x, 0 < j 2 x) (h1 : j 1 0 = 0) (h3 : j 3 0 = 0)
    (hs : PolynomialSigns m j) : PhysicalSlopeSlice m where
  B := j 1
  C := j 2
  z := fun x => -j 3 x/(2*j 2 x)
  κ := fun x => invariantP m (j 2 x) (j 3 x) (j 4 x)/(j 2 x)^2
  lam := fun x => invariantQ (j 2 x) (j 3 x) (j 4 x) (j 5 x)/(j 2 x)^3
  dB := hd 1
  dC := by
    intro x
    convert hd 2 x using 1
    field_simp [(hp x).ne']
  dz := by
    intro x
    apply ((hd 3 x).neg.div ((hd 2 x).const_mul 2) (mul_ne_zero (by norm_num) (hp x).ne')).congr_deriv
    dsimp only [invariantP,Pi.neg_apply]
    norm_num only [Nat.reduceAdd]
    field_simp [(hp x).ne']; ring
  dκ := by
    intro x
    apply ((hasDerivAt_invariantP m (hd 2 x) (hd 3 x) (hd 4 x)).div ((hd 2 x).pow 2)
      (pow_ne_zero 2 (hp x).ne')).congr_deriv
    dsimp only [invariantP,invariantQ,invariantPD,Pi.pow_apply]
    norm_num only [Nat.reduceAdd,Nat.reduceSub,Nat.cast_ofNat,pow_one]
    field_simp [(hp x).ne']; ring
  Cpos := hp
  κnonneg := fun x _ => div_nonneg (hs.P x) (sq_nonneg _)
  lamnonneg := fun x hx => div_nonneg (hs.Q x hx) (pow_nonneg (hp x).le 3)
  cone := by
    intro x hx
    have hR := hs.R x hx
    dsimp only [invariantR] at hR
    apply (div_le_iff₀ (pow_pos (hp x) 3)).mpr
    have he : 3*(-j 3 x/(2*j 2 x))*(invariantP m (j 2 x) (j 3 x) (j 4 x)/(j 2 x)^2)*(j 2 x)^3 =
        -3*j 3 x*invariantP m (j 2 x) (j 3 x) (j 4 x)/2 := by
      field_simp [(hp x).ne']
    rw [he]
    linarith
  Bzero := h1
  zzero := by rw [h3,neg_zero,zero_div]

namespace PhysicalSlopeSlice

 
theorem dC₂Φ {m : ℝ} (S : PhysicalSlopeSlice m) (x : ℝ) :
    HasDerivAt (fun x => (S.C x)^2*S.Φ x)
      ((S.C x)^2*(2*S.z x*(2*S.κ x+3*m*S.C x)-4*S.z x*S.Φ x)) x := by
  convert ((S.dC x).pow 2).mul (S.dΦ x) using 1; first | rfl | (simp only [Pi.pow_apply]; ring)

end PhysicalSlopeSlice
end SKFluctuations.Scalar

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
variable {m : ℝ} (S : PhysicalSlopeSlice m)

noncomputable def thirdTest (x : ℝ) : ℝ :=
  (4*(S.z x)^2-2*m*S.C x-2*S.κ x)^2-48*m*S.C x*(S.z x)^2+6*m^2*(S.C x)^2

noncomputable def fluxCore (s x : ℝ) : ℝ :=
  S.z x*(2*S.κ x+3*m*S.C x)+(x/(2*s)-3*S.z x/2+S.A x/2)*S.Φ x

noncomputable def rootIntegrand (s x : ℝ) : ℝ :=
  (x^2/(2*s^2)+S.R₁ s x+S.R₀ x-1/(2*s))*S.Φ x+S.G x

theorem dfluxCore (s x : ℝ) : HasDerivAt (S.fluxCore s)
    (S.thirdTest x/2-S.rootIntegrand s x-(-x/s-S.A x-3*S.z x)*S.fluxCore s x) x := by
  have hd := ((S.dz x).mul (((S.dκ x).const_mul 2).add ((S.dC x).const_mul (3*m)))).add
    (((((hasDerivAt_id x).div_const (2*s)).sub ((S.dz x).const_mul 3 |>.div_const 2)).add
      ((S.dA x).div_const 2)).mul (S.dΦ x))
  apply hd.congr_deriv
  dsimp only [thirdTest,rootIntegrand,fluxCore,R₀,R₁,G,Φ,Pi.add_apply,Pi.sub_apply,id_eq]
  ring

theorem dweightedFlux {w : ℝ → ℝ} {s : ℝ}
    (hdw : ∀ x, HasDerivAt w (w x*(-x/s-S.A x-3*S.z x)) x) (x : ℝ) :
    HasDerivAt (fun x => w x*S.fluxCore s x)
      (w x*(S.thirdTest x/2-S.rootIntegrand s x)) x := by
  convert (hdw x).mul (S.dfluxCore s x) using 1; first | rfl | ring

theorem fluxCore_zero (s : ℝ) : S.fluxCore s 0 = 0 := by
  simp only [fluxCore,S.zzero,A,S.Bzero,mul_zero,sub_zero,zero_div,add_zero,zero_mul]

theorem dweightedPrimitive {w F : ℝ → ℝ}
    (hdF : ∀ x, HasDerivAt F (-w x*S.Φ x) x) (x : ℝ) :
    HasDerivAt (fun x => F x*S.R₀ x)
      (-w x*S.Φ x*S.R₀ x+F x*(2*S.lam x-5*S.z x*S.κ x)) x :=
  (hdF x).mul (S.dR₀ x)

theorem correction_nonneg {w F : ℝ → ℝ} (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x)
    (hF : 0 ≤ F x) (hFz : F x ≤ w x*S.z x) :
    0 ≤ F x*(2*S.lam x-5*S.z x*S.κ x)+w x*S.G x := by
  have hκ := S.κnonneg x hx
  have hz := S.z_nonneg hm hx
  have hcone := S.cone x hx
  have hlam := S.lamnonneg x hx
  have he : F x*(2*S.lam x-5*S.z x*S.κ x)+w x*S.G x =
      2*(3*S.z x*S.κ x-S.lam x)*(w x*S.z x-F x)+S.z x*S.κ x*F x := by
    dsimp only [G]; ring
  rw [he]
  positivity

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar.PhysicalSlopeSlice
open Set Filter MeasureTheory
open scoped Topology
variable {m : ℝ} (S : PhysicalSlopeSlice m)

noncomputable def rootPrimitive (w : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(∫ y in (0:ℝ)..x, w y*S.Φ y)

theorem rootPrimitive_zero (w : ℝ → ℝ) : S.rootPrimitive w 0 = 0 := by
  simp only [rootPrimitive,intervalIntegral.integral_same,neg_zero]

theorem rootPrimitive_hasDerivAt {w : ℝ → ℝ} (hw : Continuous w) (x : ℝ) :
    HasDerivAt (S.rootPrimitive w) (-w x*S.Φ x) x := by
  change HasDerivAt (fun u => -(∫ y in (0:ℝ)..u, w y*S.Φ y)) (-w x*S.Φ x) x
  have hc : Continuous (fun y => w y*S.Φ y) := hw.mul S.continuous_Φ
  have hd : HasDerivAt (fun u => ∫ y in (0:ℝ)..u, w y*S.Φ y) (w x*S.Φ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [neg_one_mul,neg_mul,one_mul] using hd.const_mul (-1)

theorem rootPrimitive_tendsto {w : ℝ → ℝ}
    (hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0))
    (hcenter : ∫ x in Ioi 0, w x*S.Φ x = 0) : Tendsto (S.rootPrimitive w) atTop (𝓝 0) := by
  change Tendsto (fun x => -(∫ y in (0:ℝ)..x, w y*S.Φ y)) atTop (𝓝 0)
  simpa only [hcenter,neg_zero,id_eq] using
    (intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id).neg

theorem rootIntegral_pos {w : ℝ → ℝ} (hm : 0 < m) {s : ℝ} (hs : 0 < s)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hdw : ∀ x, HasDerivAt w (w x*(-x/s-S.A x-3*S.z x)) x)
    (hi : IntegrableOn (fun x => w x*S.Φ x) (Ioi 0))
    (hi₂ : IntegrableOn (fun x => w x*S.Φ x*x^2) (Ioi 0))
    (hi₁ : IntegrableOn (fun x => w x*S.Φ x*S.R₁ s x) (Ioi 0))
    (hi₀ : IntegrableOn (fun x => w x*S.Φ x*S.R₀ x) (Ioi 0))
    (hiG : IntegrableOn (fun x => w x*S.G x) (Ioi 0))
    (hiT : IntegrableOn (fun x => w x*S.thirdTest x) (Ioi 0))
    (hiF : IntegrableOn (fun x => S.rootPrimitive w x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0))
    (htz : Tendsto (fun x => w x*S.z x) atTop (𝓝 0))
    (htF : Tendsto (fun x => S.rootPrimitive w x*S.R₀ x) atTop (𝓝 0))
    (htFlux : Tendsto (fun x => w x*S.fluxCore s x) atTop (𝓝 0))
    (hcenter : ∫ x in Ioi 0, w x*S.Φ x = 0) :
    0 < ∫ x in Ioi 0, w x*S.thirdTest x := by
  let F := S.rootPrimitive w
  have hdF := S.rootPrimitive_hasDerivAt hw
  have hFt := S.rootPrimitive_tendsto hi hcenter
  have hFb (x : ℝ) (hx : 0 ≤ x) : 0 ≤ F x ∧ F x ≤ w x*S.z x :=
    S.weighted_tail_bounds hm hs (fun y => (hwp y).le) hdw hdF
      (S.rootPrimitive_zero w) hFt htz hx
  obtain ⟨a,ha,hφa⟩ := centered_weight_exists_zero hw S.continuous_Φ
    (fun x _ => hwp x) (S.Φ_zero_neg hm) hi hcenter
  have h₂ : 0 < ∫ x in Ioi 0, w x*S.Φ x*x^2 := centered_weight_mul_pos
    hw S.continuous_Φ (continuous_id.pow 2) (fun x _ => hwp x) (S.Φ_strictMono hm)
    (by intro x hx y hy hxy; change 0 ≤ x at hx; change 0 ≤ y at hy; nlinarith)
    ha.le hφa hi hi₂ hcenter
  have h₁ : 0 ≤ ∫ x in Ioi 0, w x*S.Φ x*S.R₁ s x := centered_weight_mul_nonneg
    (fun x _ => (hwp x).le) (S.Φ_strictMono hm).monotoneOn (S.R₁_monotone hs)
    ha.le hφa hi hi₁ hcenter
  have hFi : IntegrableOn (fun x => -w x*S.Φ x*S.R₀ x+F x*(2*S.lam x-5*S.z x*S.κ x)) (Ioi 0) := by
    apply (hi₀.neg.add hiF).congr
    filter_upwards [] with x
    simp only [Pi.add_apply,Pi.neg_apply,neg_mul,F]
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedPrimitive hdF x) hFi htF
  simp only [S.rootPrimitive_zero w,zero_mul,sub_zero] at hIBP
  have hIBP' : (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x) =
      ∫ x in Ioi 0, F x*(2*S.lam x-5*S.z x*S.κ x) := by
    simp_rw [neg_mul] at hIBP
    have hn : IntegrableOn (fun x => -(w x*S.Φ x*S.R₀ x)) (Ioi 0) := hi₀.neg
    rw [integral_add hn hiF,integral_neg] at hIBP
    linarith
  have hcor : 0 ≤ (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [hIBP',← integral_add hiF hiG]
    exact setIntegral_nonneg measurableSet_Ioi (fun x hx =>
      S.correction_nonneg hm hx.le (hFb x hx.le).1 (hFb x hx.le).2)
  have he : (fun x => w x*S.rootIntegrand s x) = fun x =>
      ((1/(2*s^2))*(w x*S.Φ x*x^2)+w x*S.Φ x*S.R₁ s x+w x*S.Φ x*S.R₀ x)-
        (1/(2*s))*(w x*S.Φ x)+w x*S.G x := by
    funext x; dsimp only [rootIntegrand]; ring
  have hi21 : IntegrableOn (fun x => (1/(2*s^2))*(w x*S.Φ x*x^2)+w x*S.Φ x*S.R₁ s x) (Ioi 0) :=
    (hi₂.const_mul _).add hi₁
  have hi210 : IntegrableOn (fun x => (1/(2*s^2))*(w x*S.Φ x*x^2)+w x*S.Φ x*S.R₁ s x+w x*S.Φ x*S.R₀ x) (Ioi 0) :=
    hi21.add hi₀
  have hi210c : IntegrableOn (fun x => (1/(2*s^2))*(w x*S.Φ x*x^2)+w x*S.Φ x*S.R₁ s x+w x*S.Φ x*S.R₀ x-
      (1/(2*s))*(w x*S.Φ x)) (Ioi 0) := hi210.sub (hi.const_mul _)
  have hroot : IntegrableOn (fun x => w x*S.rootIntegrand s x) (Ioi 0) := by
    rw [he]
    exact hi210c.add hiG
  have heq : (∫ x in Ioi 0, w x*S.rootIntegrand s x) =
      (1/(2*s^2))*(∫ x in Ioi 0, w x*S.Φ x*x^2)+
      (∫ x in Ioi 0, w x*S.Φ x*S.R₁ s x)+
      (∫ x in Ioi 0, w x*S.Φ x*S.R₀ x)-
      (1/(2*s))*(∫ x in Ioi 0, w x*S.Φ x)+(∫ x in Ioi 0, w x*S.G x) := by
    rw [he,integral_add hi210c hiG,integral_sub hi210 (hi.const_mul _),
      integral_add hi21 hi₀,integral_add (hi₂.const_mul _) hi₁,
      integral_const_mul,integral_const_mul]
  have hrpos : 0 < ∫ x in Ioi 0, w x*S.rootIntegrand s x := by
    rw [heq,hcenter,mul_zero,sub_zero]
    have hp : 0 < (1/(2*s^2))*(∫ x in Ioi 0, w x*S.Φ x*x^2) := by positivity
    linarith
  have hfluxi : IntegrableOn (fun x => w x*(S.thirdTest x/2-S.rootIntegrand s x)) (Ioi 0) := by
    apply ((hiT.mul_const (1/2)).sub hroot).congr
    filter_upwards [] with x
    simp only [Pi.sub_apply]; ring
  have hfint := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => S.dweightedFlux hdw x) hfluxi htFlux
  simp only [S.fluxCore_zero,mul_zero,sub_zero] at hfint
  have he : (fun x => w x*(S.thirdTest x/2-S.rootIntegrand s x)) =
      fun x => (w x*S.thirdTest x)*(1/2)-w x*S.rootIntegrand s x := by funext x; ring
  rw [he,integral_sub (hiT.mul_const _) hroot,integral_mul_const] at hfint
  linarith

end SKFluctuations.Scalar.PhysicalSlopeSlice

 

 

namespace SKFluctuations.Scalar
open MeasureTheory Filter Set
open scoped Topology
open Hierarchy

def PolyBounded (f : ℝ → ℝ) : Prop := ∃ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |f x| ≤ K*(1+|x|)^n

namespace PolyBounded

theorem of_absBounded {f : ℝ → ℝ} (hf : AbsBounded f) : PolyBounded f := by
  obtain ⟨K,hK,h⟩ := hf
  exact ⟨0,K,hK,fun x => by simpa only [pow_zero,mul_one] using h x⟩

theorem const (c : ℝ) : PolyBounded (fun _ : ℝ => c) := of_absBounded ⟨|c|,abs_nonneg _,fun _ => le_rfl⟩

theorem id : PolyBounded (fun x : ℝ => x) := by
  refine ⟨1,1,by norm_num,fun x => ?_⟩
  simp only [pow_one,one_mul]
  linarith

theorem add {f g : ℝ → ℝ} (hf : PolyBounded f) (hg : PolyBounded g) : PolyBounded (fun x => f x+g x) := by
  obtain ⟨n,K,hK,hf⟩ := hf
  obtain ⟨p,L,hL,hg⟩ := hg
  refine ⟨n+p,K+L,add_nonneg hK hL,fun x => ?_⟩
  have hbase : 1 ≤ 1+|x| := by linarith [abs_nonneg x]
  have hn : (1+|x|)^n ≤ (1+|x|)^(n+p) := pow_le_pow_right₀ hbase (Nat.le_add_right n p)
  have hp : (1+|x|)^p ≤ (1+|x|)^(n+p) := pow_le_pow_right₀ hbase (Nat.le_add_left p n)
  calc
    |f x+g x| ≤ |f x|+|g x| := abs_add_le _ _
    _ ≤ K*(1+|x|)^n+L*(1+|x|)^p := add_le_add (hf x) (hg x)
    _ ≤ K*(1+|x|)^(n+p)+L*(1+|x|)^(n+p) := add_le_add (mul_le_mul_of_nonneg_left hn hK) (mul_le_mul_of_nonneg_left hp hL)
    _ = _ := by ring

theorem neg {f : ℝ → ℝ} (hf : PolyBounded f) : PolyBounded (fun x => -f x) := by
  obtain ⟨n,K,hK,hf⟩ := hf
  exact ⟨n,K,hK,fun x => by simpa only [abs_neg] using hf x⟩

theorem sub {f g : ℝ → ℝ} (hf : PolyBounded f) (hg : PolyBounded g) : PolyBounded (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul {f g : ℝ → ℝ} (hf : PolyBounded f) (hg : PolyBounded g) : PolyBounded (fun x => f x*g x) := by
  obtain ⟨n,K,hK,hf⟩ := hf
  obtain ⟨p,L,hL,hg⟩ := hg
  refine ⟨n+p,K*L,mul_nonneg hK hL,fun x => ?_⟩
  rw [abs_mul]
  calc
    |f x| *|g x| ≤ (K*(1+|x|)^n)*(L*(1+|x|)^p) := mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem const_mul {f : ℝ → ℝ} (hf : PolyBounded f) (c : ℝ) : PolyBounded (fun x => c*f x) := (const c).mul hf

theorem div_const {f : ℝ → ℝ} (hf : PolyBounded f) (c : ℝ) : PolyBounded (fun x => f x/c) := by
  simpa only [div_eq_mul_inv] using hf.mul (const c⁻¹)

theorem pow {f : ℝ → ℝ} (hf : PolyBounded f) (n : ℕ) : PolyBounded (fun x => (f x)^n) := by
  induction n with
  | zero => simpa only [pow_zero] using const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

end PolyBounded

def GaussianDominated (w : ℝ → ℝ) : Prop :=
  ∃ a K : ℝ, 0 < a ∧ 0 ≤ K ∧ ∀ x, |w x| ≤ K*Real.exp (-a*x^2)

theorem gaussian_nat_integrable {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (fun x : ℝ => |x|^n*Real.exp (-a*x^2)) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq ha (s := (n:ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])).norm
  simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using hi

theorem gaussian_nat_tendsto {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun x : ℝ => |x|^n*Real.exp (-a*x^2)) atTop (𝓝 0) := by
  simpa only [Real.rpow_natCast] using
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (n:ℝ)).mono_left atTop_le_cocompact

theorem polynomial_gaussian_majorant (n : ℕ) (x : ℝ) :
    (1+|x|)^n ≤ (2:ℝ)^(n-1)*(1+|x|^n) := by
  simpa only [one_pow] using add_pow_le (show (0:ℝ) ≤ 1 by norm_num) (abs_nonneg x) n

namespace GaussianDominated
variable {w f : ℝ → ℝ}

theorem mul_poly_integrable (hw : GaussianDominated w) (hf : PolyBounded f)
    (hc : AEStronglyMeasurable (fun x => w x*f x) volume) : Integrable (fun x => w x*f x) := by
  obtain ⟨a,K,ha,hK,hw⟩ := hw
  obtain ⟨n,L,hL,hf⟩ := hf
  have hi : Integrable (fun x : ℝ => (K*L*(2:ℝ)^(n-1))*(Real.exp (-a*x^2)+|x|^n*Real.exp (-a*x^2))) :=
    ((integrable_exp_neg_mul_sq ha).add (gaussian_nat_integrable ha n)).const_mul _
  apply hi.mono' hc
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_mul]
  calc
    |w x| *|f x| ≤ (K*Real.exp (-a*x^2))*(L*(1+|x|)^n) :=
      mul_le_mul (hw x) (hf x) (abs_nonneg _) (by positivity)
    _ ≤ (K*Real.exp (-a*x^2))*(L*((2:ℝ)^(n-1)*(1+|x|^n))) := by
      gcongr
      exact polynomial_gaussian_majorant n x
    _ = _ := by ring

theorem mul_poly_tendsto (hw : GaussianDominated w) (hf : PolyBounded f) :
    Tendsto (fun x => w x*f x) atTop (𝓝 0) := by
  obtain ⟨a,K,ha,hK,hw⟩ := hw
  obtain ⟨n,L,hL,hf⟩ := hf
  have ht : Tendsto (fun x : ℝ => (K*L*(2:ℝ)^(n-1))*(Real.exp (-a*x^2)+|x|^n*Real.exp (-a*x^2))) atTop (𝓝 0) := by
    have h0 := gaussian_nat_tendsto ha 0
    simp only [pow_zero,one_mul] at h0
    simpa only [zero_add,mul_zero] using (h0.add (gaussian_nat_tendsto ha n)).const_mul (K*L*(2:ℝ)^(n-1))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro x
  rw [Real.norm_eq_abs,abs_mul]
  calc
    |w x| *|f x| ≤ (K*Real.exp (-a*x^2))*(L*(1+|x|)^n) :=
      mul_le_mul (hw x) (hf x) (abs_nonneg _) (by positivity)
    _ ≤ (K*Real.exp (-a*x^2))*(L*((2:ℝ)^(n-1)*(1+|x|^n))) := by
      gcongr
      exact polynomial_gaussian_majorant n x
    _ = _ := by ring

end GaussianDominated
end SKFluctuations.Scalar

end

end OAI
