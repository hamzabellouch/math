import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialLocalContinuity
import Mathlib.Topology.MetricSpace.Algebra

namespace OAI

/-! The C¹ limit solves the free amplitude equation wherever it stays strictly below one. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_inner_limit_free_equation_on (R : ℝ) (P : ℕ → RadialInnerData)
    (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop)
    (c b : ℝ) (hc : c ∈ Icc (599/100 : ℝ) 6)
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 c))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hTA : TendstoUniformlyOn H A atTop (Icc 0 R))
    (hTD : TendstoUniformlyOn (fun n => deriv (H n)) D atTop (Icc 0 R))
    (U : Set ℝ) (hU : IsOpen U) (hUR : U ⊆ Ioo 0 R)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hqA : ∀ r ∈ U, A r ≤ q) :
    ∀ r ∈ U, HasDerivAt A (D r) r ∧ HasDerivAt D
      (-11/r*D r-radialAmplitudePotential c b A r*A r) r := by
  have hUC : U ⊆ Icc 0 R := hUR.trans Ioo_subset_Icc_self
  have hHI : ∀ n r, r ∈ Icc 0 R → H n r ∈ Icc (999/1000 : ℝ) 1 := by
    intro n r hr
    exact ⟨(P n).lo_lower.trans ((hH n).2.2.2.2.1 r hr).1.1,
      ((hH n).2.2.2.2.1 r hr).1.2⟩
  have hP : TendstoUniformlyOn (fun n r => (H n r)^((P n).p-1)) (fun _ => 0) atTop U :=
    radial_pressure_uniform_decay (fun n => (P n).p) hp H A
      (fun n r hr => le_trans (by norm_num) (hHI n r (hUC hr)).1)
      (hTA.mono hUC) q hq0 hq1 hqA
  let V := radialAmplitudePotential c b A
  let Vn := fun n => radialAmplitudePotential (P n).c (P n).b (H n)
  have hV : TendstoUniformlyOn Vn V atTop (Icc 0 R) :=
    radialAmplitudePotential_uniform_convergence R (by simpa only [hR 0] using (P 0).hR2)
      (fun n => (P n).c) (fun n => (P n).b) c b (fun n => (P n).hc) hc hcT hbT
      H A (fun n => (hH n).1.continuous) hA hHI hAI hTA
  have hVc : ContinuousOn V U :=
    (continuousOn_radialAmplitudePotential c b R A hA
      (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI r hr).1))).mono hUC
  have hC : ContinuousOn (fun r : ℝ => 11/r) U :=
    continuousOn_const.div continuousOn_id (fun r hr => (hUR hr).1.ne')
  let Fn := fun n r => ((H n r)^((P n).p-1)-Vn n r)*H n r-(11/r)*deriv (H n) r
  have hFT : TendstoLocallyUniformlyOn Fn (fun r => -V r*A r-(11/r)*D r) atTop U := by
    have hPV := hP.tendstoLocallyUniformlyOn.sub (hV.mono hUC).tendstoLocallyUniformlyOn
    have hPA := hPV.mul₀ (hTA.mono hUC).tendstoLocallyUniformlyOn
      (continuousOn_const.sub hVc) hA.continuousOn
    have hCt : TendstoUniformlyOn (fun _ : ℕ => fun r : ℝ => 11/r)
        (fun r : ℝ => 11/r) atTop U := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
    have hCD := hCt.tendstoLocallyUniformlyOn.mul₀
        (hTD.mono hUC).tendstoLocallyUniformlyOn hC hD.continuousOn
    have ht := hPA.sub hCD
    change TendstoLocallyUniformlyOn Fn (fun r => (0-V r)*A r-(11/r)*D r) atTop U at ht
    simpa only [zero_sub] using ht
  have hFn : ∀ n r, r ∈ U → HasDerivAt (deriv (H n)) (Fn n r) r := by
    intro n r hr
    have hd := ((hH n).2.1 r (hUR hr)).hasDerivAt
    have he := (hH n).2.2.2.2.2 r (hUR hr)
    have hp1 : 1 ≤ (P n).p := by have := (P n).hp; omega
    have hpw : (H n r)^((P n).p)=(H n r)^((P n).p-1)*H n r := by
      rw [← pow_succ]
      congr 1
      omega
    apply hd.congr_deriv
    dsimp [Fn,Vn]
    rw [hpw] at he
    linarith
  intro r hr
  constructor
  · exact hasDerivAt_of_tendstoUniformlyOn hU (hTD.mono hUC)
      (Eventually.of_forall (fun n r _ => ((hH n).1 r).hasDerivAt))
      (fun r hr => hTA.tendsto_at (hUC hr)) hr
  · have hd := hasDerivAt_of_tendstoLocallyUniformlyOn hU hFT
      (Eventually.of_forall hFn) (fun r hr => hTD.tendsto_at (hUC hr)) hr
    convert! hd using 1
    ring

/-- No pressure remains at any interior point of the limiting nonunit region. -/
theorem radial_inner_limit_free_equation (R : ℝ) (P : ℕ → RadialInnerData)
    (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop)
    (c b : ℝ) (hc : c ∈ Icc (599/100 : ℝ) 6)
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 c))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hTA : TendstoUniformlyOn H A atTop (Icc 0 R))
    (hTD : TendstoUniformlyOn (fun n => deriv (H n)) D atTop (Icc 0 R)) :
    ∀ r ∈ Ioo 0 R, A r < 1 → HasDerivAt A (D r) r ∧ HasDerivAt D
      (-11/r*D r-radialAmplitudePotential c b A r*A r) r := by
  intro r hr hAr
  let q := (A r+1)/2
  let U := Ioo 0 R ∩ {t | A t < q}
  have hq0 : 0 ≤ q := by
    have h := (hAI r ⟨hr.1.le,hr.2.le⟩).1
    dsimp [q]
    linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hU : IsOpen U := isOpen_Ioo.inter (hA.isOpen_preimage _ isOpen_Iio)
  have hru : r ∈ U := ⟨hr,by dsimp [q]; linarith⟩
  exact radial_inner_limit_free_equation_on R P hR H hH hp c b hc hcT hbT A D hA hD hAI hTA hTD
    U hU (fun _ ht => ht.1) q hq0 hq1 (fun _ ht => ht.2.le) r hru

end DefocusingNLS

end OAI
