import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadialRestart

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExactSLEBarrier
variable {a : ℝ} {T : ℝ≥0} {y j q : ℝ → ℝ}

lemma Evolution.logHeight_add_deriv (h : Evolution a T y j q) {t : ℝ}
    (ht : t ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun t => Real.log (y t)+j t)
      (-2*a*(q t-(y t)^2)/(q t)^2) (Icc 0 (T : ℝ)) t := by
  convert (h.logHeight_deriv ht).add (h.jd t ht) using 1; try rfl
  field_simp [(h.qp t ht).ne']
  ring

lemma Evolution.logHeight_add_le (h : Evolution a T y j q) (ha : 0≤a)
    (hq : ∀ u∈Icc 0 (T : ℝ), (y u)^2≤q u)
    (t : ℝ) (ht : t∈Icc 0 (T : ℝ)) :
    Real.log (y t)+j t≤Real.log (y 0)+j 0 := by
  have hc : ContinuousOn (fun t => Real.log (y t)+j t) (Icc 0 (T : ℝ)) :=
    (h.yc.log (fun u hu => (h.yp u hu).ne')).add h.jc
  have hm : AntitoneOn (fun t => Real.log (y t)+j t) (Icc 0 (T : ℝ)) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (T : ℝ)) hc
      (fun u hu => (h.logHeight_add_deriv (interior_subset hu)).mono interior_subset)
      (fun u hu => div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith)
          (sub_nonneg.mpr (hq u (interior_subset hu)))) (sq_nonneg _))
  exact hm ⟨le_rfl,T.coe_nonneg⟩ ht ht.1

lemma Evolution.height_sq_le_radius (h : Evolution a T y j q) (ha : 0≤a)
    (hq : ∀ u∈Icc 0 (T : ℝ), (y u)^2≤q u) (hj0 : j 0=0)
    (t : ℝ) (ht : t∈Icc 0 (T : ℝ)) :
    (y t)^2≤y 0*(y t*Real.exp (-j t)) := by
  have hl := h.logHeight_add_le ha hq t ht
  rw [hj0,add_zero] at hl
  have he : y t≤y 0*Real.exp (-j t) := by
    have hh := Real.exp_le_exp.mpr (show Real.log (y t)≤Real.log (y 0)+ -j t by linarith)
    simpa only [Real.exp_add,Real.exp_log (h.yp t ht),
      Real.exp_log (h.yp 0 ⟨le_rfl,T.coe_nonneg⟩)] using hh
  have hh := mul_le_mul_of_nonneg_left he (h.yp t ht).le
  nlinarith only [hh]

lemma Evolution.height_sq_lower (h : Evolution a T y j q) (ha : 0≤a)
    (hq : ∀ u∈Icc 0 (T : ℝ), (y u)^2≤q u)
    (t : ℝ) (ht : t∈Icc 0 (T : ℝ)) :
    (y 0)^2≤(y t)^2+2*a*t := by
  let F : ℝ→ℝ := fun u => (y u)^2+2*a*u
  have hc : ContinuousOn F (Icc 0 (T : ℝ)) :=
    (h.yc.pow 2).add (continuousOn_const.mul continuousOn_id)
  have hd (u : ℝ) (hu : u∈Icc 0 (T : ℝ)) :
      HasDerivWithinAt F (2*a*(1-(y u)^2/q u)) (Icc 0 (T : ℝ)) u := by
    convert ((h.yd u hu).pow 2).add ((hasDerivWithinAt_id u _).const_mul (2*a)) using 1 <;> try rfl
    simp only [Nat.reduceSub,pow_one,Nat.cast_ofNat]
    ring
  have hm : MonotoneOn F (Icc 0 (T : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (T : ℝ)) hc
      (fun u hu => (hd u (interior_subset hu)).mono interior_subset)
      (fun u hu => mul_nonneg (by positivity) (sub_nonneg.mpr
        ((div_le_one (h.qp u (interior_subset hu))).mpr (hq u (interior_subset hu)))))
  simpa only [F,mul_zero,add_zero] using hm ⟨le_rfl,T.coe_nonneg⟩ ht ht.1

end ExactSLEBarrier
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator

 

lemma actualState_evolution (a : ℝ) (b : ExactSLEGenerator.Driver) (z : UpperPlane)
    (T : ℝ≥0) (hT : alive a b.1 T z.1) :
    ExactSLEBarrier.Evolution a T
      (fun u => Y (actualState a b.1 u.toNNReal z.1))
      (fun u => J (actualState a b.1 u.toNNReal z.1))
      (fun u => Q (actualState a b.1 u.toNNReal z.1)) := by
  obtain ⟨n,hn⟩ := (exhaustionStop_eventually a z b T hT).exists
  let ε := exhaustionHeight z n
  let V := localState a ε (exhaustionHeight_pos z n) z.1
  have hsafe (u : ℝ≥0) (hu : u≤T) : ε≤Y (V u b) :=
    (regionStop_safe a ε (exhaustionHeight_pos z n) z.1 (exhaustionNorm z n) 0 0 n
      (exhaustionRegion_initial z n) b u (hu.trans hn)).1
  have he (u : ℝ) (hu : u∈Icc 0 (T : ℝ)) :
      V u.toNNReal b=actualState a b.1 u.toNNReal z.1 :=
    (exhaustionStop_agrees a z n b u.toNNReal
      ((show u.toNNReal≤T by simpa using Real.toNNReal_le_toNNReal hu.2).trans hn)).2.symm
  dsimp only [V] at he
  have h := localState_evolution a ε (exhaustionHeight_pos z n) z.1 b T hsafe
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact h.yc.congr (fun u hu => congrArg Y (he u hu).symm)
  · exact h.jc.congr (fun u hu => congrArg J (he u hu).symm)
  · intro u hu; simpa only [←he u hu] using h.yp u hu
  · intro u hu; simpa only [←he u hu] using h.qp u hu
  · intro u hu
    have hh := (h.yd u hu).congr_of_mem (fun v hv => congrArg Y (he v hv).symm) hu
    simpa only [he u hu] using hh
  · intro u hu
    have hh := (h.jd u hu).congr_of_mem (fun v hv => congrArg J (he v hv).symm) hu
    simpa only [he u hu] using hh

lemma actual_height_sq_le_radius (a : ℝ) (ha : 0<a) (b : ExactSLEGenerator.Driver)
    (z : UpperPlane) (t : ℝ≥0) (ht : alive a b.1 t z.1) :
    (Y (actualState a b.1 t z.1))^2≤z.1.im*physicalRadius (actualState a b.1 t z.1) := by
  have h := (actualState_evolution a b z t ht).height_sq_le_radius ha.le
    (fun u _ => by dsimp [Q]; nlinarith only [sq_nonneg (X (actualState a b.1 u.toNNReal z.1))])
    (by simp [actualState_zero ha b z.2]) (t : ℝ) ⟨t.coe_nonneg,le_rfl⟩
  simpa only [Real.toNNReal_coe,Real.toNNReal_zero,actualState_zero ha b z.2,Y_apply,
    physicalRadius] using h

lemma actual_height_sq_lower (a : ℝ) (ha : 0<a) (b : ExactSLEGenerator.Driver)
    (z : UpperPlane) (t : ℝ≥0) (ht : alive a b.1 t z.1) :
    z.1.im^2≤(Y (actualState a b.1 t z.1))^2+2*a*t := by
  have h := (actualState_evolution a b z t ht).height_sq_lower ha.le
    (fun u _ => by dsimp [Q]; nlinarith only [sq_nonneg (X (actualState a b.1 u.toNNReal z.1))])
    (t : ℝ) ⟨t.coe_nonneg,le_rfl⟩
  simpa only [Real.toNNReal_coe,Real.toNNReal_zero,actualState_zero ha b z.2,Y_apply] using h

 

lemma level_height_bound (a : ℝ) (ha : 0<a) (b : ExactSLEGenerator.Driver)
    (z : UpperPlane) (s : ℝ) (hs : 0≤ s)
    (hfin : radialTime a b.1 z.1 (levelRadius a (2*z.1.im) s)≠∞) :
    Y (actualState a b.1 (radialTime a b.1 z.1 (levelRadius a (2*z.1.im) s)).toNNReal z.1)≤
      z.1.im*Real.exp (-a*s) := by
  have hcap : 0<2*z.1.im := mul_pos (by norm_num) z.2
  have hr : levelRadius a (2*z.1.im) s≤z.1.im := by
    simpa using levelRadius_le ha hcap hs
  have ht := radialTime_attained a ha z.1 z.2 _ (levelRadius_pos _ _ _ hcap) hr b hfin
  have hh := actual_height_sq_le_radius a ha b z _ ht.1
  rw [ht.2] at hh
  have hexp : Real.exp (-2*a*s)=(Real.exp (-a*s))^2 := by
    rw [←Real.exp_nat_mul]; congr 1; ring
  conv_rhs at hh =>
    simp only [levelRadius,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0),hexp]
  have hpos : 0<z.1.im*Real.exp (-a*s) := mul_pos z.2 (Real.exp_pos _)
  nlinarith only [hh,hpos]

 

lemma radialTime_half_lower (a : ℝ) (ha : 0<a) (b : ExactSLEGenerator.Driver)
    (z : UpperPlane) (r : ℝ) (hr : 0<r) (hr2 : r≤z.1.im/2)
    (hfin : radialTime a b.1 z.1 r≠∞) :
    z.1.im^2/(4*a)≤((radialTime a b.1 z.1 r).toNNReal : ℝ) := by
  have ht := radialTime_attained a ha z.1 z.2 r hr (by linarith [z.2]) b hfin
  have hl := actual_height_sq_lower a ha b z _ ht.1
  have hu := actual_height_sq_le_radius a ha b z _ ht.1
  rw [ht.2] at hu
  have hh := mul_le_mul_of_nonneg_left hr2 z.2.le
  apply (div_le_iff₀ (by positivity : 0<4*a)).mpr
  nlinarith only [hl,hu,hh]

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open Metric Set Filter Topology
open scoped NNReal BoundedContinuousFunction
namespace SLEExactGauge.AnalyticCompactness

lemma lipschitzOn_subball {f : ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R))
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) :
    LipschitzOnWith (2*M/(R-r)).toNNReal f (closedBall c r) := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self (hr.trans_lt hrR)))
  apply (convex_closedBall c r).lipschitzOnWith_of_nnnorm_deriv_le
  · intro z hz
    exact (hf z (hsub hz)).differentiableAt (isOpen_ball.mem_nhds (hsub hz))
  · intro z hz
    have hb : ball z (R-r) ⊆ ball c R := by
      intro w hw
      exact (dist_triangle w z c).trans_lt (by
        have hw' : dist w z < R-r := hw
        have hz' : dist z c ≤ r := hz
        linarith)
    have hh := Complex.norm_deriv_le_div_of_mapsTo_ball (hf.mono hb)
      (R₂ := 2*M) (by
        intro w hw
        change dist (f w) (f z) ≤ 2*M
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (by linarith [hM w (hb hw),hM z (hsub hz)]))
      (sub_pos.mpr hrR)
    exact_mod_cast (hh.trans (Real.le_coe_toNNReal _))

 

theorem exists_subseq_uniform {F : ℕ → ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (ball c R))
    (hM : ∀ n z, z ∈ ball c R → ‖F n z‖ ≤ M) :
    ∃ g : ℂ → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => F (φ n)) g atTop (closedBall c r) ∧
      DifferentiableOn ℂ g (ball c r) := by
  classical
  let K := closedBall c r
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall c r)
  have hl (n : ℕ) := lipschitzOn_subball hr hrR (hF n) (hM n)
  let f : ℕ → K →ᵇ ℂ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun z => F n z, (hl n).continuousOn.domRestrict⟩
  have hlf (n : ℕ) : LipschitzWith (2*M/(R-r)).toNNReal (f n) :=
    lipschitzOnWith_iff_restrict.mp (hl n)
  have heq : Equicontinuous ((↑) : range f → K → ℂ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ (2*M/(R-r)).toNNReal
    rintro ⟨g,⟨n,rfl⟩⟩
    exact hlf n
  have hc := BoundedContinuousFunction.arzela_ascoli (closedBall (0:ℂ) M)
    (isCompact_closedBall _ _) (range f) (by
      rintro g z ⟨n,rfl⟩
      change dist (F n z) 0 ≤ M
      simpa only [dist_zero_right] using
        hM n z (closedBall_subset_ball hrR z.2)) heq
  obtain ⟨g,-,φ,hφ,hg⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let g' : ℂ → ℂ := fun z => if hz : z ∈ K then g ⟨z,hz⟩ else 0
  have he (z : ℂ) (hz : z ∈ K) : g' z = g ⟨z,hz⟩ := dite_eq_left hz
  have hu : TendstoUniformlyOn (fun n => F (φ n)) g' atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hh := Metric.tendstoUniformly_iff.mp
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hg) ε hε
    filter_upwards [hh] with n hn z hz
    rw [he z hz]
    exact hn ⟨z,hz⟩
  refine ⟨g',φ,hφ,hu,?_⟩
  exact (hu.mono ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall (fun n => (hF (φ n)).mono (ball_subset_ball hrR.le))) isOpen_ball

 

theorem uniform_zero_of_accumulation {F : ℕ → ℂ → ℂ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (ball c R))
    (hM : ∀ n z, z ∈ ball c R → ‖F n z‖ ≤ M)
    (z : ℕ → ℂ) (hz : ∀ j, z j ∈ closedBall c r)
    (hzc : ∀ j, z j ≠ c) (hzlim : Tendsto z atTop (𝓝 c))
    (hFz : ∀ j, Tendsto (fun n => F n (z j)) atTop (𝓝 0)) :
    TendstoUniformlyOn F (fun _ => 0) atTop (closedBall c r) := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hbad
  have hb : ∃ᶠ n in atTop, ∃ w ∈ closedBall c r, ε ≤ ‖F n w‖ := by
    simpa only [not_forall,exists_prop,not_lt,dist_zero_left] using (show ∃ᶠ n in atTop,
      ¬∀ w ∈ closedBall c r, dist (0:ℂ) (F n w)<ε from Filter.not_eventually.mp hbad)
  obtain ⟨ψ,hψ,hψbad⟩ := subseq_forall_of_frequently (x := fun n : ℕ => n)
    (p := fun n => ∃ w ∈ closedBall c r, ε ≤ ‖F n w‖) tendsto_id hb
  let s : ℝ := (r+R)/2
  have hrs : r<s := by dsimp [s]; linarith
  have hsR : s<R := by dsimp [s]; linarith
  have hs : 0<s := hr.trans hrs
  obtain ⟨g,φ,hφ,hg,hgd⟩ := exists_subseq_uniform hs.le hsR
    (fun n => hF (ψ n)) (fun n => hM (ψ n))
  have hgzero (j : ℕ) : g (z j)=0 := by
    have hpt := hg.tendsto_at (closedBall_subset_closedBall hrs.le (hz j))
    exact tendsto_nhds_unique hpt ((hFz j).comp (hψ.comp hφ.tendsto_atTop))
  have hcl : c∈closure ({w : ℂ | g w=0} \ {c}) := by
    apply mem_closure_of_tendsto hzlim
    exact Eventually.of_forall (fun j => ⟨hgzero j,hzc j⟩)
  have heq : EqOn g (fun _ => 0) (ball c s) :=
    hgd.analyticOnNhd isOpen_ball |>.eqOn_of_preconnected_of_mem_closure
      analyticOnNhd_const (convex_ball c s).isPreconnected (mem_ball_self hs) hcl
  have hsmall := Metric.tendstoUniformlyOn_iff.mp hg ε hε
  obtain ⟨n,hn⟩ := hsmall.exists
  obtain ⟨w,hw,hwbad⟩ := hψbad (φ n)
  have hh := hn w (closedBall_subset_closedBall hrs.le hw)
  rw [heq (closedBall_subset_ball hrs hw),dist_zero_left] at hh
  exact (not_lt_of_ge hwbad) hh

 

theorem uniform_zero_on_horizontal {F : ℕ → ℂ → ℂ} {C M : ℝ} (hC : 0 ≤ C)
    (hF : ∀ n, DifferentiableOn ℂ (F n) {z : ℂ | 0 < z.im})
    (hM : ∀ n z, z ∈ ball (((C^2+2 : ℝ) : ℂ)*Complex.I) (C^2+2-1/4) →
      ‖F n z‖ ≤ M)
    (hv : ∀ y : ℝ, 0 < y → Tendsto (fun n => F n ((y:ℂ)*Complex.I)) atTop (𝓝 0)) :
    TendstoUniformlyOn F (fun _ => 0) atTop {z : ℂ | z.im=1 ∧ |z.re|≤C} := by
  let A : ℝ := C^2+2
  let c : ℂ := (A:ℂ)*Complex.I
  let r : ℝ := A-1/2
  let R : ℝ := A-1/4
  have hA : 2 ≤ A := by dsimp [A]; nlinarith [sq_nonneg C]
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r,R]; linarith
  have hcim : c.im=A := by simp [c]
  have hcre : c.re=0 := by simp [c]
  have hball : ball c R ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have hh := Complex.im_le_norm (c-z)
    rw [Complex.sub_im,hcim,norm_sub_rev,← dist_eq_norm] at hh
    have hz' : dist z c < A-1/4 := hz
    change 0 < z.im
    linarith
  let z : ℕ → ℂ := fun j => c + ((1/((j:ℝ)+2):ℝ):ℂ)*Complex.I
  have hz (j : ℕ) : z j∈closedBall c r := by
    have hj : 0 < 1/((j:ℝ)+2) := by positivity
    have hj1 : 1/((j:ℝ)+2) ≤ 1/2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith [Nat.cast_nonneg (α := ℝ) j]
    rw [mem_closedBall,dist_eq_norm]
    simp only [z,add_sub_cancel_left,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hj,Complex.norm_I,mul_one]
    dsimp [r]
    linarith
  have hzc (j : ℕ) : z j≠c := by
    intro h
    have hh := congrArg Complex.im h
    simp only [z,Complex.add_im,Complex.mul_I_im,Complex.ofReal_re] at hh
    have hp : 0 < 1/((j:ℝ)+2) := by positivity
    linarith
  have hzlim : Tendsto z atTop (𝓝 c) := by
    have hh : Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    have h' := (Complex.continuous_ofReal.tendsto 0 |>.comp hh).mul_const Complex.I |>.const_add c
    simpa only [z,Function.comp_apply,Complex.ofReal_zero,zero_mul,add_zero] using h'
  have hFz (j : ℕ) : Tendsto (fun n => F n (z j)) atTop (𝓝 0) := by
    have he : z j = (((A+1/((j:ℝ)+2):ℝ):ℂ)*Complex.I) := by
      dsimp [z,c]
      push_cast
      ring
    rw [he]
    apply hv
    have hp : 0 < 1/((j:ℝ)+2) := by positivity
    linarith
  apply (uniform_zero_of_accumulation hr hrR (fun n => (hF n).mono hball)
    hM z hz hzc hzlim hFz).mono
  intro w hw
  rw [mem_closedBall,dist_eq_norm]
  have hsq : ‖w-c‖^2=w.re^2+(1-A)^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,hcim,hcre,sub_zero,hw.1]
    ring
  have hsq2 : w.re^2 ≤ C^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg w.re) hC).mpr hw.2
  have hbound : ‖w-c‖^2 ≤ r^2 := by
    rw [hsq]
    dsimp [r,A] at *
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) hr.le).mp hbound

end SLEExactGauge.AnalyticCompactness
end
end
 

 
section
 

noncomputable section
open Metric Set Filter Topology
namespace SLEExactGauge.AngularLimits
open AnalyticCompactness

 

theorem uniform_angular_of_radial {X : Type*} (f : X → ℂ → ℂ) (g : X → ℂ)
    (S : Set X) {M : ℝ}
    (hf : ∀ x∈S, DifferentiableOn ℂ (f x) {z : ℂ | 0<z.im})
    (hM : ∀ x∈S, ∀ z : ℂ, 0<z.im → ‖z‖≤1 → ‖f x z-g x‖≤M)
    (hr : TendstoUniformlyOn (fun y : ℝ => fun x => f x ((y:ℂ)*Complex.I))
      g (𝓝[>] 0) S) {C : ℝ} (hC : 0≤C) :
    TendstoUniformlyOn
      (fun y : ℝ => fun p : X×ℝ => f p.1 ((y:ℂ)*((p.2:ℂ)+Complex.I)))
      (fun p => g p.1) (𝓝[>] 0) (S ×ˢ Icc (-C) C) := by
  classical
  apply tendstoUniformlyOn_of_seq_tendstoUniformlyOn
  intro y hy
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hbad
  let A : ℝ := C^2+2
  have hA : 0<A := by dsimp [A]; positivity
  have hb : ∃ᶠ n in atTop, ∃ p∈S ×ˢ Icc (-C) C,
      ε≤‖g p.1-f p.1 ((y n:ℂ)*((p.2:ℂ)+Complex.I))‖ := by
    simpa only [not_forall,exists_prop,not_lt,dist_eq_norm] using not_eventually.mp hbad
  have he : ∀ᶠ n in atTop, 0<y n ∧ y n≤1/(2*A) := by
    filter_upwards [hy.eventually self_mem_nhdsWithin,
      (tendsto_nhds_of_tendsto_nhdsWithin hy).eventually
        (Iio_mem_nhds (by positivity : (0:ℝ)<1/(2*A)))] with n hn hn'
    exact ⟨hn,hn'.le⟩
  have hb' := hb.and_eventually he
  obtain ⟨ψ,hψ,hψbad⟩ := subseq_forall_of_frequently
    (x := fun n : ℕ => n)
    (p := fun n => (∃ p∈S ×ˢ Icc (-C) C,
      ε≤‖g p.1-f p.1 ((y n:ℂ)*((p.2:ℂ)+Complex.I))‖) ∧
        0<y n ∧ y n≤1/(2*A)) tendsto_id hb'
  choose p hp hpb using (fun n => (hψbad n).1)
  have hyp (n : ℕ) : 0<y (ψ n) := (hψbad n).2.1
  have hyb (n : ℕ) : y (ψ n)≤1/(2*A) := (hψbad n).2.2
  let F : ℕ → ℂ → ℂ := fun n z => g (p n).1-f (p n).1 ((y (ψ n):ℂ)*z)
  have hF (n : ℕ) : DifferentiableOn ℂ (F n) {z : ℂ | 0<z.im} := by
    apply (differentiableOn_const _).sub
    apply (hf (p n).1 (hp n).1).comp
      ((differentiable_const _).mul differentiable_id).differentiableOn
    intro z hz
    change 0<((y (ψ n):ℂ)*z).im
    simpa only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero] using
      mul_pos (hyp n) hz
  have hFM (n : ℕ) (z : ℂ)
      (hz : z∈ball ((A:ℂ)*Complex.I) (A-1/4)) : ‖F n z‖≤M := by
    have hzi : 0<z.im := by
      have hh := Complex.im_le_norm ((A:ℂ)*Complex.I-z)
      simp only [Complex.sub_im,Complex.mul_I_im,Complex.ofReal_re] at hh
      rw [norm_sub_rev,← dist_eq_norm] at hh
      have hz' : dist z ((A:ℂ)*Complex.I)<A-1/4 := hz
      linarith
    have hzn : ‖z‖≤2*A := by
      have hnorm := norm_add_le (z-(A:ℂ)*Complex.I) ((A:ℂ)*Complex.I)
      rw [sub_add_cancel,← dist_eq_norm] at hnorm
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA,
        Complex.norm_I,mul_one] at hnorm
      have hz' : dist z ((A:ℂ)*Complex.I)<A-1/4 := hz
      linarith
    have hpim : 0<((y (ψ n):ℂ)*z).im := by
      simpa only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero] using
        mul_pos (hyp n) hzi
    have hpnom : ‖(y (ψ n):ℂ)*z‖≤1 := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hyp n)]
      calc
        _ ≤ (1/(2*A))*(2*A) := mul_le_mul (hyb n) hzn (norm_nonneg _) (by positivity)
        _ = 1 := one_div_mul_cancel (by positivity)
    dsimp [F]
    rw [norm_sub_rev]
    exact hM (p n).1 (hp n).1 _ hpim hpnom
  have hFv (v : ℝ) (hv : 0<v) :
      Tendsto (fun n => F n ((v:ℂ)*Complex.I)) atTop (𝓝 0) := by
    have hy0 := tendsto_nhds_of_tendsto_nhdsWithin (hy.comp hψ)
    have hz : Tendsto (fun n => y (ψ n)*v) atTop (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,Eventually.of_forall (fun n => mul_pos (hyp n) hv)⟩
      simpa only [Function.comp_apply,zero_mul] using hy0.mul_const v
    have hu := hr.seq_tendstoUniformlyOn _ hz
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu η hη] with n hn
    have hh := hn (p n).1 (hp n).1
    simpa only [F,dist_zero_right,dist_eq_norm,Complex.ofReal_mul,mul_assoc,sub_zero] using hh
  have hu := uniform_zero_on_horizontal hC hF hFM hFv
  have hs := Metric.tendstoUniformlyOn_iff.mp hu ε hε
  obtain ⟨n,hn⟩ := hs.exists
  have hseg : ((p n).2:ℂ)+Complex.I ∈ {z : ℂ | z.im=1 ∧ |z.re|≤C} := by
    simpa only [mem_ofPred_eq,Complex.add_im,Complex.add_re,Complex.ofReal_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,zero_add,add_zero] using
      (show (1:ℝ)=1 ∧ |(p n).2|≤C from ⟨rfl,abs_le.mpr (hp n).2⟩)
  have hh := hn _ hseg
  rw [dist_zero_left] at hh
  exact (not_lt_of_ge (hpb n)) hh

end SLEExactGauge.AngularLimits
end
end
 

 
section
 

noncomputable section
open Metric Set Filter Topology MeasureTheory
namespace SLEExactGauge.TraceChaining

 

theorem radial_uniform_limit_nhds_of_bands {X E : Type*} [MetricSpace E]
    [CompleteSpace E] (f : X → ℝ → E) (g : X → E) (S : Set X)
    {r : ℝ} (hr : 0<r) (hr1 : r<1) {e : ℕ → ℝ} (he : Summable e)
    (hb : ∀ᶠ n in atTop, ∀ t∈S, ∀ y : ℝ, r^(n+1)≤y → y≤r^n →
      dist (f t y) (f t (r^n))≤e n)
    (hg : ∀ t∈S, Tendsto (f t) (𝓝[>] 0) (𝓝 (g t))) :
    TendstoUniformlyOn (fun y t => f t y) g (𝓝[>] 0) S := by
  have hu := radial_uniform_limit_of_bands f g S hr hr1 he hb hg
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε2 : 0<ε/2 := by linarith
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hb
  obtain ⟨n₁,hn₁⟩ := eventually_atTop.mp
    (he.tendsto_atTop_zero.eventually (Iio_mem_nhds hε2))
  obtain ⟨n₂,hn₂⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hu (ε/2) hε2)
  let n₃ := max n₀ (max n₁ n₂)
  have hv : 0<r^(n₃+1) := pow_pos hr _
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ y : ℝ in 𝓝[>] 0, y<r^(n₃+1) from
      nhdsWithin_le_nhds (Iio_mem_nhds hv))] with y hy hyb
  intro t ht
  have hy1 : y≤1 := hyb.le.trans (pow_le_one₀ hr.le hr1.le)
  obtain ⟨n,hnlow,hnup⟩ := exists_nat_pow_near_of_lt_one hy hy1 hr hr1
  have hn3 : n₃≤n := by
    by_contra hh
    have hnlt : n+1≤n₃+1 := by omega
    have hlo := pow_le_pow_of_le_one hr.le hr1.le hnlt
    linarith
  have hbnd := hn₀ n (le_trans (le_max_left _ _) hn3) t ht y hnlow.le hnup
  have hen := hn₁ n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn3)
  have hgn := hn₂ n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn3) t ht
  calc
    _ ≤ dist (g t) (f t (r^n))+dist (f t (r^n)) (f t y) := dist_triangle _ _ _
    _ < ε := by rw [dist_comm (f t (r^n))]; linarith

end SLEExactGauge.TraceChaining
namespace SLEExactGauge.LiteralTrace
open TraceChaining AngularLimits

 

theorem radial_uniform_all_windows {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W, ∀ m H : ℕ,
      TendstoUniformlyOn (fun y t => radialValue κ b t y)
        (fun t => trace κ b (t/κ)) (𝓝[>] 0) (Icc (1/((m:ℝ)+1)) H) := by
  obtain ⟨N,hN,hbands⟩ := radial_uniform_bands hκ hκ8 hW
  filter_upwards [hbands,trace_limit_all_positive hκ hκ8 hW] with b hb hlim
  intro m H
  apply radial_uniform_limit_nhds_of_bands (fun t => radialValue κ b t)
    (fun t => trace κ b (t/κ)) _ (traceRatio_pos N) (traceRatio_lt_one hN)
    (traceError_summable hκ hκ8 hN H)
  · filter_upwards [hb m H] with n hn t ht y hy hy'
    simpa only [dist_eq_norm] using hn t ht.1 ht.2 y hy hy'
  · intro t ht
    have ht0 : 0<t := (by positivity : (0:ℝ)<1/((m:ℝ)+1)).trans_le ht.1
    have hh := hlim (t/κ) (div_pos ht0 hκ)
    simpa only [mul_div_cancel₀ _ hκ.ne'] using hh

lemma inverseFlow_shift_bound {κ t T R : ℝ} (hκ : 0<κ) (ht : 0≤t)
    (htT : t≤T) (b : Driver) (hB : ∀ u∈Icc 0 T, |driverValue b u|≤R)
    {z : ℂ} (hzi : 0<z.im) (hzn : ‖z‖≤1) :
    ‖inverseFlow κ b t (driverValue b t+z)‖≤R+3+2*a κ*T := by
  have hw : 0<((driverValue b t:ℂ)+z).im := by simpa using hzi
  have hp := surviving_flow_positiveSolution ht (inverseFlow_surviving hκ b ht hw)
  have hre : |(inverseFlow κ b t (driverValue b t+z)).re|≤R+1 := by
    apply hp.initial_abs_re_le hκ ht
    · intro u hu
      exact (hB u ⟨hu.1,hu.2.trans htT⟩).trans (by linarith)
    · rw [flow_inverseFlow hκ b ht hw]
      simp only [Complex.add_re,Complex.ofReal_re]
      exact (abs_add_le _ _).trans
        (add_le_add (hB t ⟨ht,htT⟩) ((Complex.abs_re_le_norm z).trans hzn))
  have hi : (inverseFlow κ b t (driverValue b t+z)).im≤1+2*a κ*T+1 :=
    inverseFlow_im_le hκ ht htT b hw (by simpa using (Complex.im_le_norm z).trans hzn)
  have hip := inverseFlow_im_pos hκ ht b hw
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  rw [abs_of_pos hip]
  linarith

 

theorem angular_uniform_all_windows {κ : ℝ} (hκ : 0<κ) (hκ8 : κ<8)
    {W : WienerLaw} (hW : IsWiener W) :
    ∀ᵐ b ∂W, ∀ m H : ℕ, ∀ C : ℝ, 0≤C →
      TendstoUniformlyOn
        (fun y : ℝ => fun p : ℝ×ℝ => inverseFlow κ b p.1
          (driverValue b p.1+(y:ℂ)*((p.2:ℂ)+Complex.I)))
        (fun p => trace κ b (p.1/κ)) (𝓝[>] 0)
        (Icc (1/((m:ℝ)+1)) H ×ˢ Icc (-C) C) := by
  filter_upwards [radial_uniform_all_windows hκ hκ8 hW] with b hb
  intro m H C hC
  have hc : Continuous (driverValue b) := (map_continuous b).comp continuous_real_toNNReal
  obtain ⟨R,hR,hRB⟩ := (isCompact_Icc.image hc).isBounded.exists_pos_norm_le
  have hB : ∀ u∈Icc (0:ℝ) H, |driverValue b u|≤R := by
    intro u hu
    simpa only [Real.norm_eq_abs] using hRB _ (mem_image_of_mem _ hu)
  let B : ℝ := R+3+2*a κ*H
  let S := Icc (1/((m:ℝ)+1)) (H:ℝ)
  have ht0 (t : ℝ) (ht : t∈S) : 0≤t :=
    (by positivity : (0:ℝ)≤1/((m:ℝ)+1)).trans ht.1
  have hg (t : ℝ) (ht : t∈S) : ‖trace κ b (t/κ)‖≤B := by
    apply le_of_tendsto ((hb m H).tendsto_at ht).norm
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ y : ℝ in 𝓝[>] 0, y<1 from nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))]
      with y hy hy1
    exact inverseFlow_shift_bound hκ (ht0 t ht) ht.2 b hB
      (by simpa using hy) (by simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (show 0<y from hy),Complex.norm_I,mul_one]; exact hy1.le)
  apply uniform_angular_of_radial (fun t z => inverseFlow κ b t (driverValue b t+z))
    (fun t => trace κ b (t/κ)) S (M := 2*B) _ _ (hb m H) hC
  · intro t ht z hz
    apply ((inverseFlow_hasStrictDerivAt hκ b (ht0 t ht) (by simpa using hz)).hasDerivAt.comp z
      ((hasDerivAt_id z).const_add (driverValue b t:ℂ))).differentiableAt.differentiableWithinAt
  · intro t ht z hzi hzn
    exact (norm_sub_le _ _).trans (by
      have hh := inverseFlow_shift_bound hκ (ht0 t ht) ht.2 b hB hzi hzn
      have hh' := hg t ht
      change ‖inverseFlow κ b t (driverValue b t+z)‖≤B at hh
      linarith)

end SLEExactGauge.LiteralTrace
end
end

end OAI
