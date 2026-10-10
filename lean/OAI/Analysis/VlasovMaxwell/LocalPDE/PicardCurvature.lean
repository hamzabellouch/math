import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.MixedJets
import OAI.Analysis.VlasovMaxwell.Retarded.VolterraMajorant
import OAI.Analysis.VlasovMaxwell.Regularity.CurvatureInterpolation
import OAI.Analysis.VlasovMaxwell.Regularity.MomentLimit

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_physical_integrand_curvature (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a : Vec → ℝ, ∀ E B : Vec → Vec,
      (∀ x, |a x|≤A ∧ ‖E x‖≤L ∧ ‖B x‖≤L) →
      ∀ Hf H M N : ℝ, 0≤Hf → 0≤H → 0≤M → 0≤N →
      CurvatureBound a Hf → CurvatureBound E H → CurvatureBound B H →
      (∀ x y, |a y-a x|≤M*‖y-x‖) →
      (∀ x y, ‖E y-E x‖≤N*‖y-x‖ ∧ ‖B y-B x‖≤N*‖y-x‖) →
      CurvatureBound (fun x => (a x*(1-dot n (velocity v))) •
        physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x))))
        (C*(Hf+H+2*(M+N)^2)/r^2) := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_integrand_curvature A P L
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a E B hbnd Hf H M N hHf hH hM hN ha hE hB haL hEBL x w
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv a E B hbnd Hf H M N hHf hH hM hN ha hE hB haL hEBL x w
  simp only [normalisedPhysicalIntegrand_eq hr.1.ne'] at hh
  rw [show (2:ℝ) • (r^2 • ((a x*(1-dot n (velocity v))) •
      physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x)))))=
      r^2 • ((2:ℝ) • ((a x*(1-dot n (velocity v))) •
      physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x))))) by module,
    ← smul_add,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma uniform_physical_integral_curvature (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ f : Vec → Vec → ℝ, (∀ x, Continuous (f x)) → (∀ x, HasCompactSupport (f x)) →
      (∀ x v, |f x v|≤A) → (∀ x v, P<‖v‖ → f x v=0) →
      ∀ E B : Vec → Vec, (∀ x, ‖E x‖≤L ∧ ‖B x‖≤L) →
      ∀ Hf H M N : ℝ, 0≤Hf → 0≤H → 0≤M → 0≤N →
      (∀ v, CurvatureBound (fun x => f x v) Hf) → CurvatureBound E H → CurvatureBound B H →
      (∀ v x y, |f y v-f x v|≤M*‖y-x‖) →
      (∀ x y, ‖E y-E x‖≤N*‖y-x‖ ∧ ‖B y-B x‖≤N*‖y-x‖) →
      CurvatureBound (fun x => ∫ v : Vec, (f x v*(1-dot n (velocity v))) •
        physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x))))
        (C*(Hf+H+2*(M+N)^2)/r^2) := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_integrand_curvature A P L
  refine ⟨K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro r hr n hn f hf hc hab hs E B hEB Hf H M N hHf hH hM hN hfc hEc hBc hfL hEBL
  let g : Vec → Vec → Vec := fun v x => (f x v*(1-dot n (velocity v))) •
    physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x)))
  have hint (x : Vec) : Integrable (fun v => g v x) :=
    integrable_physical_integrand (hf x) (hc x) hr.1.ne' hn (E x) (B x)
  have he (x : Vec) : (∫ v in closedBall (0:Vec) P, g v x)=∫ v, g v x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    simp only [g,hs x v (by simpa only [mem_closedBall_zero_iff,not_le] using hv),zero_mul,zero_smul]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0:Vec) P).measure_lt_top⟩
  have hbound : ∀ᵐ v ∂volume.restrict (closedBall (0:Vec) P),
      CurvatureBound (g v) (K*(Hf+H+2*(M+N)^2)/r^2) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
    exact hk r hr n hn v (mem_closedBall_zero_iff.mp hv) (fun x => f x v) E B
      (fun x => ⟨hab x v,hEB x⟩) Hf H M N hHf hH hM hN (hfc v) hEc hBc (hfL v) hEBL
  have hh := CurvatureBound.integral (fun x => (hint x).restrict) hbound
  simp only [he,Measure.real,Measure.restrict_apply_univ] at hh
  convert hh using 1
  simp only [Measure.real]
  ring

lemma CurvatureBound.cross_const_left {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {f : U → Vec} {H : ℝ} (hc : CurvatureBound f H) (n : Vec) :
    CurvatureBound (fun x => cross n (f x)) (‖n‖*H) := by
  intro x v
  rw [← cross_add_right,← cross_smul_right,← cross_sub_right]
  exact (norm_cross_le _ _).trans ((mul_le_mul_of_nonneg_left (hc x v) (norm_nonneg _)).trans_eq (by ring))

lemma uniform_retarded_density_curvature (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ), T≤1 →
      ContDiff ℝ ∞ s.f → CompactOnFiniteHorizons s →
      (∀ t∈Icc 0 T, ∀ x v, |s.f (t,x,v)|≤A) →
      (∀ t∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      (∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)‖≤L ∧ ‖s.B (t,x)‖≤L) →
      ∀ Hf H M N : ℝ, 0≤Hf → 0≤H → 0≤M → 0≤N →
      (∀ t∈Icc 0 T, ∀ v, CurvatureBound (fun x => s.f (t,x,v)) Hf) →
      (∀ t∈Icc 0 T, CurvatureBound (fun x => s.E (t,x)) H ∧ CurvatureBound (fun x => s.B (t,x)) H) →
      (∀ t∈Icc 0 T, ∀ v x y, |s.f (t,y,v)-s.f (t,x,v)|≤M*‖y-x‖) →
      SpatialFieldLip T N s.E s.B →
      ∀ t∈Icc 0 T, ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
        CurvatureBound (fun x => retardedElectricDensity s t x (x+z)) (C*(Hf+H+2*(M+N)^2)/‖z‖^2) ∧
        CurvatureBound (fun x => retardedMagneticDensity s t x (x+z)) (C*(Hf+H+2*(M+N)^2)/‖z‖^2) := by
  obtain ⟨C,hC,hk⟩ := uniform_physical_integral_curvature A P L
  refine ⟨C,hC,?_⟩
  intro s T hT hf hc hab hs hEB Hf H M N hHf hH hM hN hfc hEBc hfL hEBL t ht z hz hzt
  have htime : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hn : ‖-(‖z‖⁻¹ • z)‖=1 := by
    simpa only [coneDirection,coneRadius,sub_zero,zero_sub,norm_neg,smul_neg] using coneDirection_norm (x:=(0:Vec)) (y:=z) (norm_pos_iff.mp hz).symm
  have hslice (x : Vec) := (show RegularParticle s.f from ⟨(hf.of_le (by simp)).contDiffOn,hc⟩).slice htime.1 x
  have he : CurvatureBound (fun x => retardedElectricDensity s t x (x+z))
      (C*(Hf+H+2*(M+N)^2)/‖z‖^2) := by
    simp only [retardedElectricDensity,coneRadius_add,coneDirection_add]
    exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hT)⟩ _ hn (fun x v => s.f (t-‖z‖,x+z,v))
      (fun x => (hslice (x+z)).1.continuous) (fun x => (hslice (x+z)).2)
      (fun x v => hab _ htime (x+z) v) (fun x v hv => hs _ htime (x+z) v hv)
      (fun x => s.E (t-‖z‖,x+z)) (fun x => s.B (t-‖z‖,x+z)) (fun x => hEB _ htime (x+z))
      Hf H M N hHf hH hM hN (fun v => (hfc _ htime v).translate z)
      ((hEBc _ htime).1.translate z) ((hEBc _ htime).2.translate z)
      (fun v x y => by simpa only [add_sub_add_right_eq_sub] using hfL _ htime v (x+z) (y+z))
      (fun x y => by simpa only [add_sub_add_right_eq_sub] using hEBL _ htime (x+z) (y+z))
  refine ⟨he,?_⟩
  simpa only [retardedMagneticDensity,coneDirection_add,hn,one_mul] using he.cross_const_left (-(‖z‖⁻¹ • z))

lemma boundary_integral_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → U → W} {a : U → W} {t C D : ℝ} (ht : 0≤t)
    (hF : ∀ x, IntegrableOn (fun z => F z x) (ball (0:Vec) t))
    (ha : CurvatureBound a D)
    (hFc : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t → CurvatureBound (F z) (C/‖z‖^2)) :
    CurvatureBound (fun x => a x+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z x) (D+C*t) := by
  intro x v
  have hp : IntegrableOn (fun z => F z (x+v)+F z (x-v)) (ball (0:Vec) t) := (hF (x+v)).add (hF (x-v))
  have hm : IntegrableOn (fun z => (2:ℝ) • F z x) (ball (0:Vec) t) := (hF x).smul (2:ℝ)
  have he : (a (x+v)+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z (x+v))+
      (a (x-v)+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z (x-v))-
      (2:ℝ) • (a x+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z x)=
      (a (x+v)+a (x-v)-(2:ℝ) • a x)+(4*Real.pi)⁻¹ •
        ∫ z in ball (0:Vec) t, (F z (x+v)+F z (x-v)-(2:ℝ) • F z x) := by
    rw [integral_sub hp hm,integral_add (hF (x+v)) (hF (x-v)),integral_smul]
    module
  rw [he]
  have hb := scaled_kernel_tip_le_on ht (hp.sub hm) (C:=C*‖v‖^2) (by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact (hFc z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le x v).trans_eq (by ring))
  exact ((norm_add_le _ _).trans (add_le_add (ha x v) hb)).trans_eq (by ring)

lemma mixed_fields_curvature {d : Datum} {s : Solution} {E B : Field}
    (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hV : TransportFor s E B) {t C D : ℝ} (ht : 0<t)
    (hb : CurvatureBound (fun x => electricBoundaryField (datumBoundarySolution d) t x) D ∧
      CurvatureBound (fun x => magneticBoundaryField (datumBoundarySolution d) t x) D)
    (hden : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
      CurvatureBound (fun x => retardedElectricDensity {s with E:=E,B:=B} t x (x+z)) (C/‖z‖^2) ∧
      CurvatureBound (fun x => retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)) (C/‖z‖^2)) :
    CurvatureBound (fun x => s.E (t,x)) (D+C*t) ∧ CurvatureBound (fun x => s.B (t,x)) (D+C*t) := by
  have he (x : Vec) := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell ht x
  have hf1 := (hs.smooth_f.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=particleHalfSpace)
  have hE1 := (hE.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hB1 := (hB.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hEq : (fun x => s.E (t,x))=(fun x => electricBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity {s with E:=E,B:=B} t x (x+z)) := by
    funext x
    rw [(he x).1,(hs.boundary_eq ht x).1]
  have hBq : (fun x => s.B (t,x))=(fun x => magneticBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)) := by
    funext x
    rw [(he x).2,(hs.boundary_eq ht x).2]
  rw [hEq,hBq]
  exact ⟨boundary_integral_curvature ht.le (fun x =>
    integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
    hb.1 (fun z hz hzt => (hden z hz hzt).1),
    boundary_integral_curvature ht.le (fun x =>
    integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
    hb.2 (fun z hz hzt => (hden z hz hzt).2)⟩

def SpatialFieldCurvature (T H : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, CurvatureBound (fun x => E (t,x)) H ∧ CurvatureBound (fun x => B (t,x)) H

def PhaseParticleCurvature (T H : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc 0 T, CurvatureBound (fun z => f (t,z)) H

theorem uniform_picard_sequence_curvature {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T₀ A R P L N M : ℝ} (hT₀ : 0<T₀) (hT₀1 : T₀≤1)
    (hL : 0≤L) (hN : 0≤N) (hM : 0≤M)
    (h0 : S 0=datumBoundarySolution d)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T₀ L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
      LocalParticleBound T₀ A R P (S (n+1)).f ∧ PhaseParticleLip T₀ M (S (n+1)).f) :
    ∃ T Hf H : ℝ, 0<T ∧ T≤T₀ ∧ 0≤Hf ∧ 0≤H ∧
      (∀ n, SpatialFieldCurvature T H (S n).E (S n).B) ∧
      ∀ n, PhaseParticleCurvature T Hf (S (n+1)).f := by
  obtain ⟨D,hD,hDE,hDB,hboundary⟩ := datum_boundary_global_curvature hd
  obtain ⟨Df,hDf,hfc⟩ := smooth_compact_curvature hd.1 hd.2.1
  obtain ⟨Af,hAf,hfl⟩ := smooth_compact_lipschitz (hd.1.of_le (by simp)) hd.2.1
  obtain ⟨C,hC,hdensity⟩ := uniform_retarded_density_curvature A P L
  let K := 1+2*N+L
  let Q := Real.exp (K*T₀)
  let Hf := 4*Df*Q^2+1
  let H := D+1
  let Cf := Af*4*(6+6*L+2*H+2*N)*Q^3
  let CE := C*(Hf+H+2*(M+N)^2)
  have hK : 0≤K := by dsimp [K]; positivity
  have hQ : 0<Q := Real.exp_pos _
  have hHf : 0≤Hf := by dsimp [Hf]; positivity
  have hH : 0≤H := by dsimp [H]; positivity
  have hCf : 0≤Cf := by dsimp [Cf]; positivity
  have hCE : 0≤CE := by dsimp [CE]; positivity
  let T := min T₀ (min (Cf+1)⁻¹ (CE+1)⁻¹)
  have hT : 0<T := by dsimp [T]; positivity
  have hTT : T≤T₀ := min_le_left _ _
  have hTCf : Cf*T≤1 := by
    have ht : T≤(Cf+1)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
    have hh := (le_div_iff₀ (by positivity : 0<Cf+1)).mp (show T≤1/(Cf+1) by simpa only [one_div] using ht)
    nlinarith
  have hTCE : CE*T≤1 := by
    have ht : T≤(CE+1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
    have hh := (le_div_iff₀ (by positivity : 0<CE+1)).mp (show T≤1/(CE+1) by simpa only [one_div] using ht)
    nlinarith
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 T₀ := Icc_subset_Icc_right hTT
  have hpart (n : ℕ) (hh : SpatialFieldCurvature T H (S n).E (S n).B) :
      PhaseParticleCurvature T Hf (S (n+1)).f := by
    intro t ht
    have hb := transported_curvature (hr n).1 (hsm n).1 (hsm n).2 (hr n).2.1
      hAf hDf hL hN hH hfl hfc
      (fun r hr x => ((hc n).1 r (hsub hr) x).2)
      (fun r hr x y => ((hc n).2 r (hsub hr) x y).1)
      (fun r hr x y => ((hc n).2 r (hsub hr) x y).2)
      (fun r hr => (hh r hr).1) (fun r hr => (hh r hr).2) ht
    apply hb.mono
    have he : Real.exp ((1+2*N+L)*T)≤Q := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hTT hK)
    have he2 := pow_le_pow_left₀ (Real.exp_pos _).le he 2
    have he3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
    have htCf : Cf*t≤1 := (mul_le_mul_of_nonneg_left ht.2 hCf).trans hTCf
    have ha := mul_le_mul_of_nonneg_left he2 (show 0≤4*Df by positivity)
    have hb' := mul_le_mul_of_nonneg_left he3 (show 0≤Af*(4*(6+6*L+2*H+2*N)*t) from mul_nonneg hAf (mul_nonneg (by positivity) ht.1))
    dsimp [Hf,Cf] at *
    nlinarith
  have hstep (n : ℕ) (hh : SpatialFieldCurvature T H (S n).E (S n).B) :
      SpatialFieldCurvature T H (S (n+1)).E (S (n+1)).B := by
    have hp := hpart n hh
    intro t ht
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      simpa only [(hr n).1.initial_E,(hr n).1.initial_B] using
        And.intro (hDE.mono (by dsimp [H]; linarith)) (hDB.mono (by dsimp [H]; linarith))
    · have hbnd := hboundary t ⟨ht0,ht.2.trans (hTT.trans hT₀1)⟩
      have hden := hdensity {S (n+1) with E:=(S n).E,B:=(S n).B} T (hTT.trans hT₀1)
        (hr n).1.smooth_f (hr n).1.compact
        (fun r hrt x v => ((hr n).2.2.1 r (hsub hrt) x v).1)
        (fun r hrt x v hv => by
          by_contra hn
          exact (not_le_of_gt hv) (((hr n).2.2.1 r (hsub hrt) x v).2 hn).2)
        (fun r hrt x => (hc n).1 r (hsub hrt) x) Hf H M N hHf hH hM hN
        (fun r hrt v => (hp r hrt).spatial_slice v) hh
        (fun r hrt v x y => by
          simpa only [Prod.mk_sub_mk,sub_self,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _)] using
            (hr n).2.2.2 r (hsub hrt) (y,v) (x,v))
        (fun r hrt x y => (hc n).2 r (hsub hrt) x y) t ht
      have hb := mixed_fields_curvature (hr n).1 (hsm n).1 (hsm n).2 (hr n).2.1 ht0 hbnd hden
      have hb' : D+CE*t≤H := by
        have hct := (mul_le_mul_of_nonneg_left ht.2 hCE).trans hTCE
        dsimp [H]; linarith
      exact ⟨hb.1.mono hb',hb.2.mono hb'⟩
  have hfields (n : ℕ) : SpatialFieldCurvature T H (S n).E (S n).B := by
    induction n with
    | zero =>
      rw [h0]
      intro t ht
      exact ⟨hDE.mono (by dsimp [H]; linarith),hDB.mono (by dsimp [H]; linarith)⟩
    | succ n ih => exact hstep n ih
  exact ⟨T,Hf,H,hT,hTT,hHf,hH,hfields,fun n => hpart n (hfields n)⟩

lemma FieldControl.spatialJetBound_one {E B : Field} {T L N : ℝ}
    (hc : FieldControl T L N E B) (hN : 0≤N) :
    SpatialJetBound 1 T (max L N) E B := by
  intro t ht x i hi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
  · simpa only [norm_iteratedFDeriv_zero] using
      And.intro ((hc.1 t ht x).1.trans (le_max_left _ _)) ((hc.1 t ht x).2.trans (le_max_left _ _))
  · simp only [norm_iteratedFDeriv_one]
    have he : ‖fderiv ℝ (fun y => E (t,y)) x‖≤N := by
      apply norm_fderiv_le_of_lip' ℝ hN
      exact Eventually.of_forall fun y => (hc.2 t ht x y).1
    have hb : ‖fderiv ℝ (fun y => B (t,y)) x‖≤N := by
      apply norm_fderiv_le_of_lip' ℝ hN
      exact Eventually.of_forall fun y => (hc.2 t ht x y).2
    exact ⟨he.trans (le_max_right _ _),hb.trans (le_max_right _ _)⟩

lemma particleJetBound_one {f : Particle} {T A R P M : ℝ}
    (hb : LocalParticleBound T A R P f) (hl : PhaseParticleLip T M f) (hM : 0≤M) :
    ParticleJetBound 1 T (max A M) f := by
  intro t ht i hi z
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
  · simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using (hb t ht z.1 z.2).1.trans (le_max_left _ _)
  · rw [norm_iteratedFDeriv_one]
    apply le_trans _ (le_max_right A M)
    apply norm_fderiv_le_of_lip' ℝ hM
    exact Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hl t ht w z

theorem uniform_picard_sequence_jets {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T A R P L N M : ℝ} (_ : 0<T) (hT1 : T≤1)
    (hN : 0≤N) (hM : 0≤M) (h0 : S 0=datumBoundarySolution d)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
      LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) :
    ∀ k : ℕ, ∃ Q : ℝ, 1≤Q ∧
      (∀ n, SpatialJetBound (k+1) T Q (S n).E (S n).B) ∧
      ∀ n, ParticleJetBound (k+1) T Q (S (n+1)).f := by
  intro k
  induction k with
  | zero =>
    let Q := max (max L N) (max (max A M) 1)
    have he : max L N≤Q := le_max_left _ _
    have hf : max A M≤Q := (le_max_left _ _).trans (le_max_right _ _)
    refine ⟨Q,(le_max_right _ _).trans (le_max_right _ _),?_,?_⟩
    · intro n t ht x i hi
      exact ⟨((hc n).spatialJetBound_one hN t ht x i hi).1.trans he,
        ((hc n).spatialJetBound_one hN t ht x i hi).2.trans he⟩
    · intro n t ht i hi z
      exact (particleJetBound_one (hr n).2.2.1 (hr n).2.2.2 hM t ht i hi z).trans hf
  | succ k ih =>
    obtain ⟨Q,hQ,hfields,hparticles⟩ := ih
    obtain ⟨F,hF,htransport⟩ := transported_derivative_tame hd (k+1) (by omega) Q hQ
    obtain ⟨D,C,hD,hC,hinit,hstep⟩ := mixed_fields_derivative_tame hd (k+1) (by omega) P Q hQ
    obtain ⟨H,hH,hHmon,hH1,hHstep⟩ := exists_tame_volterra_majorant hD hC hF
    have hHpos (t : ℝ) (ht : 0≤t) : 0≤H t := zero_le_one.trans (hH1 t ht)
    have hH0 : D≤H 0 := by simpa using hHstep 0 le_rfl
    let J : ℝ → ℝ := fun u => (F+1)*(1+H u)
    have hJ : Continuous J := continuous_const.mul (continuous_const.add hH)
    have hHJ (u : ℝ) (hu : 0≤u) : H u≤J u := by
      dsimp [J]
      nlinarith [mul_nonneg hF (hHpos u hu)]
    have hparticle (n : ℕ)
        (hold : ∀ t∈Icc (0:ℝ) T, ∀ x,
          ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).E (t,y)) x‖≤H t ∧
          ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).B (t,y)) x‖≤H t) :
        ∀ t∈Icc (0:ℝ) T, ∀ z,
          ‖iteratedFDeriv ℝ (k+1+1) (fun w => (S (n+1)).f (t,w)) z‖≤F*(1+H t) := by
      intro t ht z
      exact htransport (S n).E (S n).B (hsm n).1 (hsm n).2 (S (n+1)) (hr n).1 (hr n).2.1
        t ⟨ht.1,ht.2.trans hT1⟩ (fun u hu => hfields n u ⟨hu.1,hu.2.trans ht.2⟩)
        (H t) (hHpos t ht.1) (fun u hu x => ⟨(hold u ⟨hu.1,hu.2.trans ht.2⟩ x).1.trans (hHmon hu.2),
          (hold u ⟨hu.1,hu.2.trans ht.2⟩ x).2.trans (hHmon hu.2)⟩) t ⟨ht.1,le_rfl⟩ z
    have htop : ∀ n, ∀ t∈Icc (0:ℝ) T, ∀ x,
        ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).E (t,y)) x‖≤H t ∧
        ‖iteratedFDeriv ℝ (k+1+1) (fun y => (S n).B (t,y)) x‖≤H t := by
      intro n
      induction n with
      | zero =>
        intro t ht x
        simpa only [h0,datumBoundarySolution] using
          And.intro ((hinit x).1.trans (hH0.trans (hHmon ht.1))) ((hinit x).2.trans (hH0.trans (hHmon ht.1)))
      | succ n ihn =>
        have hf := hparticle n ihn
        intro t ht x
        have hh := hstep (S (n+1)) (S n).E (S n).B (hr n).1 (hsm n).1 (hsm n).2 (hr n).2.1 T hT1
          (fun u hu y v hv => by
            by_contra hn
            exact (not_le_of_gt hv) (((hr n).2.2.1 u hu y v).2 hn).2)
          (hparticles n) (hfields n) J hJ (fun u hu => (hHpos u hu.1).trans (hHJ u hu.1))
          (fun u hu z => (hf u hu z).trans (by dsimp [J]; nlinarith [hHpos u hu.1]))
          (fun u hu y => ⟨(ihn u hu y).1.trans (hHJ u hu.1),(ihn u hu y).2.trans (hHJ u hu.1)⟩) t ht x
        exact ⟨hh.1.trans (hHstep t ht.1),hh.2.trans (hHstep t ht.1)⟩
    let B := Q+H 1+F*(1+H 1)
    have hHB : H 1≤B := by dsimp [B]; nlinarith [hHpos 1 zero_le_one]
    have hQB : Q≤B := by dsimp [B]; nlinarith [hHpos 1 zero_le_one]
    have hFB : F*(1+H 1)≤B := by dsimp [B]; linarith [hHpos 1 zero_le_one]
    refine ⟨B,hQ.trans hQB,?_,?_⟩
    · intro n t ht x i hi
      by_cases hik : i≤k+1
      · exact ⟨(hfields n t ht x i hik).1.trans hQB,(hfields n t ht x i hik).2.trans hQB⟩
      · have he : i=k+1+1 := by omega
        subst i
        exact ⟨(htop n t ht x).1.trans ((hHmon (ht.2.trans hT1)).trans hHB),
          (htop n t ht x).2.trans ((hHmon (ht.2.trans hT1)).trans hHB)⟩
    · intro n t ht i hi z
      by_cases hik : i≤k+1
      · exact (hparticles n t ht i hik z).trans hQB
      · have he : i=k+1+1 := by omega
        subst i
        exact (hparticle n (htop n) t ht z).trans
          ((mul_le_mul_of_nonneg_left (add_le_add_right (hHmon (ht.2.trans hT1)) 1) hF).trans hFB)

lemma hasFDerivWithinAt_uniform_limit_convex {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℕ → U → W} {DF : ℕ → U → (U →L[ℝ] W)}
    {f : U → W} {D : U → (U →L[ℝ] W)} {S : Set U}
    (hS : Convex ℝ S) (hcont : ContinuousOn D S)
    (hder : ∀ n, ∀ x∈S, HasFDerivWithinAt (F n) (DF n x) S x)
    (hD : TendstoUniformlyOn DF D atTop S)
    (hf : ∀ x∈S, Tendsto (fun n => F n x) atTop (𝓝 (f x))) {x : U} (hx : x∈S) :
    HasFDerivWithinAt f (D x) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousWithinAt_iff.mp (hcont x hx) (ε/2) (by positivity)
  have hunif := Metric.tendstoUniformlyOn_iff.mp hD (ε/2) (by positivity)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ),self_mem_nhdsWithin] with y hy hyS
  apply le_of_tendsto (((hf y hyS).sub (hf x hx)).sub tendsto_const_nhds).norm
  filter_upwards [hunif] with n hn
  apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hder n z hz.2).mono inter_subset_right) _
    ((convex_ball _ _).inter hS) ⟨mem_ball_self hδ,hx⟩ ⟨hy,hyS⟩
  intro z hz
  have ha := hn z hz.2
  have hb := hnear hz.2 hz.1
  rw [dist_eq_norm,norm_sub_rev] at ha
  rw [dist_eq_norm] at hb
  exact (norm_sub_le_norm_sub_add_norm_sub _ (D z) _).trans (by linarith)

lemma continuous_spatial_fderiv {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p : ℝ × U => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he (p : ℝ × U) : fderiv ℝ (fun x => F (p.1,x)) p.2 =
      (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ U) := by
    exact (((hF.differentiable (by simp)) p).hasFDerivAt.comp p.2
      ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv
  simp_rw [he]
  exact (hF.continuous_fderiv (by simp)).clm_comp continuous_const

def curlMap : (Vec →L[ℝ] Vec) →L[ℝ] Vec :=
  ({ toFun := fun A => WithLp.toLp 2 ![A (basis 1) 2-A (basis 2) 1,
        A (basis 2) 0-A (basis 0) 2,A (basis 0) 1-A (basis 1) 0]
     map_add' := by intro A B; ext i; fin_cases i <;> simp <;> ring
     map_smul' := by intro r A; ext i; fin_cases i <;> simp <;> ring } :
       (Vec →L[ℝ] Vec) →ₗ[ℝ] Vec).toContinuousLinearMap

lemma curl_eq_curlMap {g : Vec → Vec} (hg : Differentiable ℝ g) (x : Vec) :
    curl g x=curlMap (fderiv ℝ g x) := by
  have hi (i j : Fin 3) : spatialPartial (fun y => g y i) x j=(fderiv ℝ g x (basis j)) i := by
    have hh := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hg x).hasFDerivAt
    change HasFDerivAt (fun y => g y i) _ x at hh
    rw [spatialPartial,hh.fderiv]
    rfl
  ext i
  fin_cases i <;> simp [curl,curlMap,hi]

def divMap : (Vec →L[ℝ] Vec) →L[ℝ] ℝ :=
  ({ toFun := fun A => ∑ i : Fin 3, A (basis i) i
     map_add' := by intro A B; simp [Finset.sum_add_distrib]
     map_smul' := by intro r A; simp [Finset.mul_sum] } :
       (Vec →L[ℝ] Vec) →ₗ[ℝ] ℝ).toContinuousLinearMap

lemma divergence_eq_divMap {g : Vec → Vec} (hg : Differentiable ℝ g) (x : Vec) :
    divergence g x=divMap (fderiv ℝ g x) := by
  change (∑ i : Fin 3, spatialPartial (fun y => g y i) x i)=∑ i : Fin 3, (fderiv ℝ g x) (basis i) i
  apply Finset.sum_congr rfl
  intro i hi
  have hh := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hg x).hasFDerivAt
  change HasFDerivAt (fun y => g y i) _ x at hh
  rw [spatialPartial,hh.fderiv]
  rfl

lemma fderiv_spatial_slice {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} (hF : Differentiable ℝ F) (p : ℝ × U) :
    fderiv ℝ (fun x => F (p.1,x)) p.2=(fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ ℝ U) :=
  ((hF p).hasFDerivAt.comp p.2 ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv

def assembleDerivative {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Dt : W) (Dx : U →L[ℝ] W) : (ℝ × U) →L[ℝ] W :=
  (ContinuousLinearMap.fst ℝ ℝ U).smulRight Dt+Dx.comp (ContinuousLinearMap.snd ℝ ℝ U)

lemma fderiv_eq_assemble {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} (hF : Differentiable ℝ F) (p : ℝ × U) :
    fderiv ℝ F p=assembleDerivative (fderiv ℝ F p (1,0)) (fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  rw [fderiv_spatial_slice hF]
  apply ContinuousLinearMap.ext
  intro z
  change fderiv ℝ F p z=z.1 • fderiv ℝ F p (1,0)+fderiv ℝ F p (0,z.2)
  rw [← map_smul,← map_add]
  congr 1
  ext <;> simp

lemma uniform_assembleDerivative {X U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : ℕ → X → W} {D : ℕ → X → (U →L[ℝ] W)}
    {a : X → W} {d : X → (U →L[ℝ] W)} {S : Set X}
    (hA : TendstoUniformlyOn A a atTop S) (hD : TendstoUniformlyOn D d atTop S) :
    TendstoUniformlyOn (fun n x => assembleDerivative (A n x) (D n x))
      (fun x => assembleDerivative (a x) (d x)) atTop S := by
  have ha := ((ContinuousLinearMap.smulRightL ℝ (ℝ × U) W (ContinuousLinearMap.fst ℝ ℝ U)).uniformContinuous).comp_tendstoUniformlyOn hA
  have hd := (((ContinuousLinearMap.compL ℝ (ℝ × U) U W).flip (ContinuousLinearMap.snd ℝ ℝ U)).uniformContinuous).comp_tendstoUniformlyOn hD
  exact ha.add hd

lemma uniform_clm_apply_bounded {X U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : ℕ → X → (U →L[ℝ] W)} {U' : ℕ → X → U}
    {a : X → (U →L[ℝ] W)} {u : X → U} {S : Set X} {M N : ℝ}
    (hM : 0≤M) (hN : 0≤N)
    (hA : TendstoUniformlyOn A a atTop S) (hu : TendstoUniformlyOn U' u atTop S)
    (hbA : ∀ n, ∀ x∈S, ‖A n x‖≤M) (hbu : ∀ x∈S, ‖u x‖≤N) :
    TendstoUniformlyOn (fun n x => A n x (U' n x)) (fun x => a x (u x)) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(2*(M+N+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hA δ hδ,
    Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with n hnA hnu x hx
  rw [dist_comm,dist_eq_norm]
  have h1 := hnA x hx
  have h2 := hnu x hx
  rw [dist_comm,dist_eq_norm] at h1 h2
  have he : A n x (U' n x)-a x (u x)=A n x (U' n x-u x)+(A n x-a x) (u x) := by simp
  rw [he]
  apply (norm_add_le _ _).trans_lt
  have hb1 : ‖A n x (U' n x-u x)‖≤M*δ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (hbA n x hx) h2.le (norm_nonneg _) hM)
  have hb2 : ‖(A n x-a x) (u x)‖≤δ*N := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul h1.le (hbu x hx) (norm_nonneg _) hδ.le)
  have hd : δ*(2*(M+N+1))=ε := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
  nlinarith

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma c1_slab_uniform_derivative {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℕ → ℝ × U → W} {f : ℝ × U → W} {D : ℝ × U → ((ℝ × U) →L[ℝ] W)} {T : ℝ}
    (hT : 0<T) (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hf : TendstoUniformlyOn F f atTop {p | p.1∈Icc 0 T})
    (hD : TendstoUniformlyOn (fun n p => fderiv ℝ (F n) p) D atTop {p | p.1∈Icc 0 T}) :
    ContDiffOn ℝ 1 f {p | p.1∈Icc 0 T} ∧
      ∀ p, p.1∈Icc 0 T → HasFDerivWithinAt f (D p) {p | p.1∈Icc 0 T} p := by
  have he : {p : ℝ × U | p.1∈Icc 0 T}=Icc 0 T ×ˢ (univ : Set U) := by ext p; simp
  have hconv : Convex ℝ {p : ℝ × U | p.1∈Icc 0 T} := by rw [he]; exact (convex_Icc (𝕜:=ℝ) 0 T).prod (convex_univ : Convex ℝ (univ : Set U))
  have hu : UniqueDiffOn ℝ {p : ℝ × U | p.1∈Icc 0 T} := by rw [he]; exact (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have hDc : ContinuousOn D {p | p.1∈Icc 0 T} := hD.continuousOn
    (Frequently.of_forall fun n => ((hF n).continuous_fderiv (by simp)).continuousOn)
  have hd (p : ℝ × U) (hp : p.1∈Icc 0 T) := hasFDerivWithinAt_uniform_limit_convex hconv hDc
    (fun n q hq => (((hF n).differentiable (by simp)) q).hasFDerivAt.hasFDerivWithinAt)
    hD (fun q hq => hf.tendsto_at hq) hp
  refine ⟨?_,hd⟩
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n:=0) hu).mpr
  exact ⟨by simp, D, contDiffOn_zero.mpr hDc,hd⟩

lemma picard_field_full_derivative_limit {d : Datum} {S : ℕ → Solution}
    {E B : Field} {f : Particle} {T A R P H : ℝ} (_ : 0<T) (hH : 0≤H)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (hc : ∀ n, SpatialFieldCurvature T H (S (n+1)).E (S (n+1)).B)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hbf : LocalParticleBound T A R P f)
    (hfc : ContinuousOn f {p | p.1∈Icc 0 T})
    (hfl : TendstoUniformlyOn (fun n => (S (n+1)).f) f atTop {p | p.1∈Icc 0 T})
    (hEl : TendstoUniformlyOn (fun n => (S (n+1)).E) E atTop {p | p.1∈Icc 0 T})
    (hBl : TendstoUniformlyOn (fun n => (S (n+1)).B) B atTop {p | p.1∈Icc 0 T}) :
    ∃ XE XB : ℝ × Vec → (Vec →L[ℝ] Vec),
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2) XE atTop {p | p.1∈Icc 0 T} ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2) XB atTop {p | p.1∈Icc 0 T} ∧
      (∀ t∈Icc 0 T, ∀ x, HasFDerivAt (fun y => E (t,y)) (XE (t,x)) x ∧
        HasFDerivAt (fun y => B (t,y)) (XB (t,x)) x) ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (S (n+1)).E p)
        (fun p => assembleDerivative (curlMap (XB p)-current (fun z => f (p.1,z)) p.2) (XE p)) atTop {p | p.1∈Icc 0 T} ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (S (n+1)).B p)
        (fun p => assembleDerivative (-curlMap (XE p)) (XB p)) atTop {p | p.1∈Icc 0 T} ∧
      (∀ p : ℝ × Vec, p.1∈Icc 0 T → divMap (XE p)=rho (fun z => f (p.1,z)) p.2 ∧ divMap (XB p)=0) := by
  have hEslice (n : ℕ) (t : ℝ) : Differentiable ℝ (fun x => (S (n+1)).E (t,x)) :=
    ((hr n).smooth_E.differentiable (by simp)).comp ((differentiable_const t).prodMk differentiable_id)
  have hBslice (n : ℕ) (t : ℝ) : Differentiable ℝ (fun x => (S (n+1)).B (t,x)) :=
    ((hr n).smooth_B.differentiable (by simp)).comp ((differentiable_const t).prodMk differentiable_id)
  obtain ⟨XE,hXE,hdE⟩ := uniform_spatial_derivative_limit hH (fun n t ht => hEslice n t)
    (fun n t ht => (hc n t ht).1) hEl
  obtain ⟨XB,hXB,hdB⟩ := uniform_spatial_derivative_limit hH (fun n t ht => hBslice n t)
    (fun n t ht => (hc n t ht).2) hBl
  obtain ⟨hρ,hj⟩ := uniform_source_moments (fun n => (hr n).smooth_f.continuous.continuousOn) hfc hb hbf hfl
  have hcurlE := curlMap.uniformContinuous.comp_tendstoUniformlyOn hXE
  have hcurlB := curlMap.uniformContinuous.comp_tendstoUniformlyOn hXB
  have htE := hcurlB.sub hj
  have htB := hcurlE.neg
  have hfullE := uniform_assembleDerivative htE hXE
  have hfullB := uniform_assembleDerivative htB hXB
  have he (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) :
      fderiv ℝ (S (n+1)).E p=assembleDerivative
        (curlMap (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2)-current (fun z => (S (n+1)).f (p.1,z)) p.2)
        (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2) := by
    rw [fderiv_eq_assemble ((hr n).smooth_E.differentiable (by simp))]
    congr 1
    have hh := ((hr n).maxwell p.1 hp.1 p.2).1
    rw [spaceCurl_slice ((hr n).smooth_B.differentiable (by simp)),curl_eq_curlMap (hBslice n p.1)] at hh
    exact hh
  have hb' (n : ℕ) (p : ℝ × Vec) (hp : p.1∈Icc 0 T) :
      fderiv ℝ (S (n+1)).B p=assembleDerivative
        (-curlMap (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2))
        (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2) := by
    rw [fderiv_eq_assemble ((hr n).smooth_B.differentiable (by simp))]
    congr 1
    have hh := ((hr n).maxwell p.1 hp.1 p.2).2.1
    rw [spaceCurl_slice ((hr n).smooth_E.differentiable (by simp)),curl_eq_curlMap (hEslice n p.1)] at hh
    exact hh
  refine ⟨XE,XB,hXE,hXB,fun t ht x => ⟨hdE t ht x,hdB t ht x⟩,
    hfullE.congr (Eventually.of_forall fun n p hp => (he n p hp).symm),
    hfullB.congr (Eventually.of_forall fun n p hp => (hb' n p hp).symm),?_⟩
  intro p hp
  have hde := (divMap.uniformContinuous.comp_tendstoUniformlyOn hXE).tendsto_at hp
  have hdb := (divMap.uniformContinuous.comp_tendstoUniformlyOn hXB).tendsto_at hp
  have heq (n : ℕ) : divMap (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2)=rho (fun z => (S (n+1)).f (p.1,z)) p.2 := by
    rw [← divergence_eq_divMap (hEslice n p.1),← spaceDiv_slice ((hr n).smooth_E.differentiable (by simp))]
    exact ((hr n).maxwell p.1 hp.1 p.2).2.2.1
  have hbq (n : ℕ) : divMap (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2)=0 := by
    rw [← divergence_eq_divMap (hBslice n p.1),← spaceDiv_slice ((hr n).smooth_B.differentiable (by simp))]
    exact ((hr n).maxwell p.1 hp.1 p.2).2.2.2
  change Tendsto (fun n => divMap (fderiv ℝ (fun x => (S (n+1)).E (p.1,x)) p.2)) _ _ at hde
  change Tendsto (fun n => divMap (fderiv ℝ (fun x => (S (n+1)).B (p.1,x)) p.2)) _ _ at hdb
  simp only [heq,hbq] at hde hdb
  exact ⟨tendsto_nhds_unique hde (hρ.tendsto_at hp),tendsto_nhds_unique hdb tendsto_const_nhds⟩

end RVM

end

end OAI
