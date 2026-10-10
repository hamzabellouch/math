import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardBounds
import OAI.Analysis.VlasovMaxwell.Retarded.PicardKernel
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardBoundary

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma velocity_global_lipschitz (v w : Vec) : ‖velocity w-velocity v‖≤‖w-v‖ := by
  have hh := (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (contDiff_velocity (k:=1)).differentiable (by norm_num) x)
    (C:=1) (fun x _ => (norm_fderiv_velocity_le x).trans ((inv_le_one₀ (q_pos x)).mpr (by
      have hq := q_sq x
      nlinarith [q_pos x,sq_nonneg ‖x‖]))) (mem_univ v) (mem_univ w)
  simpa only [one_mul] using hh

lemma lorentzField_difference_bound {E B E' B' : Field} {t L N D : ℝ}
    (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (hB : ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ x, ‖B (t,x)-B' (t,x)‖≤D) (z z' : Phase) :
    ‖lorentzField E B (t,z)-lorentzField E' B' (t,z')‖≤(1+2*N+L)*‖z-z'‖+2*D := by
  have hpos : ‖z.1-z'.1‖≤‖z-z'‖ := by simpa only [Prod.fst_sub] using norm_fst_le (z-z')
  have hvel : ‖z.2-z'.2‖≤‖z-z'‖ := by simpa only [Prod.snd_sub] using norm_snd_le (z-z')
  have hu : ‖velocity z.2‖≤1 := (norm_velocity_lt_one _).le
  have hu' : ‖velocity z'.2‖≤1 := (norm_velocity_lt_one _).le
  have hUd : ‖velocity z.2-velocity z'.2‖≤‖z-z'‖ := (velocity_global_lipschitz z'.2 z.2).trans hvel
  have hF : ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))-
      (E' (t,z'.1)+cross (velocity z'.2) (B' (t,z'.1)))‖≤(2*N+L)*‖z-z'‖+2*D := by
    have he : E (t,z.1)+cross (velocity z.2) (B (t,z.1))-
        (E' (t,z'.1)+cross (velocity z'.2) (B' (t,z'.1)))=
        (E (t,z.1)-E (t,z'.1))+(E (t,z'.1)-E' (t,z'.1))+
        cross (velocity z.2-velocity z'.2) (B (t,z.1))+
        cross (velocity z'.2) (B (t,z.1)-B (t,z'.1))+
        cross (velocity z'.2) (B (t,z'.1)-B' (t,z'.1)) := by
      rw [cross_sub_left,cross_sub_right,cross_sub_right]
      abel
    rw [he]
    have h₁ := (hEx z'.1 z.1).trans (mul_le_mul_of_nonneg_left hpos hN)
    have h₂ := hEd z'.1
    have h₃ := (norm_cross_le _ _).trans (mul_le_mul hUd (hB z.1) (norm_nonneg _) (norm_nonneg _))
    have h₄ := (norm_cross_le _ _).trans (mul_le_mul hu' ((hBx z'.1 z.1).trans
      (mul_le_mul_of_nonneg_left hpos hN)) (norm_nonneg _) zero_le_one)
    have h₅ := (norm_cross_le _ _).trans (mul_le_mul hu' (hBd z'.1) (norm_nonneg _) zero_le_one)
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄)) h₅)
    exact hh.trans_eq (by ring)
  simp only [lorentzField]
  rw [Prod.norm_def]
  simp only [Prod.fst_sub,Prod.snd_sub]
  apply max_le
  · exact hUd.trans (by nlinarith [norm_nonneg (z-z')])
  · exact hF.trans (by nlinarith [norm_nonneg (z-z')])

lemma gronwallBound_le_exp_linear {δ K ε t : ℝ} (hK : 0<K) (hε : 0≤ε) (_ht : 0≤t) :
    gronwallBound δ K ε t≤(δ+ε*t)*Real.exp (K*t) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  have h := Real.add_one_le_exp (-(K*t))
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (K*t)).le
  rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero (K*t))] at hmul
  have hx : Real.exp (K*t)-1≤K*t*Real.exp (K*t) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hx (div_nonneg hε hK.le)
  have he : ε/K*(K*t*Real.exp (K*t))=ε*t*Real.exp (K*t) := by field_simp
  rw [he] at hh
  nlinarith

lemma SmoothLorentzFlow.backward_stability {E B E' B' : Field}
    (F : SmoothLorentzFlow E B) (G : SmoothLorentzFlow E' B') {T L N D : ℝ}
    (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (hB : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)-B' (t,x)‖≤D)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    ‖F.backward (t,z)-G.backward (t,z')‖≤
      (‖z-z'‖+2*D*t)*Real.exp ((1+2*N+L)*t) := by
  let α : ℝ → Phase := fun u => F.forward (F.backward (t,z)) (t-u)
  let β : ℝ → Phase := fun u => G.forward (G.backward (t,z')) (t-u)
  let K := 1+2*N+L
  have hK : 0<K := by dsimp [K]; linarith
  have hα (u : ℝ) : HasDerivAt α (-lorentzField E B (t-u,α u)) u := by
    have hh := (F.ode (F.backward (t,z)) (t-u)).scomp u ((hasDerivAt_id u).const_sub t)
    simpa only [α, Function.comp_def,one_smul,neg_smul] using hh
  have hβ (u : ℝ) : HasDerivAt β (-lorentzField E' B' (t-u,β u)) u := by
    have hh := (G.ode (G.backward (t,z')) (t-u)).scomp u ((hasDerivAt_id u).const_sub t)
    simpa only [β, Function.comp_def,one_smul,neg_smul] using hh
  have hfc : ContinuousOn (fun u => α u-β u) (Icc 0 t) :=
    (continuous_iff_continuousAt.mpr fun u => (hα u).continuousAt).continuousOn.sub
      (continuous_iff_continuousAt.mpr fun u => (hβ u).continuousAt).continuousOn
  have h₀ : ‖α 0-β 0‖≤‖z-z'‖ := by simp [α,β,F.right_inverse,G.right_inverse]
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hfc
    (fun u _ => ((hα u).sub (hβ u)).hasDerivWithinAt) (K:=K) (ε:=2*D) h₀
    (fun u hu => by
      have htime : t-u∈Icc 0 T := ⟨by linarith [hu.2],by linarith [ht.2,hu.1]⟩
      simpa only [neg_sub_neg,norm_sub_rev] using
        lorentzField_difference_bound hL hN hD (hB _ htime) (hEx _ htime) (hBx _ htime)
          (hEd _ htime) (hBd _ htime) (α u) (β u)) t ⟨ht.1,le_rfl⟩
  simp only [α,β,sub_self,F.initial,G.initial,sub_zero] at hh
  exact hh.trans (gronwallBound_le_exp_linear hK (by positivity) ht.1)

lemma transported_comparison {d : Datum} {s s' : Solution} {E B E' B' : Field}
    (hf : ContDiff ℝ ∞ s.f) (hg : ContDiff ℝ ∞ s'.f)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hV : TransportFor s E B) (hV' : TransportFor s' E' B')
    (h₀ : ∀ z, s.f (0,z)=d.f₀ z) (h₀' : ∀ z, s'.f (0,z)=d.f₀ z)
    {T A L N D : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)-B' (t,x)‖≤D)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    |s.f (t,z)-s'.f (t,z')|≤A*(‖z-z'‖+2*D*t)*Real.exp ((1+2*N+L)*t) := by
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  obtain ⟨G⟩ := exists_smoothLorentzFlow hE' hB'
  rw [F.transport_for_inverse hf hV,G.transport_for_inverse hg hV',h₀,h₀']
  exact (ha _ _).trans ((mul_le_mul_of_nonneg_left
    (F.backward_stability G hL hN hD hBb hEx hBx hEd hBd ht z z') hA).trans_eq (by ring))

lemma transported_spatial_lipschitz {d : Datum} {s : Solution} {E B : Field}
    (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hV : TransportFor s E B) {T A L N : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N)
    (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    |s.f (t,z)-s.f (t,z')|≤(A*Real.exp ((1+2*N+L)*T))*‖z-z'‖ := by
  have hh := transported_comparison hs.smooth_f hs.smooth_f hE hB hE hB hV hV
    hs.initial_f hs.initial_f hA hL hN (D:=0) le_rfl ha hBb hEx hBx
      (by intros; simp) (by intros; simp) ht z z'
  simp only [mul_zero,zero_mul,add_zero] at hh
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith : 0≤1+2*N+L))
  exact hh.trans ((mul_le_mul_of_nonneg_left he (mul_nonneg hA (norm_nonneg _))).trans_eq (by ring))

lemma norm_boundary_integral_difference {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F G : Vec → W} {a b : W} {t C D : ℝ} (ht : 0≤t)
    (hF : IntegrableOn F (ball (0:Vec) t)) (hG : IntegrableOn G (ball (0:Vec) t))
    (hab : ‖a-b‖≤D)
    (hFG : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t → ‖F z-G z‖≤C/‖z‖^2) :
    ‖(a+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z)-
      (b+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, G z)‖≤D+C*t := by
  rw [show (a+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z)-
      (b+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, G z)=
      (a-b)+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, (F z-G z) by
        rw [integral_sub hF hG,smul_sub]; abel]
  apply (norm_add_le _ _).trans (add_le_add hab ?_)
  apply scaled_kernel_tip_le_on ht (hF.sub hG)
  filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  exact hFG z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le

lemma mixed_fields_difference_bound {d : Datum} {s s' : Solution} {E B E' B' : Field}
    (hs : PicardRegular d s) (hs' : PicardRegular d s')
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hV : TransportFor s E B) (hV' : TransportFor s' E' B')
    {t C D : ℝ} (ht : 0<t) (x x' : Vec)
    (hb : ‖electricBoundaryField (datumBoundarySolution d) t x-
        electricBoundaryField (datumBoundarySolution d) t x'‖≤D ∧
      ‖magneticBoundaryField (datumBoundarySolution d) t x-
        magneticBoundaryField (datumBoundarySolution d) t x'‖≤D)
    (hden : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
      ‖retardedElectricDensity {s with E:=E,B:=B} t x (x+z)-
        retardedElectricDensity {s' with E:=E',B:=B'} t x' (x'+z)‖≤C/‖z‖^2 ∧
      ‖retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)-
        retardedMagneticDensity {s' with E:=E',B:=B'} t x' (x'+z)‖≤C/‖z‖^2) :
    ‖s.E (t,x)-s'.E (t,x')‖≤D+C*t ∧ ‖s.B (t,x)-s'.B (t,x')‖≤D+C*t := by
  have he := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell ht x
  have he' := mixed_physical_vector hs'.smooth_f hE' hB' hs'.smooth_E hs'.smooth_B hs'.compact hV'
    hs'.smooth_rho hs'.smooth_current hs'.maxwell ht x'
  have hf1 := (hs.smooth_f.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=particleHalfSpace)
  have hg1 := (hs'.smooth_f.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=particleHalfSpace)
  have hE1 := (hE.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hB1 := (hB.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hE1' := (hE'.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hB1' := (hB'.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hbe := hs.boundary_eq ht x
  have hbe' := hs'.boundary_eq ht x'
  constructor
  · rw [he.1,he'.1,hbe.1,hbe'.1]
    exact norm_boundary_integral_difference ht.le
      (integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
      (integrableOn_retardedElectricDensity_le (s:={s' with E:=E',B:=B'}) hg1 hE1' hB1' hs'.compact ht.le le_rfl x')
      hb.1 (fun z hz hzt => (hden z hz hzt).1)
  · rw [he.2,he'.2,hbe.2,hbe'.2]
    exact norm_boundary_integral_difference ht.le
      (integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
      (integrableOn_retardedMagneticDensity_le (s:={s' with E:=E',B:=B'}) hg1 hE1' hB1' hs'.compact ht.le le_rfl x')
      hb.2 (fun z hz hzt => (hden z hz hzt).2)

def GlobalFieldBound (T L : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, ∀ x : Vec, ‖E (t,x)‖≤L ∧ ‖B (t,x)‖≤L

def SpatialFieldLip (T N : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, ∀ x y : Vec,
    ‖E (t,y)-E (t,x)‖≤N*‖y-x‖ ∧ ‖B (t,y)-B (t,x)‖≤N*‖y-x‖

theorem uniform_global_picard_invariance {d : Datum} (hd : Admissible d) :
    ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
      GlobalFieldBound T L (fun p : ℝ × Vec => d.E₀ p.2) (fun p : ℝ × Vec => d.B₀ p.2) ∧
      ∀ U : ℝ, 0≤U → U≤T → ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → GlobalFieldBound U L E B →
        ∀ s : Solution, PicardRegular d s → TransportFor s E B →
          LocalParticleBound U A R P s.f ∧ GlobalFieldBound U L s.E s.B := by
  obtain ⟨A,R₀,P₀,hA,hR₀,hP₀,hf₀,hphase₀⟩ := datum_particle_bounds hd
  let R := R₀+1
  let P := P₀+1
  obtain ⟨D,hD,hDEB,hboundary⟩ := datum_boundary_global_bound hd
  let L := D+1
  have hL : 0<L := by dsimp [L]; linarith
  obtain ⟨C,hC,hdensity⟩ := uniform_retarded_density_bound A P L hA
  let T := min 1 (min ((2*L+1)⁻¹) ((C+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : T≤1 := min_le_left _ _
  have hT2 : T≤(2*L+1)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hT3 : T≤(C+1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hLT : 2*L*T≤1 := by
    have hh : T*(2*L+1)≤1 := (le_div_iff₀ (by positivity : 0<2*L+1)).mp (by simpa only [one_div] using hT2)
    nlinarith
  have hCT : C*T≤1 := by
    have hh : T*(C+1)≤1 := (le_div_iff₀ (by positivity : 0<C+1)).mp (by simpa only [one_div] using hT3)
    nlinarith
  refine ⟨T,A,R,P,L,hT,hT1,hA,by dsimp [R]; linarith,by dsimp [P]; linarith,hL,?_,?_⟩
  · intro t ht x
    exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
      (hDEB x).2.trans (by dsimp [L]; linarith)⟩
  · intro U hU0 hU E B hE hB hEB s hs hV
    have hU1 : U≤1 := hU.trans hT1
    have hLU : 2*L*U≤1 := (mul_le_mul_of_nonneg_left hU (by positivity)).trans hLT
    have hCU : C*U≤1 := (mul_le_mul_of_nonneg_left hU hC).trans hCT
    obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
    have hf : ∀ t∈Icc 0 U, ∀ z, |s.f (t,z)|≤A := by
      intro t ht z
      exact F.transported_sup_bound hs.smooth_f hV (fun z => by rw [hs.initial_f]; exact hf₀ z) t z
    have hphase : ∀ t∈Icc 0 U, ∀ z : Phase, s.f (t,z)≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P := by
      intro t ht z hz
      have hh := F.transported_phase_bound hs.smooth_f hV
        (R₀:=R₀) (P₀:=P₀) (T:=U) (L:=L)
        (fun z hz => hphase₀ z (by simpa only [hs.initial_f] using hz)) hL.le
        (fun r hr x hx => (hEB r hr x).1)
        (fun r hr x hx => (hEB r hr x).2) ht z hz
      constructor
      · dsimp [R]
        linarith [hh.1,ht.2]
      · dsimp [P]
        have hh' : 2*L*t≤2*L*U := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        linarith [hh.2]
    refine ⟨fun t ht x v => ⟨hf t ht (x,v),hphase t ht (x,v)⟩,?_⟩
    intro t ht x
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_B]
      exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
        (hDEB x).2.trans (by dsimp [L]; linarith)⟩
    · have hbd := hboundary t ⟨ht0,ht.2.trans hU1⟩ x
      rw [← (hs.boundary_eq ht0 x).1,← (hs.boundary_eq ht0 x).2] at hbd
      have hdens := hdensity {s with E:=E,B:=B} U hU1 hf (by
        intro r hr y v hv
        exact ⟨(hphase r hr (y,v) hv).2,hEB r hr y⟩) t ht x
      have hh := mixed_fields_bound hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
        hs.smooth_rho hs.smooth_current hs.maxwell ht0 x hbd hdens
      have hh' : C*t≤C*U := mul_le_mul_of_nonneg_left ht.2 hC
      have hbound : D+C*t≤L := by dsimp [L]; linarith
      exact ⟨hh.1.trans hbound,hh.2.trans hbound⟩

lemma uniform_picard_comparison (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (d : Datum) (s s' : Solution) (E B E' B' : Field),
      PicardRegular d s → PicardRegular d s' →
      ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → ContDiff ℝ ∞ E' → ContDiff ℝ ∞ B' →
      TransportFor s E B → TransportFor s' E' B' →
      ∀ T : ℝ, T≤1 →
      (∀ r∈Icc 0 T, ∀ x v, |s.f (r,x,v)|≤A ∧ |s'.f (r,x,v)|≤A) →
      (∀ r∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (r,x,v)=0 ∧ s'.f (r,x,v)=0) →
      GlobalFieldBound T L E B → GlobalFieldBound T L E' B' →
      ∀ t∈Ioc 0 T, ∀ x x' : Vec, ∀ D H J : ℝ,
      (‖electricBoundaryField (datumBoundarySolution d) t x-
          electricBoundaryField (datumBoundarySolution d) t x'‖≤D ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t x-
          magneticBoundaryField (datumBoundarySolution d) t x'‖≤D) →
      (∀ r∈Icc 0 T, ∀ z v, |s.f (r,x+z,v)-s'.f (r,x'+z,v)|≤H) →
      (∀ r∈Icc 0 T, ∀ z, ‖E (r,x+z)-E' (r,x'+z)‖≤J ∧
        ‖B (r,x+z)-B' (r,x'+z)‖≤J) →
      ‖s.E (t,x)-s'.E (t,x')‖≤D+C*(max H J)*t ∧
      ‖s.B (t,x)-s'.B (t,x')‖≤D+C*(max H J)*t := by
  obtain ⟨C,hC,hk⟩ := uniform_retarded_density_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro d s s' E B E' B' hs hs' hE hB hE' hB' hV hV' T hT hab hp hEB hEB' t ht x x' D H J hb hf hdiff
  apply mixed_fields_difference_bound hs hs' hE hB hE' hB' hV hV' ht.1 x x' hb
  intro z hz hzt
  have hr : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  exact hk {s with E:=E,B:=B} {s' with E:=E',B:=B'} T hT hs.smooth_f hs'.smooth_f
    hs.compact hs'.compact hab hp
    (fun r hr y => ⟨(hEB r hr y).1,(hEB r hr y).2,(hEB' r hr y).1,(hEB' r hr y).2⟩)
    t ⟨ht.1.le,ht.2⟩ x x' z hz hzt (max H J)
    (fun v => (hf _ hr z v).trans (le_max_left _ _))
    ((hdiff _ hr z).1.trans (le_max_right _ _)) ((hdiff _ hr z).2.trans (le_max_right _ _))

def FieldControl (T L N : ℝ) (E B : Field) : Prop :=
  GlobalFieldBound T L E B ∧ SpatialFieldLip T N E B

def PhaseParticleLip (T M : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc 0 T, ∀ z z' : Phase, |f (t,z)-f (t,z')|≤M*‖z-z'‖

theorem uniform_picard_control {d : Datum} (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      FieldControl T L N (fun p : ℝ × Vec => d.E₀ p.2) (fun p : ℝ × Vec => d.B₀ p.2) ∧
      (∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → FieldControl T L N E B →
        ∀ s : Solution, PicardRegular d s → TransportFor s E B →
          LocalParticleBound T A R P s.f ∧ PhaseParticleLip T M s.f ∧ FieldControl T L N s.E s.B) ∧
      (∀ (E B E' B' : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
        ContDiff ℝ ∞ E' → ContDiff ℝ ∞ B' → FieldControl T L N E B → FieldControl T L N E' B' →
        ∀ (s s' : Solution), PicardRegular d s → PicardRegular d s' →
          TransportFor s E B → TransportFor s' E' B' →
        ∀ D : ℝ, 0≤D →
          (∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D ∧ ‖B (t,x)-B' (t,x)‖≤D) →
          ∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)-s'.E (t,x)‖≤D/2 ∧ ‖s.B (t,x)-s'.B (t,x)‖≤D/2) := by
  obtain ⟨T₀,A,R,P,L,hT₀,hT₀1,hA,hR,hP,hL,h₀,hstep⟩ := uniform_global_picard_invariance hd
  obtain ⟨D₀,hD₀,hDinit,hDb⟩ := datum_boundary_global_lipschitz hd
  obtain ⟨A₁,hA₁,hAf⟩ := smooth_compact_lipschitz (hd.1.of_le (by simp)) hd.2.1
  have hAf' (z w : Phase) : |d.f₀ z-d.f₀ w|≤A₁*‖z-w‖ := by
    simpa only [Real.norm_eq_abs] using hAf w z
  obtain ⟨C,hC,hcomp⟩ := uniform_picard_comparison A P L
  let N := D₀+1
  let M := A₁*Real.exp 1
  let K := 1+2*N+L
  have hN : 0<N := by dsimp [N]; linarith
  have hM : 0≤M := by dsimp [M]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  let T := min T₀ (min K⁻¹ (min (C*(M+N)+1)⁻¹ (2*C*(2*M+1)+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hTT : T≤T₀ := min_le_left _ _
  have hT1 : T≤1 := hTT.trans hT₀1
  have hTK : K*T≤1 := by
    have hh : T≤K⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ hK).mp (show T≤1/K by simpa only [one_div] using hh)
    nlinarith
  have hTC : C*(M+N)*T≤1 := by
    have hh : T≤(C*(M+N)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<C*(M+N)+1)).mp
      (show T≤1/(C*(M+N)+1) by simpa only [one_div] using hh)
    nlinarith
  have hTC' : 2*C*(2*M+1)*T≤1 := by
    have hh : T≤(2*C*(2*M+1)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<2*C*(2*M+1)+1)).mp
      (show T≤1/(2*C*(2*M+1)+1) by simpa only [one_div] using hh)
    nlinarith
  have hexp {r : ℝ} (hr : r≤T) : Real.exp (K*r)≤Real.exp 1 :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hr hK.le).trans hTK)
  have hbase {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular d s) (hV : TransportFor s E B) :=
    hstep T hT.le hTT E B hE hB hc.1 s hs hV
  have hflip {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular d s) (hV : TransportFor s E B) :
      PhaseParticleLip T M s.f := by
    intro t ht z z'
    have hh := transported_spatial_lipschitz hs hE hB hV hA₁ hL.le hN.le hAf'
      (fun r hr x => (hc.1 r hr x).2) (fun r hr x y => (hc.2 r hr x y).1)
      (fun r hr x y => (hc.2 r hr x y).2) ht z z'
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp le_rfl) hA₁) (norm_nonneg _))
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_,?_,?_⟩
  · constructor
    · exact fun t ht x => h₀ t ⟨ht.1,ht.2.trans hTT⟩ x
    · intro t ht x y
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
  · intro E B hE hB hc s hs hV
    have hp := (hbase hE hB hc hs hV).1
    have hf := hflip hE hB hc hs hV
    refine ⟨hp,hf,(hbase hE hB hc hs hV).2,?_⟩
    intro t ht x y
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_E,hs.initial_B,hs.initial_B]
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
    · have hh := hcomp d s s E B E B hs hs hE hB hE hB hV hV T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp r hr z v).1⟩)
        (by
          intro r hr z v hv
          have hz : s.f (r,z,v)=0 := by
            by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          exact ⟨hz,hz⟩)
        hc.1 hc.1 t ⟨ht0,ht.2⟩ y x (D₀*‖y-x‖) (M*‖y-x‖) (N*‖y-x‖)
        (hDb t ⟨ht0,ht.2.trans hT1⟩ x y)
        (by
          intro r hr z v
          simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
            max_eq_left (norm_nonneg _),add_sub_add_right_eq_sub] using hf r hr (y+z,v) (x+z,v))
        (by
          intro r hr z
          simpa only [add_sub_add_right_eq_sub] using hc.2 r hr (x+z) (y+z))
      have hm : max (M*‖y-x‖) (N*‖y-x‖)≤(M+N)*‖y-x‖ := by
        apply max_le <;> nlinarith [norm_nonneg (y-x)]
      have hb : D₀*‖y-x‖+C*max (M*‖y-x‖) (N*‖y-x‖)*t≤N*‖y-x‖ := by
        calc
          _ ≤ D₀*‖y-x‖+C*((M+N)*‖y-x‖)*T := add_le_add le_rfl
            (mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity))
          _ = (D₀+C*(M+N)*T)*‖y-x‖ := by ring
          _ ≤ N*‖y-x‖ := mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩
  · intro E B E' B' hE hB hE' hB' hc hc' s s' hs hs' hV hV' D hD hdiff t ht x
    have hp := (hbase hE hB hc hs hV).1
    have hp' := (hbase hE' hB' hc' hs' hV').1
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      simp only [hs.initial_E,hs'.initial_E,hs.initial_B,hs'.initial_B,sub_self,norm_zero]
      exact ⟨by positivity,by positivity⟩
    · have hfd (r : ℝ) (hr : r∈Icc 0 T) (z : Phase) : |s.f (r,z)-s'.f (r,z)|≤2*M*D := by
        have hh := transported_comparison hs.smooth_f hs'.smooth_f hE hB hE' hB' hV hV'
          hs.initial_f hs'.initial_f hA₁ hL.le hN.le hD hAf'
          (fun u hu w => (hc.1 u hu w).2) (fun u hu w w' => (hc.2 u hu w w').1)
          (fun u hu w w' => (hc.2 u hu w w').2)
          (fun u hu w => (hdiff u hu w).1) (fun u hu w => (hdiff u hu w).2) hr z z
        simp only [sub_self,norm_zero,zero_add] at hh
        apply hh.trans
        calc
          A₁*(2*D*r)*Real.exp ((1+2*N+L)*r) = (2*D*r)*(A₁*Real.exp (K*r)) := by ring
          _ ≤ (2*D*r)*M := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hexp hr.2) hA₁) (mul_nonneg (mul_nonneg (by norm_num) hD) hr.1)
          _ ≤ (2*D*1)*M := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hr.2.trans hT1) (by positivity)) hM
          _ = 2*M*D := by ring
      have hh := hcomp d s s' E B E' B' hs hs' hE hB hE' hB' hV hV' T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp' r hr z v).1⟩)
        (by
          intro r hr z v hv
          constructor
          · by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          · by_contra hn
            exact (not_lt_of_ge ((hp' r hr z v).2 hn).2) hv)
        hc.1 hc'.1 t ⟨ht0,ht.2⟩ x x 0 (2*M*D) D (by simp)
        (fun r hr z v => hfd r hr (x+z,v)) (fun r hr z => hdiff r hr (x+z))
      have hm : max (2*M*D) D≤(2*M+1)*D := by apply max_le <;> nlinarith
      have hb : 0+C*max (2*M*D) D*t≤D/2 := by
        calc
          _ ≤ C*((2*M+1)*D)*T := by
            simpa only [zero_add] using mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity)
          _ = (2*C*(2*M+1)*T)*(D/2) := by ring
          _ ≤ 1*(D/2) := mul_le_mul_of_nonneg_right hTC' (by positivity)
          _ = D/2 := one_mul _
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩

theorem exists_contractive_picard_sequence {d : Datum} (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∃ S : ℕ → Solution, S 0=datumBoundarySolution d ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        ∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,h₀,hstep,hcontract⟩ := uniform_picard_control hd
  let Q := {s : Solution // ContDiff ℝ ∞ s.E ∧ ContDiff ℝ ∞ s.B}
  have hchoose (q : Q) : ∃ r : Q, PicardRegular d r.1 ∧ TransportFor r.1 q.1.E q.1.B := by
    obtain ⟨s,hs,hV⟩ := exists_picard_regular hd q.2.1 q.2.2
    exact ⟨⟨s,hs.smooth_E,hs.smooth_B⟩,hs,hV⟩
  choose step hs using hchoose
  let q₀ : Q := ⟨datumBoundarySolution d,
    hd.2.2.2.1.1.comp contDiff_snd,hd.2.2.2.2.1.1.comp contDiff_snd⟩
  let q : ℕ → Q := fun n => step^[n] q₀
  have hrec (n : ℕ) : q (n+1)=step (q n) := Function.iterate_succ_apply' step n q₀
  have hbound (n : ℕ) : FieldControl T L N (q n).1.E (q n).1.B := by
    induction n with
    | zero => exact h₀
    | succ n ih =>
      rw [hrec]
      exact (hstep _ _ (q n).2.1 (q n).2.2 ih _ (hs (q n)).1 (hs (q n)).2).2.2
  have hreg (n : ℕ) : PicardRegular d (q (n+1)).1 ∧ TransportFor (q (n+1)).1 (q n).1.E (q n).1.B ∧
      LocalParticleBound T A R P (q (n+1)).1.f ∧ PhaseParticleLip T M (q (n+1)).1.f := by
    rw [hrec]
    exact ⟨(hs (q n)).1,(hs (q n)).2,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).1,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).2.1⟩
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,fun n => (q n).1,rfl,
    fun n => (q n).2,hbound,hreg,?_⟩
  intro n
  induction n with
  | zero =>
    intro t ht x
    have h0 := (hbound 0).1 t ht x
    have h1 := (hbound 1).1 t ht x
    simp only [pow_zero,mul_one]
    constructor
    · exact (norm_sub_le _ _).trans (by linarith [h0.1,h1.1])
    · exact (norm_sub_le _ _).trans (by linarith [h0.2,h1.2])
  | succ n ih =>
    have hh := hcontract (q (n+1)).1.E (q (n+1)).1.B (q n).1.E (q n).1.B
      (q (n+1)).2.1 (q (n+1)).2.2 (q n).2.1 (q n).2.2 (hbound (n+1)) (hbound n)
      (q (n+1+1)).1 (q (n+1)).1 (hreg (n+1)).1 (hreg n).1 (hreg (n+1)).2.1 (hreg n).2.1
      (2*L*(1/2:ℝ)^n) (by positivity) ih
    intro t ht x
    convert hh t ht x using 1 <;> rw [pow_succ] <;> ring_nf

lemma exists_uniform_limit_geometric {X W : Type*} [NormedAddCommGroup W] [CompleteSpace W]
    {F : ℕ → X → W} {S : Set X} {C : ℝ}
    (h : ∀ n, ∀ x∈S, ‖F (n+1) x-F n x‖≤C*(1/2:ℝ)^n) :
    ∃ f : X → W, TendstoUniformlyOn F f atTop S := by
  let g : ℕ → X → W := fun n x => F (n+1) x-F n x
  have hu : Summable (fun n => C*(1/2:ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).mul_left C
  have hh := tendstoUniformlyOn_tsum_nat hu (f:=g) h
  refine ⟨fun x => F 0 x+∑' n, g n x,?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x hx
  have he : (∑ i∈Finset.range n, g i x)=F n x-F 0 x := Finset.sum_range_sub (fun n => F n x) n
  specialize hn x hx
  rw [he,dist_eq_norm] at hn
  rw [dist_eq_norm]
  convert hn using 1
  congr 1
  abel

theorem exists_picard_field_limit {d : Datum} (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∃ (S : ℕ → Solution) (E B : Field), S 0=datumBoundarySolution d ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        (∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) ∧
        TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T} ∧
        TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T} ∧
        ContinuousOn E {p | p.1∈Icc 0 T} ∧ ContinuousOn B {p | p.1∈Icc 0 T} ∧
        FieldControl T L N E B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,S,hS0,hsm,hc,hr,hg⟩ := exists_contractive_picard_sequence hd
  obtain ⟨E,hE⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).E) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).1)
  obtain ⟨B,hB⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).B) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).2)
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,S,E,B,hS0,hsm,hc,hr,hg,hE,hB,
    hE.continuousOn (Frequently.of_forall fun n => (hsm n).1.continuous.continuousOn),
    hB.continuousOn (Frequently.of_forall fun n => (hsm n).2.continuous.continuousOn),?_,?_⟩
  · intro t ht x
    exact ⟨le_of_tendsto (hE.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.1),
      le_of_tendsto (hB.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.2)⟩
  · intro t ht x y
    exact ⟨le_of_tendsto ((hE.tendsto_at (x:=(t,y)) ht).sub (hE.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.1),
      le_of_tendsto ((hB.tendsto_at (x:=(t,y)) ht).sub (hB.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.2)⟩

lemma geometric_picard_particle_differences {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T L N : ℝ} (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B)
    (hg : ∀ n, ∀ t∈Icc 0 T, ∀ x,
      ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
      ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) :
    ∃ C : ℝ, 0≤C ∧ ∀ n, ∀ t∈Icc 0 T, ∀ z : Phase,
      |(S (n+1+1)).f (t,z)-(S (n+1)).f (t,z)|≤C*(1/2:ℝ)^n := by
  obtain ⟨A,hA,hAf⟩ := smooth_compact_lipschitz (hd.1.of_le (by simp)) hd.2.1
  let K := 1+2*N+L
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨4*A*Real.exp (K*T)*L*T,by positivity,?_⟩
  intro n t ht z
  have hh := transported_comparison (hr (n+1)).1.smooth_f (hr n).1.smooth_f
    (hsm (n+1)).1 (hsm (n+1)).2 (hsm n).1 (hsm n).2 (hr (n+1)).2 (hr n).2
    (hr (n+1)).1.initial_f (hr n).1.initial_f hA hL hN (D:=2*L*(1/2:ℝ)^n) (by positivity)
    (fun z w => by simpa only [Real.norm_eq_abs] using hAf w z)
    (fun r hr x => ((hc (n+1)).1 r hr x).2)
    (fun r hr x y => ((hc (n+1)).2 r hr x y).1)
    (fun r hr x y => ((hc (n+1)).2 r hr x y).2)
    (fun r hr x => (hg n r hr x).1) (fun r hr x => (hg n r hr x).2) ht z z
  simp only [sub_self,norm_zero,zero_add] at hh
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
  apply hh.trans
  calc
    _ ≤ A*(2*(2*L*(1/2:ℝ)^n)*T)*Real.exp (K*T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ht.2 (by positivity)) hA) he (Real.exp_pos _).le (by positivity)
    _ = (4*A*Real.exp (K*T)*L*T)*(1/2:ℝ)^n := by ring

lemma picard_particle_limit {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T A R P L N M : ℝ} (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
      LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f)
    (hg : ∀ n, ∀ t∈Icc 0 T, ∀ x,
      ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
      ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) :
    ∃ f : Particle, TendstoUniformlyOn (fun n => (S (n+1)).f) f atTop {p | p.1∈Icc 0 T} ∧
      ContinuousOn f {p | p.1∈Icc 0 T} ∧ (∀ t∈Icc 0 T, ∀ z, 0≤f (t,z)) ∧
      (∀ z, f (0,z)=d.f₀ z) ∧ LocalParticleBound T A R P f ∧ PhaseParticleLip T M f := by
  obtain ⟨C,hC,hg'⟩ := geometric_picard_particle_differences hd hT hL hN hsm hc
    (fun n => ⟨(hr n).1,(hr n).2.1⟩) hg
  obtain ⟨f,hf⟩ := exists_uniform_limit_geometric (F:=fun n => (S (n+1)).f) (C:=C)
    (fun n (p : ℝ × Phase) (hp : p.1∈Icc 0 T) => by simpa only [Real.norm_eq_abs] using hg' n p.1 hp p.2)
  refine ⟨f,hf,hf.continuousOn (Frequently.of_forall fun n => (hr n).1.smooth_f.continuous.continuousOn),?_,?_,?_,?_⟩
  · intro t ht z
    exact ge_of_tendsto (hf.tendsto_at (x:=(t,z)) ht) (Eventually.of_forall fun n => (hr n).1.nonneg _)
  · intro z
    have hh := hf.tendsto_at (x:=(0,z)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT⟩)
    simp only [(hr _).1.initial_f] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · intro t ht x v
    have hb : |f (t,x,v)|≤A := le_of_tendsto (hf.tendsto_at (x:=(t,x,v)) ht).abs
      (Eventually.of_forall fun n => ((hr n).2.2.1 t ht x v).1)
    refine ⟨hb,?_⟩
    intro hn
    by_contra hnot
    have hz (n : ℕ) : (S (n+1)).f (t,x,v)=0 := by
      by_contra hnn
      exact hnot (((hr n).2.2.1 t ht x v).2 hnn)
    have hh := hf.tendsto_at (x:=(t,x,v)) ht
    simp only [hz] at hh
    exact hn (tendsto_nhds_unique hh tendsto_const_nhds)
  · intro t ht z z'
    exact le_of_tendsto ((hf.tendsto_at (x:=(t,z)) ht).sub (hf.tendsto_at (x:=(t,z')) ht)).abs
      (Eventually.of_forall fun n => (hr n).2.2.2 t ht z z')

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma picard_field_exterior {d : Datum} {s : Solution} {E B : Field}
    (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hV : TransportFor s E B) {T A R P t : ℝ} (hb : LocalParticleBound T A R P s.f)
    (ht : t∈Ioc 0 T) (x : Vec) (hx : R+T<‖x‖) :
    s.E (t,x)=electricBoundaryField (datumBoundarySolution d) t x ∧
      s.B (t,x)=magneticBoundaryField (datumBoundarySolution d) t x := by
  have he := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell ht.1 x
  have hz (z : Vec) (hz : z∈ball (0:Vec) t) :
      retardedElectricDensity {s with E:=E,B:=B} t x (x+z)=0 := by
    have hnorm : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    have hr : coneRadius x (x+z)=‖z‖ := by simp [coneRadius]
    have htime : t-coneRadius x (x+z)∈Icc 0 T := by rw [hr]; exact ⟨by linarith,by linarith [norm_nonneg z,ht.2]⟩
    have hloc : R<‖x+z‖ := by
      have htri := norm_sub_le (x+z) z
      have hid : x+z-z=x := by abel
      rw [hid] at htri
      linarith [ht.2]
    have hfzero (v : Vec) : s.f (t-coneRadius x (x+z),x+z,v)=0 := by
      by_contra hn
      exact (not_le_of_gt hloc) (((hb _ htime (x+z) v).2 hn).1)
    simp only [retardedElectricDensity,hfzero,zero_mul,zero_smul,integral_zero]
  have hzB (z : Vec) (hz' : z∈ball (0:Vec) t) :
      retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)=0 := by
    rw [retardedMagneticDensity,hz z hz']
    ext i; fin_cases i <;> simp [cross]
  have hiE : (∫ z in ball (0:Vec) t,retardedElectricDensity {s with E:=E,B:=B} t x (x+z))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact hz
  have hiB : (∫ z in ball (0:Vec) t,retardedMagneticDensity {s with E:=E,B:=B} t x (x+z))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact hzB
  simp only [hiE,hiB,smul_zero,add_zero] at he
  exact ⟨he.1.trans (hs.boundary_eq ht.1 x).1,he.2.trans (hs.boundary_eq ht.1 x).2⟩

lemma picard_uniform_limit_exterior {d : Datum} {S : ℕ → Solution} {E B : Field} {T A R P : ℝ}
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (hV : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hEl : TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T})
    (hBl : TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T}) :
    ∀ t∈Icc 0 T, ∀ x, R+T<‖x‖ → E (t,x)=(S 1).E (t,x) ∧ B (t,x)=(S 1).B (t,x) := by
  intro t ht x hx
  have hE := (hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at (x:=(t,x)) ht
  have hB := (hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at (x:=(t,x)) ht
  have heq (n : ℕ) : (S (n+1)).E (t,x)=(S 1).E (t,x) ∧ (S (n+1)).B (t,x)=(S 1).B (t,x) := by
    rcases eq_or_lt_of_le ht.1 with ht0|ht0
    · subst t
      exact ⟨(hr n).initial_E x |>.trans ((hr 0).initial_E x).symm,
        (hr n).initial_B x |>.trans ((hr 0).initial_B x).symm⟩
    · have hn := picard_field_exterior (hr n) (hsm n).1 (hsm n).2 (hV n) (hb n) ⟨ht0,ht.2⟩ x hx
      have hz := picard_field_exterior (hr 0) (hsm 0).1 (hsm 0).2 (hV 0) (hb 0) ⟨ht0,ht.2⟩ x hx
      exact ⟨hn.1.trans hz.1.symm,hn.2.trans hz.2.symm⟩
  have he (n : ℕ) := (heq n).1
  have hb' (n : ℕ) := (heq n).2
  simp only [he] at hE
  simp only [hb'] at hB
  exact ⟨tendsto_nhds_unique hE tendsto_const_nhds,tendsto_nhds_unique hB tendsto_const_nhds⟩

end RVM

end

end OAI
