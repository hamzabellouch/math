import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SlabEvolutionRegularity
import OAI.Analysis.VlasovMaxwell.Regularity.VolterraSup
import OAI.Analysis.VlasovMaxwell.Regularity.PhysicalGradient
import OAI.Analysis.VlasovMaxwell.Maxwell.FieldGradientNorm
import OAI.Analysis.VlasovMaxwell.Regularity.LowBoundaryControl
import OAI.Analysis.VlasovMaxwell.Population.UniformPopulation
import OAI.Analysis.VlasovMaxwell.LocalPDE.SmoothLocalExistence
import OAI.Analysis.VlasovMaxwell.Continuation.PrefixUniqueness

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.particle_bound_datum {d : Datum} {s : Solution} {U A : ℝ}
    (hs : SmoothClassicalPrefix d s U) (hU : 0<U) (hA : ∀ z, |d.f₀ z|≤A) :
    ∀ t∈Icc (0:ℝ) U, ∀ z, |s.f (t,z)|≤A := by
  obtain ⟨F⟩ := hs.exists_phaseFlowOn hU
  intro t ht z
  rw [F.transport_inverse hs.energyPrefix.f_smooth hs.energyPrefix.vlasov ht,hs.initial_f]
  exact hA _

lemma physical_field_integral_bound {a b : Vec} {D K J : ℝ}
    (ha : ‖a‖≤D) (hb : ‖b‖≤(4*Real.pi)*K*J) :
    ‖a+(4*Real.pi)⁻¹ • b‖≤D+K*J := by
  have hp : 0<4*Real.pi := by positivity
  calc
    ‖a+(4*Real.pi)⁻¹ • b‖≤‖a‖+‖(4*Real.pi)⁻¹ • b‖ := norm_add_le _ _
    _ = ‖a‖+(4*Real.pi)⁻¹*‖b‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
    _ ≤ D+(4*Real.pi)⁻¹*((4*Real.pi)*K*J) := add_le_add ha (mul_le_mul_of_nonneg_left hb (by positivity))
    _ = D+K*J := by field_simp

lemma physical_fields_volterra {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
    ∃ D C : ℝ, 0≤D ∧ 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
      SmoothClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ g : ℝ → ℝ, Continuous g →
        (∀ t∈Icc (0:ℝ) U, ∀ x, ‖s.E (t,x)‖+‖s.B (t,x)‖≤g t) →
        ∀ t∈Icc (0:ℝ) U, ∀ x,
          ‖s.E (t,x)‖+‖s.B (t,x)‖≤D+C*(∫ r in Icc (0:ℝ) t, 1+g r) := by
  obtain ⟨A,hA⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  obtain ⟨K,hK,hk⟩ := uniform_retarded_density_affine (max A 0) P H (le_max_right _ _)
  obtain ⟨D,hD,hDi,hDb⟩ := datum_boundary_global_jets_horizon hd H hH 0
  refine ⟨2*D,2*K,by positivity,by positivity,?_⟩
  intro U hU hUH s hs hP g hg hgb
  have hf := hs.particle_bound_datum (A:=max A 0) hU
    (fun z => by simpa only [Real.norm_eq_abs] using (hA z).trans (le_max_left A 0))
  have hinterior : ∀ t∈Ioo (0:ℝ) U, ∀ x,
      ‖s.E (t,x)‖+‖s.B (t,x)‖≤2*D+2*K*(∫ r in Icc (0:ℝ) t, 1+g r) := by
    intro t ht x
    have hv := hs.physical_vectors ht.1 ht.2 x
    have hdens (z : Vec) (hz : 0<‖z‖) (hzt : ‖z‖≤t) :=
      hk s U hUH hf hP t ⟨ht.1.le,ht.2.le⟩ x z hz hzt
    have hke := kernel_volterra_norm (g:=fun r => 1+g r) ht.1.le hK hv.2.2.1 (by fun_prop) (by
      intro z hz hzt
      apply (hdens z hz hzt).1.trans
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hK
      have hh := hgb (t-‖z‖) ⟨by linarith,by linarith [norm_nonneg z,ht.2]⟩ (x+z)
      linarith)
    have hkb := kernel_volterra_norm (g:=fun r => 1+g r) ht.1.le hK hv.2.2.2 (by fun_prop) (by
      intro z hz hzt
      apply (hdens z hz hzt).2.trans
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hK
      have hh := hgb (t-‖z‖) ⟨by linarith,by linarith [norm_nonneg z,ht.2]⟩ (x+z)
      linarith)
    have hb := (hDb t ⟨ht.1,ht.2.le.trans hUH⟩).2 x
    simp only [norm_iteratedFDeriv_zero] at hb
    have he := physical_field_integral_bound hb.1 hke
    have hm := physical_field_integral_bound hb.2 hkb
    rw [←hv.1] at he
    rw [←hv.2.1] at hm
    linarith
  intro t ht x
  have hEc : ContinuousOn (fun r => s.E (r,x)) (Icc (0:ℝ) U) :=
    hs.E_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => hr)
  have hBc : ContinuousOn (fun r => s.B (r,x)) (Icc (0:ℝ) U) :=
    hs.B_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => hr)
  have hgc : ContinuousOn (fun t => 2*D+2*K*(∫ r in Icc (0:ℝ) t, 1+g r)) (Icc (0:ℝ) U) :=
    continuousOn_const.add (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_Icc
      ((continuous_const.add hg).continuousOn.integrableOn_compact isCompact_Icc)))
  apply le_on_closure (fun r hr => hinterior r hr x)
  · rw [_root_.closure_Ioo hU.ne]
    intro r hr
    exact (hEc r hr).norm.add (hBc r hr).norm
  · simpa only [_root_.closure_Ioo hU.ne] using hgc
  · simpa only [_root_.closure_Ioo hU.ne] using ht

lemma bounded_momentum_field_bound {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ t∈Icc (0:ℝ) U, ∀ x, ‖s.E (t,x)‖+‖s.B (t,x)‖≤C := by
  obtain ⟨D,K,hD,hK,hv⟩ := physical_fields_volterra hd P H hH
  obtain ⟨C,hC,hb⟩ := volterra_uniform_bound (α:=Vec) D K H hD hK
  refine ⟨C,hC,?_⟩
  intro U hU hUH s hs hP
  apply hb U hUH (fun t x => ‖s.E (t,x)‖+‖s.B (t,x)‖)
  · obtain ⟨L,hL,hl⟩ := hs.E_jets.2 0
    obtain ⟨M,hM,hm⟩ := hs.B_jets.2 0
    refine ⟨L+M,add_nonneg hL hM,?_⟩
    intro t ht x
    simpa only [norm_iteratedFDeriv_zero] using add_le_add (hl t ht x) (hm t ht x)
  · exact hv U hU hUH s hs.classical hP

lemma ClassicalBefore.mono {d : Datum} {s : Solution} {T U : ℝ}
    (hs : ClassicalBefore d s U) (hTU : T≤U) : ClassicalBefore d s T := by
  rcases hs with ⟨hf,hE,hB,hn,hEL,hBL,hc,heq,hf₀,hE₀,hB₀⟩
  exact ⟨hf,hE,hB,hn,hEL,hBL,hc,fun t ht h => heq t ht (h.trans_le hTU),hf₀,hE₀,hB₀⟩

lemma log_one_add_mul_exp_le {C A I : ℝ} (hC : 0≤C) (hA : 0≤A) (hI : 0≤I) :
    Real.log (1+C*(A*Real.exp I))≤Real.log (1+C*A)+I := by
  have hCA : 0≤C*A := mul_nonneg hC hA
  have hpos : 0<1+C*A := by linarith
  have he : 1≤Real.exp I := Real.one_le_exp hI
  have hh : 1+C*(A*Real.exp I)≤(1+C*A)*Real.exp I := by nlinarith
  apply (Real.log_le_log (by positivity) hh).trans_eq
  rw [Real.log_mul hpos.ne' (Real.exp_ne_zero _),Real.log_exp]

lemma integral_lorentz_coefficient_bound {g : ℝ → ℝ} {L T : ℝ}
    (hg : Continuous g) (hL : 0≤L) (hT : 0≤T) (hg0 : ∀ r∈Icc (0:ℝ) T,0≤g r) :
    0≤(∫ r in 0..T,1+2*g r+L) ∧
    (∫ r in 0..T,1+2*g r+L)≤(3+L)*(∫ r in Icc (0:ℝ) T,1+g r) := by
  have hc : Continuous (fun r => 1+2*g r+L) := by fun_prop
  constructor
  · apply intervalIntegral.integral_nonneg hT
    intro r hr
    linarith [hg0 r hr]
  · rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hT,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT (hc.intervalIntegrable 0 T)
      ((continuous_const.mul (continuous_const.add hg)).intervalIntegrable 0 T)
    intro r hr
    change 1+2*g r+L≤(3+L)*(1+g r)
    nlinarith [hg0 r hr,mul_nonneg hL (hg0 r hr)]

lemma classical_electric_log_closed_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U t : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y z, ‖s.E (u,y)-s.E (u,z)‖≤g u*‖y-z‖ ∧
        ‖s.B (u,y)-s.B (u,z)‖≤g u*‖y-z‖) →
      |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|≤B+K*(∫ u in Icc (0:ℝ) U,1+g u) := by
  obtain ⟨B,C,D,K,hB,hC,hD,hK,hv⟩ := classical_electric_gradient_volterra_bound hd P A M H e i hA hH
  obtain ⟨A₀,hA₀,hLip⟩ := admissible_particle_lipschitz hd
  refine ⟨B+D*Real.log (1+C*A₀),D*(3+M)+K,?_,by positivity,?_⟩
  · exact add_nonneg hB (mul_nonneg hD (Real.log_nonneg (by nlinarith [mul_nonneg hC hA₀])))
  intro s U t x g hs hm ht htU hUH hg hg0 hfA hP hEB hDF hEx
  have hU : 0≤U := ht.le.trans htU.le
  let N := A₀*Real.exp (∫ r in 0..U,1+2*g r+M)
  have hN : 0≤N := mul_nonneg hA₀ (Real.exp_pos _).le
  have hfN := particle_gradient_volterra_before hs hU le_rfl hA₀ hM hLip hg.continuousOn hg0
    (fun u hu y => (hEB u hu y).2) (fun u hu y z => (hEx u hu z y).1) (fun u hu y z => (hEx u hu z y).2)
  have hh := hv s U t N x g hs hm ht htU hUH hN hg hg0 hfA hP hEB hDF hfN
  have hi := integral_lorentz_coefficient_bound hg hM hU hg0
  have hlog := log_one_add_mul_exp_le hC hA₀ hi.1
  have hi' : (∫ u in Icc (0:ℝ) t,1+g u)≤∫ u in Icc (0:ℝ) U,1+g u := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le ht.le,←intervalIntegral.integral_of_le hU]
    apply intervalIntegral.integral_mono_interval le_rfl ht.le htU.le _
      ((continuous_const.add hg).intervalIntegrable 0 U)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change 0≤1+g u
    linarith [hg0 u ⟨hu.1.le,hu.2⟩]
  change |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|≤B+D*Real.log (1+C*A₀)+(D*(3+M)+K)*(∫ u in Icc (0:ℝ) U,1+g u)
  dsimp [N] at hh
  nlinarith [mul_le_mul_of_nonneg_left hlog hD,mul_le_mul_of_nonneg_left hi.2 hD,
    mul_le_mul_of_nonneg_left hi' hK]

lemma classical_magnetic_log_closed_bound {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U t : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y z, ‖s.E (u,y)-s.E (u,z)‖≤g u*‖y-z‖ ∧
        ‖s.B (u,y)-s.B (u,z)‖≤g u*‖y-z‖) →
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+K*(∫ u in Icc (0:ℝ) U,1+g u) := by
  obtain ⟨B,C,D,K,hB,hC,hD,hK,hv⟩ := Magnetic.classical_magnetic_gradient_volterra_bound hd P A M H e i hA hH
  obtain ⟨A₀,hA₀,hLip⟩ := admissible_particle_lipschitz hd
  refine ⟨B+D*Real.log (1+C*A₀),D*(3+M)+K,?_,by positivity,?_⟩
  · exact add_nonneg hB (mul_nonneg hD (Real.log_nonneg (by nlinarith [mul_nonneg hC hA₀])))
  intro s U t x g hs hm ht htU hUH hg hg0 hfA hP hEB hDF hEx
  have hU : 0≤U := ht.le.trans htU.le
  let N := A₀*Real.exp (∫ r in 0..U,1+2*g r+M)
  have hN : 0≤N := mul_nonneg hA₀ (Real.exp_pos _).le
  have hfN := particle_gradient_volterra_before hs hU le_rfl hA₀ hM hLip hg.continuousOn hg0
    (fun u hu y => (hEB u hu y).2) (fun u hu y z => (hEx u hu z y).1) (fun u hu y z => (hEx u hu z y).2)
  have hh := hv s U t N x g hs hm ht htU hUH hN hg hg0 hfA hP hEB hDF hfN
  have hi := integral_lorentz_coefficient_bound hg hM hU hg0
  have hlog := log_one_add_mul_exp_le hC hA₀ hi.1
  have hi' : (∫ u in Icc (0:ℝ) t,1+g u)≤∫ u in Icc (0:ℝ) U,1+g u := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le ht.le,←intervalIntegral.integral_of_le hU]
    apply intervalIntegral.integral_mono_interval le_rfl ht.le htU.le _
      ((continuous_const.add hg).intervalIntegrable 0 U)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change 0≤1+g u
    linarith [hg0 u ⟨hu.1.le,hu.2⟩]
  change |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+D*Real.log (1+C*A₀)+(D*(3+M)+K)*(∫ u in Icc (0:ℝ) U,1+g u)
  dsimp [N] at hh
  nlinarith [mul_le_mul_of_nonneg_left hlog hD,mul_le_mul_of_nonneg_left hi.2 hD,
    mul_le_mul_of_nonneg_left hi' hK]

lemma classical_fields_gradient_current_volterra {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U t : ℝ) (x : Vec) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s →
      0<t → t<U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y z, ‖s.E (u,y)-s.E (u,z)‖≤g u*‖y-z‖ ∧
        ‖s.B (u,y)-s.B (u,z)‖≤g u*‖y-z‖) →
      |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|+
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤B+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  obtain ⟨B,K,hB,hK,hE⟩ := classical_electric_log_closed_bound hd P A M H e i hA hM hH
  obtain ⟨D,L,hD,hL,hB'⟩ := classical_magnetic_log_closed_bound hd P A M H e i hA hM hH
  refine ⟨B+D,K+L,add_nonneg hB hD,add_nonneg hK hL,?_⟩
  intro s U t x g hs hm ht htU hUH hg hg0 hfA hP hEB hDF hEx
  have hin : ∀ V∈Ioo t U,
      |deriv (fun q : ℝ => s.E (t,x+q • e) i) 0|+
      |deriv (fun q : ℝ => s.B (t,x+q • e) i) 0|≤(B+D)+(K+L)*(∫ u in Icc (0:ℝ) V,1+g u) := by
    intro V hV
    have hsub : Icc (0:ℝ) V ⊆ Icc (0:ℝ) U := fun u hu => ⟨hu.1,hu.2.trans hV.2.le⟩
    have he := hE s V t x g (hs.mono hV.2.le) hm ht hV.1 (hV.2.le.trans hUH) hg
      (fun u hu => hg0 u (hsub hu)) (fun u hu => hfA u (hsub hu)) (fun u hu => hP u (hsub hu))
      (fun u hu => hEB u (hsub hu)) (fun u hu => hDF u ⟨hu.1,hu.2.trans hV.2.le⟩)
      (fun u hu => hEx u (hsub hu))
    have hb := hB' s V t x g (hs.mono hV.2.le) hm ht hV.1 (hV.2.le.trans hUH) hg
      (fun u hu => hg0 u (hsub hu)) (fun u hu => hfA u (hsub hu)) (fun u hu => hP u (hsub hu))
      (fun u hu => hEB u (hsub hu)) (fun u hu => hDF u ⟨hu.1,hu.2.trans hV.2.le⟩)
      (fun u hu => hEx u (hsub hu))
    linarith
  have hc : ContinuousOn (fun V => (B+D)+(K+L)*(∫ u in Icc (0:ℝ) V,1+g u)) (Icc (0:ℝ) U) :=
    continuousOn_const.add (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_Icc
      ((continuous_const.add hg).continuousOn.integrableOn_compact isCompact_Icc)))
  apply le_on_closure hin continuousOn_const
  · rw [_root_.closure_Ioo htU.ne]
    exact hc.mono (fun V hV => ⟨ht.le.trans hV.1,hV.2⟩)
  · simp only [_root_.closure_Ioo htU.ne,mem_Icc,le_refl,htU.le,and_self]

lemma component_le_double_sum {F : Fin 3 → Fin 3 → ℝ} (hF : ∀ i j,0≤F i j) (i j : Fin 3) :
    F i j≤∑ i : Fin 3, ∑ j : Fin 3,F i j := by
  exact (Finset.single_le_sum (fun k _ => hF i k) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hF k l)) (Finset.mem_univ i))

lemma prefix_spatial_gradient_volterra {d : Datum} (hd : Admissible d)
    (P A M H : ℝ) (hA : 0≤A) (hM : 0≤M) (hH : 0≤H) :
    ∃ B K : ℝ, 0≤B ∧ 0≤K ∧
    ∀ (s : Solution) (U : ℝ), BoundedClassicalPrefix d s U → 0<U → U≤H →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      ∀ g : ℝ → ℝ, Continuous g →
      (∀ u∈Icc (0:ℝ) U, ∀ y,
        ‖fderiv ℝ (fun z => s.E (u,z)) y‖+‖fderiv ℝ (fun z => s.B (u,z)) y‖≤g u) →
      ∀ t∈Icc (0:ℝ) U, ∀ x,
        ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖≤
          B+K*(∫ u in Icc (0:ℝ) t,1+g u) := by
  choose B K hB hK hb using fun i j : Fin 3 =>
    classical_fields_gradient_current_volterra hd P A M H (basis j) i hA hM hH
  let D := ∑ i : Fin 3,∑ j : Fin 3,B i j
  let L := ∑ i : Fin 3,∑ j : Fin 3,K i j
  let J := A*(volume (closedBall (0:Vec) P)).toReal
  have hD : 0≤D := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hB i j))
  have hL : 0≤L := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hK i j))
  have hJ : 0≤J := by dsimp [J]; positivity
  refine ⟨18*D,18*L*(8+J),by positivity,by positivity,?_⟩
  intro s U hs hU hUH hfA hP hEB g hg hgb
  have hg0 : ∀ u∈Icc (0:ℝ) U,0≤g u := fun u hu =>
    (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hgb u hu 0)
  let G : ℝ → ℝ := fun u => 7*g u+J
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hG0 : ∀ u∈Icc (0:ℝ) U,0≤G u := fun u hu => by dsimp [G]; positivity [hg0 u hu]
  have hgG : ∀ u∈Icc (0:ℝ) U,g u≤G u := fun u hu => by dsimp [G]; nlinarith [hg0 u hu]
  have hinterior : ∀ t∈Ioo (0:ℝ) U, ∀ x,
      ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖≤
        18*D+18*L*(8+J)*(∫ u in Icc (0:ℝ) t,1+g u) := by
    intro t ht x
    obtain ⟨τ,htτ,hτU⟩ := exists_between ht.2
    obtain ⟨V,htV,hVτ⟩ := exists_between htτ
    let a := cutoffPrefix τ U s
    have heq (u : ℝ) (hu : u≤τ) := cutoffPrefix_eq hτU hu s
    have ha := hs.classical.cutoff_classical_before (ht.1.le.trans htτ.le) hτU
    have hsub : Icc (0:ℝ) V ⊆ Icc (0:ℝ) U := fun u hu => ⟨hu.1,hu.2.trans (hVτ.le.trans hτU.le)⟩
    have hfunE (u : ℝ) (hu : u≤τ) : (fun z => a.E (u,z))=(fun z => s.E (u,z)) := funext (heq u hu).2.1
    have hfunB (u : ℝ) (hu : u≤τ) : (fun z => a.B (u,z))=(fun z => s.B (u,z)) := funext (heq u hu).2.2
    have hab : ∀ u∈Icc (0:ℝ) V,∀ y,
        ‖fderiv ℝ (fun z => a.E (u,z)) y‖+‖fderiv ℝ (fun z => a.B (u,z)) y‖≤g u := by
      intro u hu y
      rw [hfunE u (hu.2.trans hVτ.le),hfunB u (hu.2.trans hVτ.le)]
      exact hgb u (hsub hu) y
    have haA : ∀ u∈Icc (0:ℝ) V,∀ y v,|a.f (u,y,v)|≤A := by
      intro u hu y v
      rw [(heq u (hu.2.trans hVτ.le)).1]
      exact hfA u (hsub hu) y v
    have haP : ∀ u∈Icc (0:ℝ) V,∀ y v,P<‖v‖ → a.f (u,y,v)=0 := by
      intro u hu y v hv
      rw [(heq u (hu.2.trans hVτ.le)).1]
      exact hP u (hsub hu) y v hv
    have haEB : ∀ u∈Icc (0:ℝ) V,∀ y,‖a.E (u,y)‖≤M ∧ ‖a.B (u,y)‖≤M := by
      intro u hu y
      rw [(heq u (hu.2.trans hVτ.le)).2.1,(heq u (hu.2.trans hVτ.le)).2.2]
      exact hEB u (hsub hu) y
    have haDF : ∀ u∈Ioc (0:ℝ) V,∀ y,‖fderiv ℝ a.E (u,y)‖≤G u ∧ ‖fderiv ℝ a.B (u,y)‖≤G u := by
      intro u hu y
      exact maxwell_full_derivative_bound ha.2.1 ha.2.2.1 ha.2.2.2.2.2.2.2.1 hu.1 (hu.2.trans_lt hVτ)
        hA (haA u ⟨hu.1.le,hu.2⟩) (haP u ⟨hu.1.le,hu.2⟩) (hab u ⟨hu.1.le,hu.2⟩) y
    have haLip : ∀ u∈Icc (0:ℝ) V,∀ y z,‖a.E (u,y)-a.E (u,z)‖≤G u*‖y-z‖ ∧
        ‖a.B (u,y)-a.B (u,z)‖≤G u*‖y-z‖ := by
      intro u hu y z
      simp only [a,(heq u (hu.2.trans hVτ.le)).2.1,(heq u (hu.2.trans hVτ.le)).2.2]
      constructor
      · apply spatial_field_lipschitz_of_gradient ((hs.E_jets.1.1 u (hsub hu)).differentiable (by simp))
        intro w
        exact (le_add_of_nonneg_right (norm_nonneg _)).trans ((hgb u (hsub hu) w).trans (hgG u (hsub hu)))
      · apply spatial_field_lipschitz_of_gradient ((hs.B_jets.1.1 u (hsub hu)).differentiable (by simp))
        intro w
        exact (le_add_of_nonneg_left (norm_nonneg _)).trans ((hgb u (hsub hu) w).trans (hgG u (hsub hu)))
    let I := ∫ u in Icc (0:ℝ) t,1+G u
    have hI : 0≤I := by
      apply setIntegral_nonneg measurableSet_Icc
      intro u hu
      linarith [hG0 u ⟨hu.1,hu.2.trans ht.2.le⟩]
    have hcomp (i j : Fin 3) :
        |fderiv ℝ (fun z => s.E (t,z)) x (basis j) i|+
        |fderiv ℝ (fun z => s.B (t,z)) x (basis j) i|≤D+L*I := by
      have hh := hb i j a V t x G (ha.mono hVτ.le) (hs.classical.cutoff_smooth hτU) ht.1 htV
        (hVτ.le.trans (hτU.le.trans hUH)) hG (fun u hu => hG0 u (hsub hu)) haA haP haEB haDF haLip
      simp only [a,(heq t htτ.le).2.1,(heq t htτ.le).2.2] at hh
      rw [(hasDerivAt_vec_component_line i ((hs.E_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)).differentiableAt).deriv,
        (hasDerivAt_vec_component_line i ((hs.B_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)).differentiableAt).deriv] at hh
      exact hh.trans (add_le_add (component_le_double_sum hB i j)
        (mul_le_mul_of_nonneg_right (component_le_double_sum hK i j) hI))
    have hC : 0≤D+L*I := by positivity
    have hEn := norm_clm_le_nine_components (fderiv ℝ (fun z => s.E (t,z)) x) hC
      (fun i j => (le_add_of_nonneg_right (abs_nonneg _)).trans (hcomp i j))
    have hBn := norm_clm_le_nine_components (fderiv ℝ (fun z => s.B (t,z)) x) hC
      (fun i j => (le_add_of_nonneg_left (abs_nonneg _)).trans (hcomp i j))
    have hi : I≤(8+J)*(∫ u in Icc (0:ℝ) t,1+g u) := by
      rw [←integral_const_mul]
      apply setIntegral_mono_on _ _ measurableSet_Icc
      · intro u hu
        change 1+(7*g u+J)≤(8+J)*(1+g u)
        nlinarith [hg0 u ⟨hu.1,hu.2.trans ht.2.le⟩,mul_nonneg hJ (hg0 u ⟨hu.1,hu.2.trans ht.2.le⟩)]
      all_goals
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop
    nlinarith [mul_le_mul_of_nonneg_left hi hL]
  intro t ht x
  have hEc : ContinuousOn (fun r => ‖fderiv ℝ (fun z => s.E (r,z)) x‖) (Icc (0:ℝ) U) := by
    simpa only [Function.comp_def,id_eq,norm_iteratedFDeriv_one] using ((hs.E_jets.1.2 1).comp
      ((continuous_id.prodMk (continuous_const (y:=x))).continuousOn (s:=Icc (0:ℝ) U)) (fun r hr => hr)).norm
  have hBc : ContinuousOn (fun r => ‖fderiv ℝ (fun z => s.B (r,z)) x‖) (Icc (0:ℝ) U) := by
    simpa only [Function.comp_def,id_eq,norm_iteratedFDeriv_one] using ((hs.B_jets.1.2 1).comp
      ((continuous_id.prodMk (continuous_const (y:=x))).continuousOn (s:=Icc (0:ℝ) U)) (fun r hr => hr)).norm
  have hgc : ContinuousOn (fun r => 18*D+18*L*(8+J)*(∫ u in Icc (0:ℝ) r,1+g u)) (Icc (0:ℝ) U) :=
    continuousOn_const.add (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_Icc
      ((continuous_const.add hg).continuousOn.integrableOn_compact isCompact_Icc)))
  apply le_on_closure (fun r hr => hinterior r hr x)
  · rw [_root_.closure_Ioo hU.ne]
    intro r hr
    exact (hEc r hr).add (hBc r hr)
  · simpa only [_root_.closure_Ioo hU.ne] using hgc
  · simpa only [_root_.closure_Ioo hU.ne] using ht

lemma bounded_momentum_field_gradient_bound {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ t∈Icc (0:ℝ) U, ∀ x,
        ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖≤C := by
  obtain ⟨M,hM,hMb⟩ := bounded_momentum_field_bound hd P H hH
  obtain ⟨A,hA⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  obtain ⟨B,K,hB,hK,hv⟩ := prefix_spatial_gradient_volterra hd P (max A 0) M H (le_max_right _ _) hM hH
  obtain ⟨C,hC,hb⟩ := volterra_uniform_bound (α:=Vec) B K H hB hK
  refine ⟨C,hC,?_⟩
  intro U hU hUH s hs hP
  apply hb U hUH (fun t x => ‖fderiv ℝ (fun z => s.E (t,z)) x‖+‖fderiv ℝ (fun z => s.B (t,z)) x‖)
  · obtain ⟨L,hL,hl⟩ := hs.E_jets.2 1
    obtain ⟨N,hN,hn⟩ := hs.B_jets.2 1
    refine ⟨L+N,add_nonneg hL hN,?_⟩
    intro t ht x
    simpa only [norm_iteratedFDeriv_one] using add_le_add (hl t ht x) (hn t ht x)
  · apply hv s U hs hU hUH
    · intro t ht x v
      exact hs.classical.particle_bound_datum (A:=max A 0) hU
        (fun z => by simpa only [Real.norm_eq_abs] using (hA z).trans (le_max_left A 0)) t ht (x,v)
    · exact hP
    · intro t ht x
      have hh := hMb U hU hUH s hs hP t ht x
      exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans hh,(le_add_of_nonneg_left (norm_nonneg _)).trans hh⟩

lemma bounded_momentum_particle_lipschitz_bound {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ t∈Icc (0:ℝ) U, ∀ z w : Phase, |s.f (t,z)-s.f (t,w)|≤C*‖z-w‖ := by
  obtain ⟨M,hM,hMb⟩ := bounded_momentum_field_bound hd P H hH
  obtain ⟨D,hD,hDb⟩ := bounded_momentum_field_gradient_bound hd P H hH
  obtain ⟨A,hA,hAb⟩ := admissible_particle_lipschitz hd
  refine ⟨A*Real.exp ((1+2*D+M)*H),by positivity,?_⟩
  intro U hU hUH s hs hP t ht z w
  have hind : ∀ r∈Ioo (0:ℝ) U,|s.f (r,z)-s.f (r,w)|≤(A*Real.exp ((1+2*D+M)*H))*‖z-w‖ := by
    intro r hr
    obtain ⟨τ,hrτ,hτU⟩ := exists_between hr.2
    let a := cutoffPrefix τ U s
    have he (u : ℝ) (hu : u≤τ) := cutoffPrefix_eq hτU hu s
    have ha := hs.classical.cutoff_classical_before (hr.1.le.trans hrτ.le) hτU
    have hsub : Icc (0:ℝ) r ⊆ Icc (0:ℝ) U := fun u hu => ⟨hu.1,hu.2.trans hr.2.le⟩
    have hcfE (u : ℝ) (hu : u≤τ) : (fun y => a.E (u,y))=(fun y => s.E (u,y)) := funext (he u hu).2.1
    have hcfB (u : ℝ) (hu : u≤τ) : (fun y => a.B (u,y))=(fun y => s.B (u,y)) := funext (he u hu).2.2
    have hBb : ∀ u∈Icc (0:ℝ) r,∀ y,‖a.B (u,y)‖≤M := by
      intro u hu y
      rw [(he u (hu.2.trans hrτ.le)).2.2]
      exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hMb U hU hUH s hs hP u (hsub hu) y)
    have hEx : ∀ u∈Icc (0:ℝ) r,∀ y x,‖a.E (u,x)-a.E (u,y)‖≤D*‖x-y‖ := by
      intro u hu y x
      simp only [a,(he u (hu.2.trans hrτ.le)).2.1]
      apply spatial_field_lipschitz_of_gradient ((hs.E_jets.1.1 u (hsub hu)).differentiable (by simp))
      intro v
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hDb U hU hUH s hs hP u (hsub hu) v)
    have hBx : ∀ u∈Icc (0:ℝ) r,∀ y x,‖a.B (u,x)-a.B (u,y)‖≤D*‖x-y‖ := by
      intro u hu y x
      simp only [a,(he u (hu.2.trans hrτ.le)).2.2]
      apply spatial_field_lipschitz_of_gradient ((hs.B_jets.1.1 u (hsub hu)).differentiable (by simp))
      intro v
      exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hDb U hU hUH s hs hP u (hsub hu) v)
    have hh := particle_lipschitz_volterra_before (g:=fun _ => D) ha hr.1.le hrτ.le hA hM hAb
      continuousOn_const (fun _ _ => hD) hBb hEx hBx z w
    simp only [(he r hrτ.le).1,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hr.2.le.trans hUH])) hA) (norm_nonneg _))
  have hfc (z : Phase) : ContinuousOn (fun r => s.f (r,z)) (Icc (0:ℝ) U) :=
    hs.classical.f_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr)
  apply le_on_closure hind
  · rw [_root_.closure_Ioo hU.ne]
    intro r hr
    exact ((hfc z r hr).sub (hfc w r hr)).abs
  · exact continuousOn_const
  · simpa only [_root_.closure_Ioo hU.ne] using ht

lemma bounded_momentum_particle_gradient_bound {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ t∈Icc (0:ℝ) U, ∀ z : Phase, ‖fderiv ℝ (fun w => s.f (t,w)) z‖≤C := by
  obtain ⟨C,hC,hb⟩ := bounded_momentum_particle_lipschitz_bound hd P H hH
  refine ⟨C,hC,?_⟩
  intro U hU hUH s hs hP t ht z
  have hLip : LipschitzWith ⟨C,hC⟩ (fun w => s.f (t,w)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (s.f (t,x)) (s.f (t,y))≤C*dist x y
    simpa only [dist_eq_norm,Real.norm_eq_abs] using hb U hU hUH s hs hP t ht x y
  exact norm_fderiv_le_of_lipschitz ℝ hLip

def secondJetSum (s : Solution) (t : ℝ) (z : Phase) : ℝ :=
  ‖iteratedFDeriv ℝ 2 (fun w => s.f (t,w)) z‖+
  ‖iteratedFDeriv ℝ 2 (fun y => s.E (t,y)) z.1‖+
  ‖iteratedFDeriv ℝ 2 (fun y => s.B (t,y)) z.1‖

lemma secondJetSum_nonneg (s : Solution) (t : ℝ) (z : Phase) : 0 ≤ secondJetSum s t z := by
  dsimp [secondJetSum]; positivity

lemma prefix_second_jet_volterra {d : Datum} (hd : Admissible d)
    (P A L M N H : ℝ) (hL : 0≤L) (hM : 0≤M) (hN : 0≤N) (hH : 0≤H) :
    ∃ D K : ℝ,0≤D ∧ 0≤K ∧ ∀ (s : Solution) (U : ℝ),
      BoundedClassicalPrefix d s U → 0<U → U≤H →
      (∀ u∈Icc (0:ℝ) U,∀ y v,|s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U,∀ y v,P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U,∀ y,‖s.E (u,y)‖≤L ∧ ‖s.B (u,y)‖≤L) →
      (∀ u∈Icc (0:ℝ) U,∀ z w : Phase,|s.f (u,z)-s.f (u,w)|≤M*‖z-w‖) →
      SpatialFieldLip U N s.E s.B →
      ∀ g : ℝ → ℝ,Continuous g →
      (∀ u∈Icc (0:ℝ) U,∀ z,secondJetSum s u z≤g u) →
      ∀ t∈Icc (0:ℝ) U,∀ z,secondJetSum s t z≤D+K*(∫ r in Icc (0:ℝ) t,1+g r) := by
  obtain ⟨D,K,hD,hK,hfield⟩ := classical_fields_curvature_volterra_bound hd A P L M N H hM hN hH
  obtain ⟨Af,hAf,hfl⟩ := admissible_particle_lipschitz hd
  obtain ⟨Df,hDf,hfc⟩ := smooth_compact_curvature hd.1 hd.2.1
  let Q := Real.exp ((1+2*N+L)*H)
  let Bf := 4*Df*Q^2
  let Kf := Af*4*Q^3*(10+6*L+2*N)
  have hQ : 0<Q := Real.exp_pos _
  have hBf : 0≤Bf := by dsimp [Bf]; positivity
  have hKf : 0≤Kf := by dsimp [Kf]; positivity
  refine ⟨6*Bf+12*D,6*Kf+24*K,by positivity,by positivity,?_⟩
  intro s U hs hU hUH hfA hP hEB hfL hEBL g hg hgb
  have hg0 : ∀ u∈Icc (0:ℝ) U,0≤g u := fun u hu => (secondJetSum_nonneg s u 0).trans (hgb u hu 0)
  have hf2 (u : ℝ) (hu : u∈Icc (0:ℝ) U) (z : Phase) :
      ‖iteratedFDeriv ℝ 2 (fun w => s.f (u,w)) z‖≤g u := by
    have hh := hgb u hu z
    dsimp [secondJetSum] at hh
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.E (u,y)) z.1),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.B (u,y)) z.1)]
  have hE2 (u : ℝ) (hu : u∈Icc (0:ℝ) U) (x : Vec) :
      ‖iteratedFDeriv ℝ 2 (fun y => s.E (u,y)) x‖≤g u := by
    have hh := hgb u hu (x,0)
    dsimp [secondJetSum] at hh
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun w => s.f (u,w)) (x,0)),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.B (u,y)) x)]
  have hB2 (u : ℝ) (hu : u∈Icc (0:ℝ) U) (x : Vec) :
      ‖iteratedFDeriv ℝ 2 (fun y => s.B (u,y)) x‖≤g u := by
    have hh := hgb u hu (x,0)
    dsimp [secondJetSum] at hh
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun w => s.f (u,w)) (x,0)),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => s.E (u,y)) x)]
  have hinterior : ∀ t∈Ioo (0:ℝ) U,∀ z,
      secondJetSum s t z≤(6*Bf+12*D)+(6*Kf+24*K)*(∫ r in Icc (0:ℝ) t,1+g r) := by
    intro t ht z
    obtain ⟨τ,htτ,hτU⟩ := exists_between ht.2
    let a := cutoffPrefix τ U s
    have heq (u : ℝ) (hu : u≤τ) := cutoffPrefix_eq hτU hu s
    have ha := hs.classical.cutoff_classical_before (ht.1.le.trans htτ.le) hτU
    have hsub : Icc (0:ℝ) τ ⊆ Icc (0:ℝ) U := fun u hu => ⟨hu.1,hu.2.trans hτU.le⟩
    have hsf (u : ℝ) (hu : u≤τ) : (fun w : Phase => a.f (u,w))=(fun w => s.f (u,w)) :=
      funext (fun w => (heq u hu).1 w)
    have hsE (u : ℝ) (hu : u≤τ) : (fun y => a.E (u,y))=(fun y => s.E (u,y)) := funext (heq u hu).2.1
    have hsB (u : ℝ) (hu : u≤τ) : (fun y => a.B (u,y))=(fun y => s.B (u,y)) := funext (heq u hu).2.2
    have hafc : ∀ u∈Icc (0:ℝ) τ,CurvatureBound (fun w : Phase => a.f (u,w)) (2*g u) := by
      intro u hu
      rw [hsf u hu.2]
      exact curvature_of_second_derivative_bound (hs.f_jets.1.1 u (hsub hu)) (hg0 u (hsub hu)) (hf2 u (hsub hu))
    have haEc : ∀ u∈Icc (0:ℝ) τ,CurvatureBound (fun y => a.E (u,y)) (2*g u) := by
      intro u hu
      rw [hsE u hu.2]
      exact curvature_of_second_derivative_bound (hs.E_jets.1.1 u (hsub hu)) (hg0 u (hsub hu)) (hE2 u (hsub hu))
    have haBc : ∀ u∈Icc (0:ℝ) τ,CurvatureBound (fun y => a.B (u,y)) (2*g u) := by
      intro u hu
      rw [hsB u hu.2]
      exact curvature_of_second_derivative_bound (hs.B_jets.1.1 u (hsub hu)) (hg0 u (hsub hu)) (hB2 u (hsub hu))
    have haEB : ∀ u∈Icc (0:ℝ) τ,∀ y,‖a.E (u,y)‖≤L ∧ ‖a.B (u,y)‖≤L := by
      intro u hu y
      simp only [a,(heq u hu.2).2.1,(heq u hu.2).2.2]
      exact hEB u (hsub hu) y
    have haL : SpatialFieldLip τ N a.E a.B := by
      intro u hu x y
      simp only [a,(heq u hu.2).2.1,(heq u hu.2).2.2]
      exact hEBL u (hsub hu) x y
    have haA : ∀ u∈Icc (0:ℝ) τ,∀ y v,|a.f (u,y,v)|≤A := by
      intro u hu y v
      rw [(heq u hu.2).1]
      exact hfA u (hsub hu) y v
    have haP : ∀ u∈Icc (0:ℝ) τ,∀ y v,P<‖v‖ → a.f (u,y,v)=0 := by
      intro u hu y v hv
      rw [(heq u hu.2).1]
      exact hP u (hsub hu) y v hv
    have haLf : ∀ u∈Icc (0:ℝ) τ,∀ v x y,|a.f (u,y,v)-a.f (u,x,v)|≤M*‖y-x‖ := by
      intro u hu v x y
      simp only [a,(heq u hu.2).1]
      have hh := hfL u (hsub hu) (y,v) (x,v)
      simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_eq_left (norm_nonneg (y-x))] using hh
    have hg2 : Continuous (fun u => 2*g u) := continuous_const.mul hg
    have hg20 : ∀ u∈Icc (0:ℝ) τ,0≤2*g u := fun u hu => by positivity [hg0 u (hsub hu)]
    have hfields := hfield a τ t (fun u => 2*g u) ha (hs.classical.cutoff_smooth hτU) ht.1 htτ
      (hτU.le.trans hUH) hg2 hg20 haA haP haEB
      (fun u hu v => (hafc u hu).spatial_slice v) (fun u hu => ⟨haEc u hu,haBc u hu⟩) haLf haL
    rw [hsE t htτ.le,hsB t htτ.le] at hfields
    have hsubt : Icc (0:ℝ) t ⊆ Icc (0:ℝ) τ := fun u hu => ⟨hu.1,hu.2.trans htτ.le⟩
    have hpart := particle_curvature_volterra_before ha ht.1.le htτ.le hAf hDf hL hN hfl hfc
      (hg2.continuousOn) (fun u hu => hg20 u (hsubt hu))
      (fun u hu y => (haEB u (hsubt hu) y).2)
      (fun u hu x y => (haL u (hsubt hu) x y).1) (fun u hu x y => (haL u (hsubt hu) x y).2)
      (fun u hu => haEc u (hsubt hu)) (fun u hu => haBc u (hsubt hu))
    rw [hsf t htτ.le] at hpart
    let I := ∫ r in Icc (0:ℝ) t,1+g r
    have hI : 0≤I := integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have := hg0 r ⟨hr.1,hr.2.trans ht.2.le⟩
      change 0≤1+g r; linarith)
    have hInt2 : (∫ r in Icc (0:ℝ) t,1+2*g r)≤2*I := by
      rw [←integral_const_mul]
      apply setIntegral_mono_on _ _ measurableSet_Icc (fun r hr => by linarith)
      all_goals
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop
    have hIntP : (∫ r in 0..t,6+6*L+2*(2*g r)+2*N)≤(10+6*L+2*N)*I := by
      rw [intervalIntegral.integral_of_le ht.1.le,←integral_Icc_eq_integral_Ioc,←integral_const_mul]
      apply setIntegral_mono_on _ _ measurableSet_Icc
      · intro r hr
        have hg' := hg0 r ⟨hr.1,hr.2.trans ht.2.le⟩
        change 6+6*L+2*(2*g r)+2*N≤(10+6*L+2*N)*(1+g r)
        nlinarith [mul_nonneg hL hg',mul_nonneg hN hg']
      all_goals
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        fun_prop
    have hQt : Real.exp ((1+2*N+L)*t)≤Q := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (ht.2.le.trans hUH) (by positivity))
    have hpart' : CurvatureBound (fun w => s.f (t,w)) (Bf+Kf*I) := by
      apply hpart.mono
      have h0 : 0≤∫ r in 0..t,6+6*L+2*(2*g r)+2*N := by
        apply intervalIntegral.integral_nonneg ht.1.le
        intro r hr
        have := hg0 r ⟨hr.1,hr.2.trans ht.2.le⟩
        positivity
      dsimp [Bf,Kf]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hQt 2) (by positivity)
      · exact (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hQt 3)
          (by positivity)) hIntP h0 (by positivity)).trans_eq (by ring)
    have hfields' : CurvatureBound (fun y => s.E (t,y)) (D+K*(2*I)) ∧
        CurvatureBound (fun y => s.B (t,y)) (D+K*(2*I)) := ⟨hfields.1.mono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hInt2 hK)),
      hfields.2.mono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hInt2 hK))⟩
    have hp := hpart'.second_derivative_bound (by positivity) ((hs.f_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)) z
    have he := hfields'.1.second_derivative_bound (by positivity) ((hs.E_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)) z.1
    have hb := hfields'.2.second_derivative_bound (by positivity) ((hs.B_jets.1.1 t ⟨ht.1.le,ht.2.le⟩).differentiable (by simp)) z.1
    dsimp [secondJetSum]
    nlinarith
  intro t ht z
  have hcont : ContinuousOn (fun r => secondJetSum s r z) (Icc (0:ℝ) U) := by
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact (((hs.f_jets.1.2 2).comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))).norm
      · exact (((hs.E_jets.1.2 2).comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))).norm
    · exact (((hs.B_jets.1.2 2).comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))).norm
  have hgc : ContinuousOn (fun r => (6*Bf+12*D)+(6*Kf+24*K)*(∫ u in Icc (0:ℝ) r,1+g u)) (Icc (0:ℝ) U) :=
    continuousOn_const.add (continuousOn_const.mul (intervalIntegral.continuousOn_primitive_Icc
      ((continuous_const.add hg).continuousOn.integrableOn_compact isCompact_Icc)))
  apply le_on_closure (fun r hr => hinterior r hr z)
  · simpa only [_root_.closure_Ioo hU.ne] using hcont
  · simpa only [_root_.closure_Ioo hU.ne] using hgc
  · simpa only [_root_.closure_Ioo hU.ne] using ht

lemma bounded_momentum_second_jet_bound {d : Datum} (hd : Admissible d) (P H : ℝ) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (U : ℝ), 0<U → U≤H → ∀ (s : Solution),
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∀ t∈Icc (0:ℝ) U, ∀ z, secondJetSum s t z≤C := by
  obtain ⟨L,hL,hLb⟩ := bounded_momentum_field_bound hd P H hH
  obtain ⟨N,hN,hNb⟩ := bounded_momentum_field_gradient_bound hd P H hH
  obtain ⟨M,hM,hMb⟩ := bounded_momentum_particle_lipschitz_bound hd P H hH
  obtain ⟨A,hA⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  obtain ⟨D,K,hD,hK,hv⟩ := prefix_second_jet_volterra hd P (max A 0) L M N H hL hM hN hH
  obtain ⟨C,hC,hb⟩ := volterra_uniform_bound (α:=Phase) D K H hD hK
  refine ⟨C,hC,?_⟩
  intro U hU hUH s hs hP
  apply hb U hUH (secondJetSum s)
  · obtain ⟨Cf,hCf,hf⟩ := hs.f_jets.2 2
    obtain ⟨CE,hCE,hE⟩ := hs.E_jets.2 2
    obtain ⟨CB,hCB,hB⟩ := hs.B_jets.2 2
    exact ⟨Cf+CE+CB,by positivity,fun t ht z => add_le_add (add_le_add (hf t ht z) (hE t ht z.1)) (hB t ht z.1)⟩
  · apply hv s U hs hU hUH
    · intro t ht x v
      exact hs.classical.particle_bound_datum (A:=max A 0) hU
        (fun z => by simpa only [Real.norm_eq_abs] using (hA z).trans (le_max_left A 0)) t ht (x,v)
    · exact hP
    · intro t ht x
      have hh := hLb U hU hUH s hs hP t ht x
      exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans hh,(le_add_of_nonneg_left (norm_nonneg _)).trans hh⟩
    · exact hMb U hU hUH s hs hP
    · intro t ht x y
      constructor
      · apply spatial_field_lipschitz_of_gradient ((hs.E_jets.1.1 t ht).differentiable (by simp))
        intro z
        exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hNb U hU hUH s hs hP t ht z)
      · apply spatial_field_lipschitz_of_gradient ((hs.B_jets.1.1 t ht).differentiable (by simp))
        intro z
        exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hNb U hU hUH s hs hP t ht z)

lemma family_datum_restart_control {ι : Type*} {d : ι → Datum}
    (hd : ∀ j, Admissible (d j)) {A R P L J : ℝ}
    (hA : 0≤A) (hL : 0≤L) (hJ : 0≤J)
    (hf : ∀ j z, |(d j).f₀ z|≤A)
    (hrp : ∀ j (z : Phase), (d j).f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P)
    (hl : ∀ j z w, |(d j).f₀ z-(d j).f₀ w|≤L*‖z-w‖)
    (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
    (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J) :
    ∃ D D₁ : ℝ, 0≤D ∧ 0≤D₁ ∧ ∀ j, DatumRestartControl (d j) A R P D D₁ L := by
  have hp (j : ι) (x v : Vec) (hv : P<‖v‖) : (d j).f₀ (x,v)=0 := by
    by_contra hh
    exact (not_le_of_gt hv) (hrp j (x,v) hh).2
  have hfl (j : ι) (x y v : Vec) : |(d j).f₀ (y,v)-(d j).f₀ (x,v)|≤L*‖y-x‖ := by
    simpa only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using hl j (y,v) (x,v)
  choose CE hCE hEe using family_electricConeBoundary_datum_bound_global hd hA hJ hf hp hEj hBj
  choose CB hCB hBb using family_magneticConeBoundary_datum_bound_global hd hA hJ hf hp hEj hBj
  choose LE hLE hEl using family_electricConeBoundary_datum_lipschitz hd hL hJ hp hfl hEj hBj
  choose LB hLB hBl using family_magneticConeBoundary_datum_lipschitz hd hL hJ hp hfl hEj hBj
  let S := ∑ i : Fin 3, (CE i+CB i)
  let N := ∑ i : Fin 3, (LE i+LB i)
  have hS : 0≤S := Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i)
  have hN : 0≤N := Finset.sum_nonneg fun i _ => add_nonneg (hLE i) (hLB i)
  have hEC (i : Fin 3) : CE i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCB i]
  have hBC (i : Fin 3) : CB i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCE i]
  have hEL (i : Fin 3) : LE i≤N := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hLE j) (hLB j)) (Finset.mem_univ i)
    dsimp [N]; linarith [hLB i]
  have hBL (i : Fin 3) : LB i≤N := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hLE j) (hLB j)) (Finset.mem_univ i)
    dsimp [N]; linarith [hLE i]
  refine ⟨3*S+J,3*N+3*J,by positivity,by positivity,?_⟩
  intro j
  refine ⟨hf j,hrp j,?_,?_,?_,?_,hl j⟩
  · intro x
    have he : ‖(d j).E₀ x‖≤J := by simpa only [norm_iteratedFDeriv_zero] using hEj j 0 (by norm_num) x
    have hb : ‖(d j).B₀ x‖≤J := by simpa only [norm_iteratedFDeriv_zero] using hBj j 0 (by norm_num) x
    exact ⟨he.trans (by linarith),hb.trans (by linarith)⟩
  · intro t ht x
    exact ⟨(norm_le_three_of_coordinate_bound hS (v:=electricBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hEe i j t ht x).trans (hEC i))).trans (by linarith),
      (norm_le_three_of_coordinate_bound hS (v:=magneticBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hBb i j t ht x).trans (hBC i))).trans (by linarith)⟩
  · intro x y
    have he := (spatial_lipschitz_of_low_jets (hd j).2.2.2.1.1 hJ (hEj j) x y).1
    have hb := (spatial_lipschitz_of_low_jets (hd j).2.2.2.2.1.1 hJ (hBj j) x y).1
    exact ⟨he.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)),
      hb.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))⟩
  · intro t ht x y
    have he := norm_le_three_of_coordinate_bound (mul_nonneg hN (norm_nonneg (y-x)))
      (v:=electricBoundaryField (datumBoundarySolution (d j)) t y-electricBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hEl i j t ht x y).trans (mul_le_mul_of_nonneg_right (hEL i) (norm_nonneg _)))
    have hb := norm_le_three_of_coordinate_bound (mul_nonneg hN (norm_nonneg (y-x)))
      (v:=magneticBoundaryField (datumBoundarySolution (d j)) t y-magneticBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hBl i j t ht x y).trans (mul_le_mul_of_nonneg_right (hBL i) (norm_nonneg _)))
    constructor
    · exact he.trans (by nlinarith [mul_nonneg hJ (norm_nonneg (y-x))])
    · exact hb.trans (by nlinarith [mul_nonneg hJ (norm_nonneg (y-x))])

theorem family_bounded_classical_prefix {ι : Type*} {d : ι → Datum}
    (hd : ∀ j, Admissible (d j)) {A R P L J : ℝ}
    (hA : 0≤A) (hR : 0≤R) (hP : 0≤P) (hL : 0≤L) (hJ : 0≤J)
    (hf : ∀ j z, |(d j).f₀ z|≤A)
    (hrp : ∀ j (z : Phase), (d j).f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P)
    (hl : ∀ j z w, |(d j).f₀ z-(d j).f₀ w|≤L*‖z-w‖)
    (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
    (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J) :
    ∃ T : ℝ, 0<T ∧ ∀ j, ∃ s : Solution, BoundedClassicalPrefix (d j) s T := by
  obtain ⟨D,D₁,hD,hD₁,hcaps⟩ := family_datum_restart_control hd hA hL hJ hf hrp hl hEj hBj
  obtain ⟨T,hT,hfamily⟩ := family_local_spatially_smooth_bounded_classical hd hA hR hP hD hD₁ hL hcaps
  refine ⟨T,hT,?_⟩
  intro j
  obtain ⟨s,hs,heq,hf,hE,hB⟩ := hfamily j
  obtain ⟨hfs,hEs,hBs⟩ := hs.smooth hT heq hf.1 hE.1 hB.1
  exact ⟨s,hs.toSmooth hfs hEs hBs,heq,hf,hE,hB⟩

lemma SmoothClassicalPrefix.spatial_support_datum {d : Datum} {s : Solution} {U R : ℝ}
    (hs : SmoothClassicalPrefix d s U) (hU : 0<U)
    (hR : ∀ z : Phase, d.f₀ z≠0 → ‖z.1‖≤R) :
    ∀ t∈Icc (0:ℝ) U, ∀ z : Phase, s.f (t,z)≠0 → ‖z.1‖≤R+t := by
  obtain ⟨F⟩ := hs.exists_phaseFlowOn hU
  intro t ht z hz
  obtain ⟨w,rfl⟩ := (F.bijective t ht).surjective z
  have hw : d.f₀ w≠0 := by
    rw [F.transport hs.energyPrefix.f_smooth hs.energyPrefix.vlasov ht,hs.initial_f] at hz
    exact hz
  obtain ⟨c,hc,hl⟩ := F.timelike hU.le w
  have hdist := hl.dist_le_mul t ht 0 (show (0:ℝ)∈Icc (0:ℝ) U from ⟨le_rfl,hU.le⟩)
  simp only [F.initial,dist_eq_norm,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] at hdist
  calc
    ‖(F.flow w t).1‖ ≤ ‖(F.flow w t).1-w.1‖+‖w.1‖ := by
      simpa only [sub_add_cancel] using norm_add_le ((F.flow w t).1-w.1) w.1
    _ ≤ (c:ℝ)*t+R := add_le_add hdist (hR w hw)
    _ ≤ R+t := by nlinarith [ht.1]

theorem bounded_momentum_uniform_restart {d : Datum} (hd : Admissible d)
    (P H : ℝ) (hH : 0≤H) :
    ∃ δ : ℝ, 0<δ ∧ ∀ U : ℝ, 0<U → U≤H → ∀ s : Solution,
      BoundedClassicalPrefix d s U →
      (∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) →
      ∃ a : Solution, BoundedClassicalPrefix d a (U+δ) ∧
        ∀ t∈Icc (0:ℝ) U, (∀ z, a.f (t,z)=s.f (t,z)) ∧
          (∀ x, a.E (t,x)=s.E (t,x)) ∧ (∀ x, a.B (t,x)=s.B (t,x)) := by
  obtain ⟨A,R,P₀,hA,hR,hP₀,hfa,hrp⟩ := datum_particle_bounds hd
  obtain ⟨C₀,hC₀,hzero⟩ := bounded_momentum_field_bound hd P H hH
  obtain ⟨C₁,hC₁,hone⟩ := bounded_momentum_field_gradient_bound hd P H hH
  obtain ⟨C₂,hC₂,htwo⟩ := bounded_momentum_second_jet_bound hd P H hH
  obtain ⟨L,hL,hfl⟩ := bounded_momentum_particle_lipschitz_bound hd P H hH
  let I := {p : ℝ × Solution // 0<p.1 ∧ p.1≤H ∧ BoundedClassicalPrefix d p.2 p.1 ∧
    ∀ t∈Icc (0:ℝ) p.1, ∀ x v, P<‖v‖ → p.2.f (t,x,v)=0}
  let data : I → Datum := fun i => timeSliceDatum i.1.2 i.1.1
  have hi0 (i : I) : 0 < i.1.1 := i.2.1
  have hiH (i : I) : i.1.1≤H := i.2.2.1
  have hs (i : I) : BoundedClassicalPrefix d i.1.2 i.1.1 := i.2.2.2.1
  have hp (i : I) := i.2.2.2.2
  have hi (i : I) : i.1.1∈Icc (0:ℝ) i.1.1 := ⟨(hi0 i).le,le_rfl⟩
  have hdata (i : I) : Admissible (data i) :=
    (hs i).classical.slice_admissible (hs i).closed_equations (hs i).E_jets (hs i).B_jets (hi i)
  have hf (i : I) (z : Phase) : |(data i).f₀ z|≤A :=
    (hs i).classical.particle_bound_datum (hi0 i) hfa _ (hi i) z
  have hsupp (i : I) (z : Phase) (hz : (data i).f₀ z≠0) : ‖z.1‖≤R+H ∧ ‖z.2‖ ≤ max P 0 := by
    constructor
    · exact ((hs i).classical.spatial_support_datum (hi0 i) (fun z hz => (hrp z hz).1) _ (hi i) z hz).trans
        (by linarith [hiH i])
    · apply (le_of_not_gt ?_).trans (le_max_left P 0)
      intro hv
      exact hz (hp i _ (hi i) z.1 z.2 hv)
  have hLip (i : I) (z w : Phase) : |(data i).f₀ z-(data i).f₀ w|≤L*‖z-w‖ :=
    hfl _ (hi0 i) (hiH i) _ (hs i) (hp i) _ (hi i) z w
  let J := C₀+C₁+C₂
  have hJ : 0≤J := by dsimp [J]; positivity
  have hEz (i : I) (x : Vec) : ‖(data i).E₀ x‖≤C₀ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hzero _ (hi0 i) (hiH i) _ (hs i) (hp i) _ (hi i) x)
  have hBz (i : I) (x : Vec) : ‖(data i).B₀ x‖≤C₀ :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hzero _ (hi0 i) (hiH i) _ (hs i) (hp i) _ (hi i) x)
  have hEone (i : I) (x : Vec) : ‖fderiv ℝ (data i).E₀ x‖≤C₁ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hone _ (hi0 i) (hiH i) _ (hs i) (hp i) _ (hi i) x)
  have hBone (i : I) (x : Vec) : ‖fderiv ℝ (data i).B₀ x‖≤C₁ :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hone _ (hi0 i) (hiH i) _ (hs i) (hp i) _ (hi i) x)
  have hEtwo (i : I) (x : Vec) : ‖iteratedFDeriv ℝ 2 (data i).E₀ x‖≤C₂ := by
    have hh := htwo _ (hi0 i) (hiH i) _ (hs i) (hp i) _ (hi i) (x,0)
    dsimp [secondJetSum] at hh
    change ‖iteratedFDeriv ℝ 2 (fun y => i.1.2.E (i.1.1,y)) x‖≤C₂
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun w => i.1.2.f (i.1.1,w)) (x,0)),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => i.1.2.B (i.1.1,y)) x)]
  have hBtwo (i : I) (x : Vec) : ‖iteratedFDeriv ℝ 2 (data i).B₀ x‖≤C₂ := by
    have hh := htwo _ (hi0 i) (hiH i) _ (hs i) (hp i) _ (hi i) (x,0)
    dsimp [secondJetSum] at hh
    change ‖iteratedFDeriv ℝ 2 (fun y => i.1.2.B (i.1.1,y)) x‖≤C₂
    linarith [norm_nonneg (iteratedFDeriv ℝ 2 (fun w => i.1.2.f (i.1.1,w)) (x,0)),
      norm_nonneg (iteratedFDeriv ℝ 2 (fun y => i.1.2.E (i.1.1,y)) x)]
  have hEj (i : I) (k : ℕ) (hk : k≤2) (x : Vec) : ‖iteratedFDeriv ℝ k (data i).E₀ x‖≤J := by
    interval_cases k
    · simpa only [norm_iteratedFDeriv_zero] using (hEz i x).trans (by dsimp [J]; linarith)
    · simpa only [norm_iteratedFDeriv_one] using (hEone i x).trans (by dsimp [J]; linarith)
    · exact (hEtwo i x).trans (by dsimp [J]; linarith)
  have hBj (i : I) (k : ℕ) (hk : k≤2) (x : Vec) : ‖iteratedFDeriv ℝ k (data i).B₀ x‖≤J := by
    interval_cases k
    · simpa only [norm_iteratedFDeriv_zero] using (hBz i x).trans (by dsimp [J]; linarith)
    · simpa only [norm_iteratedFDeriv_one] using (hBone i x).trans (by dsimp [J]; linarith)
    · exact (hBtwo i x).trans (by dsimp [J]; linarith)
  obtain ⟨δ,hδ,hfamily⟩ := family_bounded_classical_prefix hdata hA (add_nonneg hR hH)
    (le_max_right P 0) hL hJ hf hsupp hLip hEj hBj
  refine ⟨δ,hδ,?_⟩
  intro U hU hUH s hss hP
  let i : I := ⟨(U,s),hU,hUH,hss,hP⟩
  obtain ⟨a,ha⟩ := hfamily i
  refine ⟨pasteSolution U s a,hss.paste hU hδ ha,?_⟩
  intro t ht
  exact ⟨congrFun (timePaste_left U s.f a.f ht.2),congrFun (timePaste_left U s.E a.E ht.2),
    congrFun (timePaste_left U s.B a.B ht.2)⟩

theorem bounded_momentum_arbitrarily_long_prefix {d : Datum} (hd : Admissible d)
    (H : ℝ) (hH : 0≤H) (P : ℝ)
    (hP : ∀ U : ℝ, 0<U → U≤H → ∀ s : Solution,
      BoundedClassicalPrefix d s U →
      ∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) :
    ∃ U : ℝ, H<U ∧ ∃ s : Solution, BoundedClassicalPrefix d s U := by
  by_contra hn
  have hup (U : ℝ) (s : Solution) (hs : BoundedClassicalPrefix d s U) : U≤H := by
    by_contra hh
    exact hn ⟨U,lt_of_not_ge hh,s,hs⟩
  obtain ⟨δ,hδ,hext⟩ := bounded_momentum_uniform_restart hd P H hH
  obtain ⟨T,hT,s₀,hs₀⟩ := exists_bounded_classical_prefix d hd
  have grow : ∀ n : ℕ, ∃ U : ℝ, 0<U ∧ (n:ℝ)*δ≤U ∧
      ∃ s : Solution, BoundedClassicalPrefix d s U := by
    intro n
    induction n with
    | zero => exact ⟨T,hT,by simp; exact hT.le,s₀,hs₀⟩
    | succ n ih =>
      obtain ⟨U,hU,hnU,s,hs⟩ := ih
      obtain ⟨a,ha,_⟩ := hext U hU (hup U s hs) s hs (hP U hU (hup U s hs) s hs)
      refine ⟨U+δ,by linarith,?_,a,ha⟩
      push_cast
      nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt (H/δ)
  obtain ⟨U,hU,hnum,s,hs⟩ := grow n
  have hh : H<(n:ℝ)*δ := (div_lt_iff₀ hδ).mp hn
  linarith [hup U s hs]

lemma time_slab_mem_nhdsWithin {X : Type*} [TopologicalSpace X]
    {p : ℝ × X} {H : ℝ} (hp : p.1<H) :
    {z : ℝ × X | z.1∈Icc (0:ℝ) H} ∈ 𝓝[{z : ℝ × X | 0 ≤ z.1}] p := by
  have hh : {z : ℝ × X | z.1<H} ∈ 𝓝 p :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hp
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hh] with z hz hzH
  exact ⟨hz,hzH.le⟩

lemma contDiffOn_halfspace_of_slabs {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ × X → Y} {k : ℕ∞ω}
    (hf : ∀ T : ℝ, 0 ≤ T → ContDiffOn ℝ k f {z : ℝ × X | z.1∈Icc (0:ℝ) T}) :
    ContDiffOn ℝ k f {z : ℝ × X | 0 ≤ z.1} := by
  intro p hp
  change 0 ≤ p.1 at hp
  exact (hf (p.1+1) (by linarith) p ⟨hp,by linarith⟩).mono_of_mem_nhdsWithin
    (time_slab_mem_nhdsWithin (by linarith))

lemma timeContinuousL2_of_slabs {F : Field}
    (hF : ∀ H : ℝ, 0 ≤ H → ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec),
      ContinuousOn G (Icc (0:ℝ) H) ∧
      ∀ t∈Icc (0:ℝ) H, (G t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    TimeContinuousL2 F := by
  choose G hG he using fun H : ℝ => hF (max H 0) (le_max_right H 0)
  let g : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t => G t t
  have hself (t : ℝ) (ht : 0 ≤ t) : (g t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x)) :=
    he t t ⟨ht,le_max_left t 0⟩
  have heq (H t : ℝ) (ht : t∈Icc (0:ℝ) H) : g t=G H t := by
    apply Lp.ext
    exact (hself t ht.1).trans (he H t ⟨ht.1,ht.2.trans (le_max_left H 0)⟩).symm
  refine ⟨g,?_,hself⟩
  intro t ht
  have hmem : Icc (0:ℝ) (max (t+1) 0) ∈ 𝓝[Ici 0] t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<t+1 by linarith))] with r hr hrH
    exact ⟨hr,hrH.le.trans (le_max_left (t+1) 0)⟩
  have hc := (hG (t+1) t ⟨ht,by linarith [le_max_left (t+1) 0]⟩).mono_of_mem_nhdsWithin hmem
  apply hc.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<t+1 by linarith))] with r hr hrH
  exact heq (t+1) r ⟨hr,hrH.le⟩

theorem global_classical_of_arbitrarily_long_prefixes {d : Datum}
    (hpre : ∀ H : ℝ, 0 ≤ H → ∃ U : ℝ, H<U ∧ ∃ a : Solution, SmoothClassicalPrefix d a U) :
    ∃ s : Solution, Classical d s ∧ SmoothOnFiniteHorizons s ∧
      ∀ s' : Solution, Classical d s' → SameNonnegativeTime s s' := by
  choose U hU a ha using fun H : ℝ => hpre (max H 0) (le_max_right H 0)
  let s : Solution := ⟨fun p => (a p.1).f p,fun p => (a p.1).E p,fun p => (a p.1).B p⟩
  have heq (H t : ℝ) (ht : t∈Icc (0:ℝ) H) :
      (∀ z, s.f (t,z)=(a H).f (t,z)) ∧
      (∀ x, s.E (t,x)=(a H).E (t,x)) ∧ (∀ x, s.B (t,x)=(a H).B (t,x)) := by
    exact (ha t).unique (ha H) ht.1 ((le_max_left t 0).trans (hU t).le)
      (ht.2.trans ((le_max_left H 0).trans (hU H).le))
  have hsm : SmoothOnFiniteHorizons s := by
    intro T hT
    have htU : T ≤ U T := (le_max_left T 0).trans (hU T).le
    have hh := (ha T).mono htU
    exact ⟨hh.f_smooth.congr (fun p hp => (heq T p.1 hp).1 p.2),
      hh.E_smooth.congr (fun p hp => (heq T p.1 hp).2.1 p.2),
      hh.B_smooth.congr (fun p hp => (heq T p.1 hp).2.2 p.2)⟩
  have hregf : ContDiffOn ℝ 1 s.f particleHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).1.of_le (by simp))
  have hregE : ContDiffOn ℝ 1 s.E fieldHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).2.1.of_le (by simp))
  have hregB : ContDiffOn ℝ 1 s.B fieldHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).2.2.of_le (by simp))
  have hpos (t : ℝ) (ht : 0 ≤ t) (z : Phase) : 0 ≤ s.f (t,z) :=
    (ha t).nonnegative t ⟨ht,(le_max_left t 0).trans (hU t).le⟩ z
  have hL2E : TimeContinuousL2 s.E := by
    apply timeContinuousL2_of_slabs
    intro H hH
    obtain ⟨G,hG,hrep⟩ := (ha H).E_L2
    refine ⟨G,hG.mono (Icc_subset_Icc_right ((le_max_left H 0).trans (hU H).le)),?_⟩
    intro t ht
    exact (hrep t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩).trans
      (Filter.Eventually.of_forall fun x => ((heq H t ht).2.1 x).symm)
  have hL2B : TimeContinuousL2 s.B := by
    apply timeContinuousL2_of_slabs
    intro H hH
    obtain ⟨G,hG,hrep⟩ := (ha H).B_L2
    refine ⟨G,hG.mono (Icc_subset_Icc_right ((le_max_left H 0).trans (hU H).le)),?_⟩
    intro t ht
    exact (hrep t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩).trans
      (Filter.Eventually.of_forall fun x => ((heq H t ht).2.2 x).symm)
  have hcompact : CompactOnFiniteHorizons s := by
    intro H hH
    obtain ⟨K,hK,hk⟩ := (ha H).compact
    refine ⟨K,hK,?_⟩
    intro t ht
    rw [show (fun z => s.f (t,z))=(fun z => (a H).f (t,z)) from funext (heq H t ht).1]
    exact hk t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩
  have hequations : Equations s := by
    intro t ht
    let H := t+1
    have htH : t ≤ H := by dsimp [H]; linarith
    have htU : t<U H := lt_of_le_of_lt (htH.trans (le_max_left H 0)) (hU H)
    have hh := (ha H).equations t ht htU
    have heqt := heq H t ⟨ht,htH⟩
    have hf (z : Phase) :
        derivWithin (fun r => s.f (r,z)) (Ici 0) t =
          derivWithin (fun r => (a H).f (r,z)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).1 z
    have hE (x : Vec) :
        derivWithin (fun r => s.E (r,x)) (Ici 0) t =
          derivWithin (fun r => (a H).E (r,x)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).2.1 x
    have hB (x : Vec) :
        derivWithin (fun r => s.B (r,x)) (Ici 0) t =
          derivWithin (fun r => (a H).B (r,x)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).2.2 x
    simpa only [hf,hE,hB,heqt.1,heqt.2.1,heqt.2.2] using hh
  have hc : Classical d s := ⟨hregf,hregE,hregB,hpos,hL2E,hL2B,hcompact,hequations,
    (ha 0).initial_f,(ha 0).initial_E,(ha 0).initial_B⟩
  exact ⟨s,hc,hsm,fun s' hs' => classical_unique hc hs'⟩

theorem global_classical_of_uniform_prefix_momentum {d : Datum} (hd : Admissible d)
    (hMom : ∀ H : ℝ, 0 ≤ H → ∃ P : ℝ, ∀ U : ℝ, 0<U → U ≤ H → ∀ s : Solution,
      BoundedClassicalPrefix d s U →
      ∀ t∈Icc (0:ℝ) U, ∀ x v, P<‖v‖ → s.f (t,x,v)=0) :
    ∃ s : Solution, Classical d s ∧ SmoothOnFiniteHorizons s ∧
      ∀ s' : Solution, Classical d s' → SameNonnegativeTime s s' := by
  apply global_classical_of_arbitrarily_long_prefixes
  intro H hH
  obtain ⟨P,hP⟩ := hMom H hH
  obtain ⟨U,hU,s,hs⟩ := bounded_momentum_arbitrarily_long_prefix hd H hH P hP
  exact ⟨U,hU,s,hs.classical⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

theorem global_classical_of_uniform_physical_increment {d : Datum} (hd : Admissible d)
    (hproducer : ∀ H : ℝ, 0 ≤ H → ∃ M A P₀ : ℝ, 0 < M ∧ 0 < A ∧
      ∀ U : ℝ, 0 < U → U ≤ H → ∀ s : Solution,
      BoundedClassicalPrefix d s U → ∀ F : PhaseFlowOn s.E s.B U,
        PopulationIncrement (fun z t => (F.flow z t).2) (tsupport d.f₀) U M A P₀) :
    ∃ s : Solution, Classical d s ∧ SmoothOnFiniteHorizons s ∧
      ∀ s' : Solution, Classical d s' → SameNonnegativeTime s s' := by
  classical
  apply global_classical_of_uniform_prefix_momentum hd
  intro H hH
  obtain ⟨M,A,P₀,hM,hA,hinc⟩ := hproducer H hH
  let ι := {p : ℝ × Solution // 0 < p.1 ∧ p.1 ≤ H ∧ BoundedClassicalPrefix d p.2 p.1}
  let F (i : ι) : PhaseFlowOn i.val.2.E i.val.2.B i.val.1 :=
    Classical.choice (i.property.2.2.classical.exists_phaseFlowOn i.property.1)
  obtain ⟨P,hP⟩ := hd.uniform_physical_support_of_increment
    (ι:=ι) (s:=fun i => i.val.2) (T:=fun i => i.val.1) (H:=H)
    (fun i => i.property.1) (fun i => i.property.2.1) F
    (fun i => i.property.2.2.classical.energyPrefix)
    (fun i => i.property.2.2.classical.initial_f)
    hM hA (fun i => hinc i.val.1 i.property.1 i.property.2.1 i.val.2 i.property.2.2 (F i))
  refine ⟨P,?_⟩
  intro U hU hUH s hs t ht x v hv
  exact hP ⟨(U,s),hU,hUH,hs⟩ t ht x v hv

end RVM

end

end OAI
