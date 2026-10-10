import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.BranchIntegral

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_normalised_physical_kernel (P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec, ‖E‖≤L → ‖B‖≤L →
      ‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C := by
  let K : Set (ℝ × Vec × Vec × Vec × Vec) :=
    Icc 0 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P ×ˢ
      closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))
  let r : (ℝ × Vec × Vec × Vec × Vec) → ℝ := Prod.fst
  let n : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.1
  let v : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.1
  let E : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.1
  let B : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.2
  have hr : Continuous r := continuous_fst
  have hn : Continuous n := continuous_snd.fst
  have hv : Continuous v := continuous_snd.snd.fst
  have hE : Continuous E := continuous_snd.snd.snd.fst
  have hB : Continuous B := continuous_snd.snd.snd.snd
  have hu := (contDiff_velocity (k:=1)).continuous.comp hv
  have ha : Continuous (fun p => fderiv ℝ velocity (v p) (E p+cross (velocity (v p)) (B p))) :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp hv).clm_apply
      (hE.add ((contDiff_cross (k:=1)).continuous.comp (hu.prodMk hB)))
  have hd : Continuous (fun p => 1-dot (n p) (velocity (v p))) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hk := hd.continuousOn.smul (continuousOn_normalisedElectricKernel
    hr.continuousOn hn.continuousOn hu.continuousOn ha.continuousOn (S:=K) (by
      intro p hp
      exact (cone_denom_pos (v p) (n p) (by simpa only [n,mem_sphere,dist_zero_right] using hp.2.1)).ne'))
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hk).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro r hr n hn v hv E B hE hB
  apply le_trans (hC _ ⟨(r,n,v,E,B),?_,rfl⟩) (le_max_right _ _)
  exact ⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall_zero_iff] using hv,
    by simpa only [mem_closedBall_zero_iff] using hE,
    by simpa only [mem_closedBall_zero_iff] using hB⟩

lemma uniform_physical_kernel (P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec, ‖E‖≤L → ‖B‖≤L →
      ‖(1-dot n (velocity v)) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C/r^2 := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_physical_kernel P L
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv E B hE hB
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv E B hE hB
  rw [normalisedElectricKernel_eq hr.1.ne',smul_comm (1-dot n (velocity v)),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma physical_integral_bound {A P C r : ℝ} {n E B : Vec} {f : Vec → ℝ}
    (hA : 0≤A)
    (hbound : ∀ v : Vec, ‖v‖≤P →
      ‖(1-dot n (velocity v)) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C/r^2)
    (hf : ∀ v, |f v|≤A) (hs : ∀ v, P<‖v‖ → f v=0) :
    ‖∫ v : Vec, (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤
      (A*C*volume.real (closedBall (0:Vec) P))/r^2 := by
  let g : Vec → Vec := fun v => (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
    (fderiv ℝ velocity v (E+cross (velocity v) B))
  have he : (∫ v in closedBall (0:Vec) P, g v)=∫ v, g v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hv' : P<‖v‖ := by simpa only [mem_closedBall_zero_iff,not_le] using hv
    simp [g,hs v hv']
  change ‖∫ v, g v‖≤_
  rw [← he]
  have hb : ∀ v∈closedBall (0:Vec) P, ‖g v‖≤A*(C/r^2) := by
    intro v hv
    have hv' : ‖v‖≤P := mem_closedBall_zero_iff.mp hv
    dsimp [g]
    rw [mul_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hf v) (hbound v hv') (norm_nonneg _) hA
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume) (isCompact_closedBall (0:Vec) P).measure_lt_top hb
  exact hh.trans_eq (by ring)

lemma uniform_retarded_density_bound (A P L : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ), T≤1 →
      (∀ t∈Icc 0 T, ∀ z, |s.f (t,z)|≤A) →
      (∀ t∈Icc 0 T, ∀ (x v : Vec), s.f (t,x,v)≠0 →
        ‖v‖≤P ∧ ‖s.E (t,x)‖≤L ∧ ‖s.B (t,x)‖≤L) →
      ∀ t∈Icc 0 T, ∀ (x z : Vec), 0<‖z‖ → ‖z‖≤t →
        ‖retardedElectricDensity s t x (x+z)‖≤C/‖z‖^2 ∧
        ‖retardedMagneticDensity s t x (x+z)‖≤C/‖z‖^2 := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_kernel P L
  refine ⟨A*K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro s T hT hf hs t ht x z hz hzt
  have htime : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hxy : x≠x+z := by
    intro he
    have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa using he.symm)
    exact (norm_pos_iff.mp hz) hh
  have he : ‖retardedElectricDensity s t x (x+z)‖≤
      (A*K*volume.real (closedBall (0:Vec) P))/‖z‖^2 := by
    by_cases hn : ∃ v : Vec, s.f (t-‖z‖,x+z,v)≠0
    · obtain ⟨v,hv⟩ := hn
      have hEB := hs _ htime _ v hv
      unfold retardedElectricDensity
      rw [coneRadius_add]
      apply physical_integral_bound hA
      · intro u hu
        exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hT)⟩ _ (coneDirection_norm hxy)
          u hu _ _ hEB.2.1 hEB.2.2
      · intro u
        exact hf _ htime (x+z,u)
      · intro u hu
        by_contra hnu
        exact (not_lt_of_ge (hs _ htime _ u hnu).1) hu
    · have hzero : ∀ v : Vec, s.f (t-‖z‖,x+z,v)=0 := by simpa using hn
      simp only [retardedElectricDensity,coneRadius_add,hzero,zero_mul,zero_smul,integral_zero,norm_zero]
      positivity
  refine ⟨he,?_⟩
  exact (norm_cross_le _ _).trans (by simpa only [coneDirection_norm hxy,one_mul] using he)

lemma kernel_tip_le_on {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : IntegrableOn F (ball (0:Vec) R))
    (hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖^2) :
    ‖∫ z in ball (0:Vec) R, F z‖≤4*Real.pi*C*R := by
  have hbound : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C*‖z‖^(-(2:ℝ)) := by
    simpa only [Real.rpow_neg (norm_nonneg _),Real.rpow_two,div_eq_mul_inv] using hb
  have hi := integrableOn_norm_rpow_neg (R:=R) (by norm_num : (2:ℝ)<3)
  calc
    _ ≤ ∫ z in ball (0:Vec) R, ‖F z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in ball (0:Vec) R, C*‖z‖^(-(2:ℝ)) := integral_mono_ae hF.norm (hi.const_mul C) hbound
    _ = 4*Real.pi*C*R := by
      rw [integral_const_mul,integral_ball_norm_rpow_neg (by norm_num : (2:ℝ)<3) hR]
      norm_num only [show (3:ℝ)-2=1 by norm_num,Real.rpow_one,div_one]
      ring

namespace SmoothLorentzFlow

lemma spatial_travel_bound {E B : Field} (F : SmoothLorentzFlow E B) (z : Phase)
    {T t : ℝ} (ht : t∈Icc 0 T) : ‖(F.forward z t).1-z.1‖≤t := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f:=fun r => (F.forward z r).1) (f':=fun r => velocity (F.forward z r).2)
    (fun r (_ : r∈Icc 0 T) => ((ContinuousLinearMap.fst ℝ Vec Vec).hasFDerivAt.comp_hasDerivAt r (F.ode z r)).hasDerivWithinAt)
    (fun r (_ : r∈Ico 0 T) => (norm_velocity_lt_one _).le) t ht
  simpa only [F.initial,one_mul,sub_zero] using hh

lemma momentum_travel_bound {E B : Field} (F : SmoothLorentzFlow E B) (z : Phase)
    {T t R L : ℝ} (ht : t∈Icc 0 T) (hz : ‖z.1‖+T≤R)
    (_hL : 0≤L) (hE : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R → ‖E (r,x)‖≤L)
    (hB : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R → ‖B (r,x)‖≤L) :
    ‖(F.forward z t).2-z.2‖≤(2*L)*t := by
  have hspace (r : ℝ) (hr : r∈Icc 0 T) : ‖(F.forward z r).1‖≤R := by
    calc
      _ ≤ ‖(F.forward z r).1-z.1‖+‖z.1‖ := norm_le_norm_sub_add _ _
      _ ≤ r+‖z.1‖ := add_le_add (F.spatial_travel_bound z hr) le_rfl
      _ ≤ R := by linarith [hr.2]
  have hb (r : ℝ) (hr : r∈Ico 0 T) :
      ‖E (r,(F.forward z r).1)+cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1))‖≤2*L := by
    have hh := Ico_subset_Icc_self hr
    calc
      _ ≤ ‖E (r,(F.forward z r).1)‖+‖cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1))‖ := norm_add_le _ _
      _ ≤ L + 1*L := add_le_add (hE r hh _ (hspace r hh))
        ((norm_cross_le _ _).trans (mul_le_mul (norm_velocity_lt_one _).le
          (hB r hh _ (hspace r hh)) (norm_nonneg _) (by norm_num)))
      _ = 2*L := by ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f:=fun r => (F.forward z r).2)
    (f':=fun r => E (r,(F.forward z r).1)+cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1)))
    (fun r (_ : r∈Icc 0 T) => ((ContinuousLinearMap.snd ℝ Vec Vec).hasFDerivAt.comp_hasDerivAt r (F.ode z r)).hasDerivWithinAt) hb t ht
  simpa only [F.initial,sub_zero] using hh

lemma transport_for {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,F.forward z t)=s.f (0,z) := by
  have hd (r : ℝ) : HasDerivAt (fun r => s.f (r,F.forward z r)) (0:ℝ) r := by
    have hh := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (F.ode z r))
    change HasDerivAt (fun r => s.f (r,F.forward z r))
      (fderiv ℝ s.f (r,F.forward z r) (1,lorentzField E B (r,F.forward z r))) r at hh
    rw [hV] at hh
    exact hh
  have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [F.initial] using he

lemma transport_for_inverse {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,z)=s.f (0,F.backward (t,z)) := by
  simpa only [F.right_inverse] using F.transport_for hf hV t (F.backward (t,z))

lemma transported_sup_bound {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) {A : ℝ}
    (hA : ∀ z, |s.f (0,z)|≤A) (t : ℝ) (z : Phase) : |s.f (t,z)|≤A := by
  rw [F.transport_for_inverse hf hV]
  exact hA _

lemma transported_phase_bound {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) {R₀ P₀ T L t : ℝ}
    (h₀ : ∀ z : Phase, s.f (0,z)≠0 → ‖z.1‖≤R₀ ∧ ‖z.2‖≤P₀)
    (hL : 0≤L) (hE : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R₀+T → ‖E (r,x)‖≤L)
    (hB : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R₀+T → ‖B (r,x)‖≤L)
    (ht : t∈Icc 0 T) (z : Phase) (hz : s.f (t,z)≠0) :
    ‖z.1‖≤R₀+t ∧ ‖z.2‖≤P₀+2*L*t := by
  let z₀ := F.backward (t,z)
  have he : F.forward z₀ t=z := F.right_inverse t z
  have hz₀ : s.f (0,z₀)≠0 := by
    rw [← F.transport_for_inverse hf hV]
    exact hz
  have hb := h₀ z₀ hz₀
  have hx := F.spatial_travel_bound z₀ ht
  have hv := F.momentum_travel_bound z₀ ht (by linarith [hb.1]) hL hE hB
  rw [he] at hx hv
  constructor
  · exact (norm_le_norm_sub_add z.1 z₀.1).trans (by linarith [hb.1])
  · exact (norm_le_norm_sub_add z.2 z₀.2).trans (by linarith [hb.2])

end SmoothLorentzFlow

lemma datum_boundary_uniform_bound {d : Datum} (hd : Admissible d) (R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ (∀ x, ‖d.E₀ x‖≤C ∧ ‖d.B₀ x‖≤C) ∧
      ∀ t∈Ioc (0:ℝ) 1, ∀ x∈closedBall (0:Vec) R,
        ‖electricBoundaryField (datumBoundarySolution d) t x‖≤C ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤C := by
  choose CE hCE hEe using fun i : Fin 3 => electricConeBoundary_datum_bound hd 1 R i
  choose CB hCB hBb using fun i : Fin 3 => magneticConeBoundary_datum_bound hd 1 R i
  obtain ⟨E₀,hE₀⟩ := hd.2.2.2.1.2 0
  obtain ⟨B₀,hB₀⟩ := hd.2.2.2.2.1.2 0
  let S := (∑ i : Fin 3, CE i)+(∑ i : Fin 3, CB i)
  have hS : 0≤S := add_nonneg (Finset.sum_nonneg (fun i _ => hCE i))
    (Finset.sum_nonneg (fun i _ => hCB i))
  let C := 3*S+max E₀ 0+max B₀ 0
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_,?_⟩
  · intro x
    constructor
    · have hh : ‖d.E₀ x‖≤E₀ := by simpa only [norm_iteratedFDeriv_zero] using hE₀ x
      dsimp [C]
      linarith [le_max_left E₀ 0,le_max_right B₀ 0]
    · have hh : ‖d.B₀ x‖≤B₀ := by simpa only [norm_iteratedFDeriv_zero] using hB₀ x
      dsimp [C]
      linarith [le_max_left B₀ 0,le_max_right E₀ 0]
  · intro t ht x hx
    have hEe' : ‖electricBoundaryField (datumBoundarySolution d) t x‖≤3*S := by
      apply norm_le_three_of_coordinate_bound hS
      intro i
      exact (hEe i t ht x hx).trans (by
        have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hCE j) (Finset.mem_univ i)
        have hh' : 0≤∑ j : Fin 3, CB j := Finset.sum_nonneg (fun j _ => hCB j)
        dsimp [S]
        linarith)
    have hBb' : ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤3*S := by
      apply norm_le_three_of_coordinate_bound hS
      intro i
      exact (hBb i t ht x hx).trans (by
        have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hCB j) (Finset.mem_univ i)
        have hh' : 0≤∑ j : Fin 3, CE j := Finset.sum_nonneg (fun j _ => hCE j)
        dsimp [S]
        linarith)
    have hh : 3*S≤C := by dsimp [C]; linarith [le_max_right E₀ 0,le_max_right B₀ 0]
    exact ⟨hEe'.trans hh,hBb'.trans hh⟩

lemma mixed_physical_vector {s : Solution} {E B : Field}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ s.E) (hB' : ContDiff ℝ ∞ s.B)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s E B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor s) {t : ℝ} (ht : 0<t) (x : Vec) :
    s.E (t,x)=electricBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity {s with E:=E,B:=B} t x (x+z) ∧
    s.B (t,x)=magneticBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity {s with E:=E,B:=B} t x (x+z) := by
  have hf1 : ContDiffOn ℝ 1 s.f particleHalfSpace := (hf.of_le (by simp)).contDiffOn
  have hE1 : ContDiffOn ℝ 1 E fieldHalfSpace := (hE.of_le (by simp)).contDiffOn
  have hB1 : ContDiffOn ℝ 1 B fieldHalfSpace := (hB.of_le (by simp)).contDiffOn
  constructor
  · ext i
    have hD := integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_electric_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hρ hj hM ht x i).trans
      (by simpa only [electricBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => electricConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)
  · ext i
    have hD := integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_magnetic_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hj hM ht x i).trans
      (by simpa only [magneticBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => magneticConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

lemma scaled_kernel_tip_le_on {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : IntegrableOn F (ball (0:Vec) R))
    (hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖^2) :
    ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) R, F z‖≤C*R := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(4*Real.pi)⁻¹)]
  calc
    _ ≤ (4*Real.pi)⁻¹*(4*Real.pi*C*R) :=
      mul_le_mul_of_nonneg_left (kernel_tip_le_on hR hF hb) (by positivity)
    _ = C*R := by field_simp

lemma mixed_fields_bound {s : Solution} {E B : Field}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ s.E) (hB' : ContDiff ℝ ∞ s.B)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s E B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor s) {t C D : ℝ} (ht : 0<t) (x : Vec)
    (hD : ‖electricBoundaryField s t x‖≤D ∧ ‖magneticBoundaryField s t x‖≤D)
    (hden : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
      ‖retardedElectricDensity {s with E:=E,B:=B} t x (x+z)‖≤C/‖z‖^2 ∧
      ‖retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)‖≤C/‖z‖^2) :
    ‖s.E (t,x)‖≤D+C*t ∧ ‖s.B (t,x)‖≤D+C*t := by
  have hf1 : ContDiffOn ℝ 1 s.f particleHalfSpace := (hf.of_le (by simp)).contDiffOn
  have hE1 : ContDiffOn ℝ 1 E fieldHalfSpace := (hE.of_le (by simp)).contDiffOn
  have hB1 : ContDiffOn ℝ 1 B fieldHalfSpace := (hB.of_le (by simp)).contDiffOn
  have he := mixed_physical_vector hf hE hB hE' hB' hc hV hρ hj hM ht x
  have hEe : ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
      retardedElectricDensity {s with E:=E,B:=B} t x (x+z)‖≤C*t := by
    apply scaled_kernel_tip_le_on ht.le
      (integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x)
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact (hden z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le).1
  have hBb : ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
      retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)‖≤C*t := by
    apply scaled_kernel_tip_le_on ht.le
      (integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x)
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact (hden z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le).2
  constructor
  · rw [he.1]
    exact (norm_add_le _ _).trans (add_le_add hD.1 hEe)
  · rw [he.2]
    exact (norm_add_le _ _).trans (add_le_add hD.2 hBb)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

structure PicardRegular (d : Datum) (s : Solution) : Prop where
  smooth_f : ContDiff ℝ ∞ s.f
  smooth_E : ContDiff ℝ ∞ s.E
  smooth_B : ContDiff ℝ ∞ s.B
  nonneg : ∀ p, 0 ≤ s.f p
  compact : CompactOnFiniteHorizons s
  l2E : TimeContinuousL2 s.E
  l2B : TimeContinuousL2 s.B
  initial_f : ∀ z, s.f (0,z)=d.f₀ z
  initial_E : ∀ x, s.E (0,x)=d.E₀ x
  initial_B : ∀ x, s.B (0,x)=d.B₀ x
  maxwell : MaxwellFor s
  smooth_rho : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2)
  smooth_current : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2)

theorem exists_picard_regular {d : Datum} (hd : Admissible d) {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ∃ s : Solution, PicardRegular d s ∧ TransportFor s E B := by
  obtain ⟨hf,hc,hn,hE0,hB0,hEL,hBL,hDE,hDB⟩ := hd
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  let f := F.particle d.f₀
  let ρ : ℝ × Vec → ℝ := fun p => rho (fun z => f (p.1,z)) p.2
  let j : Field := fun p => current (fun z => f (p.1,z)) p.2
  have hρ : ContDiff ℝ ∞ ρ := F.rho_smooth hf hc
  have hj : ContDiff ℝ ∞ j := F.current_smooth hf hc
  have hρ0 (x : Vec) : divergence d.E₀ x=ρ (0,x) := by
    simpa only [ρ,f,F.particle_initial] using hDE x
  let s : Solution := ⟨f,maxwellElectric d.E₀ d.B₀ ρ j,maxwellMagnetic d.E₀ d.B₀ j⟩
  have hsc : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0 := by
    intro t ht x
    rw [spaceDiv_slice (hj.differentiable (by simp))]
    exact F.source_conservation hf hc t x
  obtain ⟨hLe,hLb⟩ := maxwell_timeContinuousL2 hE0.1 hB0.1 hρ hj hEL hBL hρ0 hDB (by
    intro T hT
    obtain ⟨R,hR,hz⟩ := F.source_spatial_support hc (-1) (T+1)
    exact ⟨R,hz⟩)
  refine ⟨s,?_,F.particle_vlasov_direction hf⟩
  exact ⟨F.contDiff_particle hf,contDiff_maxwellElectric hE0.1 hB0.1 hρ hj,
    contDiff_maxwellMagnetic hE0.1 hB0.1 hj,F.particle_nonneg hn,
    fun T _ => F.particle_compact hc 0 T,hLe,hLb,F.particle_initial d.f₀,
    maxwellElectric_initial hE0.1,maxwellMagnetic_initial hB0.1,
    fun t ht x => constructed_maxwell_equations hE0.1 hB0.1 hρ hj hsc hρ0 hDB ht x,
    hρ,hj⟩

def LocalFieldBound (T R L : ℝ) (E B : Field) : Prop :=
  ∀ t∈Icc 0 T, ∀ x : Vec, ‖x‖≤R → ‖E (t,x)‖≤L ∧ ‖B (t,x)‖≤L

def LocalParticleBound (T A R P : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc 0 T, ∀ x v : Vec, |f (t,x,v)|≤A ∧
    (f (t,x,v)≠0 → ‖x‖≤R ∧ ‖v‖≤P)

lemma datum_particle_bounds {d : Datum} (hd : Admissible d) :
    ∃ A R P : ℝ, 0≤A ∧ 0≤R ∧ 0≤P ∧ (∀ z, |d.f₀ z|≤A) ∧
      ∀ z : Phase, d.f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P := by
  obtain ⟨A,hA⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  obtain ⟨R,hR⟩ := (hd.2.1.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨P,hP⟩ := (hd.2.1.image continuous_snd).isBounded.exists_norm_le
  refine ⟨max A 0,max R 0,max P 0,le_max_right _ _,le_max_right _ _,le_max_right _ _,
    fun z => (hA z).trans (le_max_left _ _),?_⟩
  intro z hz
  exact ⟨(hR _ ⟨z,subset_tsupport _ hz,rfl⟩).trans (le_max_left _ _),
    (hP _ ⟨z,subset_tsupport _ hz,rfl⟩).trans (le_max_left _ _)⟩

lemma PicardRegular.boundary_eq {d : Datum} {s : Solution} (hs : PicardRegular d s)
    {t : ℝ} (ht : 0<t) (x : Vec) :
    electricBoundaryField s t x=electricBoundaryField (datumBoundarySolution d) t x ∧
    magneticBoundaryField s t x=magneticBoundaryField (datumBoundarySolution d) t x := by
  constructor
  · ext i
    exact electricConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i
  · ext i
    exact magneticConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i

theorem uniform_picard_invariance {d : Datum} (hd : Admissible d) :
    ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
      LocalFieldBound T R L (fun p : ℝ × Vec => d.E₀ p.2) (fun p : ℝ × Vec => d.B₀ p.2) ∧
      ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → LocalFieldBound T R L E B →
        ∀ s : Solution, PicardRegular d s → TransportFor s E B →
          LocalParticleBound T A R P s.f ∧ LocalFieldBound T R L s.E s.B := by
  obtain ⟨A,R₀,P₀,hA,hR₀,hP₀,hf₀,hphase₀⟩ := datum_particle_bounds hd
  let R := R₀+1
  let P := P₀+1
  obtain ⟨D,hD,hDEB,hboundary⟩ := datum_boundary_uniform_bound hd R
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
  · intro t ht x hx
    exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
      (hDEB x).2.trans (by dsimp [L]; linarith)⟩
  · intro E B hE hB hEB s hs hV
    obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
    have hf : ∀ t∈Icc 0 T, ∀ z, |s.f (t,z)|≤A := by
      intro t ht z
      exact F.transported_sup_bound hs.smooth_f hV (fun z => by rw [hs.initial_f]; exact hf₀ z) t z
    have hphase : ∀ t∈Icc 0 T, ∀ z : Phase, s.f (t,z)≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P := by
      intro t ht z hz
      have hh := F.transported_phase_bound hs.smooth_f hV
        (R₀:=R₀) (P₀:=P₀) (T:=T) (L:=L)
        (fun z hz => hphase₀ z (by simpa only [hs.initial_f] using hz)) hL.le
        (fun r hr x hx => (hEB r hr x (by dsimp [R]; linarith)).1)
        (fun r hr x hx => (hEB r hr x (by dsimp [R]; linarith)).2) ht z hz
      constructor
      · dsimp [R]
        linarith [hh.1,ht.2]
      · dsimp [P]
        have hh' : 2*L*t≤2*L*T := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        linarith [hh.2]
    refine ⟨fun t ht x v => ⟨hf t ht (x,v),hphase t ht (x,v)⟩,?_⟩
    intro t ht x hx
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_B]
      exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
        (hDEB x).2.trans (by dsimp [L]; linarith)⟩
    · have hbd := hboundary t ⟨ht0,ht.2.trans hT1⟩ x (mem_closedBall_zero_iff.mpr hx)
      rw [← (hs.boundary_eq ht0 x).1,← (hs.boundary_eq ht0 x).2] at hbd
      have hdens := hdensity {s with E:=E,B:=B} T hT1 hf (by
        intro r hr y v hv
        exact ⟨(hphase r hr (y,v) hv).2,hEB r hr y (hphase r hr (y,v) hv).1⟩) t ht x
      have hh := mixed_fields_bound hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
        hs.smooth_rho hs.smooth_current hs.maxwell ht0 x hbd hdens
      have hh' : C*t≤C*T := mul_le_mul_of_nonneg_left ht.2 hC
      have hbound : D+C*t≤L := by dsimp [L]; linarith
      exact ⟨hh.1.trans hbound,hh.2.trans hbound⟩

theorem exists_uniform_picard_sequence {d : Datum} (hd : Admissible d) :
    ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
      ∃ S : ℕ → Solution,
        (S 0).E=(fun p : ℝ × Vec => d.E₀ p.2) ∧
        (S 0).B=(fun p : ℝ × Vec => d.B₀ p.2) ∧
        (∀ n, LocalFieldBound T R L (S n).E (S n).B) ∧
        ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f := by
  obtain ⟨T,A,R,P,L,hT,hT1,hA,hR,hP,hL,h₀,hstep⟩ := uniform_picard_invariance hd
  let Q := {s : Solution // ContDiff ℝ ∞ s.E ∧ ContDiff ℝ ∞ s.B}
  have hchoose (q : Q) : ∃ r : Q, PicardRegular d r.1 ∧ TransportFor r.1 q.1.E q.1.B := by
    obtain ⟨s,hs,hV⟩ := exists_picard_regular hd q.2.1 q.2.2
    exact ⟨⟨s,hs.smooth_E,hs.smooth_B⟩,hs,hV⟩
  choose step hs using hchoose
  let q₀ : Q := ⟨datumBoundarySolution d,
    hd.2.2.2.1.1.comp contDiff_snd,hd.2.2.2.2.1.1.comp contDiff_snd⟩
  let q : ℕ → Q := fun n => step^[n] q₀
  have hrec (n : ℕ) : q (n+1)=step (q n) := Function.iterate_succ_apply' step n q₀
  have hbound (n : ℕ) : LocalFieldBound T R L (q n).1.E (q n).1.B := by
    induction n with
    | zero => exact h₀
    | succ n ih =>
      rw [hrec]
      exact (hstep _ _ (q n).2.1 (q n).2.2 ih _ (hs (q n)).1 (hs (q n)).2).2
  refine ⟨T,A,R,P,L,hT,hT1,hA,hR,hP,hL,fun n => (q n).1,rfl,rfl,hbound,?_⟩
  intro n
  change PicardRegular d (q (n+1)).1 ∧ TransportFor (q (n+1)).1 (q n).1.E (q n).1.B ∧
    LocalParticleBound T A R P (q (n+1)).1.f
  rw [hrec]
  exact ⟨(hs (q n)).1,(hs (q n)).2,
    (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).1⟩

end RVM

end

end OAI
