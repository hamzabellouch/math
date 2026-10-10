import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM
attribute [local instance] Measure.Subtype.measureSpace
section SphereJets
local instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
lemma freeWave_derivative_bound_horizon {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (n : ℕ) (H : ℝ) {C : ℝ} (hC : 0≤C)
    (hg0 : ∀ x, ‖iteratedFDeriv ℝ n g x‖≤C)
    (hg1 : ∀ x, ‖iteratedFDeriv ℝ (n+1) g x‖≤C)
    (hh0 : ∀ x, ‖iteratedFDeriv ℝ n h x‖≤C)
    {t : ℝ} (ht : t∈Icc (0:ℝ) H) (x : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => freeWave g h (t,y)) x‖≤(1+2*H)*C := by
  let A : Sphere → Vec → ℝ := fun a y => g (y+t • a.1)
  let B : Sphere → Vec → ℝ := fun a y => fderiv ℝ g (y+t • a.1) a.1
  let D : Sphere → Vec → ℝ := fun a y => h (y+t • a.1)
  have hA : SmoothCompactFamily A := SmoothCompactFamily.ofJoint
    (hg.comp (contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst))) continuous_subtype_val
  have hB : SmoothCompactFamily B := SmoothCompactFamily.ofJoint
    (((hg.fderiv_right (m:=∞) (by simp)).comp (contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst))).clm_apply
      contDiff_fst) continuous_subtype_val
  have hD : SmoothCompactFamily D := SmoothCompactFamily.ofJoint
    (hh.comp (contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst))) continuous_subtype_val
  have ha := sphere_average_derivative_bound hA n (fun a y => by
    dsimp only [A]; rw [iteratedFDeriv_comp_add_right]; exact hg0 _) x
  have hd := sphere_average_derivative_bound hD n (fun a y => by
    dsimp only [D]; rw [iteratedFDeriv_comp_add_right]; exact hh0 _) x
  have hb := sphere_average_derivative_bound hB n (fun a y => by
    change ‖iteratedFDeriv ℝ n (fun z => (fun w => fderiv ℝ g w a.1) (z+t • a.1)) y‖≤C
    rw [iteratedFDeriv_comp_add_right (f:=fun w => fderiv ℝ g w a.1) n (t • a.1) y]
    have hh' := norm_iteratedFDeriv_clm_apply_const (x:=y+t • a.1)
      (hg.fderiv_right (m:=∞) (by simp)).contDiffAt (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞)
      (c:=a.1)
    rw [sphere_norm a,one_mul,norm_iteratedFDeriv_fderiv] at hh'
    exact hh'.trans (hg1 _)) x
  let a : Vec → ℝ := fun y => (4*Real.pi)⁻¹ • ∫ u, A u y ∂sphereMeasure
  let b : Vec → ℝ := fun y => (4*Real.pi)⁻¹ • ∫ u, B u y ∂sphereMeasure
  let c : Vec → ℝ := fun y => (4*Real.pi)⁻¹ • ∫ u, D u y ∂sphereMeasure
  have has : ContDiff ℝ ∞ a := (contDiff_integral_smoothFamily sphereMeasure hA).const_smul _
  have hbs : ContDiff ℝ ∞ b := (contDiff_integral_smoothFamily sphereMeasure hB).const_smul _
  have hcs : ContDiff ℝ ∞ c := (contDiff_integral_smoothFamily sphereMeasure hD).const_smul _
  have he : (fun y => freeWave g h (t,y))=(fun y => a y+t • b y+t • c y) := by
    funext y
    rw [freeWave_sphere hg]
    simp only [a,b,c,A,B,D,smul_eq_mul]
    ring
  rw [he]
  have hb' : ‖iteratedFDeriv ℝ n (fun y => t • b y) x‖≤t*C := by
    rw [iteratedFDeriv_const_smul_apply' ((hbs.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
      Real.norm_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left hb ht.1
  have hc' : ‖iteratedFDeriv ℝ n (fun y => t • c y) x‖≤t*C := by
    rw [iteratedFDeriv_const_smul_apply' ((hcs.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
      Real.norm_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left hd ht.1
  exact (norm_iteratedFDeriv_add_le (has.add (hbs.const_smul t)) (hcs.const_smul t) n x).trans
    ((add_le_add ((norm_iteratedFDeriv_add_le has (hbs.const_smul t) n x).trans
      (add_le_add ha hb')) hc').trans (by nlinarith [ht.2]))

end SphereJets
lemma BoundedSmooth.freeWave_coordinate_jets_horizon {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (H : ℝ) (hH : 0≤H) (n : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) H, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => freeWave (fun z => E z i) (fun z => curl B z i) (t,y)) x‖≤C ∧
      ‖iteratedFDeriv ℝ n (fun y => freeWave (fun z => B z i) (fun z => -curl E z i) (t,y)) x‖≤C := by
  obtain ⟨A,hA⟩ := hE.2 n
  obtain ⟨D,hD⟩ := hE.2 (n+1)
  obtain ⟨K,hK⟩ := hB.2 n
  obtain ⟨L,hL⟩ := hB.2 (n+1)
  let C := max A 0+2*max D 0+max K 0+2*max L 0
  have hC : 0≤C := by dsimp [C]; positivity
  have hAC : A≤C := by dsimp [C]; linarith [le_max_left A 0,le_max_right D 0,le_max_right K 0,le_max_right L 0]
  have hDC : 2*D≤C := by dsimp [C]; linarith [le_max_left D 0,le_max_right A 0,le_max_right K 0,le_max_right L 0]
  have hKC : K≤C := by dsimp [C]; linarith [le_max_left K 0,le_max_right D 0,le_max_right A 0,le_max_right L 0]
  have hLC : 2*L≤C := by dsimp [C]; linarith [le_max_left L 0,le_max_right D 0,le_max_right K 0,le_max_right A 0]
  have hD0 : 0≤D := (norm_nonneg _).trans (hD 0)
  have hL0 : 0≤L := (norm_nonneg _).trans (hL 0)
  have hp : ContDiff ℝ ∞ (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  refine ⟨(1+2*H)*C,by positivity,?_⟩
  intro t ht x
  constructor
  · apply freeWave_derivative_bound_horizon (hp.comp hE.1) (hp.comp (contDiff_curl hB.1)) n H hC
      (fun y => (norm_iteratedFDeriv_coordinate hE.1 n y i).trans ((hA y).trans hAC))
      (fun y => (norm_iteratedFDeriv_coordinate hE.1 (n+1) y i).trans ((hD y).trans (by linarith)))
      (fun y => (norm_iteratedFDeriv_curl_coordinate hB.1 n y i).trans
        ((mul_le_mul_of_nonneg_left (hL y) (by norm_num)).trans hLC)) ht x
  · apply freeWave_derivative_bound_horizon (hp.comp hB.1) (hp.comp (contDiff_curl hE.1) |>.neg) n H hC
      (fun y => (norm_iteratedFDeriv_coordinate hB.1 n y i).trans ((hK y).trans hKC))
      (fun y => (norm_iteratedFDeriv_coordinate hB.1 (n+1) y i).trans ((hL y).trans (by linarith))) _ ht x
    intro y
    change ‖iteratedFDeriv ℝ n (-(fun z => curl E z i)) y‖≤C
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact (norm_iteratedFDeriv_curl_coordinate hE.1 n y i).trans
      ((mul_le_mul_of_nonneg_left (hD y) (by norm_num)).trans hDC)

lemma datumWeightedSphere_smooth_bound_horizon {f : Phase → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {H : Vec × Vec → ℝ}
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) (n : ℕ) (T : ℝ) (hT : 0≤T) :
    ContDiff ℝ ∞ (datumWeightedSphere f H) ∧ ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => datumWeightedSphere f H (t,y)) x‖≤C := by
  obtain ⟨P,hP⟩ := (hc.image continuous_snd).isBounded.exists_norm_le
  have hzero (x v : Vec) (hv : v∉closedBall (0:Vec) P) : f (x,v)=0 := by
    by_contra hne
    exact hv (mem_closedBall_zero_iff.mpr (hP v ⟨(x,v),subset_tsupport _ hne,rfl⟩))
  let : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : CompactSpace (closedBall (0:Vec) P) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  let α := Sphere × closedBall (0:Vec) P
  let μ : Measure α := sphereMeasure.prod volume
  let c : α → ℝ := fun a => H (a.1.1,a.2.1)
  let F : α → (ℝ × Vec) → ℝ := fun a p => f (p.2+p.1 • a.1.1,a.2.1)
  have hcc : Continuous c := hH.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
    (fun a => ⟨a.1.2,mem_univ _⟩)
  have hF : SmoothCompactFamily F := SmoothCompactFamily.ofJoint
    (hf.comp ((contDiff_snd.snd.add (contDiff_snd.fst.smul contDiff_fst.fst)).prodMk contDiff_fst.snd))
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hG := hF.const_smul hcc
  have he : datumWeightedSphere f H=(fun p : ℝ × Vec => (4*Real.pi)⁻¹*p.1*(∫ a, c a*F a p ∂μ)) := by
    funext p
    have hint : Integrable (fun a : α => c a*F a p) μ :=
      (hcc.mul (hF.continuous.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi : (∫ a : α, c a*F a p ∂μ)=
        ∫ a : Sphere, ∫ v : Vec, f (p.2+p.1 • a.1,v)*H (a.1,v) ∂volume ∂sphereMeasure := by
      rw [show μ=sphereMeasure.prod volume from rfl,integral_prod _ hint]
      apply integral_congr_ae
      exact ae_of_all _ (fun a => by
        dsimp only [c,F]
        rw [integral_subtype measurableSet_closedBall (fun v => H (a.1,v)*f (p.2+p.1 • a.1,v))]
        have hz : (∫ v in closedBall (0:Vec) P, H (a.1,v)*f (p.2+p.1 • a.1,v))=
            ∫ v : Vec, H (a.1,v)*f (p.2+p.1 • a.1,v) := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro v hv
          rw [hzero _ _ hv,mul_zero]
        rw [hz]
        apply integral_congr_ae
        exact ae_of_all _ (fun v => mul_comm _ _))
    rw [hi]
    simp only [datumWeightedSphere,integral_const_mul]
    ring
  have hs : ContDiff ℝ ∞ (datumWeightedSphere f H) := by
    rw [he]
    exact (contDiff_const.mul contDiff_fst).mul (contDiff_integral_smoothFamily μ hG)
  refine ⟨hs,?_⟩
  obtain ⟨D,hD,hd⟩ := smooth_compact_jets_bound hf hc n
  obtain ⟨L,hL⟩ := hcc.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  let C := max L 0
  have hC : 0≤C := le_max_right _ _
  have hcB (a : α) : |c a|≤C := (hL a).trans (le_max_left _ _)
  refine ⟨(4*Real.pi)⁻¹*(T*(μ.real univ*(C*D))),by positivity,?_⟩
  intro t ht x
  have hFt : SmoothCompactFamily (fun a : α => fun y : Vec => f (y+t • a.1.1,a.2.1)) :=
    SmoothCompactFamily.ofJoint
      (hf.comp ((contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst.fst)).prodMk contDiff_fst.snd))
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hGt := hFt.const_smul hcc
  have hj := norm_iteratedFDeriv_integral_le μ n hGt x
  have hb (a : α) : ‖iteratedFDeriv ℝ n (fun y => c a*f (y+t • a.1.1,a.2.1)) x‖≤C*D := by
    rw [show (fun y => c a*f (y+t • a.1.1,a.2.1))=(fun y => c a • (fun z => f (z,a.2.1)) (y+t • a.1.1)) from rfl,
      iteratedFDeriv_const_smul_apply' (((hFt.1 a).of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
      Real.norm_eq_abs,iteratedFDeriv_comp_add_right (f:=fun z => f (z,a.2.1)) n (t • a.1.1) x]
    exact mul_le_mul (hcB a) ((norm_iteratedFDeriv_phase_slice hf n _ _).trans (hd n le_rfl _))
      (norm_nonneg _) hC
  have hint : Integrable (fun a => ‖iteratedFDeriv ℝ n (fun y => c a • f (y+t • a.1.1,a.2.1)) x‖) μ :=
    ((hGt.2 n).comp (continuous_const.prodMk continuous_id)).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hij := hj.trans (integral_mono hint (integrable_const (C*D)) hb)
  simp only [integral_const,smul_eq_mul] at hij
  have hej : (fun y => datumWeightedSphere f H (t,y))=
      (fun y => ((4*Real.pi)⁻¹*t) • (∫ a, c a • f (y+t • a.1.1,a.2.1) ∂μ)) := by
    funext y
    rw [he]
    rfl
  rw [hej,iteratedFDeriv_const_smul_apply' (((contDiff_integral_smoothFamily μ hGt).of_le
    (by exact_mod_cast le_top)).contDiffAt),norm_smul,Real.norm_of_nonneg (mul_nonneg (by positivity) ht.1 : 0≤(4*Real.pi)⁻¹*t)]
  exact (mul_le_mul_of_nonneg_left hij (mul_nonneg (by positivity) ht.1)).trans (by
    have hn : 0≤μ.real univ*(C*D) := by positivity
    calc
      _ = (4*Real.pi)⁻¹*(t*(μ.real univ*(C*D))) := by ring
      _ ≤ (4*Real.pi)⁻¹*(T*(μ.real univ*(C*D))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht.2 hn) (by positivity))

lemma electricConeBoundary_datum_jets_horizon {d : Datum} (hd : Admissible d) (T : ℝ) (hT : 0≤T) (k : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T,
      ContDiff ℝ ∞ (fun x => electricConeBoundary (datumBoundarySolution d) t x i 0) ∧
      ∀ x, ‖iteratedFDeriv ℝ k (fun y => electricConeBoundary (datumBoundarySolution d) t y i 0) x‖≤C := by
  have hp (j : Fin 3) : ContDiff ℝ ∞ (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).contDiff
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_jets_horizon hd.2.2.2.1 hd.2.2.2.2.1 T hT k i
  obtain ⟨hFs,B,hB,hflux⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (continuousOn_fluxWeight (continuousOn_datumElectricFluxKernel i)) k T hT
  obtain ⟨hRs,D,hD,hrho⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (((hp i).continuous.comp continuous_fst).continuousOn) k T hT
  obtain ⟨hJs,L,hL,hcurrent⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (((hp i).continuous.comp ((contDiff_velocity (k:=1)).continuous.comp continuous_snd)).continuousOn) k T hT
  let a := freeWave (fun y => d.E₀ y i) (fun y => curl d.B₀ y i)
  let b := datumWeightedSphere d.f₀ (fun p => dot p.1 (datumElectricFluxKernel i (-p.1,p.2)))
  let c := datumWeightedSphere d.f₀ (fun p => p.1 i)
  let e := datumWeightedSphere d.f₀ (fun p => velocity p.2 i)
  have has : ContDiff ℝ ∞ a := contDiff_freeWave ((hp i).comp hd.2.2.2.1.1)
    ((hp i).comp (contDiff_curl hd.2.2.2.2.1.1))
  refine ⟨A+B+D+L,by positivity,?_⟩
  intro t ht
  have heq : (fun x => electricConeBoundary (datumBoundarySolution d) t x i 0)=
      (fun x => a (t,x)-b (t,x)-c (t,x)-e (t,x)) := by
    funext x
    simp only [electricConeBoundary,sub_zero]
    simp_rw [datum_initial_electric_flux_normalised d i ht.1]
    rw [←datumWeightedSphere_flux hd.1.continuous hd.2.1 (continuousOn_datumElectricFluxKernel i)]
    simp only [datumBoundarySolution]
    rw [←datumWeightedSphere_rho,←datumWeightedSphere_waveCurrent hd]
  rw [heq]
  have ha := has.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hb := hFs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hc := hRs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hd' := hJs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  refine ⟨((ha.sub hb).sub hc).sub hd',?_⟩
  intro x
  exact (norm_iteratedFDeriv_sub_le ((ha.sub hb).sub hc) hd' k x).trans (add_le_add
    ((norm_iteratedFDeriv_sub_le (ha.sub hb) hc k x).trans (add_le_add
      ((norm_iteratedFDeriv_sub_le ha hb k x).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x).1
        (hflux t ⟨ht.1.le,ht.2⟩ x))) (hrho t ⟨ht.1.le,ht.2⟩ x)))
    (hcurrent t ⟨ht.1.le,ht.2⟩ x))

lemma magneticConeBoundary_datum_jets_horizon {d : Datum} (hd : Admissible d) (T : ℝ) (hT : 0≤T) (k : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T,
      ContDiff ℝ ∞ (fun x => magneticConeBoundary (datumBoundarySolution d) t x i 0) ∧
      ∀ x, ‖iteratedFDeriv ℝ k (fun y => magneticConeBoundary (datumBoundarySolution d) t y i 0) x‖≤C := by
  have hp (j : Fin 3) : ContDiff ℝ ∞ (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).contDiff
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_jets_horizon hd.2.2.2.1 hd.2.2.2.2.1 T hT k i
  obtain ⟨hFs,B,hB,hflux⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (continuousOn_fluxWeight (continuousOn_datumMagneticFluxKernel i)) k T hT
  obtain ⟨hRs,D,hD,hmoment⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    ((continuous_datumMagneticMoment i).continuousOn) k T hT
  let a := freeWave (fun y => d.B₀ y i) (fun y => -curl d.E₀ y i)
  let b := datumWeightedSphere d.f₀ (fun p => dot p.1 (datumMagneticFluxKernel i (-p.1,p.2)))
  let c := datumWeightedSphere d.f₀ (fun p => p.1 (curlA i)*velocity p.2 (curlB i)-
    p.1 (curlB i)*velocity p.2 (curlA i))
  have has : ContDiff ℝ ∞ a := contDiff_freeWave ((hp i).comp hd.2.2.2.2.1.1)
    (((hp i).comp (contDiff_curl hd.2.2.2.1.1)).neg)
  refine ⟨A+B+D,by positivity,?_⟩
  intro t ht
  have heq : (fun x => magneticConeBoundary (datumBoundarySolution d) t x i 0)=
      (fun x => a (t,x)-b (t,x)+c (t,x)) := by
    funext x
    simp only [magneticConeBoundary,sub_zero]
    simp_rw [datum_initial_magnetic_flux_normalised d i ht.1]
    rw [←datumWeightedSphere_flux hd.1.continuous hd.2.1 (continuousOn_datumMagneticFluxKernel i)]
    simp only [datumBoundarySolution]
    rw [←datumWeightedSphere_magneticMoment hd]
  rw [heq]
  have ha := has.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hb := hFs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hc := hRs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  refine ⟨(ha.sub hb).add hc,?_⟩
  intro x
  exact (norm_iteratedFDeriv_add_le (ha.sub hb) hc k x).trans (add_le_add
    ((norm_iteratedFDeriv_sub_le ha hb k x).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x).2
      (hflux t ⟨ht.1.le,ht.2⟩ x))) (hmoment t ⟨ht.1.le,ht.2⟩ x))

lemma datum_boundary_global_jets_horizon {d : Datum} (hd : Admissible d) (T : ℝ) (hT : 0≤T) (k : ℕ) :
    ∃ C : ℝ, 0≤C ∧
      (∀ x, ‖iteratedFDeriv ℝ k d.E₀ x‖≤C ∧ ‖iteratedFDeriv ℝ k d.B₀ x‖≤C) ∧
      ∀ t∈Ioc (0:ℝ) T,
        (ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) ∧
          ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t)) ∧
        ∀ x, ‖iteratedFDeriv ℝ k (electricBoundaryField (datumBoundarySolution d) t) x‖≤C ∧
          ‖iteratedFDeriv ℝ k (magneticBoundaryField (datumBoundarySolution d) t) x‖≤C := by
  choose CE hCE he using electricConeBoundary_datum_jets_horizon hd T hT k
  choose CB hCB hb using magneticConeBoundary_datum_jets_horizon hd T hT k
  obtain ⟨D,hD⟩ := hd.2.2.2.1.2 k
  obtain ⟨L,hL⟩ := hd.2.2.2.2.1.2 k
  let C := max D 0+max L 0+∑ i, (CE i+CB i)
  have hC : 0≤C := add_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))
    (Finset.sum_nonneg (fun i _ => add_nonneg (hCE i) (hCB i)))
  have hEC (i) : CE i≤C := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [C]; linarith [le_max_right D 0,le_max_right L 0,hCB i]
  have hBC (i) : CB i≤C := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [C]; linarith [le_max_right D 0,le_max_right L 0,hCE i]
  refine ⟨3*C,by positivity,?_,?_⟩
  · intro x
    have hS : 0≤∑ i, (CE i+CB i) := Finset.sum_nonneg (fun i _ => add_nonneg (hCE i) (hCB i))
    constructor
    · exact (hD x).trans (by dsimp [C]; linarith [le_max_left D 0,le_max_right L 0])
    · exact (hL x).trans (by dsimp [C]; linarith [le_max_left L 0,le_max_right D 0])
  · intro t ht
    have hes : ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) :=
      contDiff_euclidean.mpr (fun i => (he i t ht).1)
    have hbs : ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t) :=
      contDiff_euclidean.mpr (fun i => (hb i t ht).1)
    refine ⟨⟨hes,hbs⟩,fun x => ⟨?_,?_⟩⟩
    · exact norm_iteratedFDeriv_vec_le hes k hC (fun i y => ((he i t ht).2 y).trans (hEC i)) x
    · exact norm_iteratedFDeriv_vec_le hbs k hC (fun i y => ((hb i t ht).2 y).trans (hBC i)) x

end RVM
end

end OAI
