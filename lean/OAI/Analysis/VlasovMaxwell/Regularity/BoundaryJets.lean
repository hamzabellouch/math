import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ParticleTame

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section
universe u v

lemma SmoothCompactFamily.const_smul {α : Type v} {E W : Type u} [TopologicalSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : α → E → W} (hF : SmoothCompactFamily F) {c : α → ℝ} (hc : Continuous c) :
    SmoothCompactFamily (fun a x => c a • F a x) := by
  refine ⟨fun a => (hF.1 a).const_smul _,fun n => ?_⟩
  have he (p : E × α) : iteratedFDeriv ℝ n (fun x => c p.2 • F p.2 x) p.1 =
      c p.2 • iteratedFDeriv ℝ n (F p.2) p.1 :=
    iteratedFDeriv_const_smul_apply' ((hF.1 p.2).of_le (by exact_mod_cast le_top)).contDiffAt
  simp_rw [he]
  exact (hc.comp continuous_snd).smul (hF.2 n)

lemma norm_iteratedFDeriv_add_le {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (fun y => f y+g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖ := by
  change ‖iteratedFDeriv ℝ n (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (i:=n) (x:=x) ((hf.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((hg.of_le (by exact_mod_cast le_top)).contDiffAt)]
  exact norm_add_le _ _

lemma norm_iteratedFDeriv_sub_le {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (fun y => f y-g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖ := by
  change ‖iteratedFDeriv ℝ n (f-g) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (i:=n) (x:=x) ((hf.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((hg.of_le (by exact_mod_cast le_top)).contDiffAt)]
  exact norm_sub_le _ _

local instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

lemma sphere_average_derivative_bound {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Sphere → Vec → W} (hF : SmoothCompactFamily F) (n : ℕ) {C : ℝ}
    (hC : ∀ a x, ‖iteratedFDeriv ℝ n (F a) x‖≤C) (x : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => (4*Real.pi)⁻¹ • ∫ a, F a y ∂sphereMeasure) x‖ ≤ C := by
  have hI := contDiff_integral_smoothFamily sphereMeasure hF
  rw [iteratedFDeriv_const_smul_apply' ((hI.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
    Real.norm_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  have hi := norm_iteratedFDeriv_integral_le sphereMeasure n hF x
  have hint : Integrable (fun a => ‖iteratedFDeriv ℝ n (F a) x‖) sphereMeasure :=
    ((hF.2 n).comp (continuous_const.prodMk continuous_id)).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb := integral_mono hint (integrable_const C) (fun a => hC a x)
  simp only [integral_const,smul_eq_mul,sphere_area] at hb
  exact (mul_le_mul_of_nonneg_left (hi.trans hb) (by positivity)).trans_eq (by field_simp)

lemma freeWave_derivative_bound {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (n : ℕ) {C : ℝ} (hC : 0≤C)
    (hg0 : ∀ x, ‖iteratedFDeriv ℝ n g x‖≤C)
    (hg1 : ∀ x, ‖iteratedFDeriv ℝ (n+1) g x‖≤C)
    (hh0 : ∀ x, ‖iteratedFDeriv ℝ n h x‖≤C)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => freeWave g h (t,y)) x‖≤3*C := by
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

end

section
attribute [local instance] Measure.Subtype.measureSpace

def datumWeightedSphere (f : Phase → ℝ) (H : Vec × Vec → ℝ) (p : ℝ × Vec) : ℝ :=
  (4*Real.pi)⁻¹*(∫ a : Sphere, p.1*(∫ v : Vec, f (p.2+p.1 • a.1,v)*H (a.1,v)) ∂sphereMeasure)

lemma datumWeightedSphere_smooth_bound {f : Phase → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {H : Vec × Vec → ℝ}
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) (n : ℕ) :
    ContDiff ℝ ∞ (datumWeightedSphere f H) ∧ ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x,
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
  refine ⟨(4*Real.pi)⁻¹*(μ.real univ*(C*D)),by positivity,?_⟩
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
      _ ≤ (4*Real.pi)⁻¹*(μ.real univ*(C*D)) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hn ht.2) (by positivity))

end

lemma norm_iteratedFDeriv_coordinate {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {F : U → Vec} (hF : ContDiff ℝ ∞ F) (n : ℕ) (x : U) (i : Fin 3) :
    ‖iteratedFDeriv ℝ n (fun y => F y i) x‖≤‖iteratedFDeriv ℝ n F x‖ := by
  let L := PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i
  have hL : ‖L‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [L,PiLp.proj_apply,one_mul,Real.norm_eq_abs] using norm_coordinate_le v i
  have hh := L.norm_iteratedFDeriv_comp_left (x:=x) hF.contDiffAt (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞)
  exact hh.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

lemma norm_iteratedFDeriv_curl_coordinate {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x : Vec) (i : Fin 3) :
    ‖iteratedFDeriv ℝ n (fun y => curl F y i) x‖≤2*‖iteratedFDeriv ℝ (n+1) F x‖ := by
  have he : (fun y => curl F y i)=(fun y => (fderiv ℝ F y (basis (curlA i))) (curlB i)-
      (fderiv ℝ F y (basis (curlB i))) (curlA i)) := by
    funext y
    fin_cases i <;> simp [curl,curlA,curlB,spatialPartial,coordinate_fderiv_apply (hF.differentiable (by simp))]
  have hd := hF.fderiv_right (m:=∞) (by simp)
  have ha (a b : Fin 3) : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ F y (basis a) b) x‖≤
      ‖iteratedFDeriv ℝ (n+1) F x‖ := by
    have hb := norm_iteratedFDeriv_clm_apply_const hd.contDiffAt
      (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞) (x:=x) (c:=basis a)
    have hba : ‖basis a‖=1 := by
      change ‖(PiLp.single 2 a (1:ℝ) : Vec)‖=1
      simp
    rw [hba,one_mul,norm_iteratedFDeriv_fderiv] at hb
    exact (norm_iteratedFDeriv_coordinate (hd.clm_apply contDiff_const) n x b).trans hb
  rw [he]
  have haS := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) (curlB i)).contDiff.comp (hd.clm_apply (contDiff_const (c:=basis (curlA i))))
  have hbS := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) (curlA i)).contDiff.comp (hd.clm_apply (contDiff_const (c:=basis (curlB i))))
  exact (norm_iteratedFDeriv_sub_le haS hbS n x).trans ((add_le_add (ha _ _) (ha _ _)).trans_eq (by ring))

lemma BoundedSmooth.freeWave_coordinate_jets {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (n : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x,
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
  refine ⟨3*C,by positivity,?_⟩
  intro t ht x
  constructor
  · apply freeWave_derivative_bound (hp.comp hE.1) (hp.comp (contDiff_curl hB.1)) n hC
      (fun y => (norm_iteratedFDeriv_coordinate hE.1 n y i).trans ((hA y).trans hAC))
      (fun y => (norm_iteratedFDeriv_coordinate hE.1 (n+1) y i).trans ((hD y).trans (by linarith)))
      (fun y => (norm_iteratedFDeriv_curl_coordinate hB.1 n y i).trans
        ((mul_le_mul_of_nonneg_left (hL y) (by norm_num)).trans hLC)) ht x
  · apply freeWave_derivative_bound (hp.comp hB.1) (hp.comp (contDiff_curl hE.1) |>.neg) n hC
      (fun y => (norm_iteratedFDeriv_coordinate hB.1 n y i).trans ((hK y).trans hKC))
      (fun y => (norm_iteratedFDeriv_coordinate hB.1 (n+1) y i).trans ((hL y).trans (by linarith))) _ ht x
    intro y
    change ‖iteratedFDeriv ℝ n (-(fun z => curl E z i)) y‖≤C
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact (norm_iteratedFDeriv_curl_coordinate hE.1 n y i).trans
      ((mul_le_mul_of_nonneg_left (hD y) (by norm_num)).trans hDC)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma datum_velocity_integrable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {f : Phase → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {H : Vec × Vec → W} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ))
    (x n : Vec) (hn : ‖n‖=1) : Integrable (fun v => f (x,v) • H (n,v)) := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hf.comp (continuous_const.prodMk continuous_id)).smul
      (hH.comp_continuous (continuous_const.prodMk continuous_id)
        (fun v => ⟨mem_sphere_zero_iff_norm.mpr hn,mem_univ v⟩))
  · exact HasCompactSupport.intro hK (fun v hv => by rw [hz x v hv,zero_smul])

lemma datumWeightedSphere_flux {f : Phase → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {H : Vec × Vec → Vec} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) (t : ℝ) (x : Vec) :
    datumWeightedSphere f (fun p => dot p.1 (H (-p.1,p.2))) (t,x)=
      (4*Real.pi)⁻¹*(∫ a : Sphere, t*dot a.1 (∫ v, f (x+t • a.1,v) • H (-a.1,v)) ∂sphereMeasure) := by
  unfold datumWeightedSphere
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  have hi := datum_velocity_integrable hf hc hH (x+t • a.1) (-a.1) (by rw [norm_neg,sphere_norm a])
  have he := (innerSL ℝ a.1).integral_comp_comm hi
  simp only [innerSL_apply_apply,←dot_eq_inner,dot_smul_right] at he
  rw [←he]

lemma continuousOn_fluxWeight {H : Vec × Vec → Vec}
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ContinuousOn (fun p : Vec × Vec => dot p.1 (H (-p.1,p.2))) (sphere (0:Vec) 1 ×ˢ univ) := by
  exact (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_fst.continuousOn.prodMk (hH.comp
    (continuous_fst.neg.prodMk continuous_snd).continuousOn (by
      intro p hp
      exact ⟨by simpa only [mem_sphere_zero_iff_norm,Pi.neg_apply,norm_neg] using hp.1,mem_univ _⟩)))

lemma datum_current_eq_integral {d : Datum} (hd : Admissible d) (x : Vec) (j : Fin 3) :
    current d.f₀ x j=∫ v, d.f₀ (x,v)*velocity v j := by
  have hi := datum_velocity_integrable hd.1.continuous hd.2.1
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn)
    x (basis 0) (by change ‖(PiLp.single 2 0 (1:ℝ) : Vec)‖=1; simp)
  exact integral_vec_apply hi j

lemma datumWeightedSphere_rho (d : Datum) (t : ℝ) (x : Vec) (i : Fin 3) :
    datumWeightedSphere d.f₀ (fun p => p.1 i) (t,x)=
      (4*Real.pi)⁻¹*(∫ a : Sphere, t*a.1 i*rho d.f₀ (x+t • a.1) ∂sphereMeasure) := by
  unfold datumWeightedSphere rho
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  rw [integral_mul_const]
  ring

lemma datumWeightedSphere_current {d : Datum} (hd : Admissible d) (t : ℝ) (x : Vec)
    (i j : Fin 3) :
    datumWeightedSphere d.f₀ (fun p => p.1 i*velocity p.2 j) (t,x)=
      (4*Real.pi)⁻¹*(∫ a : Sphere, t*a.1 i*current d.f₀ (x+t • a.1) j ∂sphereMeasure) := by
  unfold datumWeightedSphere
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  rw [datum_current_eq_integral hd]
  simp_rw [show ∀ v : Vec, d.f₀ (x+t • a.1,v)*(a.1 i*velocity v j)=
    a.1 i*(d.f₀ (x+t • a.1,v)*velocity v j) by intro v; ring]
  rw [integral_const_mul]
  ring

lemma datumWeightedSphere_waveCurrent {d : Datum} (hd : Admissible d) (t : ℝ) (x : Vec) (i : Fin 3) :
    datumWeightedSphere d.f₀ (fun p => velocity p.2 i) (t,x)=
      waveK (fun y => current d.f₀ y i) (t,x) := by
  simp only [datumWeightedSphere,waveK,sphereSum,integral_const_mul,datum_current_eq_integral hd]

lemma electricConeBoundary_datum_jets {d : Datum} (hd : Admissible d) (k : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1,
      ContDiff ℝ ∞ (fun x => electricConeBoundary (datumBoundarySolution d) t x i 0) ∧
      ∀ x, ‖iteratedFDeriv ℝ k (fun y => electricConeBoundary (datumBoundarySolution d) t y i 0) x‖≤C := by
  have hp (j : Fin 3) : ContDiff ℝ ∞ (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).contDiff
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_jets hd.2.2.2.1 hd.2.2.2.2.1 k i
  obtain ⟨hFs,B,hB,hflux⟩ := datumWeightedSphere_smooth_bound hd.1 hd.2.1
    (continuousOn_fluxWeight (continuousOn_datumElectricFluxKernel i)) k
  obtain ⟨hRs,D,hD,hrho⟩ := datumWeightedSphere_smooth_bound hd.1 hd.2.1
    (((hp i).continuous.comp continuous_fst).continuousOn) k
  obtain ⟨hJs,L,hL,hcurrent⟩ := datumWeightedSphere_smooth_bound hd.1 hd.2.1
    (((hp i).continuous.comp ((contDiff_velocity (k:=1)).continuous.comp continuous_snd)).continuousOn) k
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

end RVM

end

end OAI
