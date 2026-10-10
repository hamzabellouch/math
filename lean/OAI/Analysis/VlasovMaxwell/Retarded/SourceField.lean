import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.SpaceDiv

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM
lemma magneticResidual_initial_deriv {E B j : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j)
    (hBw : ∀ x, fieldBox B (0,x)=spaceCurl j (0,x))
    (hEt : ∀ x, dirD E (1,0) (0,x)=spaceCurl B (0,x)-j (0,x))
    (hdiv : ∀ x, spaceDiv B (0,x)=0) (x : Vec) :
    dirD (magneticResidual E B) (1,0) (0,x)=0 := by
  have hEc := spaceCurl_of_slice_eq ((contDiff_dirD hE _).differentiable (by simp))
    (((contDiff_spaceCurl hB).sub hj).differentiable (by simp)) hEt x
  rw [spaceCurl_sub ((contDiff_spaceCurl hB).differentiable (by simp))
    (hj.differentiable (by simp))] at hEc
  have hgrad : waveGradient (spaceDiv B) (0,x)=0 := by
    rw [waveGradient_slice ((contDiff_spaceDiv hB).differentiable (by simp)),funext hdiv]
    ext i; simp
  have hw := fieldBox_curl_curl hB (0,x)
  rw [hBw,hgrad,add_zero] at hw
  unfold magneticResidual
  rw [dirD_add ((contDiff_dirD hB _).differentiable (by simp))
    ((contDiff_spaceCurl hE).differentiable (by simp))]
  dsimp only
  rw [dirD_spaceCurl hE,hEc]
  linear_combination (norm := module) hw

lemma wave_system_implies_maxwell {E B j : Field} {ρ : ℝ × Vec → ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hj : ContDiff ℝ ∞ j) (hρ : ContDiff ℝ ∞ ρ)
    (hEw : ∀ t, 0 ≤ t → ∀ x, fieldBox E (t,x)= -waveGradient ρ (t,x)-dirD j (1,0) (t,x))
    (hBw : ∀ t, 0 ≤ t → ∀ x, fieldBox B (t,x)=spaceCurl j (t,x))
    (hcont : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0)
    (hEt : ∀ x, dirD E (1,0) (0,x)=spaceCurl B (0,x)-j (0,x))
    (hBt : ∀ x, dirD B (1,0) (0,x)= -spaceCurl E (0,x))
    (hDE : ∀ x, spaceDiv E (0,x)=ρ (0,x))
    (hDB : ∀ x, spaceDiv B (0,x)=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    dirD E (1,0) (t,x)=spaceCurl B (t,x)-j (t,x) ∧
    dirD B (1,0) (t,x)= -spaceCurl E (t,x) := by
  have hR : electricResidual E B j (t,x)=0 := by
    apply field_wave_zero (contDiff_electricResidual hE hB hj)
      (fun r hr => electricResidual_box hE hB hj hρ
        (fun r hr => hEw r hr.le) (fun r hr => hBw r hr.le) hcont hr) _
      (electricResidual_initial_deriv hE hB hj hρ (hEw 0 le_rfl) hBt hDE) ht x
    intro y
    simp only [electricResidual,hEt]
    module
  have hS : magneticResidual E B (t,x)=0 := by
    apply field_wave_zero (contDiff_magneticResidual hE hB)
      (fun r hr => magneticResidual_box hE hB hj hρ
        (fun r hr => hEw r hr.le) (fun r hr => hBw r hr.le) hr) _
      (magneticResidual_initial_deriv hE hB hj (hBw 0 le_rfl) hEt hDB) ht x
    intro y
    simp only [magneticResidual,hBt,neg_add_cancel]
  unfold electricResidual at hR
  unfold magneticResidual at hS
  constructor
  · linear_combination (norm := module) hR
  · linear_combination (norm := module) hS

def sourceField (J : Field) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => sourceWave (fun q => J q i) p)

lemma sourceField_apply (J : Field) (p : ℝ × Vec) (i : Fin 3) :
    sourceField J p i = sourceWave (fun q => J q i) p := rfl

lemma contDiff_sourceField {J : Field} (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (sourceField J) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_sourceWave (contDiff_component hJ i)

lemma sourceField_initial (J : Field) (x : Vec) : sourceField J (0,x)=0 := by
  ext i
  exact sourceWave_initial_value (fun p => J p i) x

lemma sourceField_initial_deriv {J : Field} (hJ : ContDiff ℝ ∞ J) (x : Vec) :
    dirD (sourceField J) (1,0) (0,x)=0 := by
  ext i
  rw [← dirD_component ((contDiff_sourceField hJ).differentiable (by simp))]
  exact sourceWave_time_initial (contDiff_component hJ i) x

lemma sourceField_box {J : Field} (hJ : ContDiff ℝ ∞ J)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) : fieldBox (sourceField J) (t,x)=J (t,x) := by
  ext i
  exact sourceWave_box (contDiff_component hJ i) ht x

lemma freeField_fieldBox {G H : Vec → Vec} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) : fieldBox (freeField G H) (t,x)=0 := by
  ext i
  exact freeField_box hG hH ht x i

def maxwellElectric (E₀ B₀ : Vec → Vec) (ρ : ℝ × Vec → ℝ) (j : Field) : Field :=
  fun p => freeField E₀ (fun x => curl B₀ x-j (0,x)) p +
    sourceField (fun q => -waveGradient ρ q-dirD j (1,0) q) p

def maxwellMagnetic (E₀ B₀ : Vec → Vec) (j : Field) : Field :=
  fun p => freeField B₀ (fun x => -curl E₀ x) p+sourceField (spaceCurl j) p

lemma contDiff_maxwellElectric {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (maxwellElectric E₀ B₀ ρ j) :=
  (contDiff_freeField hE ((contDiff_curl hB).sub (contDiff_field_slice hj 0))).add
    (contDiff_sourceField ((contDiff_waveGradient hρ).neg.sub (contDiff_dirD hj _)))

lemma contDiff_maxwellMagnetic {E₀ B₀ : Vec → Vec} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (maxwellMagnetic E₀ B₀ j) :=
  (contDiff_freeField hB (contDiff_curl hE).neg).add
    (contDiff_sourceField (contDiff_spaceCurl hj))

lemma maxwellElectric_initial {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (x : Vec) : maxwellElectric E₀ B₀ ρ j (0,x)=E₀ x := by
  simp only [maxwellElectric,freeField_initial hE,sourceField_initial,add_zero]

lemma maxwellMagnetic_initial {E₀ B₀ : Vec → Vec} {j : Field}
    (hB : ContDiff ℝ ∞ B₀) (x : Vec) : maxwellMagnetic E₀ B₀ j (0,x)=B₀ x := by
  simp only [maxwellMagnetic,freeField_initial hB,sourceField_initial,add_zero]

lemma maxwellElectric_initial_deriv {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) (x : Vec) :
    dirD (maxwellElectric E₀ B₀ ρ j) (1,0) (0,x)=curl B₀ x-j (0,x) := by
  unfold maxwellElectric
  rw [dirD_add ((contDiff_freeField hE ((contDiff_curl hB).sub
      (contDiff_field_slice hj 0))).differentiable (by simp))
    ((contDiff_sourceField ((contDiff_waveGradient hρ).neg.sub
      (contDiff_dirD hj _))).differentiable (by simp))]
  dsimp only
  rw [freeField_initial_deriv hE ((contDiff_curl hB).sub (contDiff_field_slice hj 0)),
    sourceField_initial_deriv ((contDiff_waveGradient hρ).neg.sub (contDiff_dirD hj _)),add_zero]

lemma maxwellMagnetic_initial_deriv {E₀ B₀ : Vec → Vec} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hj : ContDiff ℝ ∞ j) (x : Vec) :
    dirD (maxwellMagnetic E₀ B₀ j) (1,0) (0,x)= -curl E₀ x := by
  unfold maxwellMagnetic
  rw [dirD_add ((contDiff_freeField hB (contDiff_curl hE).neg).differentiable (by simp))
    ((contDiff_sourceField (contDiff_spaceCurl hj)).differentiable (by simp))]
  dsimp only
  rw [freeField_initial_deriv hB (contDiff_curl hE).neg,
    sourceField_initial_deriv (contDiff_spaceCurl hj),add_zero]

lemma maxwellElectric_box {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    fieldBox (maxwellElectric E₀ B₀ ρ j) (t,x)= -waveGradient ρ (t,x)-dirD j (1,0) (t,x) := by
  unfold maxwellElectric
  rw [fieldBox_add (contDiff_freeField hE ((contDiff_curl hB).sub (contDiff_field_slice hj 0)))
    (contDiff_sourceField ((contDiff_waveGradient hρ).neg.sub (contDiff_dirD hj _)))]
  dsimp only
  rw [freeField_fieldBox hE ((contDiff_curl hB).sub (contDiff_field_slice hj 0)) ht,
    sourceField_box ((contDiff_waveGradient hρ).neg.sub (contDiff_dirD hj _)) ht,zero_add]

lemma maxwellMagnetic_box {E₀ B₀ : Vec → Vec} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hj : ContDiff ℝ ∞ j) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    fieldBox (maxwellMagnetic E₀ B₀ j) (t,x)=spaceCurl j (t,x) := by
  unfold maxwellMagnetic
  rw [fieldBox_add (contDiff_freeField hB (contDiff_curl hE).neg)
    (contDiff_sourceField (contDiff_spaceCurl hj))]
  dsimp only
  rw [freeField_fieldBox hB (contDiff_curl hE).neg ht,sourceField_box (contDiff_spaceCurl hj) ht,zero_add]

lemma spaceDiv_of_slice_eq {F G : Field} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) {t : ℝ} (he : ∀ x, F (t,x)=G (t,x)) (x : Vec) :
    spaceDiv F (t,x)=spaceDiv G (t,x) := by
  rw [spaceDiv_slice hF,spaceDiv_slice hG,show (fun y => F (t,y)) =
    (fun y => G (t,y)) from funext he]

lemma maxwell_first_order {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
    (hcont : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0)
    (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    dirD (maxwellElectric E₀ B₀ ρ j) (1,0) (t,x)=
      spaceCurl (maxwellMagnetic E₀ B₀ j) (t,x)-j (t,x) ∧
    dirD (maxwellMagnetic E₀ B₀ j) (1,0) (t,x)=
      -spaceCurl (maxwellElectric E₀ B₀ ρ j) (t,x) := by
  have hEc := contDiff_maxwellElectric hE hB hρ hj
  have hBc := contDiff_maxwellMagnetic hE hB hj
  apply wave_system_implies_maxwell hEc hBc hj hρ
    (fun r hr => maxwellElectric_box hE hB hρ hj hr)
    (fun r hr => maxwellMagnetic_box hE hB hj hr) hcont
    (fun y => ?_) (fun y => ?_) (fun y => ?_) (fun y => ?_) ht x
  · rw [maxwellElectric_initial_deriv hE hB hρ hj,
      spaceCurl_slice (hBc.differentiable (by simp))]
    simp only [maxwellMagnetic_initial hB]
  · rw [maxwellMagnetic_initial_deriv hE hB hj,
      spaceCurl_slice (hEc.differentiable (by simp))]
    simp only [maxwellElectric_initial hE]
  · rw [spaceDiv_slice (hEc.differentiable (by simp))]
    simpa only [maxwellElectric_initial hE] using hDE y
  · rw [spaceDiv_slice (hBc.differentiable (by simp))]
    simpa only [maxwellMagnetic_initial hB] using hDB y

lemma spaceDiv_add {F G : Field} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (p : ℝ × Vec) :
    spaceDiv (fun q => F q+G q) p=spaceDiv F p+spaceDiv G p := by
  simp only [spaceDiv,dirD_add hF hG,PiLp.add_apply,Finset.sum_add_distrib]

lemma spaceDiv_sub {F G : Field} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (p : ℝ × Vec) :
    spaceDiv (fun q => F q-G q) p=spaceDiv F p-spaceDiv G p := by
  simp only [spaceDiv,dirD_sub hF hG,PiLp.sub_apply,Finset.sum_sub_distrib]

lemma spaceDiv_neg (F : Field) (p : ℝ × Vec) :
    spaceDiv (fun q => -F q) p= -spaceDiv F p := by
  simp only [spaceDiv,dirD_neg_field,PiLp.neg_apply,Finset.sum_neg_distrib]

lemma scalar_time_constant {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (hdu : ∀ t, 0<t → ∀ x, dirD u (1,0) (t,x)=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) : u (t,x)=u (0,x) := by
  have hc : Continuous (fun r : ℝ => dirD u (1,0) (r,x)) :=
    (contDiff_dirD hu _).continuous.comp (continuous_id.prodMk continuous_const)
  have he : EqOn (fun r : ℝ => dirD u (1,0) (r,x)) (fun _ => (0:ℝ)) (Ioi 0) :=
    fun r hr => hdu r hr x
  have hder (r : ℝ) (hr : 0 ≤ r) : deriv (fun s : ℝ => u (s,x)) r=0 := by
    rw [deriv_slice_eq_dirD (hu.differentiable (by simp))]
    exact he.closure hc continuous_const (by simpa only [closure_Ioi,mem_Ici] using hr)
  have hdiff : Differentiable ℝ (fun r : ℝ => u (r,x)) :=
    (hu.differentiable (by simp)).comp (differentiable_id.prodMk (differentiable_const x))
  have hn := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_deriv_le
    (fun r _hr => hdiff r) (C:=0) (fun r hr => by rw [hder r hr.1]; simp)
    ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩
  have hz : u (t,x)-u (0,x)=0 := norm_eq_zero.mp (le_antisymm (by simpa using hn) (norm_nonneg _))
  exact sub_eq_zero.mp hz

lemma maxwell_gauss_propagation {E B j : Field} {ρ : ℝ × Vec → ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hj : ContDiff ℝ ∞ j) (hρ : ContDiff ℝ ∞ ρ)
    (hfirst : ∀ t, 0 ≤ t → ∀ x,
      dirD E (1,0) (t,x)=spaceCurl B (t,x)-j (t,x) ∧
      dirD B (1,0) (t,x)= -spaceCurl E (t,x))
    (hcont : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0)
    (hDE : ∀ x, spaceDiv E (0,x)=ρ (0,x)) (hDB : ∀ x, spaceDiv B (0,x)=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) : spaceDiv E (t,x)=ρ (t,x) ∧ spaceDiv B (t,x)=0 := by
  have hdu : ∀ r, 0<r → ∀ y, dirD (fun p => spaceDiv E p-ρ p) (1,0) (r,y)=0 := by
    intro r hr y
    rw [dirD_sub ((contDiff_spaceDiv hE).differentiable (by simp))
      (hρ.differentiable (by simp))]
    dsimp only
    rw [dirD_spaceDiv hE,spaceDiv_of_slice_eq
      ((contDiff_dirD hE _).differentiable (by simp))
      (((contDiff_spaceCurl hB).sub hj).differentiable (by simp))
      (fun z => (hfirst r hr.le z).1),
      spaceDiv_sub ((contDiff_spaceCurl hB).differentiable (by simp))
        (hj.differentiable (by simp)),spaceDiv_spaceCurl hB]
    linarith [hcont r hr y]
  have hdv : ∀ r, 0<r → ∀ y, dirD (spaceDiv B) (1,0) (r,y)=0 := by
    intro r hr y
    rw [dirD_spaceDiv hB,spaceDiv_of_slice_eq
      ((contDiff_dirD hB _).differentiable (by simp))
      ((contDiff_spaceCurl hE).neg.differentiable (by simp))
      (fun z => (hfirst r hr.le z).2),spaceDiv_neg,spaceDiv_spaceCurl hE,neg_zero]
  constructor
  · have he := scalar_time_constant ((contDiff_spaceDiv hE).sub hρ) hdu ht x
    rw [hDE,sub_self] at he
    exact sub_eq_zero.mp he
  · rw [scalar_time_constant (contDiff_spaceDiv hB) hdv ht,hDB]

theorem constructed_maxwell_equations {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j)
    (hcont : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0)
    (hDE : ∀ x, divergence E₀ x=ρ (0,x)) (hDB : ∀ x, divergence B₀ x=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    let E := maxwellElectric E₀ B₀ ρ j
    let B := maxwellMagnetic E₀ B₀ j
    dirD E (1,0) (t,x)=spaceCurl B (t,x)-j (t,x) ∧
    dirD B (1,0) (t,x)= -spaceCurl E (t,x) ∧
    spaceDiv E (t,x)=ρ (t,x) ∧ spaceDiv B (t,x)=0 := by
  have hEc := contDiff_maxwellElectric hE hB hρ hj
  have hBc := contDiff_maxwellMagnetic hE hB hj
  have hfirst (r : ℝ) (hr : 0 ≤ r) (y : Vec) :=
    maxwell_first_order hE hB hρ hj hcont hDE hDB hr y
  refine ⟨(hfirst t ht x).1,(hfirst t ht x).2,?_⟩
  apply maxwell_gauss_propagation hEc hBc hj hρ hfirst hcont
    (fun y => ?_) (fun y => ?_) ht x
  · rw [spaceDiv_slice (hEc.differentiable (by simp))]
    simpa only [maxwellElectric_initial hE] using hDE y
  · rw [spaceDiv_slice (hBc.differentiable (by simp))]
    simpa only [maxwellMagnetic_initial hB] using hDB y

lemma causal_local_energy_bound {e : ℝ × Vec → ℝ} {S : Field} {T R ε : ℝ}
    (he : ContDiff ℝ ∞ e) (hS : ContDiff ℝ ∞ S)
    (hT : 0 ≤ T) (hR : T ≤ R) (hε : 0<ε)
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t+divergence (fun y => S (t,y)) x=0)
    (x₀ : Vec) :
    (∫ x : Vec, coneCutoff R ε x₀ (T,x)*e (T,x))  ≤
      ∫ x : Vec, coneCutoff R ε x₀ (0,x)*e (0,x) := by
  let g := coneCutoff R ε x₀
  let G : ℝ → ℝ := fun t => ∫ x : Vec, g (t,x)*e (t,x)
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 R := fun t ht => ⟨ht.1,ht.2.trans hR⟩
  have hgc : ContDiff ℝ 1 g := contDiff_coneCutoff R ε x₀
  have hgz : ∀ t ∈ Icc 0 T, ∀ x ∉ closedBall x₀ R, g (t,x)=0 := by
    intro t ht x hx
    exact coneCutoff_zero_outside hε (hsub ht) hx
  have hGc : ContinuousOn G (Icc 0 T) := by
    apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ R)
      (hgc.continuous.continuousOn.mul he.continuous.continuousOn)
    intro t ht x hx
    change g (t,x)*e (t,x)=0
    rw [hgz t ht x hx,zero_mul]
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    deriv_moving_local_energy isOpen_Ioo (he.of_le (by simp)).contDiffOn
      (hS.of_le (by simp)).contDiffOn hcons (isCompact_closedBall x₀ R) hgc.contDiffOn
      (fun r hr x hx => hgz r ⟨hr.1.le,hr.2.le⟩ x hx) ht
  have hanti : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hGc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t ht).deriv]
      apply integral_nonpos
      intro x
      exact cone_energy_integrand_nonpos hε (hsub ⟨ht.1.le,ht.2.le⟩).2
        (he0 t ⟨ht.1.le,ht.2.le⟩ x) (hflux t ht x) x x₀
  exact hanti ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT

lemma coneCutoff_one_on_ball {T r : ℝ} (hr : 0 ≤ r) {x : Vec}
    (hx : x ∈ closedBall (0:Vec) r) : coneCutoff (T+r+1) 1 0 (T,x)=1 := by
  apply Real.smoothTransition.one_of_one_le
  have hn : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
  dsimp [coneArgument]
  simp only [sub_zero,div_one]
  nlinarith [sq_le_sq₀ (norm_nonneg x) hr |>.mpr hn]

lemma causal_energy_integrable {e : ℝ × Vec → ℝ} {S : Field} {T : ℝ}
    (he : ContDiff ℝ ∞ e) (hS : ContDiff ℝ ∞ S) (hT : 0 ≤ T)
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t+divergence (fun y => S (t,y)) x=0)
    (hinit : Integrable (fun x => e (0,x))) :
    Integrable (fun x => e (T,x)) ∧ (∫ x : Vec, e (T,x)) ≤ ∫ x : Vec, e (0,x) := by
  have hball (n : ℕ) : (∫ x in closedBall (0:Vec) (n:ℝ), e (T,x))  ≤  ∫ x : Vec, e (0,x) := by
    let R : ℝ := T+(n:ℝ)+1
    let g := coneCutoff R 1 (0:Vec)
    have hR : T ≤ R := by dsimp [R]; linarith [Nat.cast_nonneg (α:=ℝ) n]
    have hgC (t : ℝ) (ht : t∈Icc 0 T) : HasCompactSupport (fun x => g (t,x)) :=
      compactSupport_of_zero_off (isCompact_closedBall (0:Vec) R)
        (fun x hx => coneCutoff_zero_outside (by norm_num) ⟨ht.1,ht.2.trans hR⟩ hx)
    have hgc (t : ℝ) : Continuous (fun x => g (t,x)) :=
      (contDiff_coneCutoff R 1 (0:Vec) (k:=1)).continuous.comp (continuous_const.prodMk continuous_id)
    have hI (t : ℝ) (ht : t∈Icc 0 T) : Integrable (fun x => g (t,x)*e (t,x)) :=
      ((hgc t).mul (he.continuous.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
        (hgC t ht).mul_right
    calc
      _ = ∫ x in closedBall (0:Vec) (n:ℝ), g (T,x)*e (T,x) := by
        apply setIntegral_congr_fun isClosed_closedBall.measurableSet
        intro x hx
        change e (T,x)=g (T,x)*e (T,x)
        rw [show g (T,x)=1 from coneCutoff_one_on_ball (Nat.cast_nonneg n) hx,one_mul]
      _  ≤  ∫ x : Vec, g (T,x)*e (T,x) :=
        setIntegral_le_integral (hI T ⟨hT,le_rfl⟩) (ae_of_all _ (fun x =>
          mul_nonneg (Real.smoothTransition.nonneg _) (he0 T ⟨hT,le_rfl⟩ x)))
      _  ≤  ∫ x : Vec, g (0,x)*e (0,x) :=
        causal_local_energy_bound he hS hT hR (by norm_num) he0 hflux hcons 0
      _  ≤  ∫ x : Vec, e (0,x) := by
        apply integral_mono (hI 0 ⟨le_rfl,hT⟩) hinit
        intro x
        exact mul_le_of_le_one_left (he0 0 ⟨le_rfl,hT⟩ x) (Real.smoothTransition.le_one _)
  have hcov : AECover (volume : Measure Vec) atTop (fun n : ℕ => closedBall (0:Vec) (n:ℝ)) :=
    aecover_closedBall tendsto_natCast_atTop_atTop
  have hIt : Integrable (fun x => e (T,x)) :=
    hcov.integrable_of_integral_bounded_of_nonneg_ae (∫ x : Vec, e (0,x))
      (fun _ => (he.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (isCompact_closedBall _ _)) (ae_of_all _ (he0 T ⟨hT,le_rfl⟩)) (Eventually.of_forall hball)
  exact ⟨hIt,le_of_tendsto (hcov.integral_tendsto_of_countably_generated hIt) (Eventually.of_forall hball)⟩

lemma divergence_neg (F : Vec → Vec) (x : Vec) :
    divergence (fun y => -F y) x= -divergence F x := by
  simp only [divergence,PiLp.neg_apply,spatialPartial,fderiv_fun_neg,neg_apply,
    Finset.sum_neg_distrib]

lemma causal_energy_conserved {e : ℝ × Vec → ℝ} {S : Field} {T : ℝ}
    (he : ContDiff ℝ ∞ e) (hS : ContDiff ℝ ∞ S) (hT : 0 ≤ T)
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t+divergence (fun y => S (t,y)) x=0)
    (hinit : Integrable (fun x => e (0,x))) :
    Integrable (fun x => e (T,x)) ∧ (∫ x : Vec, e (T,x))=∫ x : Vec, e (0,x) := by
  obtain ⟨hIt,hle⟩ := causal_energy_integrable he hS hT he0 hflux hcons hinit
  let R : ℝ × Vec → ℝ × Vec := fun p => (T-p.1,p.2)
  have hR : ContDiff ℝ ∞ R := (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  have hrev : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (T-r,x)) t+divergence (fun y => -S (T-t,y)) x=0 := by
    intro t ht x
    have hdt := ((he.differentiable (by simp)).comp
      (differentiable_id.prodMk (differentiable_const x)) (T-t)).hasDerivAt
    have hh := hdt.comp t ((hasDerivAt_id t).const_sub T)
    change HasDerivAt (fun r => e (T-r,x)) (deriv (fun r => e (r,x)) (T-t) * (-1)) t at hh
    rw [hh.deriv,divergence_neg]
    have hhcons := hcons (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ x
    dsimp only [Function.comp_def] at *
    linarith
  have hrevi : Integrable (fun x => e (T-(0:ℝ),x)) := by simpa using hIt
  have hy := causal_energy_integrable (he.comp hR) (hS.comp hR).neg hT
    (fun t ht x => he0 (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ x)
    (fun t ht x => by
      simpa only [Function.comp_def,R,norm_neg] using
        (hflux (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩ x))
    hrev hrevi
  refine ⟨hIt,le_antisymm hle ?_⟩
  simpa only [Function.comp_def,R,sub_self,sub_zero] using hy.2

def maxwellEnergy (E B : Field) (p : ℝ × Vec) : ℝ := (‖E p‖^2+‖B p‖^2)/2

def maxwellFlux (E B : Field) (p : ℝ × Vec) : Vec := cross (E p) (B p)

lemma contDiff_maxwellEnergy {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (maxwellEnergy E B) := ((hE.norm_sq ℝ).add (hB.norm_sq ℝ)).div_const 2

lemma contDiff_maxwellFlux {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (maxwellFlux E B) := contDiff_cross.comp (hE.prodMk hB)

lemma maxwellEnergy_nonneg (E B : Field) (p : ℝ × Vec) : 0  ≤  maxwellEnergy E B p := by
  unfold maxwellEnergy; positivity

lemma maxwellFlux_le (E B : Field) (p : ℝ × Vec) : ‖maxwellFlux E B p‖  ≤  maxwellEnergy E B p :=
  poynting_norm_le_energy (E p) (B p)

end RVM
end

end OAI
