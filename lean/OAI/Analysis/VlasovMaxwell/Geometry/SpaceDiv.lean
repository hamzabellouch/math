import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.WaveGradient

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

def spaceDiv (F : Field) (p : ℝ × Vec) : ℝ :=
  ∑ i : Fin 3, dirD F (0, basis i) p i

lemma contDiff_spaceDiv {F : Field} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spaceDiv F) :=
  ContDiff.sum (fun i _ => contDiff_component (contDiff_dirD hF _) i)

lemma spaceDiv_slice {F : Field} (hF : Differentiable ℝ F) (t : ℝ) (x : Vec) :
    spaceDiv F (t,x) = divergence (fun y => F (t,y)) x := by
  unfold spaceDiv divergence
  apply Finset.sum_congr rfl
  intro i _
  have hc : Differentiable ℝ (fun p => F p i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiable.comp hF
  rw [spatialPartial_time_slice (hc (t,x))]
  exact (dirD_component hF (t,x) (0,basis i) i).symm

lemma dirD_spaceDiv {F : Field} (hF : ContDiff ℝ ∞ F) (e p : ℝ × Vec) :
    dirD (spaceDiv F) e p = spaceDiv (dirD F e) p := by
  unfold spaceDiv
  rw [dirD_sum Finset.univ (fun i _ =>
    (contDiff_component (contDiff_dirD hF _) i).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [dirD_component ((contDiff_dirD hF _).differentiable (by simp)),
    dirD_comm hF (0,basis i) e]

lemma spaceDiv_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) (p : ℝ × Vec) :
    spaceDiv (spaceCurl F) p = 0 := by
  rw [spaceDiv_slice ((contDiff_spaceCurl hF).differentiable (by simp))]
  have he : (fun y => spaceCurl F (p.1,y)) = curl (fun y => F (p.1,y)) :=
    funext (spaceCurl_slice (hF.differentiable (by simp)) p.1)
  rw [he]
  exact divergence_curl (contDiff_field_slice hF p.1) p.2

lemma dirD_component_fun {F : Field} (hF : Differentiable ℝ F)
    (e : ℝ × Vec) (i : Fin 3) :
    (fun p => dirD F e p i) = dirD (fun p => F p i) e :=
  funext (fun p => (dirD_component hF p e i).symm)

lemma waveBox_dirD_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (hw : ∀ t, 0<t → ∀ x, waveBox u (t,x)=0)
    {t : ℝ} (ht : 0<t) (e : ℝ × Vec) (x : Vec) :
    waveBox (dirD u e) (t,x)=0 := by
  rw [waveBox_dirD hu]
  have he : waveBox u =ᶠ[𝓝 (t,x)] fun _ => (0:ℝ) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (lt_mem_nhds ht)] with p hp
    exact hw p.1 hp p.2
  rw [dirD_eq_of_eventuallyEq he]
  simp [dirD]

lemma waveBox_spaceCurl_zero {F : Field} (hF : ContDiff ℝ ∞ F)
    (hw : ∀ i : Fin 3, ∀ t, 0<t → ∀ x, waveBox (fun p => F p i) (t,x)=0)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    waveBox (fun p => spaceCurl F p i) (t,x)=0 := by
  have he : (fun p => spaceCurl F p i) =
      fun p => dirD (fun z => F z (curlB i)) (0,basis (curlA i)) p -
        dirD (fun z => F z (curlA i)) (0,basis (curlB i)) p := by
    funext p
    simp only [spaceCurl_apply,dirD_component (hF.differentiable (by simp))]
  rw [he,waveBox_sub (contDiff_dirD (contDiff_component hF _) _)
    (contDiff_dirD (contDiff_component hF _) _)]
  dsimp only
  rw [waveBox_dirD_zero (contDiff_component hF _) (hw _) ht,
    waveBox_dirD_zero (contDiff_component hF _) (hw _) ht,sub_self]

def freeField (G H : Vec → Vec) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => freeWave (fun x => G x i) (fun x => H x i) p)

lemma freeField_apply (G H : Vec → Vec) (p : ℝ × Vec) (i : Fin 3) :
    freeField G H p i = freeWave (fun x => G x i) (fun x => H x i) p := rfl

lemma contDiff_freeField {G H : Vec → Vec}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (freeField G H) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_freeWave (contDiff_component hG i) (contDiff_component hH i)

lemma freeField_initial {G H : Vec → Vec} (hG : ContDiff ℝ ∞ G) (x : Vec) :
    freeField G H (0,x)=G x := by
  ext i
  exact freeWave_initial (contDiff_component hG i) x

lemma freeField_initial_deriv {G H : Vec → Vec}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (x : Vec) :
    dirD (freeField G H) (1,0) (0,x)=H x := by
  ext i
  rw [← dirD_component ((contDiff_freeField hG hH).differentiable (by simp)),
    ← deriv_slice_eq_dirD ((contDiff_component (contDiff_freeField hG hH) i).differentiable (by simp))]
  exact freeWave_initial_velocity (contDiff_component hG i) (contDiff_component hH i) x

lemma freeField_box {G H : Vec → Vec}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) (i : Fin 3) :
    waveBox (fun p => freeField G H p i) (t,x)=0 := by
  have hc : Continuous (fun t => waveBox (fun p => freeField G H p i) (t,x)) :=
    (contDiff_waveBox (contDiff_component (contDiff_freeField hG hH) i)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have he : EqOn (fun t => waveBox (fun p => freeField G H p i) (t,x))
      (fun _ => (0:ℝ)) (Ioi 0) := by
    intro t ht
    exact freeWave_box (contDiff_component hG i) (contDiff_component hH i) ht x
  exact he.closure hc continuous_const (by simpa only [closure_Ioi,mem_Ici] using ht)

lemma field_wave_initial_second {F : Field} {G : Vec → Vec}
    (hF : ContDiff ℝ ∞ F) (hG : ∀ x, F (0,x)=G x)
    (hw : ∀ x i, waveBox (fun p => F p i) (0,x)=0) (x : Vec) (i : Fin 3) :
    dirD (dirD F (1,0)) (1,0) (0,x) i = laplace (fun y => G y i) x := by
  have h := hw x i
  rw [waveBox_component_eq hF] at h
  have he : (fun y => F (0,y) i) = fun y => G y i := by funext y; rw [hG]
  rw [he] at h
  exact sub_eq_zero.mp h

def vacuumElectric (E₀ B₀ : Vec → Vec) : Field := freeField E₀ (curl B₀)
def vacuumMagnetic (E₀ B₀ : Vec → Vec) : Field := freeField B₀ (fun x => -curl E₀ x)

lemma contDiff_vacuumElectric {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀) :
    ContDiff ℝ ∞ (vacuumElectric E₀ B₀) :=
  contDiff_freeField hE (contDiff_curl hB)

lemma contDiff_vacuumMagnetic {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀) :
    ContDiff ℝ ∞ (vacuumMagnetic E₀ B₀) :=
  contDiff_freeField hB (contDiff_curl hE).neg

lemma spaceCurl_of_slice_eq {F G : Field} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) {t : ℝ} (he : ∀ x, F (t,x)=G (t,x)) (x : Vec) :
    spaceCurl F (t,x)=spaceCurl G (t,x) := by
  rw [spaceCurl_slice hF,spaceCurl_slice hG,show (fun y => F (t,y)) =
    (fun y => G (t,y)) from funext he]

lemma dirD_neg_field (F : Field) (e p : ℝ × Vec) :
    dirD (fun q => -F q) e p = -dirD F e p := by
  simp [dirD,fderiv_fun_neg]

lemma wave_maxwell_residual {F G : Field}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFw : ∀ i : Fin 3, ∀ t, 0 ≤ t → ∀ x, waveBox (fun p => F p i) (t,x)=0)
    (hGw : ∀ i : Fin 3, ∀ t, 0<t → ∀ x, waveBox (fun p => G p i) (t,x)=0)
    (hF0 : ∀ x, dirD F (1,0) (0,x)=spaceCurl G (0,x))
    (hG0 : ∀ x, dirD G (1,0) (0,x)= -spaceCurl F (0,x))
    (hdiv : ∀ x, divergence (fun y => F (0,y)) x=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    dirD F (1,0) (t,x)=spaceCurl G (t,x) := by
  ext i
  apply sub_eq_zero.mp
  apply wave_zero ((contDiff_component (contDiff_dirD hF _) i).sub
    (contDiff_component (contDiff_spaceCurl hG) i)) _ _ _ ht x
  · intro r hr y
    rw [waveBox_sub (contDiff_component (contDiff_dirD hF _) i)
      (contDiff_component (contDiff_spaceCurl hG) i)]
    dsimp only
    rw [dirD_component_fun (hF.differentiable (by simp)),
      waveBox_dirD_zero (contDiff_component hF i) (fun r hr => hFw i r hr.le) hr,
      waveBox_spaceCurl_zero hG hGw hr,sub_self]
  · intro y
    rw [hF0,sub_self]
  · intro y
    rw [deriv_slice_eq_dirD (((contDiff_component (contDiff_dirD hF _) i).sub
      (contDiff_component (contDiff_spaceCurl hG) i)).differentiable (by simp)),
      dirD_sub ((contDiff_component (contDiff_dirD hF _) i).differentiable (by simp))
        ((contDiff_component (contDiff_spaceCurl hG) i).differentiable (by simp))]
    dsimp only
    rw [dirD_component ((contDiff_dirD hF _).differentiable (by simp)),
      dirD_component ((contDiff_spaceCurl hG).differentiable (by simp)),dirD_spaceCurl hG]
    have hc := spaceCurl_of_slice_eq ((contDiff_dirD hG _).differentiable (by simp))
      ((contDiff_spaceCurl hF).neg.differentiable (by simp)) hG0 y
    rw [spaceCurl_neg] at hc
    rw [hc,PiLp.neg_apply,spaceCurl_spaceCurl_component hF,
      field_wave_initial_second hF (fun _ => rfl) (fun y i => hFw i 0 le_rfl y)]
    have hd : divergence (fun y => F (0,y)) = fun _ => (0:ℝ) := funext hdiv
    rw [hd]
    simp [spatialPartial]

lemma vacuumElectric_initial {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (x : Vec) : vacuumElectric E₀ B₀ (0,x)=E₀ x :=
  freeField_initial hE x

lemma vacuumMagnetic_initial {E₀ B₀ : Vec → Vec}
    (hB : ContDiff ℝ ∞ B₀) (x : Vec) : vacuumMagnetic E₀ B₀ (0,x)=B₀ x :=
  freeField_initial hB x

lemma vacuum_maxwell_first_order {E₀ B₀ : Vec → Vec}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hDE : ∀ x, divergence E₀ x=0) (hDB : ∀ x, divergence B₀ x=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    dirD (vacuumElectric E₀ B₀) (1,0) (t,x)=spaceCurl (vacuumMagnetic E₀ B₀) (t,x) ∧
    dirD (vacuumMagnetic E₀ B₀) (1,0) (t,x)= -spaceCurl (vacuumElectric E₀ B₀) (t,x) := by
  have hEs := contDiff_vacuumElectric hE hB
  have hBs := contDiff_vacuumMagnetic hE hB
  have hEc (y : Vec) : spaceCurl (vacuumElectric E₀ B₀) (0,y)=curl E₀ y := by
    rw [spaceCurl_slice (hEs.differentiable (by simp))]
    congr 1
    exact funext (vacuumElectric_initial hE)
  have hBc (y : Vec) : spaceCurl (vacuumMagnetic E₀ B₀) (0,y)=curl B₀ y := by
    rw [spaceCurl_slice (hBs.differentiable (by simp))]
    congr 1
    exact funext (vacuumMagnetic_initial hB)
  have hEt (y : Vec) : dirD (vacuumElectric E₀ B₀) (1,0) (0,y)=
      spaceCurl (vacuumMagnetic E₀ B₀) (0,y) := by
    rw [hBc]
    exact freeField_initial_deriv hE (contDiff_curl hB) y
  have hBt (y : Vec) : dirD (vacuumMagnetic E₀ B₀) (1,0) (0,y)=
      -spaceCurl (vacuumElectric E₀ B₀) (0,y) := by
    rw [hEc]
    exact freeField_initial_deriv hB (contDiff_curl hE).neg y
  have hEw (i : Fin 3) (r : ℝ) (hr : 0 ≤ r) (y : Vec) :
      waveBox (fun p => vacuumElectric E₀ B₀ p i) (r,y)=0 :=
    freeField_box hE (contDiff_curl hB) hr y i
  have hBw (i : Fin 3) (r : ℝ) (hr : 0 ≤ r) (y : Vec) :
      waveBox (fun p => vacuumMagnetic E₀ B₀ p i) (r,y)=0 :=
    freeField_box hB (contDiff_curl hE).neg hr y i
  constructor
  · apply wave_maxwell_residual hEs hBs hEw (fun i r hr => hBw i r hr.le) hEt hBt
      (fun y => ?_) ht x
    rw [show (fun y => vacuumElectric E₀ B₀ (0,y)) = E₀ from
      funext (vacuumElectric_initial hE)]
    exact hDE y
  · have h := wave_maxwell_residual hBs hEs.neg hBw
      (fun i r hr y => by
        simpa only [PiLp.neg_apply,waveBox_neg,neg_zero] using
          congrArg Neg.neg (hEw i r hr.le y))
      (fun y => by rw [spaceCurl_neg]; exact hBt y)
      (fun y => by rw [dirD_neg_field,hEt])
      (fun y => by
        rw [show (fun y => vacuumMagnetic E₀ B₀ (0,y)) = B₀ from
          funext (vacuumMagnetic_initial hB)]
        exact hDB y) ht x
    simpa only [spaceCurl_neg] using h

def fieldBox (F : Field) (p : ℝ × Vec) : Vec :=
  WithLp.toLp 2 (fun i => waveBox (fun q => F q i) p)

lemma fieldBox_apply (F : Field) (p : ℝ × Vec) (i : Fin 3) :
    fieldBox F p i = waveBox (fun q => F q i) p := rfl

lemma contDiff_fieldBox {F : Field} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fieldBox F) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_waveBox (contDiff_component hF i)

lemma fieldBox_add {F G : Field} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    fieldBox (fun p => F p+G p) = fun p => fieldBox F p+fieldBox G p := by
  funext p; ext i
  simp only [fieldBox_apply,PiLp.add_apply,waveBox_add (contDiff_component hF i)
    (contDiff_component hG i)]

lemma fieldBox_sub {F G : Field} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    fieldBox (fun p => F p-G p) = fun p => fieldBox F p-fieldBox G p := by
  funext p; ext i
  simp only [fieldBox_apply,PiLp.sub_apply,waveBox_sub (contDiff_component hF i)
    (contDiff_component hG i)]

lemma fieldBox_neg (F : Field) :
    fieldBox (fun p => -F p) = fun p => -fieldBox F p := by
  funext p; ext i
  simp only [fieldBox_apply,PiLp.neg_apply,waveBox_neg]

lemma fieldBox_dirD {F : Field} (hF : ContDiff ℝ ∞ F) (e p : ℝ × Vec) :
    fieldBox (dirD F e) p = dirD (fieldBox F) e p := by
  ext i
  rw [fieldBox_apply,dirD_component_fun (hF.differentiable (by simp)),
    waveBox_dirD (contDiff_component hF i),← dirD_component
      ((contDiff_fieldBox hF).differentiable (by simp))]
  rfl

lemma fieldBox_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) (p : ℝ × Vec) :
    fieldBox (spaceCurl F) p = spaceCurl (fieldBox F) p := by
  ext i
  have he : (fun q => spaceCurl F q i) =
      fun q => dirD (fun z => F z (curlB i)) (0,basis (curlA i)) q -
        dirD (fun z => F z (curlA i)) (0,basis (curlB i)) q := by
    funext q
    simp only [spaceCurl_apply,dirD_component (hF.differentiable (by simp))]
  rw [fieldBox_apply,he,waveBox_sub (contDiff_dirD (contDiff_component hF _) _)
    (contDiff_dirD (contDiff_component hF _) _)]
  simp only [spaceCurl_apply,waveBox_dirD (contDiff_component hF _),
    ← dirD_component ((contDiff_fieldBox hF).differentiable (by simp))]
  rfl

lemma waveGradient_add {u v : ℝ × Vec → ℝ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) :
    waveGradient (fun p => u p+v p) = fun p => waveGradient u p+waveGradient v p := by
  funext p; ext i
  simp only [waveGradient_apply,dirD_add hu hv,PiLp.add_apply]

lemma waveGradient_sub {u v : ℝ × Vec → ℝ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) :
    waveGradient (fun p => u p-v p) = fun p => waveGradient u p-waveGradient v p := by
  funext p; ext i
  simp only [waveGradient_apply,dirD_sub hu hv,PiLp.sub_apply]

lemma waveGradient_neg (u : ℝ × Vec → ℝ) :
    waveGradient (fun p => -u p)=fun p => -waveGradient u p := by
  funext p; ext i
  simp [waveGradient_apply,dirD,fderiv_fun_neg,PiLp.neg_apply]

lemma dirD_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (e p : ℝ × Vec) :
    dirD (waveGradient u) e p = waveGradient (dirD u e) p := by
  ext i
  rw [← dirD_component ((contDiff_waveGradient hu).differentiable (by simp))]
  exact dirD_comm hu (0,basis i) e p

lemma spaceCurl_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (p : ℝ × Vec) :
    spaceCurl (waveGradient u) p=0 := by
  ext i
  rw [spaceCurl_apply,← dirD_component ((contDiff_waveGradient hu).differentiable (by simp)),
    ← dirD_component ((contDiff_waveGradient hu).differentiable (by simp))]
  change dirD (dirD u (0,basis (curlB i))) (0,basis (curlA i)) p -
    dirD (dirD u (0,basis (curlA i))) (0,basis (curlB i)) p = 0
  rw [dirD_comm hu (0,basis (curlB i)) (0,basis (curlA i)),sub_self]

lemma fieldBox_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (p : ℝ × Vec) :
    fieldBox (waveGradient u) p=waveGradient (waveBox u) p := by
  ext i
  exact waveBox_dirD hu (0,basis i) p

lemma fieldBox_curl_curl {F : Field} (hF : ContDiff ℝ ∞ F) (p : ℝ × Vec) :
    dirD (dirD F (1,0)) (1,0) p + spaceCurl (spaceCurl F) p =
      fieldBox F p + waveGradient (spaceDiv F) p := by
  rcases p with ⟨t,x⟩
  ext i
  rw [PiLp.add_apply,PiLp.add_apply,fieldBox_apply,waveBox_component_eq hF,
    spaceCurl_spaceCurl_component hF,waveGradient_apply,
    dirD_spatial_slice ((contDiff_spaceDiv hF).differentiable (by simp))]
  have he : (fun y => spaceDiv F (t,y)) = divergence (fun y => F (t,y)) :=
    funext (spaceDiv_slice (hF.differentiable (by simp)) t)
  rw [he]
  ring

lemma waveGradient_eq_of_eventuallyEq {u v : ℝ × Vec → ℝ} {p : ℝ × Vec}
    (h : u =ᶠ[𝓝 p] v) : waveGradient u p=waveGradient v p := by
  ext i
  exact dirD_eq_of_eventuallyEq h (0,basis i)

lemma field_wave_zero {F : Field} (hF : ContDiff ℝ ∞ F)
    (hw : ∀ t, 0<t → ∀ x, fieldBox F (t,x)=0)
    (h0 : ∀ x, F (0,x)=0) (h1 : ∀ x, dirD F (1,0) (0,x)=0)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) : F (t,x)=0 := by
  ext i
  apply wave_zero (contDiff_component hF i) _ _ _ ht x
  · intro r hr y
    exact congrArg (fun v : Vec => v i) (hw r hr y)
  · intro y
    exact congrArg (fun v : Vec => v i) (h0 y)
  · intro y
    rw [deriv_slice_eq_dirD ((contDiff_component hF i).differentiable (by simp)),
      dirD_component (hF.differentiable (by simp)),h1]
    rfl

def electricResidual (E B j : Field) : Field :=
  fun p => dirD E (1,0) p-spaceCurl B p+j p

def magneticResidual (E B : Field) : Field :=
  fun p => dirD B (1,0) p+spaceCurl E p

lemma contDiff_electricResidual {E B j : Field} (hE : ContDiff ℝ ∞ E)
    (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (electricResidual E B j) :=
  ((contDiff_dirD hE _).sub (contDiff_spaceCurl hB)).add hj

lemma contDiff_magneticResidual {E B : Field} (hE : ContDiff ℝ ∞ E)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (magneticResidual E B) :=
  (contDiff_dirD hB _).add (contDiff_spaceCurl hE)

lemma electricResidual_box {E B j : Field} {ρ : ℝ × Vec → ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hj : ContDiff ℝ ∞ j) (hρ : ContDiff ℝ ∞ ρ)
    (hEw : ∀ t, 0<t → ∀ x, fieldBox E (t,x)=
      -waveGradient ρ (t,x)-dirD j (1,0) (t,x))
    (hBw : ∀ t, 0<t → ∀ x, fieldBox B (t,x)=spaceCurl j (t,x))
    (hcont : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0)
    {t : ℝ} (ht : 0<t) (x : Vec) : fieldBox (electricResidual E B j) (t,x)=0 := by
  have hEd := dirD_eq_of_eventuallyEq (positive_time_eventuallyEq (F:=fieldBox E)
    (G:=fun p => -waveGradient ρ p-dirD j (1,0) p) hEw ht x) (1,0)
  rw [dirD_sub ((contDiff_waveGradient hρ).neg.differentiable (by simp))
    ((contDiff_dirD hj _).differentiable (by simp))] at hEd
  dsimp only at hEd
  rw [dirD_neg_field,dirD_waveGradient hρ] at hEd
  have hBc := spaceCurl_eq_of_eventuallyEq (positive_time_eventuallyEq hBw ht x)
  have hgc := waveGradient_eq_of_eventuallyEq (positive_time_eventuallyEq
    (F:=fun p => dirD ρ (1,0) p+spaceDiv j p) (G:=fun _ => 0) hcont ht x)
  rw [waveGradient_add ((contDiff_dirD hρ _).differentiable (by simp))
    ((contDiff_spaceDiv hj).differentiable (by simp))] at hgc
  have hg0 : waveGradient (fun _ : ℝ × Vec => (0:ℝ)) (t,x)=0 := by
    ext i; simp [waveGradient_apply,dirD]
  rw [hg0] at hgc
  have hwj := fieldBox_curl_curl hj (t,x)
  unfold electricResidual
  rw [fieldBox_add ((contDiff_dirD hE _).sub (contDiff_spaceCurl hB)) hj,
    fieldBox_sub (contDiff_dirD hE _) (contDiff_spaceCurl hB)]
  dsimp only
  rw [fieldBox_dirD hE,fieldBox_spaceCurl hB,hEd,hBc]
  linear_combination (norm := module) -hwj -hgc

lemma magneticResidual_box {E B j : Field} {ρ : ℝ × Vec → ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hj : ContDiff ℝ ∞ j) (hρ : ContDiff ℝ ∞ ρ)
    (hEw : ∀ t, 0<t → ∀ x, fieldBox E (t,x)=
      -waveGradient ρ (t,x)-dirD j (1,0) (t,x))
    (hBw : ∀ t, 0<t → ∀ x, fieldBox B (t,x)=spaceCurl j (t,x))
    {t : ℝ} (ht : 0<t) (x : Vec) : fieldBox (magneticResidual E B) (t,x)=0 := by
  have hBd := dirD_eq_of_eventuallyEq (positive_time_eventuallyEq hBw ht x) (1,0)
  rw [dirD_spaceCurl hj] at hBd
  have hEc := spaceCurl_eq_of_eventuallyEq (positive_time_eventuallyEq (F:=fieldBox E)
    (G:=fun p => -waveGradient ρ p-dirD j (1,0) p) hEw ht x)
  rw [spaceCurl_sub ((contDiff_waveGradient hρ).neg.differentiable (by simp))
    ((contDiff_dirD hj _).differentiable (by simp)),spaceCurl_neg] at hEc
  dsimp only at hEc
  rw [spaceCurl_waveGradient hρ,neg_zero,zero_sub] at hEc
  unfold magneticResidual
  rw [fieldBox_add (contDiff_dirD hB _) (contDiff_spaceCurl hE)]
  dsimp only
  rw [fieldBox_dirD hB,fieldBox_spaceCurl hE,hBd,hEc,add_neg_cancel]

lemma electricResidual_initial_deriv {E B j : Field} {ρ : ℝ × Vec → ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hj : ContDiff ℝ ∞ j) (hρ : ContDiff ℝ ∞ ρ)
    (hEw : ∀ x, fieldBox E (0,x)= -waveGradient ρ (0,x)-dirD j (1,0) (0,x))
    (hBt : ∀ x, dirD B (1,0) (0,x)= -spaceCurl E (0,x))
    (hdiv : ∀ x, spaceDiv E (0,x)=ρ (0,x)) (x : Vec) :
    dirD (electricResidual E B j) (1,0) (0,x)=0 := by
  have hBc := spaceCurl_of_slice_eq ((contDiff_dirD hB _).differentiable (by simp))
    ((contDiff_spaceCurl hE).neg.differentiable (by simp)) hBt x
  rw [spaceCurl_neg] at hBc
  have hgrad : waveGradient (spaceDiv E) (0,x)=waveGradient ρ (0,x) := by
    rw [waveGradient_slice ((contDiff_spaceDiv hE).differentiable (by simp)),
      waveGradient_slice (hρ.differentiable (by simp)),funext hdiv]
  have hw := fieldBox_curl_curl hE (0,x)
  rw [hEw,hgrad] at hw
  unfold electricResidual
  rw [dirD_add (((contDiff_dirD hE _).sub (contDiff_spaceCurl hB)).differentiable (by simp))
    (hj.differentiable (by simp)),dirD_sub ((contDiff_dirD hE _).differentiable (by simp))
      ((contDiff_spaceCurl hB).differentiable (by simp))]
  dsimp only
  rw [dirD_spaceCurl hB,hBc]
  linear_combination (norm := module) hw

end RVM
end

end OAI
