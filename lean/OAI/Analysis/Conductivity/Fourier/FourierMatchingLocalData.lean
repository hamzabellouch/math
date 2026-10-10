import Mathlib
import OAI.Analysis.Conductivity.Geometry.TorusLocalizedMoments
import OAI.Analysis.Conductivity.Fourier.FourierMatchingInterpolation

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma flatTensorLaplacian_congr_nhds (s : Fin 3 → ℝ) {f g : Coord3 → ℝ} {x : Coord3}
    (h : f=ᶠ[𝓝 x] g) : flatTensorLaplacian s f x=flatTensorLaplacian s g x :=
  congrArg (flatTensorLaplacianCLM s) ((h.iteratedFDeriv ℝ 2).self_of_nhds)

lemma fourier_left_coeff_bound {k : ℤ} {b : (Fin 2 → ℤ) → ℝ} {B : ℝ}
    (hb : ∀ h,|b h|≤B) (h : Fin 2 → ℤ) :
    |(Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h|≤1+B :=
  (abs_add_le _ _).trans (add_le_add (single_fourier_coeff_bound _ _) (hb h))

lemma fourierMatchingPair_left_fourier {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {B p : ℝ}
    (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y)
    {x : Coord3} (hx : x 0∈Ioo 0 2) :
    (fun y => fourierMatchingPair s k f g (p,y) 0)=ᶠ[𝓝 x] affineFourierField s a pa 1 0 ∧
    (fun y => fourierMatchingPair s k f g (p,y) 1)=ᶠ[𝓝 x]
      flatFourier s (fun h => (Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h) pb := by
  have hn : ∀ᶠ y in 𝓝 x,y 0∈Ioo 0 2 :=
    (isOpen_Ioo.preimage (continuous_apply 0)).mem_nhds hx
  constructor
  · filter_upwards [hn] with y hy
    change y 0+fourierMatchingCutoff (y 0)*f (p,y)=_
    rw [fourierMatchingCutoff_left hy.2.le,one_mul,hf y ⟨hy.1.le,by linarith [hy.2]⟩]
    simp only [affineFourierField,one_mul,add_zero]
  · filter_upwards [hn] with y hy
    change flatPhaseMode s ![0,k] 0 y+fourierMatchingCutoff (y 0)*g (p,y)=_
    rw [fourierMatchingCutoff_left hy.2.le,one_mul,hg y ⟨hy.1.le,by linarith [hy.2]⟩,
      flatFourier_add hs (single_fourier_coeff_bound ![0,k]) hb hy.1,
      flatFourier_single,hp,one_mul]

lemma fourierMatchingPair_right_fourier (s : Fin 3 → ℝ) (k : ℤ) (f g : ℝ×Coord3 → ℝ)
    (pa pb : (Fin 2 → ℤ) → ℝ) (hp : pb ![0,k]=0) (p : ℝ) {x : Coord3} (hx : 4<x 0) :
    (fun y => fourierMatchingPair s k f g (p,y) 0)=ᶠ[𝓝 x] affineFourierField s (fun _ => 0) pa 1 0 ∧
    (fun y => fourierMatchingPair s k f g (p,y) 1)=ᶠ[𝓝 x] flatFourier s (Pi.single ![0,k] 1) pb := by
  have hn : ∀ᶠ y in 𝓝 x,4<y 0 := (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx
  constructor
  · filter_upwards [hn] with y hy
    change y 0+fourierMatchingCutoff (y 0)*f (p,y)=_
    simp only [fourierMatchingCutoff_right hy.le,zero_mul,add_zero,affineFourierField,
      flatFourier_zero,one_mul]
  · filter_upwards [hn] with y hy
    change flatPhaseMode s ![0,k] 0 y+fourierMatchingCutoff (y 0)*g (p,y)=_
    rw [fourierMatchingCutoff_right hy.le,zero_mul,add_zero,flatFourier_single,hp,one_mul]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma periodicSourceMoment_neg (T : ℝ) (u : Coord3 → Fin 2 → ℝ) (r : Fin 2 → Coord3 → ℝ) :
    periodicSourceMoment T u (fun j x => -r j x)=-periodicSourceMoment T u r := by
  have hpoint (x : Coord3) : u x 1*(-r 0 x)-u x 0*(-r 1 x)=
      -(u x 1*r 0 x-u x 0*r 1 x) := by ring
  ext i
  fin_cases i
  · change (∫ t,∫ y in 0..T,∫ z in 0..T,-r 0 ![t,y,z])=-(∫ t,∫ y in 0..T,∫ z in 0..T,r 0 ![t,y,z])
    simp only [intervalIntegral.integral_neg,integral_neg]
  · change (∫ t,∫ y in 0..T,∫ z in 0..T,-r 1 ![t,y,z])=-(∫ t,∫ y in 0..T,∫ z in 0..T,r 1 ![t,y,z])
    simp only [intervalIntegral.integral_neg,integral_neg]
  · change (∫ t,∫ y in 0..T,∫ z in 0..T,u ![t,y,z] 1*(-r 0 ![t,y,z])-u ![t,y,z] 0*(-r 1 ![t,y,z]))=
        -(∫ t,∫ y in 0..T,∫ z in 0..T,u ![t,y,z] 1*r 0 ![t,y,z]-u ![t,y,z] 0*r 1 ![t,y,z])
    simp only [hpoint,intervalIntegral.integral_neg,integral_neg]

theorem fourier_matching_three_moments {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a b : Fin 2 → (Fin 2 → ℤ) → ℝ} {pa pb : Fin 2 → (Fin 2 → ℤ) → ℝ}
    {Ba Bb ga gb : Fin 2 → ℝ} {l d α : ℝ} {β : Fin 2 → ℝ}
    (ha : ∀ e h,|a e h|≤Ba e) (hb : ∀ e h,|b e h|≤Bb e)
    (hga : ∀ e,0<ga e) (hgb : ∀ e,0<gb e)
    (hra : ∀ e h,a e h≠0 → ga e≤torusRate s h)
    (hrb : ∀ e h,b e h≠0 → gb e≤torusRate s h)
    (hl : 0<l) (hld : l≤d) {u : Coord3 → Fin 2 → ℝ} {r : Fin 2 → Coord3 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hup : AngularPeriodic (2*Real.pi) u)
    (he0 : ∀ e x,x 0=![l,d] e → (fun y => u y 0)=ᶠ[𝓝 x] affineFourierField s (a e) (pa e) α (β e))
    (he1 : ∀ e x,x 0=![l,d] e → (fun y => u y 1)=ᶠ[𝓝 x] flatFourier s (b e) (pb e))
    (hrs : ∀ j,tsupport (r j)⊆{x | x 0∈Icc l d})
    (hre : ∀ j x,x 0∈Icc l d → r j x=symmetricSource (fun _ => flatBackgroundTensor s) u j x) :
    periodicSourceMoment (2*Real.pi) u r=0 ∧
      periodicSourceMoment (2*Real.pi) u (fun j x => -r j x)=0 := by
  have ht (e : Fin 2) : 0<![l,d] e := by fin_cases e; exact hl; exact hl.trans_le hld
  have he (e : Fin 2) := fourier_pair_boundary_flux hs (ha e) (hb e) (hga e) (hgb e)
    (hra e) (hrb e) α (β e) (ht e) (hu.differentiable (by simp)) (he0 e) (he1 e)
  have heL := he 0
  have heR := he 1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at heL heR
  have hm := periodic_localized_source_moment_formula (by positivity : 0≤2*Real.pi) hld
    (H:=fun _ => flatBackgroundTensor s) contDiff_const hu (fun _ _ => rfl) hup
    (fun _ => flatBackgroundTensor_symm s) hrs hre
  have hz : periodicSourceMoment (2*Real.pi) u r=0 := by
    rw [hm]
    ext i
    fin_cases i
    · change _-_=0
      rw [heR.1,heL.1,sub_self]
    · change _-_=0
      rw [heR.2.1,heL.2.1,sub_self]
    · change _-_=0
      rw [heR.2.2,heL.2.2,sub_self]
  exact ⟨hz,by rw [periodicSourceMoment_neg,hz,neg_zero]⟩

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma fourierMatchingResidual_exact {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B p : ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y)
    (j : Fin 2) (x : Coord3) (hx : 0<x 0) :
    fourierMatchingResidual s k f g j (p,x)=
      -symmetricSource (fun _ => flatBackgroundTensor s) (fun y => fourierMatchingPair s k f g (p,y)) j x := by
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fourierMatchingPair s k f g (p,y)) :=
    (fourierMatchingPair_smooth s k hfs hgs).comp ((contDiff_const (c:=p)).prodMk contDiff_id)
  by_cases hmid : x 0∈Icc 2 4
  · simp only [fourierMatchingResidual,fourierResidualCutoff_one hmid,neg_mul,one_mul]
  have hz : symmetricSource (fun _ => flatBackgroundTensor s) (fun y => fourierMatchingPair s k f g (p,y)) j x=0 := by
    rw [flatBackgroundTensor_source hu]
    by_cases hleft : x 0<2
    · have he := fourierMatchingPair_left_fourier hs k hb hp hf hg (x:=x) ⟨hx,hleft⟩
      fin_cases j
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 0) x=0
        rw [flatTensorLaplacian_congr_nhds s he.1]
        exact affineFourierField_harmonic hs ha 1 0 hx
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 1) x=0
        rw [flatTensorLaplacian_congr_nhds s he.2]
        exact flatFourier_harmonic hs (fourier_left_coeff_bound hb) hx
    · have hright : 4<x 0 := by
        by_contra hh
        exact hmid ⟨le_of_not_gt hleft,le_of_not_gt hh⟩
      have he := fourierMatchingPair_right_fourier s k f g pa pb hp p hright
      fin_cases j
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 0) x=0
        rw [flatTensorLaplacian_congr_nhds s he.1]
        exact affineFourierField_harmonic hs (B:=0) (by intro h; simp) 1 0 (by linarith)
      · change flatTensorLaplacian s (fun y => fourierMatchingPair s k f g (p,y) 1) x=0
        rw [flatTensorLaplacian_congr_nhds s he.2]
        exact flatFourier_harmonic hs (single_fourier_coeff_bound ![0,k]) (by linarith)
  simp only [fourierMatchingResidual,hz,mul_zero,neg_zero]

lemma fourier_single_plus_rate {s : Fin 3 → ℝ} {k : ℤ} {b : (Fin 2 → ℤ) → ℝ}
    (hb : ∀ h,b h≠0 → torusRate s ![0,k]≤torusRate s h) :
    ∀ h,(Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h≠0 → torusRate s ![0,k]≤torusRate s h := by
  classical
  intro h hh
  by_cases he : h=![0,k]
  · subst h; exact le_rfl
  · apply hb h
    simpa only [Pi.single_eq_of_ne he,zero_add] using hh

lemma fourierMatchingResidual_moments {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B p ga : ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (hfp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hgp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x)))
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hga : 0<ga) (hgb : 0<torusRate s ![0,k])
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]≤torusRate s h)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y) :
    periodicSourceMoment (2*Real.pi) (fun y => fourierMatchingPair s k f g (p,y))
      (fun j y => fourierMatchingResidual s k f g j (p,y))=0 := by
  classical
  let aa : Fin 2 → (Fin 2 → ℤ) → ℝ := ![a,fun _ => 0]
  let bb : Fin 2 → (Fin 2 → ℤ) → ℝ := ![fun h => (Pi.single ![0,k] (1:ℝ) : (Fin 2 → ℤ) → ℝ) h+b h,Pi.single ![0,k] 1]
  have haa : ∀ e h,|aa e h|≤![A,0] e := by intro e h; fin_cases e; exact ha h; simp [aa]
  have hbb : ∀ e h,|bb e h|≤![1+B,1] e := by
    intro e h
    fin_cases e
    · exact fourier_left_coeff_bound hb h
    · exact single_fourier_coeff_bound _ _
  have hraa : ∀ e h,aa e h≠0 → ga≤torusRate s h := by
    intro e h hh
    fin_cases e
    · exact hra h hh
    · exact False.elim (hh rfl)
  have hrbb : ∀ e h,bb e h≠0 → torusRate s ![0,k]≤torusRate s h := by
    intro e h hh
    fin_cases e
    · exact fourier_single_plus_rate hrb h hh
    · by_cases he : h=![0,k]
      · subst h; exact le_rfl
      · exact False.elim (hh (Pi.single_eq_of_ne he 1))
  have he (e : Fin 2) (x : Coord3) (hx : x 0=![1,5] e) :
      (fun y => fourierMatchingPair s k f g (p,y) 0)=ᶠ[𝓝 x] affineFourierField s (aa e) pa 1 0 ∧
      (fun y => fourierMatchingPair s k f g (p,y) 1)=ᶠ[𝓝 x] flatFourier s (bb e) pb := by
    fin_cases e
    · exact fourierMatchingPair_left_fourier hs k hb hp hf hg ⟨by simpa using hx ▸ (show (0:ℝ)<1 by norm_num),by simpa using hx ▸ (show (1:ℝ)<2 by norm_num)⟩
    · exact fourierMatchingPair_right_fourier s k f g pa pb hp p (by simpa using hx ▸ (show (4:ℝ)<5 by norm_num))
  have hrs (j : Fin 2) : tsupport (fun y => -fourierMatchingResidual s k f g j (p,y))⊆{x | x 0∈Icc 1 5} := by
    rw [show (fun y => -fourierMatchingResidual s k f g j (p,y))= -(fun y => fourierMatchingResidual s k f g j (p,y)) from rfl,tsupport_neg]
    exact fourierMatchingResidual_support s k f g p j
  have hre (j : Fin 2) (x : Coord3) (hx : x 0∈Icc 1 5) :
      -fourierMatchingResidual s k f g j (p,x)= symmetricSource (fun _ => flatBackgroundTensor s)
        (fun y => fourierMatchingPair s k f g (p,y)) j x := by
    rw [fourierMatchingResidual_exact hs k hfs hgs ha hb hp hf hg j x (by linarith [hx.1]),neg_neg]
  have hu : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fourierMatchingPair s k f g (p,y)) :=
    (fourierMatchingPair_smooth s k hfs hgs).comp ((contDiff_const (c:=p)).prodMk contDiff_id)
  have hm := fourier_matching_three_moments hs haa hbb (fun _ => hga) (fun _ => hgb)
    hraa hrbb (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤5)
    hu
    (fourierMatchingPair_periodic s k hfp hgp p) (fun e x hx => (he e x hx).1) (fun e x hx => (he e x hx).2) hrs hre
  simpa only [neg_neg,Function.comp_apply] using hm.2

end ScalarConductivity

end

end OAI
