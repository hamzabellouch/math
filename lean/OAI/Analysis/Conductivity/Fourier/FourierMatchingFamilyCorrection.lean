import Mathlib
import OAI.Analysis.Conductivity.Fourier.FourierMatchingLocalData

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

lemma axial_torusRate_pos {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) : 0<torusRate s ![0,k] := by
  have hb := torusRate_lower hs ![0,k]
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  have hp := abs_pos.mpr hk'
  simp only [torusSize,Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_zero,abs_zero,zero_add] at hb
  linarith

lemma fourierMatchingFamily_correction {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {f g : ℝ×Coord3 → ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (hfp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x)))
    (hgp : ∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x)))
    (hfz : ∀ x,f (0,x)=0) (hgz : ∀ x,g (0,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ p in 𝓝 (0:ℝ),periodicSourceMoment (2*Real.pi) (fun y => fourierMatchingPair s k f g (p,y))
      (fun j y => fourierMatchingResidual s k f g j (p,y))=0 →
      ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic (2*Real.pi) H ∧
        tsupport H⊆{x | x 0∈Icc (1/2) (11/2)} ∧ (∀ x,(H x).IsSymm) ∧
        (∀ j,symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j=(fun y => fourierMatchingResidual s k f g j (p,y))) ∧
        ∀ x,‖H x‖≤ε := by
  have hF := fourierMatchingPair_smooth s k hfs hgs
  have hF0 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => fourierMatchingPair s k f g z 0) :=
    (contDiff_apply ℝ ℝ (0:Fin 2)).comp hF
  have hF1 : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z => fourierMatchingPair s k f g z 1) :=
    (contDiff_apply ℝ ℝ (1:Fin 2)).comp hF
  have hup (p : ℝ) : AngularPeriodic (2*Real.pi)
      (fun y => ![fourierMatchingPair s k f g (p,y) 0,fourierMatchingPair s k f g (p,y) 1]) :=
    fourierMatchingPair_periodic s k hfp hgp p
  have hub (x : Coord3) : fourierMatchingPair s k f g (0,x) 0=x 0 := by
    simp [fourierMatchingPair,hfz]
  have hvb (x : Coord3) : fourierMatchingPair s k f g (0,x) 1=
      pureWallMode 1 (torusRate s ![0,k]) (k:ℝ) (boxCoordinates x) := by
    simp [fourierMatchingPair,hgz,pureWallMode_eq_flatPhaseMode]
  have hlam := axial_torusRate_pos hs hk
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  exact periodic_pure_mode_family_correction hF0 hF1 (0:ℝ)
    (by norm_num : (1:ℝ)≠0) hlam.ne' hk' (by positivity : 0<2*Real.pi)
    (by norm_num : (1/2:ℝ)<1) (by norm_num : (5:ℝ)<11/2) hub hvb hup
    (fourierMatchingResidual_smooth s k hfs hgs)
    (fourierMatchingResidual_base hs k hfz hgz)
    (fun j p => fourierMatchingResidual_periodic s k hfp hgp p j)
    (fun j p => fourierMatchingResidual_support s k f g p j) hε

lemma fourierMatching_corrected_equation {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (k : ℤ) {f g : ℝ×Coord3 → ℝ} {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B p : ℝ}
    (hfs : ContDiff ℝ (↑(⊤:ℕ∞)) f) (hgs : ContDiff ℝ (↑(⊤:ℕ∞)) g)
    (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B) (hp : pb ![0,k]=0)
    (hf : ∀ y : Coord3,y 0∈Icc 0 6 → f (p,y)=flatFourier s a pa y)
    (hg : ∀ y : Coord3,y 0∈Icc 0 6 → g (p,y)=flatFourier s b pb y)
    {H : Coord3 → Mat3} (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H)
    (hHr : ∀ j,symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j=(fun y => fourierMatchingResidual s k f g j (p,y))) :
    ∀ j x,0<x 0 → symmetricSource (fun y => flatBackgroundTensor s+H y)
      (fun y => fourierMatchingPair s k f g (p,y)) j x=0 := by
  intro j x hx
  have hFs : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y : Coord3 => fourierMatchingPair s k f g (p,y)) :=
    (fourierMatchingPair_smooth s k hfs hgs).comp ((contDiff_const (c:=p)).prodMk contDiff_id)
  have hadd := congrFun (symmetricSource_add (H:=fun _ => flatBackgroundTensor s) (K:=H) contDiff_const hH hFs j) x
  have hr := congrFun (hHr j) x
  have hre := fourierMatchingResidual_exact hs k hfs hgs ha hb hp hf hg j x hx
  change symmetricSource (fun y => flatBackgroundTensor s+H y) (fun y => fourierMatchingPair s k f g (p,y)) j x=
      symmetricSource (fun _ => flatBackgroundTensor s) (fun y => fourierMatchingPair s k f g (p,y)) j x+
        symmetricSource H (fun y => fourierMatchingPair s k f g (p,y)) j x at hadd
  exact hadd.trans (by rw [hr,hre,add_neg_cancel])

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real Matrix
open scoped Matrix.Norms.Elementwise

theorem smooth_fourier_matching {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) :
    ∃ f g : ℝ×Coord3 → ℝ,
      ContDiff ℝ (↑(⊤:ℕ∞)) f ∧ ContDiff ℝ (↑(⊤:ℕ∞)) g ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => f (p,x))) ∧
      (∀ p,AngularPeriodic (2*Real.pi) (fun x => g (p,x))) ∧
      (∀ p∈Ioc 0 (1/2),∀ x : Coord3,x 0∈Icc 0 6 →
        f (p,x)=flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x ∧
        g (p,x)=flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ p in 𝓝 (0:ℝ),p∈Ioc 0 (1/2) →
        ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ AngularPeriodic (2*Real.pi) H ∧
          tsupport H⊆{x | x 0∈Icc (1/2) (11/2)} ∧ (∀ x,(H x).IsSymm) ∧
          (∀ x,‖H x‖≤ε) ∧ ∀ j x,0<x 0 →
            symmetricSource (fun y => flatBackgroundTensor s+H y) (fun y => fourierMatchingPair s k f g (p,y)) j x=0 := by
  obtain ⟨f,hfs,hfp,hfz,hfe⟩ := exists_smooth_periodic_normalized_tail
    (lam:=0) (T0:=10) (δ:=1) (R:=7) (phase:=pa) hs hga hA ha (by norm_num)
    (by simpa only [zero_add] using hra) (by norm_num)
  obtain ⟨g,hgs,hgp,hgz,hge⟩ := exists_smooth_periodic_normalized_tail
    (lam:=torusRate s ![0,k]) (T0:=10) (δ:=1) (R:=7) (phase:=pb) hs hgb hB hb (by norm_num)
    hrb (by norm_num)
  have hdata (p : ℝ) (hp : p∈Ioc 0 (1/2)) (x : Coord3) (hx : x 0∈Icc 0 6) :
      f (p,x)=flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x ∧
      g (p,x)=flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x := by
    have hx' : x 0∈Icc (-7:ℝ) 7 := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    constructor
    · rw [hfe p hp x hx',flatFourier_normalized_translation]
    · rw [hge p hp x hx',flatFourier_normalized_translation]
  refine ⟨f,g,hfs,hgs,hfp,hgp,hdata,?_⟩
  intro ε hε
  have hlam := axial_torusRate_pos hs hk
  have hcor := fourierMatchingFamily_correction hs hk hfs hgs hfp hgp (hfz 0 le_rfl) (hgz 0 le_rfl) hε
  filter_upwards [hcor] with p hcor
  intro hp
  have hT : 0≤10+1/p := by have hpos := hp.1; positivity
  let aa := normalizedFourierCoefficients s 0 (10+1/p) a
  let bb := normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b
  have haa : ∀ h,|aa h|≤A := normalizedFourierCoefficients_bound ha hT
    (fun h hh => hga.le.trans (hra h hh))
  have hbb : ∀ h,|bb h|≤B := normalizedFourierCoefficients_bound hb hT
    (fun h hh => by linarith [hrb h hh])
  have hraa : ∀ h,aa h≠0 → ga≤torusRate s h := by
    intro h hh
    exact hra h (fun hz => hh ((normalizedFourierCoefficients_zero_iff _ _ _ _ _).mpr hz))
  have hrbb : ∀ h,bb h≠0 → torusRate s ![0,k]≤torusRate s h := by
    intro h hh
    have hn : b h≠0 := fun hz => hh ((normalizedFourierCoefficients_zero_iff _ _ _ _ _).mpr hz)
    linarith [hrb h hn]
  have hff (x : Coord3) (hx : x 0∈Icc 0 6) : f (p,x)=flatFourier s aa pa x := (hdata p hp x hx).1
  have hgg (x : Coord3) (hx : x 0∈Icc 0 6) : g (p,x)=flatFourier s bb pb x := (hdata p hp x hx).2
  have hm := fourierMatchingResidual_moments hs k hfs hgs hfp hgp haa hbb hpb hga hlam hraa hrbb hff hgg
  obtain ⟨H,hH,hHp,hHs,hHsy,hHr,hHb⟩ := hcor hm
  refine ⟨H,hH,hHp,hHs,hHsy,hHb,?_⟩
  exact fourierMatching_corrected_equation hs k hfs hgs haa hbb hpb hff hgg hH hHr

end ScalarConductivity

end
end

end OAI
