import Mathlib
import OAI.Analysis.Conductivity.Fourier.FourierMatchingElliptic
import OAI.Analysis.Conductivity.Variational.SimpleLevelNull

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

lemma exists_angular_translate_mem_box {T : ℝ} (hT : 0<T) {a b : ℝ} (x : Coord3)
    (hx : x 0∈Icc a b) :
    ∃ n : Fin 2 → ℤ,x+angularShift T n∈Icc ![a,0,0] ![b,T,T] := by
  let n : Fin 2 → ℤ := fun i => -⌊x i.succ/T⌋
  have hn (i : Fin 2) : 0≤x i.succ+T*(n i:ℝ) ∧ x i.succ+T*(n i:ℝ)≤T := by
    have h0 := (le_div_iff₀ hT).mp (Int.floor_le (x i.succ/T))
    have h1 := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (x i.succ/T))
    simp only [n,Int.cast_neg]
    constructor <;> nlinarith
  refine ⟨n,?_,?_⟩
  · intro i
    fin_cases i
    · change a≤x 0+0
      simpa only [add_zero] using hx.1
    · exact (hn 0).1
    · exact (hn 1).1
  · intro i
    fin_cases i
    · change x 0+0≤b
      simpa only [add_zero] using hx.2
    · exact (hn 0).2
    · exact (hn 1).2

variable {P : Type*} [TopologicalSpace P]

lemma periodic_band_nonzero_eventually {F G : P×Coord3 → ℝ}
    (hF : Continuous F) (hG : Continuous G) {T : ℝ} (hT : 0<T)
    (hpF : ∀ p,AngularPeriodic T (fun x => F (p,x)))
    (hpG : ∀ p,AngularPeriodic T (fun x => G (p,x)))
    (p₀ : P) (a b : ℝ)
    (hb : ∀ x : Coord3,x 0∈Icc a b → F (p₀,x)≠0 ∨ G (p₀,x)≠0) :
    ∀ᶠ p in 𝓝 p₀,∀ x : Coord3,x 0∈Icc a b → F (p,x)≠0 ∨ G (p,x)≠0 := by
  have he : ∀ᶠ p in 𝓝 p₀,∀ x∈Icc (![a,0,0] : Coord3) ![b,T,T], F (p,x)≠0 ∨ G (p,x)≠0 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x hx
    rcases hb x ⟨hx.1 0,hx.2 0⟩ with hf|hg
    · exact (hF.continuousAt.eventually_ne hf).mono (fun z hz => Or.inl hz)
    · exact (hG.continuousAt.eventually_ne hg).mono (fun z hz => Or.inr hz)
  filter_upwards [he] with p hp
  intro x hx
  obtain ⟨n,hn⟩ := exists_angular_translate_mem_box hT x hx
  simpa only [hpF p n x,hpG p n x] using hp (x+angularShift T n) hn

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory Real

lemma pairMinor_wallCoordinatePair {v : Box3 → ℝ} (hv : Differentiable ℝ v) (x : Coord3) :
    pairMinor (wallCoordinatePair v) x=wallDerivative v (boxCoordinates x) := by
  simp [pairMinor,wallCoordinatePair_derivative hv,boxCoordinates_apply,wallDerivative]
  rfl

lemma direction_boxCoordinates {v : Box3 → ℝ} (hv : Differentiable ℝ v) (x : Coord3) :
    direction (Pi.single 2 1) (fun y => v (boxCoordinates y)) x=wallDerivative v (boxCoordinates x) := by
  change fderiv ℝ (v ∘ boxCoordinates) x (Pi.single 2 1)=_
  rw [boxCoordinates_fderiv v hv]
  simp [wallDerivative,boxCoordinates_apply]
  rfl

lemma pureMode_pairMinor_noncritical {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0) (x : Coord3) :
    pairMinor (wallCoordinatePair (pureWallMode σ lam k)) x≠0 ∨
      direction (Pi.single 2 1) (pairMinor (wallCoordinatePair (pureWallMode σ lam k))) x≠0 := by
  have hs := pureWallMode_smooth σ lam k
  have he : pairMinor (wallCoordinatePair (pureWallMode σ lam k))=
      fun x => wallDerivative (pureWallMode σ lam k) (boxCoordinates x) :=
    funext (pairMinor_wallCoordinatePair (hs.differentiable (by simp)))
  rw [he,direction_boxCoordinates ((wallDerivative_smooth hs).differentiable (by simp))]
  dsimp only
  rw [boxCoordinates_apply,pureWallMode_normalDerivative,pureWallMode_normalSecond]
  by_cases hz : sin (k*x 2)=0
  · right
    have hc : cos (k*x 2)≠0 := by
      intro hc
      have hh := sin_sq_add_cos_sq (k*x 2)
      rw [hz,hc] at hh
      norm_num at hh
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) hc) (pow_ne_zero 2 hk))
  · left
    exact mul_ne_zero (mul_ne_zero hσ (exp_ne_zero _)) (mul_ne_zero (neg_ne_zero.mpr hz) hk)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma familyDirection_smooth {f : P×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (v : Coord3) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : P×Coord3 => direction v (fun y => f (z.1,y)) z.2) := by
  have hh : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : (P×Coord3)×Coord3 => f (z.1.1,z.2)) :=
    hf.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact (hh.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

lemma AngularPeriodic.direction {T : ℝ} {f : Coord3 → ℝ} (hf : AngularPeriodic T f) (v : Coord3) :
    AngularPeriodic T (direction v f) := by
  intro n x
  change _root_.fderiv ℝ f (x+angularShift T n) v=_root_.fderiv ℝ f x v
  rw [hf.fderiv n x]

theorem periodic_pure_mode_rank_eventually {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {T : ℝ} (hT : 0<T)
    (hp : ∀ p,AngularPeriodic T (fun x => u (p,x))) (p₀ : P)
    {σ lam k : ℝ} (hσ : σ≠0) (hk : k≠0)
    (hb : ∀ x,u (p₀,x)=wallCoordinatePair (pureWallMode σ lam k) x) (a b : ℝ) :
    ∀ᶠ p in 𝓝 p₀,∀ x : Coord3,x 0∈Icc a b → pairMinor (fun y => u (p,y)) x=0 →
      direction (Pi.single 2 1) (pairMinor (fun y => u (p,y))) x≠0 := by
  have hM := familyPairMinor_smooth hu
  have hN := familyDirection_smooth hM (Pi.single 2 1)
  have he := periodic_band_nonzero_eventually hM.continuous hN.continuous hT
    (fun p => (hp p).pairMinor) (fun p => (hp p).pairMinor.direction (Pi.single 2 1)) p₀ a b (by
      intro x _
      have hh : (fun y => u (p₀,y))=wallCoordinatePair (pureWallMode σ lam k) := funext hb
      simpa only [hh] using pureMode_pairMinor_noncritical hσ hk (lam:=lam) x)
  filter_upwards [he] with p hp
  intro x hx hz
  exact (hp x hx).resolve_left (not_not.mpr hz)

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

theorem elliptic_fourier_matching_regular {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : k≠0) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ p : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧
      ∃ (u : Coord3 → Fin 2 → ℝ) (D : Coord3 → Mat3),
        ContDiff ℝ (↑(⊤:ℕ∞)) u ∧ ContDiff ℝ (↑(⊤:ℕ∞)) D ∧
        AngularPeriodic (2*Real.pi) u ∧ AngularPeriodic (2*Real.pi) D ∧
        (∀ x,(D x).IsSymm) ∧
        (∀ x v,(1/4)*(v ⬝ᵥ v)≤v ⬝ᵥ (D x*ᵥv) ∧
          v ⬝ᵥ (D x*ᵥv)≤(3*‖flatBackgroundTensor s‖+1)*(v ⬝ᵥ v)) ∧
        (∀ j x,0<x 0 → symmetricSource D u j x=0) ∧
        (∀ x,x 0∉Icc (1/2) (11/2) → D x=flatBackgroundTensor s) ∧
        (∀ x,x 0∈Icc 0 (1/2) → u x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
            flatPhaseMode s ![0,k] 0 x+
              flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
        (∀ x,4≤x 0 → u x=![x 0,flatPhaseMode s ![0,k] 0 x]) ∧
        ∀ᵐ x : Coord3,x 0∈Ioo 0 6 → LinearIndependent ℝ (gradientColumns (fderiv ℝ u x)).col := by
  obtain ⟨f,g,hfs,hgs,hfp,hgp,hfz,hgz,hdata,hcor⟩ := smooth_fourier_matching_with_origin (pa:=pa) hs hk hA hB ha hb hga hgb hra hrb hpb
  have hF := fourierMatchingPair_smooth s k hfs hgs
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk
  have hbase (x : Coord3) : fourierMatchingPair s k f g (0,x)=
      wallCoordinatePair (pureWallMode 1 (torusRate s ![0,k]) (k:ℝ)) x := by
    ext j
    fin_cases j <;> simp [fourierMatchingPair,hfz,hgz,wallCoordinatePair,pureWallMode_eq_flatPhaseMode]
  have hRank := periodic_pure_mode_rank_eventually hF (by positivity : 0<2*Real.pi)
    (fourierMatchingPair_periodic s k hfp hgp) 0 (by norm_num : (1:ℝ)≠0) hk' hbase 0 6
  have hh := (hcor (1/12) (by norm_num)).and hRank
  obtain ⟨r,hr,hrb'⟩ := Metric.mem_nhds_iff.mp hh
  let p := min (r/2) (min (δ/2) (1/4))
  have hp : 0<p := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hpr : p<r := (min_le_left _ _).trans_lt (by linarith)
  have hpδ : p<δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hp2 : p≤1/2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨hc,hr⟩ := hrb' (show p∈Metric.ball (0:ℝ) r from by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hp] using hpr)
  obtain ⟨H,hHs,hHp,hHt,hHsym,hHb,hHe⟩ := hc ⟨hp,hp2⟩
  refine ⟨p,⟨hp,hp2⟩,hpδ,(fun x => fourierMatchingPair s k f g (p,x)),
    (fun x => flatBackgroundTensor s+H x),
    (fourierMatchingPair_smooth s k hfs hgs).comp (contDiff_const.prodMk contDiff_id),
    contDiff_const.add hHs,fourierMatchingPair_periodic s k hfp hgp p,?_,?_,?_,hHe,?_,?_,?_,?_⟩
  · intro n x
    dsimp only
    rw [hHp n x]
  · intro x
    exact (flatBackgroundTensor_symm s).add (hHsym x)
  · intro x v
    exact flatBackgroundTensor_small_perturbation hs (hHb x) v
  · intro x hx
    have hz : H x=0 := image_eq_zero_of_notMem_tsupport (fun hx' => hx (hHt hx'))
    dsimp only
    rw [hz,add_zero]
  · intro x hx
    have hd := hdata p ⟨hp,hp2⟩ x ⟨hx.1,by linarith [hx.2]⟩
    simp only [fourierMatchingPair,fourierMatchingCutoff_left (show x 0≤2 by linarith [hx.2]),one_mul,hd.1,hd.2]
  · intro x hx
    simp only [fourierMatchingPair,fourierMatchingCutoff_right hx,zero_mul,add_zero]

  · have hU : IsOpen {x : Coord3 | x 0∈Ioo (0:ℝ) 6} :=
      isOpen_Ioo.preimage (continuous_apply 0)
    have ha := simple_coord_zero_ae (pairMinor_smooth (hF.comp (contDiff_const.prodMk contDiff_id)))
      hU.measurableSet (by
        intro x hx
        exact hr x ⟨hx.1.le,hx.2.le⟩)
    filter_upwards [ha] with x hx
    intro hxU
    exact pairMinor_rank (hx hxU)

end ScalarConductivity

end

end OAI
