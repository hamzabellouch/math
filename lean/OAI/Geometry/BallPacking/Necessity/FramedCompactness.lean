import Mathlib
import OAI.Geometry.BallPacking.Necessity.GradientLimits

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity.FramedCR
open HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter Function
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

def HasFrame (J : E →L[ℝ] E) : Prop :=
  ∃ S : E ≃L[ℝ] E, ∀ v, S (J v)=Complex.I • S v

def centeredFrame  (S : E ≃L[ℝ] E) (p : E)
    (u : ℂ → E) : ℂ → E := fun z => S (u z-p)

def frozenCoefficient  (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    (B : ℂ → (E →L[ℝ] E)) : ℂ → (E →L[ℝ] E) := fun z =>
      S.toContinuousLinearMap.comp ((B z-J).comp S.symm.toContinuousLinearMap)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem centeredFrame_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (p : E)
    {u : ℂ → E} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (centeredFrame S p u) :=
  S.contDiff.comp (hu.sub contDiff_const)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem centeredFrame_fderiv [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (p : E)
    {u : ℂ → E} (hu : Differentiable ℝ u) (z : ℂ) :
    fderiv ℝ (centeredFrame S p u) z=S.toContinuousLinearMap.comp (fderiv ℝ u z) := by
  exact (S.hasFDerivAt.comp z ((hu z).hasFDerivAt.sub_const p)).fderiv

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem frozenCoefficient_smooth [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    {B : ℂ → (E →L[ℝ] E)} (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (frozenCoefficient S J B) :=
  contDiff_const.clm_comp ((hB.sub contDiff_const).clm_comp contDiff_const)

theorem frozen_CR_equation  (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    (hS : ∀ v, S (J v)=Complex.I • S v) (p : E)
    {u : ℂ → E} (hu : Differentiable ℝ u) (B : ℂ → (E →L[ℝ] E)) {z : ℂ}
    (hCR : fderiv ℝ u z Complex.I=B z (fderiv ℝ u z 1)) :
    fderiv ℝ (centeredFrame S p u) z Complex.I-
      Complex.I • fderiv ℝ (centeredFrame S p u) z 1=
      frozenCoefficient S J B z (fderiv ℝ (centeredFrame S p u) z 1) := by
  rw [centeredFrame_fderiv S p hu z]
  change S (fderiv ℝ u z Complex.I)-Complex.I • S (fderiv ℝ u z 1)=
    S ((B z-J) (S.symm (S (fderiv ℝ u z 1))))
  simp only [S.symm_apply_apply,sub_apply,map_sub,hCR,hS]

def frameConjugation  (S : E ≃L[ℝ] E) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ (E) (E) (E) S.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ (E) (E) (E)).flip S.symm.toContinuousLinearMap)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
@[simp] theorem frameConjugation_apply [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (B : (E →L[ℝ] E)) :
    frameConjugation S B=S.toContinuousLinearMap.comp (B.comp S.symm.toContinuousLinearMap) := rfl

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem frozenCoefficient_fderiv [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : E ≃L[ℝ] E) (J : (E →L[ℝ] E))
    {B : ℂ → (E →L[ℝ] E)} (hB : Differentiable ℝ B) (z : ℂ) :
    fderiv ℝ (frozenCoefficient S J B) z=(frameConjugation S).comp (fderiv ℝ B z) :=
  ((frameConjugation S).hasFDerivAt.comp z ((hB z).hasFDerivAt.sub_const J)).fderiv

theorem frozen_CR_no_gradient_loss 
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (B : ℕ → ℂ → (E →L[ℝ] E)) (hB : ∀ j, ContDiff ℝ ∞ (B j))
    (p : E) (J : (E →L[ℝ] E)) (hJ : HasFrame J)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hBD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (B j) z‖ ≤ K)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I=B j z (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => p) atTop (Metric.closedBall (0:ℂ) 3))
    (hB0 : TendstoUniformlyOn B (fun _ => J) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  obtain ⟨S,hS⟩ := hJ
  let U : ℕ → ℂ → E := fun j => centeredFrame S p (u j)
  let A : ℕ → ℂ → (E →L[ℝ] E) := fun j => frozenCoefficient S J (B j)
  have hU : ∀ j, ContDiff ℝ ∞ (U j) := fun j => centeredFrame_smooth S p (hu j)
  have hA : ∀ j, ContDiff ℝ ∞ (A j) := fun j => frozenCoefficient_smooth S J (hB j)
  have hUD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (U j) z‖ ≤ ‖S.toContinuousLinearMap‖*L := by
    filter_upwards [huD] with j hj
    intro z hz
    rw [show fderiv ℝ (U j) z=S.toContinuousLinearMap.comp (fderiv ℝ (u j) z) from
      centeredFrame_fderiv S p ((hu j).differentiable (by simp)) z]
    exact (S.toContinuousLinearMap.opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hj z hz) (norm_nonneg _))
  have hAD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (A j) z‖ ≤ ‖frameConjugation S‖*K := by
    filter_upwards [hBD] with j hj
    intro z hz
    rw [show fderiv ℝ (A j) z=(frameConjugation S).comp (fderiv ℝ (B j) z) from
      frozenCoefficient_fderiv S J ((hB j).differentiable (by simp)) z]
    exact ((frameConjugation S).opNorm_comp_le _).trans
      (mul_le_mul_of_nonneg_left (hj z hz) (norm_nonneg _))
  have hACR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (U j) z Complex.I-Complex.I • fderiv ℝ (U j) z 1=
        A j z (fderiv ℝ (U j) z 1) := by
    filter_upwards [hCR] with j hj
    intro z hz
    exact frozen_CR_equation S J hS p ((hu j).differentiable (by simp)) (B j) (hj z hz)
  have hU0 : TendstoUniformlyOn U (fun _ => (0:E)) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hc : ContinuousAt (fun x : E => S (x-p)) p :=
      S.continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    convert continuousAt_comp_uniform_constant hc hu0 using 1
    all_goals try simp only [U,sub_self,map_zero]
    all_goals rfl
  have hA0 : TendstoUniformlyOn A (fun _ => (0:(E →L[ℝ] E))) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hc : ContinuousAt (fun x : (E →L[ℝ] E) => frameConjugation S (x-J)) J :=
      (frameConjugation S).continuous.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    convert continuousAt_comp_uniform_constant hc hB0 using 1
    all_goals try simp only [A,frameConjugation_apply,sub_self,map_zero]
    all_goals rfl
  have hlim := smallCR_sequence_derivative_zero U hU A hA
    (mul_nonneg (norm_nonneg S.toContinuousLinearMap) hL)
    (mul_nonneg (norm_nonneg (frameConjugation S)) hK) hUD hAD hACR hU0 hA0
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => show ‖fderiv ℝ (u j) 0‖ ≤ ‖S.symm.toContinuousLinearMap‖*‖fderiv ℝ (U j) 0‖ from ?_)
    (by simpa using hlim.const_mul ‖S.symm.toContinuousLinearMap‖)
  have he : fderiv ℝ (u j) 0=S.symm.toContinuousLinearMap.comp (fderiv ℝ (U j) 0) := by
    rw [show fderiv ℝ (U j) 0=S.toContinuousLinearMap.comp (fderiv ℝ (u j) 0) from
      centeredFrame_fderiv S p ((hu j).differentiable (by simp)) 0]
    apply ContinuousLinearMap.ext
    intro z
    change (fderiv ℝ (u j) 0) z=S.symm (S ((fderiv ℝ (u j) 0) z))
    simp
  rw [he]
  exact S.symm.toContinuousLinearMap.opNorm_comp_le _

theorem field_CR_no_gradient_loss (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j)) (p : E)
    {L : ℝ} (hL : 0 ≤ L)
    (huD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (u j) z‖ ≤ L)
    (hCR : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (hu0 : TendstoUniformlyOn u (fun _ => p) atTop (Metric.closedBall (0:ℂ) 3)) :
    Tendsto (fun j => ‖fderiv ℝ (u j) 0‖) atTop (𝓝 0) := by
  let B : ℕ → ℂ → (E →L[ℝ] E) := fun j z => H (t j,u j z)
  have hs : s ∈ Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hts (Eventually.of_forall ht)
  have hB (j : ℕ) : ContDiff ℝ ∞ (B j) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact ContDiffAt.comp (g := H) (f := fun z => (t j,u j z)) z
      (hH (t j,u j z) (ht j)) (contDiffAt_const.prodMk (hu j).contDiffAt)
  have hBounded : Bornology.IsBounded
      ((fderiv ℝ H) '' (Icc (0:ℝ) 1 ×ˢ Metric.closedBall p 1)) :=
    ((isCompact_Icc.prod (isCompact_closedBall p 1)).image_of_continuousOn
      (fun y hy => ((hH y hy.1).continuousAt_fderiv (by simp)).continuousWithinAt)).isBounded
  obtain ⟨K,hK,hKb⟩ := hBounded.exists_pos_norm_le
  have hB0 : TendstoUniformlyOn B (fun _ => H (s,p)) atTop (Metric.closedBall (0:ℂ) 3) := by
    convert continuousAt_comp_uniform_constant (hH (s,p) hs).continuousAt
      (uniform_constant_prod hts hu0) using 1
  have hBD : ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
      ‖fderiv ℝ (B j) z‖ ≤ K*L := by
    filter_upwards [huD,Metric.tendstoUniformlyOn_iff.mp hu0 1 (by norm_num)] with j hj hju
    intro z hz
    have hmem : (t j,u j z) ∈ Icc (0:ℝ) 1 ×ˢ Metric.closedBall p 1 :=
      ⟨ht j,by simpa [Metric.mem_closedBall,dist_comm] using (hju z hz).le⟩
    have hd : HasFDerivAt (fun z => (t j,u j z))
        ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)) z :=
      (hasFDerivAt_const (t j) z).prodMk ((hu j).differentiable (by simp) z).hasFDerivAt
    have he : fderiv ℝ (B j) z=(fderiv ℝ H (t j,u j z)).comp
        ((0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)) :=
      (HasFDerivAt.comp (g := H) (f := fun z => (t j,u j z)) z
        ((hH (t j,u j z) (ht j)).differentiableAt (by simp)).hasFDerivAt hd).fderiv
    rw [he]
    apply ((fderiv ℝ H (t j,u j z)).opNorm_comp_le _).trans
    have hnorm : ‖(0 : ℂ →L[ℝ] ℝ).prod (fderiv ℝ (u j) z)‖=‖fderiv ℝ (u j) z‖ := by
      rw [ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
    rw [hnorm]
    exact mul_le_mul (hKb _ ⟨(t j,u j z),hmem,rfl⟩) (hj z hz) (norm_nonneg _) hK.le
  exact frozen_CR_no_gradient_loss u hu B hB p (H (s,p))
    (hHF (s,p) hs) hL (mul_nonneg hK.le hL) huD hBD hCR hu0 hB0

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem rescaleMap_CR_I [FiniteDimensional ℂ E] [CompleteSpace E]
    {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hu : Differentiable ℝ u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=J (u z) (fderiv ℝ u z 1))
    (x : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaleMap u x r) z Complex.I=
      J (rescaleMap u x r z) (fderiv ℝ (rescaleMap u x r) z 1) := by
  rw [rescaleMap_fderiv hu]
  simpa only [smul_apply,map_smul,rescaleMap] using
    congrArg (fun v : E => r • v) (hCR (x+r • z))

theorem field_C0_gradient_bound (H : ℝ × E → E →L[ℝ] E)
    (hH : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → ContDiffAt ℝ ∞ H y)
    (hHF : ∀ y : ℝ × E, y.1 ∈ Icc (0:ℝ) 1 → HasFrame (H y))
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ Icc (0:ℝ) 1) {s : ℝ}
    (hts : Tendsto t atTop (𝓝 s))
    (u : ℕ → ℂ → E) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hCR : ∀ j z, fderiv ℝ (u j) z Complex.I=H (t j,u j z) (fderiv ℝ (u j) z 1))
    (v : ℂ → E) (hv : TendstoLocallyUniformly u v atTop)
    (c : ℂ) {R : ℝ} (_hR : 0 ≤ R) :
    ∃ L ≥ 0, ∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall c R, ‖fderiv ℝ (u j) z‖ ≤ L := by
  by_contra hn
  have hbad (j : ℕ) : ∃ i ≥ j, ∃ z ∈ Metric.closedBall c R,
      (j:ℝ)+1 < ‖fderiv ℝ (u i) z‖ := by
    have hnot : ¬ ∀ᶠ i in atTop, ∀ z ∈ Metric.closedBall c R,
        ‖fderiv ℝ (u i) z‖ ≤ (j:ℝ)+1 := by
      intro hh
      exact hn ⟨(j:ℝ)+1,by positivity,hh⟩
    rw [Filter.eventually_atTop] at hnot
    push Not at hnot
    obtain ⟨i,hi,z,hz,hbig⟩ := hnot j
    exact ⟨i,hi,z,hz,hbig⟩
  choose a ha z hz hbig using hbad
  have hat : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
  have hpos (j : ℕ) : 0 < ‖fderiv ℝ (u (a j)) (z j)‖ := lt_trans (by positivity) (hbig j)
  choose x hx hweight hlarger hlocal using
    (fun j => weighted_gradient_maximum (u (a j)) (hu (a j)) (z j) (by norm_num : (0:ℝ)<1) (hpos j))
  have hxmem (j : ℕ) : x j ∈ Metric.closedBall c (R+1) := by
    have h1 : dist (x j) (z j) < 1 := hx j
    have h2 : dist (z j) c ≤ R := hz j
    rw [Metric.mem_closedBall]
    linarith [dist_triangle (x j) (z j) c]
  obtain ⟨d,hd,φ,hφ,hφx⟩ := (isCompact_closedBall c (R+1)).tendsto_subseq hxmem
  let b : ℕ → ℕ := fun j => a (φ j)
  have hbt : Tendsto b atTop atTop := hat.comp hφ.tendsto_atTop
  let g : ℕ → ℝ := fun j => ‖fderiv ℝ (u (b j)) (x (φ j))‖
  have hgp (j : ℕ) : 0 < g j := (hpos (φ j)).trans_le (hlarger (φ j))
  have hgb (j : ℕ) : (φ j:ℝ)+1 < g j := (hbig (φ j)).trans_le (hlarger (φ j))
  have hgt : Tendsto g atTop atTop := by
    apply tendsto_atTop_mono (fun j => (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans (hgb j).le)
    exact tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  let r : ℕ → ℝ := fun j => (g j)⁻¹
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hgt
  let U : ℕ → ℂ → E := fun j => rescaleMap (u (b j)) (x (φ j)) (r j)
  have hUs (j : ℕ) : ContDiff ℝ ∞ (U j) := rescaleMap_smooth (hu (b j)) _ _
  have hlim : TendstoUniformlyOn U (fun _ => v d) atTop (Metric.closedBall (0:ℂ) 3) := by
    have hv' := locally_uniform_reindex hv hbt
    have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
    convert rescaled_maps_uniform_constant hv' hvc.continuousAt hφx hrt
      (Metric.isBounded_closedBall (x := (0:ℂ)) (r := 3)) using 1
    rfl
  have hUb : ∀ᶠ j in atTop, ‖fderiv ℝ (U j) 0‖=1 ∧
      ∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ (U j) z‖ ≤ 2 := by
    filter_upwards [eventually_ge_atTop (6:ℕ)] with j hj
    apply weighted_rescale_bounds ((hu (b j)).differentiable (by simp)) (hgp j)
    · have hφj : j ≤ φ j := hφ.id_le j
      have h6 : (6:ℝ) ≤ φ j := by exact_mod_cast le_trans hj hφj
      have hw := hweight (φ j)
      dsimp [g,b] at hgb
      nlinarith [hbig (φ j)]
    · exact hlocal (φ j)
  have hUCR : ∀ j z, fderiv ℝ (U j) z Complex.I=
      H (t (b j),U j z) (fderiv ℝ (U j) z 1) := by
    intro j z
    exact rescaleMap_CR_I (J := fun x => H (t (b j),x)) ((hu (b j)).differentiable (by simp)) (hCR (b j)) _ _ _
  have hzero := field_CR_no_gradient_loss H hH hHF (fun j => t (b j))
    (fun j => ht (b j)) (hts.comp hbt) U hUs (v d) (by norm_num : (0:ℝ) ≤ 2)
    (hUb.mono (fun j hj => hj.2)) (Eventually.of_forall (fun j z _ => hUCR j z)) hlim
  have hone : Tendsto (fun j => ‖fderiv ℝ (U j) 0‖) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' (hUb.mono (fun j hj => hj.1.symm))
  have he : (0:ℝ)=1 := tendsto_nhds_unique hzero hone
  norm_num at he

end HigherDimensionalBallPacking.Rigidity.FramedCR
open scoped ContDiff Topology
open Set Filter Function

namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem holder_gradient_limit_C1 (f : ℕ → ℂ → E) (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (v : ℂ → E) (hv : TendstoLocallyUniformly f v atTop)
    {M C α : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hα : 0 < α)
    (hval : ∀ j z, z ∈ Metric.closedBall (0:ℂ) 1 → ‖f j z‖ ≤ M)
    (hD : ∀ j x y, ‖fderiv ℝ (f j) x-fderiv ℝ (f j) y‖ ≤ C*‖x-y‖^α) :
    ContDiff ℝ 1 v ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (f (φ j))) (fderiv ℝ v) atTop := by
  classical
  let D : ℕ → ℂ → (ℂ →L[ℝ] E) := fun j => fderiv ℝ (f j)
  have hD0 (j : ℕ) : ‖D j 0‖ ≤ 2*M+C := by
    have hh := derivative_bound_of_holder_and_values (f j) ((hf j).differentiable (by simp))
      hM hC (by norm_num : (0:ℝ)<1) hα.le (hval j)
      (fun z _ => by simpa using hD j z 0)
    simpa only [div_one,Real.one_rpow,mul_one] using hh
  have hpoint (j : ℕ) (z : ℂ) : ‖D j z‖ ≤ 2*M+C+C*‖z‖^α := by
    have hh := norm_sub_le (D j z-D j 0) (-D j 0)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hh
    have h := hD j z 0
    simp only [sub_zero] at h
    exact hh.trans (by linarith [hD0 j])
  have heq : UniformEquicontinuous D := by
    apply Metric.uniformEquicontinuous_iff.mpr
    intro ε hε
    have hg : Tendsto (fun r : ℝ => C*r^α) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hα.ne'] using
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.const_mul C
    have hh := hg.eventually (gt_mem_nhds hε)
    obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp hh
    refine ⟨δ,hδ,?_⟩
    intro z w hzw j
    rw [dist_eq_norm]
    apply (hD j z w).trans_lt
    apply hδb
    simpa [Metric.mem_ball,dist_eq_norm] using hzw
  let F : ℕ → C(ℂ,(ℂ →L[ℝ] E)) := fun j => ⟨D j,(hf j).continuous_fderiv (by simp)⟩
  have heqr : Equicontinuous (fun f : Set.range F => (f.val : ℂ → (ℂ →L[ℝ] E))) := by
    let ψ : Set.range F → ℕ := fun f => f.property.choose
    have hp (f : Set.range F) : F (ψ f) = f.val := f.property.choose_spec
    have he : (fun f : Set.range F => (f.val : ℂ → (ℂ →L[ℝ] E))) = D ∘ ψ := by
      funext f z
      exact congrArg (fun g : C(ℂ,(ℂ →L[ℝ] E)) => g z) (hp f).symm
    rw [he]
    exact heq.equicontinuous.comp ψ
  let : T2Space (UniformOnFun ℂ (ℂ →L[ℝ] E) {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have hcomp : IsCompact (closure (Set.range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(ℂ,(ℂ →L[ℝ] E)) => (f : ℂ → (ℂ →L[ℝ] E)))
      (𝔖 := {K | IsCompact K}) (fun K hK => hK)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      exact heqr.equicontinuousOn K
    · intro K hK z hz
      refine ⟨Metric.closedBall 0 (2*M+C+C*‖z‖^α),isCompact_closedBall _ _,?_⟩
      rintro f ⟨j,rfl⟩
      rw [Metric.mem_closedBall,dist_zero_right]
      convert hpoint j z using 1
  obtain ⟨w,hw,φ,hφ,hφw⟩ := hcomp.tendsto_subseq (x := F)
    (fun j => subset_closure (mem_range_self j))
  have hloc : TendstoLocallyUniformly (fun j => D (φ j)) w atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hφw
  have hvl := locally_uniform_reindex hv hφ.tendsto_atTop
  have hvD (x : ℂ) : HasFDerivAt v (w x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      hloc.tendstoLocallyUniformlyOn (fun j z _ => ((hf (φ j)).differentiable (by simp) z).hasFDerivAt)
      (fun z _ => hvl.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)) (mem_univ x)
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨w,w.continuous,hvD⟩,φ,hφ,?_⟩
  convert hloc using 1
  funext z
  exact (hvD z).fderiv

end

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance packageC1Norm (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance packageC1Space (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance packageCompactNorm (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance packageCompactSpace (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

private theorem exists_principal_threshold (B K : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      B*max δ ((2*δ)^((2:ℝ)/3)*K^((1:ℝ)/3)) ≤ 1/2 := by
  let g : ℝ → ℝ := fun r => B*max r ((2*r)^((2:ℝ)/3)*K^((1:ℝ)/3))
  have hg : Continuous g := by
    exact continuous_const.mul (continuous_id.max
      (((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 2/3)).comp
        (continuous_const.mul continuous_id)).mul continuous_const))
  have hg0 : g 0=0 := by simp [g,Real.zero_rpow (show (2:ℝ)/3 ≠ 0 by norm_num)]
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, g r < 1/2 := by
    have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (gt_mem_nhds (show g 0 < (1:ℝ)/2 by rw [hg0]; norm_num))
  have hr1 : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
    (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hr0 : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,h0,h1,hg⟩ := (hr0.and (hr1.and hev)).exists
  exact ⟨r,h0,h1.le,hg.le⟩

theorem smallCR_local_modulus (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) :
    ∃ (χ : ℂ → ℝ) (δ C : ℝ), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[𝓝 0] (fun _ => (1:ℝ)) ∧ (∀ z, |χ z| ≤ 1) ∧
      tsupport χ ⊆ Metric.closedBall (0:ℂ) 3 ∧ 0 < δ ∧ 0 ≤ C ∧
      ∀ (u : ℂ → E) (A : ℂ → E →L[ℝ] E),
        ContDiff ℝ ∞ u → ContDiff ℝ ∞ A →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖u z‖ ≤ 1) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ u z‖ ≤ L) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖A z‖ ≤ δ) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3, ‖fderiv ℝ A z‖ ≤ K) →
        (∀ z ∈ Metric.closedBall (0:ℂ) 3,
          fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=A z (fderiv ℝ u z 1)) →
        ∀ x y, ‖fderiv ℝ (fun z => χ z • u z) x-fderiv ℝ (fun z => χ z • u z) y‖ ≤
          C*‖x-y‖^((1:ℝ)/3) := by
  obtain ⟨χ,θ,D,hD,hχ,hχc,hθ,hθc,hχ2,hθ3,hχ1,hθ1,hχθ,hd⟩ := exists_nested_complex_cutoffs
  have hχ3 : tsupport χ ⊆ Metric.closedBall (0:ℂ) 3 :=
    hχ2.trans (Metric.closedBall_subset_closedBall (by norm_num))
  let B := 2*‖compactCRInverse (E := E) 3‖*‖c1HolderDx (E := E)‖
  obtain ⟨δ,hδ,hδ1,hsmall⟩ := exists_principal_threshold B (K+D)
  refine ⟨χ,δ,localSchauderBound E 3 D L (K+D),hχ,hχc,hχ1,
    fun z => (hχθ z).1,hχ3,hδ,?_,?_⟩
  · dsimp [localSchauderBound]
    positivity
  intro u A hu hA huv huD hAv hAD hCR
  let AA : ℂ → E →L[ℝ] E := fun z => θ z • A z
  have hAA : ContDiff ℝ ∞ AA := hθ.smul hA
  have hAAc : HasCompactSupport AA := hθc.smul_right
  have hAAs : tsupport AA ⊆ Metric.closedBall (0:ℂ) 3 :=
    (tsupport_smul_subset_left θ A).trans hθ3
  have hb := cutoff_smul_bounds hθ hA hθ3 (C := 1) (D := D) (M := δ) (L := K)
    (by norm_num) hD hδ.le hK (fun z => (hχθ z).2) (fun z => (hd z).2.2) hAv hAD
  have hAAv : ∀ z, ‖AA z‖ ≤ δ := by simpa only [one_mul] using hb.1
  have hAAD : ∀ z, ‖fderiv ℝ AA z‖ ≤ K+D := by
    intro z
    exact (hb.2 z).trans (by nlinarith)
  apply cutoff_smallCR_schauder 3 χ hχ hχc hχ3 AA hAA hAAc hAAs u hu
    hD hL (add_nonneg hK hD) hδ.le hδ1 (fun z => (hd z).1)
    (fun z => (hd z).2.1) (fun z hz => huv z (hχ3 hz)) (fun z hz => huD z (hχ3 hz))
    hAAv hAAD
  · intro z hz
    rw [show AA z=A z by simp only [AA,hθ1 z hz,one_smul]]
    exact hCR z (hχ3 hz)
  · dsimp [B] at hsmall
    nlinarith only [hsmall]

end

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

theorem smallCR_C1_closure_threshold (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (u : ℕ → ℂ → E) (A : ℕ → ℂ → E →L[ℝ] E)
      (v : ℂ → E), (∀ j, ContDiff ℝ ∞ (u j)) → (∀ j, ContDiff ℝ ∞ (A j)) →
      TendstoLocallyUniformly u v atTop →
      (∀ᶠ j in atTop, ∀ z ∈ Metric.closedBall (0:ℂ) 3,
        ‖u j z‖ ≤ 1 ∧ ‖fderiv ℝ (u j) z‖ ≤ L ∧ ‖A j z‖ ≤ δ ∧
        ‖fderiv ℝ (A j) z‖ ≤ K ∧
        fderiv ℝ (u j) z Complex.I-Complex.I • fderiv ℝ (u j) z 1=
          A j z (fderiv ℝ (u j) z 1)) →
      ContDiffAt ℝ 1 v 0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun j => fderiv ℝ (u (φ j)) 0) atTop (𝓝 (fderiv ℝ v 0)) := by
  obtain ⟨χ,δ,C,hχ,hχc,hχ1,hχb,hχ3,hδ,hC,hmod⟩ := smallCR_local_modulus (E := E) L K hL hK
  refine ⟨δ,hδ,?_⟩
  intro u A v hu hA hv hb
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  let f : ℕ → ℂ → E := fun j z => χ z • u (j+N) z
  let w : ℂ → E := fun z => χ z • v z
  have hvc : Continuous v := hv.continuous (Eventually.of_forall (fun j => (hu j).continuous)).frequently
  have hχlim : TendstoLocallyUniformly (fun _ : ℕ => χ) χ atTop := by
    exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
      (tendsto_const_nhds (x := (⟨χ,hχ.continuous⟩ : C(ℂ,ℝ))))
  have hflim : TendstoLocallyUniformly f w atTop := by
    exact hχlim.smul₀ (locally_uniform_reindex hv (tendsto_add_atTop_nat N)) hχ.continuous hvc
  have hfb (j : ℕ) (z : ℂ) (hz : z ∈ Metric.closedBall (0:ℂ) 1) : ‖f j z‖ ≤ 1 := by
    have hu1 := (hN (j+N) (Nat.le_add_left N j) z
      ((Metric.closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 3)) hz)).1
    calc ‖f j z‖ = |χ z| *‖u (j+N) z‖ := by simp only [f,norm_smul,Real.norm_eq_abs]
         _ ≤ 1*1 := mul_le_mul (hχb z) hu1 (norm_nonneg _) (by norm_num)
         _ = 1 := one_mul 1
  have hfmod (j : ℕ) := hmod (u (j+N)) (A (j+N)) (hu _) (hA _)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.2.1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.2.2.1)
    (fun z hz => (hN _ (Nat.le_add_left N j) z hz).2.2.2.2)
  obtain ⟨hw,φ,hφ,hφD⟩ := holder_gradient_limit_C1 f (fun j => hχ.smul (hu (j+N))) w hflim
    (by norm_num : (0:ℝ) ≤ 1) hC (by norm_num : (0:ℝ) < 1/3) hfb hfmod
  have he (g : ℂ → E) : (fun z => χ z • g z) =ᶠ[𝓝 0] g := by
    filter_upwards [hχ1] with z hz
    simp only [hz,one_smul]
  refine ⟨hw.contDiffAt.congr_of_eventuallyEq (he v).symm,fun j => φ j+N,
    fun i j hij => Nat.add_lt_add_right (hφ hij) N,?_⟩
  have hd := hφD.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (0:ℂ))
  convert hd using 1
  · funext j
    exact (he (u (φ j+N))).fderiv_eq.symm
  · exact congrArg nhds (he v).fderiv_eq.symm

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem locally_uniform_small_ball {u : ℕ → ℂ → E} {v : ℂ → E}
    (hv : TendstoLocallyUniformly u v atTop) {c : ℂ} (hvc : ContinuousAt v c)
    {t : ℕ → ℝ} {s : ℝ} (ht : Tendsto t atTop (𝓝 s))
    {G : ℝ × E → F} (hG : ContinuousAt G (s,v c)) (hG0 : G (s,v c)=0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ᶠ j in atTop,
      ∀ z ∈ Metric.closedBall c r, ‖G (t j,u j z)‖ ≤ ε := by
  obtain ⟨δ,hδ,hδG⟩ := Metric.continuousAt_iff.mp hG ε hε
  obtain ⟨a,ha,hav⟩ := Metric.continuousAt_iff.mp hvc (δ/2) (by linarith)
  obtain ⟨U,hU,hUf⟩ := hv _ (Metric.dist_mem_uniformity (by linarith : (0:ℝ)<δ/2)) c
  obtain ⟨b,hb,hbU⟩ := Metric.mem_nhds_iff.mp hU
  let r := min 1 (min a b/2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos (lt_min ha hb))
  refine ⟨r,hr,min_le_left _ _,?_⟩
  filter_upwards [hUf,Metric.tendsto_nhds.mp ht δ hδ] with j hj hjt
  intro z hz
  have hza : dist z c < a := by
    have h := (show dist z c ≤ r from hz).trans (min_le_right 1 (min a b/2))
    linarith [min_le_left a b,lt_min ha hb]
  have hzb : dist z c < b := by
    have h := (show dist z c ≤ r from hz).trans (min_le_right 1 (min a b/2))
    linarith [min_le_right a b,lt_min ha hb]
  have h1 : dist (v z) (u j z)<δ/2 := hj z (hbU hzb)
  have h2 : dist (v z) (v c)<δ/2 := hav hza
  have hu : dist (u j z) (v c)<δ := by
    have hh := dist_triangle (u j z) (v z) (v c)
    rw [dist_comm (u j z) (v z)] at hh
    linarith
  have hh := hδG (show dist (t j,u j z) (s,v c)<δ by rw [Prod.dist_eq]; exact max_lt hjt hu)
  simpa only [hG0,dist_zero_right] using hh.le

end HigherDimensionalBallPacking.Rigidity

end

end OAI
