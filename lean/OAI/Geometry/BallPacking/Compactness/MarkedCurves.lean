import Mathlib
import OAI.Geometry.BallPacking.Compactness.FrozenCR
import OAI.Geometry.BallPacking.Campanato.TranslatedSquare

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

def anchoredEnergyFamily (p : Phase n) (B θ : ℝ) : Set C(ℂ,Phase n) :=
  {u | u 0=p ∧ ContDiff ℝ ∞ u ∧
    ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k}

lemma anchoredEnergyFamily_equicontinuous (p : Phase n) {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) :
    Equicontinuous (fun u : anchoredEnergyFamily p B θ => (u.val : ℂ → Phase n)) := by
  intro z
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB hθ hθ1 hε
  refine ⟨δ,hδ,?_⟩
  intro w hw u
  exact hmod u.val u.property.2.1 u.property.2.2 z w (by rwa [dist_comm])

lemma anchoredEnergyFamily_pointwise (p : Phase n) {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) (z : ℂ) :
    ∃ Q : Set (Phase n),IsCompact Q ∧ ∀ u∈anchoredEnergyFamily p B θ,u z∈Q := by
  obtain ⟨M,hM⟩ := energy_family_point_bound
    (F := fun u : anchoredEnergyFamily p B θ => (u.val : ℂ → Phase n))
    (fun u => u.property.1) (fun u => u.property.2.1) hB hθ hθ1
    (fun u => u.property.2.2) z
  refine ⟨Metric.closedBall 0 M,isCompact_closedBall 0 M,?_⟩
  intro u hu
  simpa only [Metric.mem_closedBall,dist_zero_right] using hM ⟨u,hu⟩

lemma anchoredEnergyFamily_compactClosure (p : Phase n) {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) :
    IsCompact (closure (anchoredEnergyFamily p B θ)) := by
  let : T2Space (UniformOnFun ℂ (Phase n) {K : Set ℂ | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun u : C(ℂ,Phase n) => (u : ℂ → Phase n))
    (𝔖 := {K : Set ℂ | IsCompact K}) (fun K hK => hK)
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding)
  · intro K hK
    exact (anchoredEnergyFamily_equicontinuous p hB hθ hθ1).equicontinuousOn K
  · intro K hK z hz
    exact anchoredEnergyFamily_pointwise p hB hθ hθ1 z

lemma energy_family_czero_subsequence {p : Phase n} {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) (u : ℕ → ℂ → Phase n)
    (hu : ∀ j,ContDiff ℝ ∞ (u j)) (hp : ∀ j,u j 0=p)
    (he : ∀ j,∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve (u j) c) ((1/16)^k)≤B*θ^k) :
    ∃ v : C(ℂ,Phase n),v 0=p ∧ ∃ φ : ℕ → ℕ,StrictMono φ ∧
      ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn (fun j => u (φ j)) v atTop K := by
  let f : ℕ → C(ℂ,Phase n) := fun j => ⟨u j,(hu j).continuous⟩
  have hf (j : ℕ) : f j∈closure (anchoredEnergyFamily p B θ) :=
    subset_closure ⟨hp j,hu j,he j⟩
  obtain ⟨v,hv,φ,hφ,hlim⟩ := (anchoredEnergyFamily_compactClosure p hB hθ hθ1).tendsto_subseq hf
  have heval : Tendsto (fun j => u (φ j) 0) atTop (𝓝 (v 0)) :=
    ((show Continuous (fun g : C(ℂ,Phase n) => g 0) from continuous_eval_const 0).tendsto v).comp hlim
  have hv0 : v 0=p := tendsto_nhds_unique heval (by simpa only [hp] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)))
  refine ⟨v,hv0,φ,hφ,?_⟩
  intro K hK
  exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim) K hK

lemma exact_marked_line_uniform_energy {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n) (p q : Phase n) :
    ∃ B θ : ℝ,0<B ∧ 0<θ ∧ θ<1 ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ c : ℂ,∀ k : ℕ,
      radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k := by
  obtain ⟨D,hD,hup⟩ := exact_line_slope_upper_bound hJs hJ hJc hST hT hout p q
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_local_energy_of_slope hJs hJ hJc hST hT hout
  refine ⟨C+M*D,θ,by positivity,hθ,hθ1,?_⟩
  intro t ht u hu c k
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  have hh := he t ht p q u hu a hlim c k
  have hsum : C+M*stdDot n a a≤C+M*D := add_le_add (le_refl C) (mul_le_mul_of_nonneg_left
    (hup t ht u hu a ha hlim) hM)
  exact hh.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

theorem exact_marked_line_czero_compactness {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ j,t j∈Icc (0:ℝ) 1)
    {u : ℕ → ℂ → Phase n} (hu : ∀ j,AffineLineCurve (lineHomotopy J (t j)) p q (u j)) :
    ∃ v : C(ℂ,Phase n),v 0=p ∧ v 1=q ∧ ∃ φ : ℕ → ℕ,StrictMono φ ∧
      ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn (fun j => u (φ j)) v atTop K := by
  obtain ⟨B,θ,hB,hθ,hθ1,he⟩ := exact_marked_line_uniform_energy hJs hJ hJc hST hT hout p q
  obtain ⟨v,hv,φ,hφ,hsub⟩ := energy_family_czero_subsequence hB.le hθ.le hθ1 u
    (fun j => (hu j).1) (fun j => (hu j).2.2.1) (fun j => he (t j) (ht j) (u j) (hu j))
  have hlim : Tendsto (fun j => u (φ j) 1) atTop (𝓝 (v 1)) :=
    (hsub {1} isCompact_singleton).tendsto_at (mem_singleton 1)
  have hq : v 1=q := tendsto_nhds_unique hlim (by
    simpa only [fun j => (hu (φ j)).2.2.2.1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q)))
  exact ⟨v,hv,hq,φ,hφ,hsub⟩

theorem exact_marked_line_gradient_bound {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n) (p q : Phase n) :
    ∃ M : ℝ,0<M ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ z : ℂ,‖fderiv ℝ u z‖≤M := by
  let I := {v : ℝ × (ℂ → Phase n) // v.1∈Icc (0:ℝ) 1 ∧ AffineLineCurve (lineHomotopy J v.1) p q v.2}
  let A : I → Phase n → End n := fun i => lineHomotopy J i.val.1
  let U : I → ℂ → Phase n := fun i => i.val.2
  obtain ⟨L,G,hL,hG,hJL,hP,hPi⟩ := exact_homotopy_target_bounds hJs hJ hJc
  obtain ⟨B,θ,hB,hθ,hθ1,he⟩ := exact_marked_line_uniform_energy hJs hJ hJc hST hT hout p q
  have hm : ∀ ε : ℝ,0<ε →∃ δ : ℝ,0<δ ∧ ∀ i x y,dist x y<δ →dist (U i x) (U i y)<ε := by
    intro ε hε
    obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB.le hθ.le hθ1 hε
    refine ⟨δ,hδ,?_⟩
    intro i x y hxy
    exact hmod (U i) i.property.2.1 (he i.val.1 i.property.1 (U i) i.property.2) x y hxy
  obtain ⟨M,hM,hbound⟩ := equicontinuous_CR_derivative_bound A U
    (fun i => i.property.2.1) (fun i => (lineHomotopy_slice_contDiff hJs hJ i.property.1).continuous)
    (fun i x => lineHomotopy_compatible hJ i.property.1 x) (fun i => i.property.2.2.1)
    hL hG (fun i => hJL i.val.1 i.property.1) (fun i => hP i.val.1 i.property.1)
    (fun i => hPi i.val.1 i.property.1) hm
  refine ⟨M,hM,?_⟩
  intro t ht u hu z
  exact hbound ⟨(t,u),ht,hu⟩ z

local instance eljcInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance eljcInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance eljcInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance eljcInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

def markedLocalCurve (u : ℂ → Phase n) (c : ℂ) (r : ℝ) (z : ℂ) : Phase n :=
  rescaledCurve u c r z-u c

lemma markedLocalCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (markedLocalCurve u c r) := (rescaledCurve_smooth hu c r).sub contDiff_const

lemma markedLocalCurve_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) {M : ℝ}
    (hd : ∀ z,‖fderiv ℝ u z‖≤M) (c : ℂ) {r : ℝ} (hr : 0≤r) (z : ℂ) :
    ‖markedLocalCurve u c r z‖≤M*r*‖z‖ := by
  have hh := norm_sub_le_of_deriv_bound (hu.differentiable (by simp)) hd (c+r • z) c
  rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hh
  exact hh.trans_eq (by ring)

lemma bilinear_cauchy {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace X] [CompleteSpace Y] (B : X →L[ℝ] Y →L[ℝ] Z)
    {x : ℕ → X} {y : ℕ → Y} (hx : CauchySeq x) (hy : CauchySeq y) :
    CauchySeq (fun i => B (x i) (y i)) := by
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete hx
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hy
  have hc : Continuous (fun p : X × Y => B p.1 p.2) :=
    (B.continuous.comp continuous_fst).clm_apply continuous_snd
  exact ((hc.tendsto (a,b)).comp (ha.prodMk_nhds hb)).cauchySeq

lemma cauchy_mapJet {P : ℕ → End n} {v : ℕ → COne ℂ (Phase n)}
    (hP : CauchySeq P) (hv : CauchySeq v) :
    CauchySeq (fun i => mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n) (P i) (v i)) :=
  bilinear_cauchy (mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n)) hP hv

lemma undo_frozen_cutoff {A : Phase n → End n} {x : Phase n} (hx : Compatible (A x))
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (b : ContDiffBump (0:ℂ)) :
    mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n) (compatibleFrame (A x)).inverse
      (cutoffCurveJet b (frozenCurve_smooth (J := A) x hu))=
      cutoffCurveJet b (hu.sub (contDiff_const (c := x))) := by
  apply cValue_ext
  intro z
  rw [mapJetBilinear_value,cutoffCurveJet_value,cutoffCurveJet_value,map_smul]
  change b z • ((compatibleFrame (A x)).inverse (compatibleFrame (A x) (u z-x)))=b z • (u z-x)
  rw [compatibleFrame_inverse_left hx]

theorem exact_marked_local_jet_cauchy {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n)
    {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1)
    {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {u : ℕ → ℂ → Phase n} (hu : ∀ i,AffineLineCurve (lineHomotopy J (t i)) p q (u i))
    {v : ℂ → Phase n} (huc : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) :
    ∃ r : ℝ,0<r ∧ r≤1 ∧ ∀ c : ℂ,
      CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i).1 c r)) := by
  obtain ⟨M,hM,hgrad⟩ := exact_marked_line_gradient_bound hJs hJ hJc hST hT hout p q
  obtain ⟨L,G,hL,hG,hJL,hP,hPi⟩ := exact_homotopy_target_bounds hJs hJ hJc
  have hG0 : 0≤G := by linarith
  have hGM : 0≤G*M := mul_nonneg hG0 hM.le
  obtain ⟨δ,hδ,hdisk⟩ := disk_nonlinear_jet_cauchy (E := Phase n) (by positivity : 0≤G^3*L) hGM
  let r := min 1 (δ/(2*(G*M+1)))
  have hr : 0<r := lt_min zero_lt_one (div_pos hδ (by positivity))
  have hr1 : r≤1 := min_le_left _ _
  have hrδ : G*(M*r*2)≤δ := by
    have hh := (le_div_iff₀ (by positivity : 0<2*(G*M+1))).mp (min_le_right (1:ℝ) (δ/(2*(G*M+1))))
    nlinarith
  refine ⟨r,hr,hr1,?_⟩
  intro c
  let A : ℕ → Phase n → End n := fun i => lineHomotopy J (t i)
  let P : ℕ → End n := fun i => compatibleFrame (A i (u i c))
  let R : ℕ → ℂ → Phase n := fun i => rescaledCurve (u i) c r
  let W : ℕ → ℂ → Phase n := fun i => frozenCurve (A i) (u i c) (R i)
  let F : ℕ → Phase n → End n := fun i => frozenTargetCoefficient (A i) (u i c)
  have hR : ∀ i,ContDiff ℝ ∞ (R i) := fun i => rescaledCurve_smooth (hu i).1 c r
  have hW : ∀ i,ContDiff ℝ ∞ (W i) := fun i => frozenCurve_smooth (u i c) (hR i)
  have hc : Tendsto (fun i => u i c) atTop (𝓝 (v c)) :=
    (huc {c} isCompact_singleton).tendsto_at (mem_singleton c)
  have hPc := exact_frame_tendsto hJs hJ ht hs hc
  have hFL : ∀ i x y,‖F i x-F i y‖≤(G^3*L)*‖x-y‖ := fun i =>
    frozenTargetCoefficient_lipschitz hL hG0 (hJL (t i) (ht i)) (hP (t i) (ht i) _) (hPi (t i) (ht i) _)
  have hW0 : ∀ i,W i 0=0 := by
    intro i
    simp only [W,frozenCurve,R,rescaledCurve,smul_zero,add_zero,sub_self,map_zero]
  have hzbound : ∀ i z,‖z‖≤2 →‖markedLocalCurve (u i) c r z‖≤M*r*2 := by
    intro i z hz
    exact (markedLocalCurve_bound (hu i).1 (hgrad (t i) (ht i) (u i) (hu i)) c hr.le z).trans
      (mul_le_mul_of_nonneg_left hz (mul_nonneg hM.le hr.le))
  have hWb : ∀ i z,‖z‖≤2 →‖W i z‖≤δ := by
    intro i z hz
    have hh := (P i).le_opNorm (markedLocalCurve (u i) c r z)
    exact hh.trans ((mul_le_mul (hP (t i) (ht i) _) (hzbound i z hz) (norm_nonneg _) hG0).trans hrδ)
  have hWD : ∀ i z,‖z‖≤2 →‖fderiv ℝ (W i) z‖≤G*M := by
    intro i z _
    rw [frozenCurve_fderiv (u i c) ((hR i).differentiable (by simp) z),rescaledCurve_fderiv (hu i).1]
    have hd : ‖r • fderiv ℝ (u i) (c+r • z)‖≤M := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le]
      exact (mul_le_mul_of_nonneg_left (hgrad (t i) (ht i) (u i) (hu i) _) hr.le).trans
        (by nlinarith)
    exact ((P i).opNorm_comp_le _).trans (mul_le_mul (hP (t i) (ht i) _) hd (norm_nonneg _) hG0)
  have hZb : ∀ i,∀ z∈Metric.closedBall (0:ℂ) 2,‖markedLocalCurve (u i) c r z‖≤M*2 := by
    intro i z hz
    have hz' : ‖z‖≤2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    exact (hzbound i z hz').trans (by nlinarith)
  have hZc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z∈Metric.closedBall (0:ℂ) 2,
      ‖markedLocalCurve (u i) c r z-markedLocalCurve (u j) c r z‖≤ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := centered_rescaled_cauchy huc c r ε hε
    exact ⟨N,fun i hi j hj z hz => hN i hi j hj z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)⟩
  have hWc' := uniform_clm_cauchy_on hG0 (mul_nonneg hM.le (by norm_num : (0:ℝ)≤2))
    (fun i => hP (t i) (ht i) (u i c)) hZb hPc.1.cauchySeq hZc
  have hWc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →‖W i z-W j z‖≤ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hWc' ε hε
    exact ⟨N,fun i hi j hj z hz => hN i hi j hj z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)⟩
  have hFc' := uniform_values_cauchy_on
    (frozenHomotopy_tendstoUniformlyOn hJs hJ ht hs hc (isCompact_closedBall (0:Phase n) δ))
  have hFc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖x‖≤δ →‖F i x-F j x‖≤ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hFc' ε hε
    exact ⟨N,fun i hi j hj x hx => hN i hi j hj x (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)⟩
  have hcr : ∀ i z,‖z‖<2 →fderiv ℝ (W i) z Complex.I-Complex.I • fderiv ℝ (W i) z 1=
      F i (W i z) (fderiv ℝ (W i) z 1) := by
    intro i z _
    exact frozenCurve_CR (lineHomotopy_compatible hJ (ht i) _) ((hR i).differentiable (by simp) z)
      (rescaledCurve_CR (hu i).1 (hu i).2.1 c r z)
  have hwcauchy := hdisk W hW F
    (fun i => frozenTargetCoefficient_continuous (lineHomotopy_slice_contDiff hJs hJ (ht i)).continuous _)
    (fun i => frozenTargetCoefficient_zero _ _) hFL hW0 hWb hWD hWc hFc hcr
  have hmapped := cauchy_mapJet hPc.2.cauchySeq hwcauchy
  have he (i : ℕ) : mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n) (P i).inverse (cutoffCurveJet smallDiskBump (hW i))=
      cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i).1 c r) :=
    undo_frozen_cutoff (lineHomotopy_compatible hJ (ht i) _) (hR i) smallDiskBump
  change CauchySeq (fun i => mapJetBilinear (D := ℂ) (E := Phase n) (F := Phase n)
    (P i).inverse (cutoffCurveJet smallDiskBump (hW i))) at hmapped
  simpa only [he] using hmapped

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped Topology BoundedContinuousFunction
open Set Filter
variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance chpInst1 : NormedAddCommGroup (HMap X E) := inferInstance
local instance chpInst2 : NormedSpace ℝ (HMap X E) := inferInstance

lemma compact_local_holder_cauchy {K : Set X} (hK : IsCompact K) {ρ : ℝ} (hρ : 0<ρ)
    {g : ℕ → HMap X E} (hg : ∀ i x,x∉K →valueCLM _ (g i) x=0)
    (hl : ∀ c : X,∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,
      (∀ x,dist x c<ρ →‖valueCLM _ (g i-g j) x‖≤ε) ∧
      (∀ x y,dist x c<ρ →dist y c<ρ →
        ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤ε*dist x y^((1:ℝ)/3))) :
    CauchySeq g := by
  classical
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let δ := ρ/2
  have hδ : 0<δ := half_pos hρ
  have hdα : 0<δ^((1:ℝ)/3) := Real.rpow_pos_of_pos hδ _
  let e := min (ε/2) (ε/4*δ^((1:ℝ)/3))
  have he : 0<e := lt_min (half_pos hε) (mul_pos (by positivity) hdα)
  obtain ⟨a,_,ha,hcover⟩ := hK.finite_cover_balls hδ
  choose N hN using fun c => hl c e he
  let m := ha.toFinset.sup N
  have hm {c : X} (hc : c∈a) : N c ≤ m := Finset.le_sup (ha.mem_toFinset.mpr hc)
  refine ⟨m,fun i hi j hj => ?_⟩
  have hchoose {x : X} (hx : x∈K) : ∃ c∈a,dist x c<δ := by
    have hh := hcover hx
    simp only [mem_iUnion] at hh
    obtain ⟨c,hc,hxc⟩ := hh
    exact ⟨c,hc,hxc⟩
  have hv (x : X) : ‖valueCLM _ (g i-g j) x‖≤e := by
    by_cases hx : x∈K
    · obtain ⟨c,hc,hxc⟩ := hchoose hx
      exact (hN c i ((hm hc).trans hi) j ((hm hc).trans hj)).1 x (by dsimp [δ] at hxc; linarith)
    · change ‖valueCLM _ (g i) x-valueCLM _ (g j) x‖≤e
      rw [hg i x hx,hg j x hx,sub_self,norm_zero]
      exact he.le
  have hnear {x y : X} (hx : x∈K) (hxy : dist x y<δ) :
      ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤(ε/2)*dist x y^((1:ℝ)/3) := by
    obtain ⟨c,hc,hxc⟩ := hchoose hx
    have hyc : dist y c<ρ := by
      have ht := dist_triangle y x c
      rw [dist_comm y x] at ht
      dsimp [δ] at hxy hxc
      linarith
    have hh := (hN c i ((hm hc).trans hi) j ((hm hc).trans hj)).2 x y
      (by dsimp [δ] at hxc; linarith) hyc
    exact hh.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (dist_nonneg) _))
  have hh (x y : X) :
      ‖valueCLM _ (g i-g j) x-valueCLM _ (g i-g j) y‖≤(ε/2)*dist x y^((1:ℝ)/3) := by
    by_cases hxy : dist x y<δ
    · by_cases hx : x∈K
      · exact hnear hx hxy
      by_cases hy : y∈K
      · have hn := hnear hy (by rwa [dist_comm] : dist y x<δ)
        rw [norm_sub_rev,dist_comm y x] at hn
        exact hn
      · change ‖(valueCLM _ (g i) x-valueCLM _ (g j) x)-
          (valueCLM _ (g i) y-valueCLM _ (g j) y)‖≤_
        simp only [hg i x hx,hg j x hx,hg i y hy,hg j y hy,sub_self,norm_zero]
        positivity
    · have hpow : δ^((1:ℝ)/3)≤dist x y^((1:ℝ)/3) :=
        Real.rpow_le_rpow hδ.le (le_of_not_gt hxy) (by norm_num)
      have he2 : 2*e≤(ε/2)*δ^((1:ℝ)/3) := by
        have hi := min_le_right (ε/2) (ε/4*δ^((1:ℝ)/3))
        dsimp [e]
        nlinarith
      exact (norm_sub_le _ _).trans ((add_le_add (hv x) (hv y)).trans
        ((by linarith : e+e≤(ε/2)*δ^((1:ℝ)/3)).trans
          (mul_le_mul_of_nonneg_left hpow (half_pos hε).le)))
  have hnorm := norm_le_of_bounds (g i-g j) (half_pos hε).le (half_pos hε).le
    (fun x => (hv x).trans (min_le_left _ _)) hh
  rw [max_self] at hnorm
  rw [dist_eq_norm]
  exact hnorm.trans_lt (half_lt_self hε)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open scoped BoundedContinuousFunction
open HolderCompletion
variable {n : ℕ}

lemma dilatedCurve_reconstruction (u : ℂ → Phase n) {a : Phase n} (ha : a≠0) (z : ℂ) :
    dilatedCurve u (slopeScale a) ((Real.sqrt (stdDot n a a) : ℂ)*z)=u z := by
  unfold dilatedCurve
  rw [←mul_assoc,←Complex.ofReal_mul]
  have he : slopeScale a*Real.sqrt (stdDot n a a)=1 :=
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (stdDot_pos ha)).ne'
  rw [he,Complex.ofReal_one,one_mul]

theorem exact_marked_line_source_escape {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n)
    (p q : Phase n) (hpq : p≠q) {Q : ℝ} (hQ : 0≤Q) :
    ∃ R : ℝ,0<R ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ c : ℂ,
      ‖u c‖≤Q →‖c‖≤R := by
  obtain ⟨d,hd,hlo⟩ := exact_line_slope_lower_bound hJs hJ hJc hST hT hout hpq
  obtain ⟨R,hR,hesc⟩ := exact_unit_line_source_escape hJs hJ hJc hST hT hout p hQ
  have hroot : 0<Real.sqrt d := Real.sqrt_pos.mpr hd
  refine ⟨R/Real.sqrt d,div_pos hR hroot,?_⟩
  intro t ht u hu c hc
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  have hs : (slopeScale a : ℂ)≠0 := by exact_mod_cast (slopeScale_pos ha).ne'
  have hlu := dilatedCurve_slope hlim hs
  have hnorm : stdDot n ((slopeScale a : ℂ) • a) ((slopeScale a : ℂ) • a)=1 := by
    simpa only [Complex.coe_smul] using normalizedSlope_unit ha
  have hh := hesc t ht (u (slopeScale a)) (dilatedCurve u (slopeScale a)) (hu.dilate hs)
    ((slopeScale a : ℂ) • a) hnorm hlu ((Real.sqrt (stdDot n a a) : ℂ)*c) (by
      rw [dilatedCurve_reconstruction u ha c]; exact hc)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hh
  have hlow := Real.sqrt_le_sqrt (hlo t ht u hu a ha hlim)
  apply (le_div_iff₀ hroot).mpr
  have hm : ‖c‖*Real.sqrt d≤Real.sqrt (stdDot n a a)*‖c‖ := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hlow (norm_nonneg c)
  exact hm.trans hh

lemma norm_le_of_capacity_le {x : Phase n} {S : ℝ} (hx : capacity x≤S) :
    ‖x‖≤Real.sqrt (max S 0/Real.pi) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  apply (le_div_iff₀ Real.pi_pos).mpr
  have hh := mul_le_mul_of_nonneg_left (norm_sq_le_stdDot x) Real.pi_pos.le
  rw [capacity_eq_stdDot] at hx
  nlinarith [le_max_left S 0]

theorem exact_marked_line_uniform_defect_support {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S<capacity x →J x=standardJ n)
    (p q : Phase n) (hpq : p≠q) :
    ∃ R : ℝ,0<R ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ c : ℂ,R<‖c‖ →
        lineHomotopy J t (u c)=standardJ n ∧ HolderCompletion.geometricResidual u c=0 := by
  obtain ⟨R,hR,hesc⟩ := exact_marked_line_source_escape hJs hJ hJc hST hT hout p q hpq
    (Real.sqrt_nonneg (max S 0/Real.pi))
  refine ⟨R,hR,?_⟩
  intro t ht u hu c hc
  have hcap : S<capacity (u c) := by
    by_contra! h
    exact (not_le_of_gt hc) (hesc t ht u hu c (norm_le_of_capacity_le h))
  have hstd := lineHomotopy_outside hout ht (u c) hcap
  refine ⟨hstd,?_⟩
  rw [geometricResidual_at_CR (hu.2.1 c),hstd,sub_self,zero_apply]

local instance lrInst1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance lrInst2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance lrInst3 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance lrInst4 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance

def localResidual {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (r : ℝ) : HMap ℂ (Phase n) :=
  standardJetCR (cutoffCurveJet smallDiskBump (markedLocalCurve_smooth hu c r))

lemma cutoffCurveJet_local_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (b : ContDiffBump (0:ℂ)) {z : ℂ} (hz : ‖z‖<b.rIn) :
    cDeriv (cutoffCurveJet b hu) z=fderiv ℝ u z := by
  rw [←c_fderiv]
  have hb := b.eventuallyEq_one_of_mem_ball (by simpa only [Metric.mem_ball,dist_zero_right] using hz)
  have he : (cValue (cutoffCurveJet b hu) : ℂ → Phase n)=ᶠ[𝓝 z] u := by
    filter_upwards [hb] with w hw
    rw [cutoffCurveJet_value,hw]
    exact one_smul ℝ (u w)
  exact he.fderiv_eq

lemma localResidual_value {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (c : ℂ) (r : ℝ) {z : ℂ} (hz : ‖z‖<(1:ℝ)/4) :
    valueCLM _ (localResidual hu c r) z=r • geometricResidual u (c+r • z) := by
  rw [localResidual,standardJetCR_value,cutoffCurveJet_local_fderiv (markedLocalCurve_smooth hu c r) smallDiskBump hz]
  have he : fderiv ℝ (markedLocalCurve u c r) z=fderiv ℝ (rescaledCurve u c r) z := by
    exact (((rescaledCurve_smooth hu c r).differentiable (by simp) z).hasFDerivAt.sub_const (u c)).fderiv
  rw [he,rescaledCurve_fderiv hu]
  simp only [smul_apply,geometricResidual,smul_sub]
  rw [smul_comm Complex.I r]

lemma localResidual_at_original {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (c : ℂ) {r : ℝ} (hr : 0<r) {x : ℂ} (hx : dist x c<r/4) :
    geometricResidual u x=r⁻¹ • valueCLM _ (localResidual hu c r) (r⁻¹ • (x-c)) := by
  have hz : ‖r⁻¹ • (x-c)‖<(1:ℝ)/4 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),←dist_eq_norm]
    apply (inv_mul_lt_iff₀ hr).mpr
    linarith
  rw [localResidual_value hu c r hz,inv_smul_smul₀ hr.ne',smul_inv_smul₀ hr.ne',add_sub_cancel]

lemma localResidual_cauchy {u : ℕ → ℂ → Phase n} (hu : ∀ i,ContDiff ℝ ∞ (u i))
    (c : ℂ) (r : ℝ)
    (hc : CauchySeq (fun i => cutoffCurveJet smallDiskBump (markedLocalCurve_smooth (hu i) c r))) :
    CauchySeq (fun i => localResidual (hu i) c r) :=
  (standardJetCR (E := Phase n)).uniformContinuous.comp_cauchySeq hc

end HigherDimensionalBallPacking.Rigidity
end

end OAI
