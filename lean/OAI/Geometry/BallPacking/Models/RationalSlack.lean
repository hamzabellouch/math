import Mathlib
import OAI.Geometry.BallPacking.Models.SurfaceComparison
import OAI.Geometry.BallPacking.Models.EqualNormalModelConvergence

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators
open Set
open scoped Pointwise
open MeasureTheory

theorem exists_rational_above_in_open {ι : Type*} [Fintype ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) {r : ι → ℝ} (hr : r ∈ U) :
    ∃ q : ι → ℚ, (∀ i, r i < q i) ∧ (fun i => (q i : ℝ)) ∈ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.1 hU r hr
  have hinterval (i : ι) : ∃ q : ℚ, r i < q ∧ (q : ℝ) < r i+ε/2 :=
    exists_rat_btwn (by linarith)
  choose q hlo hhi using hinterval
  refine ⟨q,hlo,hball ?_⟩
  rw [Metric.mem_ball]
  apply (dist_pi_lt_iff hε).2
  intro i
  rw [Real.dist_eq,abs_of_pos (sub_pos.mpr (hlo i))]
  linarith [hhi i]

theorem rational_small_slack {ι : Type*} [Fintype ι] (n : ℕ) (r : ι → ℝ)
    (hhalf : ∀ i, r i < 1/2) (hvol : ∑ i,r i^n < 1) :
    ∃ q : ι → ℚ, (∀ i, r i < q i) ∧ (∀ i, (q i : ℝ) < 1/2) ∧
      ∑ i,(q i : ℝ)^n < 1 := by
  let U : Set (ι → ℝ) := {s | (∀ i,s i<1/2) ∧ ∑ i,s i^n<1}
  have hU : IsOpen U := by
    have ha : IsOpen {s : ι → ℝ | ∀ i,s i<1/2} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
    exact ha.inter (isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).pow n)
      continuous_const)
  obtain ⟨q,hq,hUq⟩ := exists_rational_above_in_open hU (show r∈U from ⟨hhalf,hvol⟩)
  exact ⟨q,hq,hUq⟩

theorem rational_packing_slack {ι : Type*} [Fintype ι] (n : ℕ) (R : ℝ) (r : ι → ℝ)
    (hvol : ∑ i,r i^n < R^n) (hpair : ∀ i j, i≠j → r i+r j<R) :
    ∃ q : ι → ℚ, (∀ i,r i<q i) ∧ (∑ i,(q i:ℝ)^n)<R^n ∧
      ∀ i j, i≠j → (q i:ℝ)+(q j:ℝ)<R := by
  let U : Set (ι → ℝ) := {s | (∑ i,s i^n)<R^n ∧ ∀ i j,i≠j → s i+s j<R}
  have hpairOpen : IsOpen {s : ι → ℝ | ∀ i j,i≠j → s i+s j<R} := by
    simp only [ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    refine isOpen_iInter_of_finite fun _h => ?_
    exact isOpen_lt ((continuous_apply i).add (continuous_apply j)) continuous_const
  have hU : IsOpen U := (isOpen_lt
    (continuous_finsetSum _ fun i _ => (continuous_apply i).pow n) continuous_const).inter hpairOpen
  obtain ⟨q,hq,hUq⟩ := exists_rational_above_in_open hU (show r∈U from ⟨hvol,hpair⟩)
  exact ⟨q,hq,hUq⟩

theorem exists_rational_below_in_open {ι : Type*} [Fintype ι]
    {U : Set (ι → ℝ)} (hU : IsOpen U) {r : ι → ℝ} (hr : r ∈ U) :
    ∃ q : ι → ℚ, (∀ i, (q i : ℝ) < r i) ∧ (fun i => (q i : ℝ)) ∈ U := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.1 hU r hr
  have hinterval (i : ι) : ∃ q : ℚ, r i-ε/2 < q ∧ (q : ℝ) < r i :=
    exists_rat_btwn (by linarith)
  choose q hlo hhi using hinterval
  refine ⟨q,hhi,hball ?_⟩
  rw [Metric.mem_ball]
  apply (dist_pi_lt_iff hε).2
  intro i
  rw [Real.dist_eq,abs_of_neg (sub_neg.mpr (hhi i))]
  linarith [hlo i]

theorem rational_truncation_1d (F : ℝ → ℝ) (hF : Continuous F)
    {s l c : ℝ} (hls : l<s) (hc : c<F s) :
    ∃ h d : ℚ, l<h ∧ h<d ∧ (d:ℝ)<s ∧ c<F h := by
  have ho : IsOpen {x : ℝ | l<x ∧ c<F x} :=
    (isOpen_lt continuous_const continuous_id).inter (isOpen_lt continuous_const hF)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.1 ho s ⟨hls,hc⟩
  obtain ⟨h,hlo,hhi⟩ := exists_rat_btwn (show s-ε<s by linarith)
  have hm : (h:ℝ)∈Metric.ball s ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr hhi)]
    linarith
  obtain ⟨d,hhd,hds⟩ := exists_rat_btwn hhi
  exact ⟨h,d,(hball hm).1,by exact_mod_cast hhd,hds,(hball hm).2⟩

theorem rational_truncation_2d (F : ℝ×ℝ → ℝ) (hF : Continuous F)
    {s₁ s₂ l c : ℝ} (hl₁ : l<s₁) (hl₂ : l<s₂) (hc : c<F (s₁,s₂)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ,
      l<h₁ ∧ h₁<d₁ ∧ (d₁:ℝ)<s₁ ∧
      l<h₂ ∧ h₂<d₂ ∧ (d₂:ℝ)<s₂ ∧ c<F (h₁,h₂) := by
  let U : Set (Fin 2 → ℝ) := {p | l<p 0 ∧ l<p 1 ∧ c<F (p 0,p 1)}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (hF.comp ((continuous_apply 0).prodMk (continuous_apply 1)))))
  let r : Fin 2 → ℝ := ![s₁,s₂]
  have hr : r∈U := ⟨hl₁,hl₂,hc⟩
  obtain ⟨h,hlt,hmem⟩ := exists_rational_below_in_open hU hr
  have hh₁ : (h 0:ℝ)<s₁ := hlt 0
  have hh₂ : (h 1:ℝ)<s₂ := hlt 1
  obtain ⟨d₁,hd₁,hs₁⟩ := exists_rat_btwn hh₁
  obtain ⟨d₂,hd₂,hs₂⟩ := exists_rat_btwn hh₂
  exact ⟨h 0,h 1,d₁,d₂,hmem.1,by exact_mod_cast hd₁,hs₁,
    hmem.2.1,by exact_mod_cast hd₂,hs₂,hmem.2.2⟩

theorem smul_momentSimplex (m : ℕ) {τ : ℝ} (hτ : 0 < τ) (h : ℝ) :
    τ • momentSimplex m h = momentSimplex m (τ*h) := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    refine ⟨fun i => mul_nonneg hτ.le (hq.1 i),?_⟩
    simpa only [Pi.smul_apply,smul_eq_mul,←Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hq.2 hτ.le
  · intro hp
    refine ⟨τ⁻¹ • p,⟨fun i => mul_nonneg (inv_nonneg.2 hτ.le) (hp.1 i),?_⟩,?_⟩
    · have he := mul_le_mul_of_nonneg_left hp.2 (inv_nonneg.2 hτ.le)
      simpa only [Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,←mul_assoc,
        inv_mul_cancel₀ hτ.ne',one_mul] using he
    · simp [smul_smul,hτ.ne']

def smallModelGap {m : ℕ} {ι : Type*} [Fintype ι] (r : ι → ℝ) (p : Fin m → ℝ) : ℝ :=
  (2:ℝ)^m*(1-2*∑ j,p j)-∑ i,max (r i-∑ j,p j) 0

theorem continuous_smallModelGap {m : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) : Continuous (@smallModelGap m ι _ r) := by
  unfold smallModelGap
  fun_prop

theorem smallModelGap_eq_cappedAffine {m : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) : @smallModelGap m ι _ r =
      cappedAffine ((2:ℝ)^m) (fun _ => (2:ℝ)^m*2) r (fun _ => 1) := by
  funext p
  simp only [smallModelGap,cappedAffine,one_mul,←Finset.mul_sum]
  ring

theorem integral_smallModelGap {m : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i,0 ≤ r i) {h : ℝ} (hh : 0 ≤ h) (hrh : ∀ i,r i ≤ h) :
    (∫ p in momentSimplex m h, smallModelGap r p) =
      smallModelMean m h-(∑ i,r i^(m+1))/((m+1).factorial : ℝ) := by
  have hcap (i : ι) : momentSimplex m (r i) ⊆ momentSimplex m h :=
    fun _ hp => ⟨hp.1,hp.2.trans (hrh i)⟩
  unfold smallModelGap
  rw [integral_sub]
  · rw [integral_small_model m hh,integral_sum_tents r hr
      (momentSimplex_isClosed m h).measurableSet (fun _ hp => hp.1) hcap]
  · apply ContinuousOn.integrableOn_compact (momentSimplex_isCompact m h)
    fun_prop
  · exact continuousOn_finsetSum _ (fun _ _ => by fun_prop) |>.integrableOn_compact
      (momentSimplex_isCompact m h)

theorem exists_small_model_comparison_data {m : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : ∀ i,0 < r i) (hhalf : ∀ i,r i < 1/2)
    (hvol : ∑ i,r i^(m+1) < 1) :
    ∃ h d : ℚ, ∃ τ a : ℝ,
      (∀ i,r i<h) ∧ h<d ∧ (d:ℝ)<1/2 ∧ 0<(h:ℝ) ∧
      0<τ ∧ τ<1 ∧ 0<a ∧
      (∀ i,momentSimplex m (r i) ⊆ τ • momentSimplex m h) ∧
      ConcaveOn ℝ (momentSimplex m h) (smallModelGap r) ∧
      (0 < ∫ p in momentSimplex m h, smallModelGap r p) ∧
      ∀ p ∈ momentSimplex m h, p ∉ τ • momentSimplex m h → a ≤ smallModelGap r p := by
  classical
  let S := Finset.univ.image r
  have hS : S.Nonempty := Finset.image_nonempty.2 Finset.univ_nonempty
  let R := S.max' hS
  have hR (i : ι) : r i ≤ R := Finset.le_max' S (r i) (Finset.mem_image_of_mem r (Finset.mem_univ i))
  have hRhalf : R<1/2 := (Finset.max'_lt_iff S hS).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hx
    exact hhalf i)
  have hRpos : 0<R := (hr (Classical.arbitrary ι)).trans_le (hR _)
  have hfac : (0:ℝ)<((m+1).factorial : ℝ) := by positivity
  have hlim : (∑ i,r i^(m+1))/((m+1).factorial : ℝ)<smallModelMean m (1/2) := by
    rw [smallModelMean_half]
    exact div_lt_div_of_pos_right hvol hfac
  obtain ⟨h,d,hRh,hhd,hd,hmean⟩ := rational_truncation_1d (smallModelMean m)
    (continuous_smallModelMean m) hRhalf hlim
  have hh : (0:ℝ)<h := hRpos.trans hRh
  have hhhalf : (h:ℝ)<1/2 := (by exact_mod_cast hhd : (h:ℝ)<d).trans hd
  have hratio : R/(h:ℝ)<1 := (div_lt_one hh).2 hRh
  obtain ⟨τ,hτlo,hτhi⟩ := exists_between hratio
  have hτ : 0<τ := (div_pos hRpos hh).trans hτlo
  have hRτ : R<τ*(h:ℝ) := (div_lt_iff₀ hh).1 hτlo
  let a := (2:ℝ)^m*(1-2*(h:ℝ))
  have ha : 0<a := mul_pos (by positivity) (by linarith)
  refine ⟨h,d,τ,a,fun i => (hR i).trans_lt hRh,hhd,hd,hh,hτ,hτhi,ha,?_,?_,?_,?_⟩
  · intro i p hp
    rw [smul_momentSimplex m hτ]
    exact ⟨hp.1,hp.2.trans ((hR i).trans hRτ.le)⟩
  · rw [smallModelGap_eq_cappedAffine]
    apply concaveOn_cappedAffine _ _ _ _ (fun _ => by norm_num)
    intro x hx y hy u v hu hv huv
    refine ⟨fun i => add_nonneg (mul_nonneg hu (hx.1 i)) (mul_nonneg hv (hy.1 i)),?_⟩
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,←Finset.mul_sum]
    have := add_le_add (mul_le_mul_of_nonneg_left hx.2 hu) (mul_le_mul_of_nonneg_left hy.2 hv)
    nlinarith
  · rw [integral_smallModelGap r (fun i => (hr i).le) hh.le (fun i => (hR i).trans hRh.le)]
    linarith
  · intro p hp hout
    have hs : τ*(h:ℝ)<∑ j,p j := by
      rw [smul_momentSimplex m hτ] at hout
      exact lt_of_not_ge (fun he => hout ⟨hp.1,he⟩)
    have hzero (i : ι) : max (r i-∑ j,p j) 0=0 := max_eq_right (by linarith [hR i])
    simp only [smallModelGap,hzero,Finset.sum_const_zero,sub_zero]
    exact mul_le_mul_of_nonneg_left (by linarith [hp.2]) (by positivity)

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 theorem actual_small_normal_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) :
    ∃ h d : ℚ, (∀ i,r i<h) ∧ h<d ∧ (d:ℝ)<1/2 ∧
      ∃ ℓ,∃ φ : Fin N → Ambient (m+3) → Surface m × PlanePhase (Fin (m+2)),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+3) (r' i))
          (fun _ => successorStandardForm (m+2))
          (globalHorizontalCoupling phaseArea
            (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+3) (r' i))
          (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) ×ˢ
            (planeMoments ⁻¹' momentSimplex (m+2) h)))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+3) (r' i))
          (φ j '' closedBall (m+3) (r' j))) := by
  classical
  obtain ⟨h,d,τ,d₀,hrh,hhd,hd,hh,hτ,hτ1,hd₀,_hcap,hconc,hmean,houter⟩ :=
    exists_small_model_comparison_data r hr hhalf hvol
  have hhalf' : (h:ℝ)<1/2 := (show (h:ℝ)<d by exact_mod_cast hhd).trans hd
  have hcoef : 2*(h:ℝ)<1 := by linarith
  let bF : Fin 1 → Moments (m+2) := fun _ _ => 1
  let cF : Fin 1 → ℝ := fun _ => h
  have hreg : region bF cF=momentSimplex (m+2) h := by
    ext p
    simp [region,momentSimplex,bF,cF]
  have hcomp : IsCompact (region bF cF) := hreg ▸ momentSimplex_isCompact (m+2) h
  have hP : ∀ p∈region bF cF,(∀ j,0≤p j) ∧ (∑ j,p j)≤h := by
    intro p hp
    rw [hreg] at hp
    exact hp
  let K := fun ℓ => projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)
  have hK ℓ : IsCompact (K ℓ) := projectionDomain_compact (parameters m) _
  have hKn ℓ : K ℓ⊆interior (K (ℓ+1)) := by
    apply projectionDomain_nested
    simp only [exhaustionRadius,Nat.cast_add,Nat.cast_one]
    linarith
  have hKc ℓ : IsConnected (interior (K ℓ)) :=
    projectionDomain_interior_connected (exhaustionRadius_pos (parameters m) ℓ)
      (exhaustionRadius_branch (parameters m) ℓ)
  obtain ⟨H,_hw,hclock,hpos⟩ := exists_positive_fixed_annularHandleData m
  have hsimp i p (hp : ∀ j,0≤p j) (ht : (∑ j,p j)≤r i) : p∈region bF cF := by
    rw [hreg]
    exact ⟨hp,ht.trans (hrh i).le⟩
  have hface (i : Fin N) (p : Moments (m+2)) (_hp : ∀ j,0≤p j) (ht : (∑ j,p j)≤r i) ν :
      (∑ j,bF ν j*p j)≠cF ν := by
    simpa only [bF,cF,one_mul] using ne_of_lt (ht.trans_lt (hrh i))
  obtain ⟨ℓ,φ,hφ,hφK,hdisj⟩ := Annular.exhausted_surface_packing bF cF
    (fun _ _ => by norm_num [bF]) (fun _ => hh) hcomp
    (fun p => (2:ℝ)^(m+2)*equalNormalCoefficient (m+2) 2 p)
    (continuous_const.mul (equalNormalCoefficient_smooth (m+2) 2).continuous).continuousOn
    (fun p hp => mul_pos (by positivity)
      (equalNormalCoefficient_pos (by norm_num) hcoef (hP p hp).2))
    r r' hr' hrr hsimp hface (by rw [hreg]; exact hconc)
    (by simpa only [hreg,equalNormalCoefficient,smallModelGap] using hmean)
    hτ hτ1 hd₀ (by simpa only [hreg,equalNormalCoefficient,smallModelGap] using houter)
    K hK hKn (projectionDomain_cover (parameters m) (2+∑ j,‖parameters m j‖))
    (fun ℓ => (hKc ℓ).isPreconnected) (fun ℓ => (hKc ℓ).nonempty)
    (fun ℓ => projectionDomain_smoothBoundary (exhaustionRadius_pos (parameters m) ℓ)
      (exhaustionRadius_branch (parameters m) ℓ)) (positivePlaneTransitions (parameters m))
    H (half_pos H.width_pos) (by linarith [H.width_pos]) (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1:ℝ)/4<1/2) hpos hclock
    (curveFSForm_smooth (parameters m) (1/Real.pi)) (curveFSForm_skew (parameters m) (1/Real.pi))
    (fun c y hy => curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) c hy)
    (fun _ p => equalNormalCoefficient (m+2) 2 p.1)
    (fun _ => (equalNormalCoefficient_smooth (m+2) 2).contMDiff.comp contMDiff_fst)
    (fun _ p hp _ _ => equalNormalCoefficient_pos (by norm_num) hcoef (hP p hp).2)
    (fun _ => normalHorizontalPrimitive (parameters m) 2)
    (fun _ => normalHorizontalPrimitive_smooth (parameters m) 2)
    (fun _ => normalHorizontalPrimitive_exterior (parameters m) 2)
    (normalHorizontalPrimitive_area_limit (parameters m) (by norm_num) hcoef hP)
  refine ⟨h,d,hrh,hhd,hd,ℓ,φ,hφ,?_,hdisj⟩
  simpa only [planeRegion,hreg] using hφK

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

local instance : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

def physicalParameter (L : ℝ) (p : Moments 2) : Radial.Plane := (L*p 0,L*p 1)

theorem physicalParameter_smooth (L : ℝ) : ContDiff ℝ ∞ (physicalParameter L) := by
  unfold physicalParameter
  fun_prop

def cubicExhaustion (ℓ : ℕ) : Set BaseCurve :=
  projectionDomain (parameters 0) (exhaustionRadius (parameters 0) ℓ)

theorem cubicExhaustion_compact (ℓ : ℕ) : IsCompact (cubicExhaustion ℓ) :=
  projectionDomain_compact (parameters 0) _

def physicalPrimitive {A B : ℕ} (D S : ℕ) (c L : ℝ) (p : Moments 2) :
    ManifoldOneForm RealModel BaseCurve :=
  radialPrimitive (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c
    (physicalParameter L p)

def physicalArea (D S : ℕ) (c L : ℝ) (p : Moments 2) : ℝ :=
  c*(3*((D:ℝ)-3*(L*p 0+L*p 1))-2*max ((S:ℝ)-(L*p 0+L*p 1)) 0)*Real.pi

 theorem physicalArea_continuous (D S : ℕ) (c L : ℝ) : Continuous (physicalArea D S c L) := by
  unfold physicalArea
  fun_prop

 theorem exists_physicalPrimitive_extension {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) (c L : ℝ) {P : Set (Moments 2)} (hP : IsCompact P)
    (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B)) (ℓ : ℕ) :
    ∃ Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve,
      SmoothOneFormFamily Γ ∧ ∀ᶠ q in 𝓝ˢ (P ×ˢ cubicExhaustion ℓ),
        physicalParameter L q.1∈Radial.lowerTrapezoid A B →
        Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2 := by
  obtain ⟨Γ,hΓ,he⟩ := exists_radialPrimitive_smooth_extension hA hAB
    (cubicDegree D) (cubicMarkedOrder S) c (hP.image (physicalParameter_smooth L).continuous)
    (image_subset_iff.mpr hPS) (cubicExhaustion_compact ℓ)
  refine ⟨Γ ∘ physicalParameter L,hΓ.comp (physicalParameter_smooth L),?_⟩
  apply mem_nhdsSet_iff_forall.mpr
  intro q hq
  have hn := mem_nhdsSet_iff_forall.mp he (physicalParameter L q.1,q.2)
    ⟨mem_image_of_mem _ hq.1,hq.2⟩
  have hc : Continuous (fun q : Moments 2 × BaseCurve => (physicalParameter L q.1,q.2)) :=
    ((physicalParameter_smooth L).continuous.comp continuous_fst).prodMk continuous_snd
  exact hc.continuousAt.eventually hn

 theorem physicalPrimitive_extension_curvature {A B : ℕ} {D S : ℕ} {c L : ℝ}
    {P : Set (Moments 2)} {ℓ : ℕ} {Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve}
    (he : ∀ᶠ q in 𝓝ˢ (P ×ˢ cubicExhaustion ℓ),
      physicalParameter L q.1∈Radial.lowerTrapezoid A B →
      Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2)
    {p : Moments 2} (hp : p∈P) (hs : physicalParameter L p∈Radial.lowerTrapezoid A B)
    {x : BaseCurve} (hx : x∈cubicExhaustion ℓ) :
    manifoldExteriorOneForm (Γ p) x=
      radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c
        (physicalParameter L p) x := by
  apply manifoldExteriorOneForm_congr_germ
  have hn := mem_nhdsSet_iff_forall.mp he (p,x) ⟨hp,hx⟩
  filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hn] with y hy
  exact hy hs

 theorem physicalArea_uniform {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {P : Set (Moments 2)} (hP : IsCompact P) (L : ℝ)
    (hPS : MapsTo (physicalParameter L) P (Radial.lowerTrapezoid A B))
    {c : ℝ} (hc : 0<c) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
      (manifoldExteriorOneForm (physicalPrimitive (A := A) (B := B) D S c L p)))
      (physicalArea D S c L) atTop P := by
  have hlim := (tendstoUniformlyOn_radial_cubic_area hA hS0 hAB hSB hB hS
    (hP.image (physicalParameter_smooth L).continuous) (image_subset_iff.mpr hPS) hc).comp
    (physicalParameter L)
  have hh := hlim.mono (show P⊆physicalParameter L ⁻¹' (physicalParameter L '' P) from
    fun p hp => mem_image_of_mem _ hp)
  unfold physicalArea
  simpa only [Function.comp_def,physicalPrimitive,physicalParameter,sub_add_eq_sub_sub,
    markedHeight,planeVector,Matrix.cons_val_zero,Matrix.cons_val_one,radialForm] using! hh

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

 theorem FormNeighborhoodEmbedding.congr_target_near
    {K : Set N} {D : Set M} {σ : ManifoldTwoForm F N} {Ω Ω' : ManifoldTwoForm E M}
    {f : N → M} (hf : FormNeighborhoodEmbedding K σ Ω f)
    (hmap : MapsTo f K D) (he : Ω =ᶠ[𝓝ˢ D] Ω') : FormNeighborhoodEmbedding K σ Ω' f := by
  obtain ⟨U,hU,hKU,hs,hfemb,hσ⟩ := hf
  obtain ⟨V,hV,hDV,hVe⟩ := mem_nhdsSet_iff_exists.mp he
  let W := U ∩ f ⁻¹' V
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hU hV
  have hWU : W⊆U := inter_subset_left
  refine ⟨W,hW,fun x hx => ⟨hKU hx,hDV (hmap hx)⟩,hs.mono hWU,
    hfemb.comp (Topology.IsEmbedding.inclusion hWU),?_⟩
  intro x hx v w
  rw [← hVe hx.2]
  exact hσ x hx.1 v w

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [IsManifold 𝓘(ℝ,E) ∞ M]

 theorem globalHorizontalCoupling_congr_joint (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ Γ' : V → ManifoldOneForm E M} {z : M × V}
    (h : ∀ᶠ q in 𝓝 z,Γ q.2 q.1=Γ' q.2 q.1) :
    globalHorizontalCoupling Ω Γ z=globalHorizontalCoupling Ω Γ' z := by
  have he : productHorizontalLift Γ=ᶠ[𝓝 z] productHorizontalLift Γ' := by
    filter_upwards [h] with q hq
    exact congrArg (fun L : E →L[ℝ] ℝ => L.comp (ContinuousLinearMap.fst ℝ E V)) hq
  exact congrArg (fun B => Ω.bilinearComp (ContinuousLinearMap.snd ℝ E V)
    (ContinuousLinearMap.snd ℝ E V)+B) (manifoldExteriorOneForm_congr_germ he)

 omit [NormedSpace ℝ P] in
 theorem globalHorizontalCoupling_congr_near (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ Γ' : P → ManifoldOneForm E M} {μ : V → P} (hμ : Continuous μ)
    {K : Set (P × M)} {D : Set (M × V)} (hDK : MapsTo (fun z : M × V => (μ z.2,z.1)) D K)
    (h : ∀ᶠ q in 𝓝ˢ K,Γ q.1 q.2=Γ' q.1 q.2) :
    globalHorizontalCoupling Ω (Γ ∘ μ)=ᶠ[𝓝ˢ D] globalHorizontalCoupling Ω (Γ' ∘ μ) := by
  obtain ⟨U,hU,hKU,hUe⟩ := mem_nhdsSet_iff_exists.mp h
  let R : M × V → P × M := fun z => (μ z.2,z.1)
  have hR : Continuous R := (hμ.comp continuous_snd).prodMk continuous_fst
  have hO : IsOpen (R ⁻¹' U) := hU.preimage hR
  apply Filter.mem_of_superset (hO.mem_nhdsSet.mpr (fun z hz => hKU (hDK hz)))
  intro z hz
  apply globalHorizontalCoupling_congr_joint Ω
  filter_upwards [hO.mem_nhds hz] with q hq
  exact hUe hq

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

local instance : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

 theorem physicalArea_pos {A B D S : ℕ} (hB : 3*B<D) (hS : 3*S<D)
    {c L : ℝ} (hc : 0<c) {p : Moments 2}
    (hp : physicalParameter L p∈Radial.lowerTrapezoid A B) : 0<physicalArea D S c L p := by
  have hb : 3*(B:ℝ)<D := by exact_mod_cast hB
  have hs : 3*(S:ℝ)<D := by exact_mod_cast hS
  have ht : L*p 0+L*p 1<(B:ℝ) := hp.2.2.2
  unfold physicalArea
  apply mul_pos (mul_pos hc ?_) Real.pi_pos
  by_cases hh : (S:ℝ)≤L*p 0+L*p 1
  · rw [max_eq_right (sub_nonpos.mpr hh)]
    linarith
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hh))]
    linarith

 theorem actual_cubic_representative_packing {A B D S N q : ℕ} [Nonempty (Fin N)]
    (hA : 0<A) (hS0 : 0<S) (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {c L : ℝ} (hc : 0<c)
    (bF : Fin q → Moments 2) (cF : Fin q → ℝ)
    (hbF : ∀ ν j,0≤bF ν j) (hcF : ∀ ν,0<cF ν) (hcomp : IsCompact (region bF cF))
    (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
    (r r' : Fin N → ℝ) (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j)≤r i → p∈region bF cF)
    (hface : ∀ i,∀ p : Moments 2,(∀ j,0≤p j) → (∑ j,p j)≤r i →
      ∀ ν,(∑ j,bF ν j*p j)≠cF ν)
    (hconc : ConcaveOn ℝ (region bF cF) (fun p => physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0))
    (hmean : 0<∫ p in region bF cF,physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0<d₀)
    (houter : ∀ p∈region bF cF,p∉τ • region bF cF →
      d₀≤physicalArea D S c L p-∑ i,max (r i-∑ j,p j) 0) :
    ∃ ℓ,∃ Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve,
      SmoothOneFormFamily Γ ∧
      (∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
        physicalParameter L q.1∈Radial.lowerTrapezoid A B →
        Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) ∧
      ∃ φ : Fin N → Ambient 3 → BaseCurve × PlanePhase (Fin 2),
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (globalHorizontalCoupling phaseArea (Γ ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall 3 (r' i)) (interior (cubicExhaustion ℓ ×ˢ planeRegion bF cF))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall 3 (r' i)) (φ j '' closedBall 3 (r' j))) := by
  choose Γ hΓ he using fun ℓ => exists_physicalPrimitive_extension hA hAB D S c L hcomp hPS ℓ
  have hform ℓ p (hp : p∈region bF cF) x (hx : x∈cubicExhaustion ℓ) :=
    physicalPrimitive_extension_curvature (he ℓ) hp (hPS hp) hx
  have hlim : TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral (cubicExhaustion_compact ℓ)
      (manifoldExteriorOneForm (Γ ℓ p))) (physicalArea D S c L) atTop (region bF cF) := by
    apply (physicalArea_uniform hA hS0 hAB hSB hB hS hcomp L hPS hc).congr
    filter_upwards [] with ℓ
    intro p hp
    exact (compactSurfaceFormIntegral_congr (cubicExhaustion_compact ℓ)
      (fun x hx => hform ℓ p hp x hx)).symm
  have hmono ℓ : cubicExhaustion ℓ⊆interior (cubicExhaustion (ℓ+1)) := by
    apply projectionDomain_nested
    simp only [exhaustionRadius,Nat.cast_add,Nat.cast_one]
    linarith
  have hconn ℓ : IsConnected (interior (cubicExhaustion ℓ)) :=
    projectionDomain_interior_connected (exhaustionRadius_pos (parameters 0) ℓ)
      (exhaustionRadius_branch (parameters 0) ℓ)
  have hcover : (⋃ ℓ,cubicExhaustion ℓ)=univ :=
    projectionDomain_cover (parameters 0) (2+∑ j,‖parameters 0 j‖)
  obtain ⟨H,_hw,hclock,hpos⟩ := exists_positive_fixed_annularHandleData 0
  have hcurv ℓ p (hp : p∈region bF cF) b y (hy : y∈(extChartAt 𝓘(ℝ,Plane) b).target)
      (hx : (extChartAt 𝓘(ℝ,Plane) b).symm y∈cubicExhaustion ℓ) :
      0<chartTwoForm (manifoldExteriorOneForm (Γ ℓ p)) b y (1,0) (0,1) := by
    dsimp only [chartTwoForm]
    erw [hform ℓ p hp _ hx]
    exact radialForm_positive hA hAB (cubicMarked_lt_degree hB hS) hc (hPS hp) b hy
  obtain ⟨ℓ,φ,hφ,hm,hd⟩ := Annular.exhausted_curvature_surface_packing bF cF hbF hcF hcomp
    (physicalArea D S c L) (physicalArea_continuous D S c L).continuousOn
    (fun p hp => physicalArea_pos hB hS hc (hPS hp)) r r' hr' hrr hsimplex hface
    hconc hmean hτ hτ1 hd₀ houter cubicExhaustion cubicExhaustion_compact hmono hcover
    (fun ℓ => (hconn ℓ).isPreconnected) (fun ℓ => (hconn ℓ).nonempty)
    (fun ℓ => projectionDomain_smoothBoundary (exhaustionRadius_pos (parameters 0) ℓ)
      (exhaustionRadius_branch (parameters 0) ℓ)) (positivePlaneTransitions (parameters 0))
    H (half_pos H.width_pos) (by linarith [H.width_pos]) (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1:ℝ)/4<1/2) hpos hclock
    (DiagonalQuadrics.curveFSForm_smooth (parameters 0) (1/Real.pi)) (DiagonalQuadrics.curveFSForm_skew (parameters 0) (1/Real.pi))
    (fun b y hy => DiagonalQuadrics.curveFSForm_positive (parameters 0) (one_div_pos.mpr Real.pi_pos) b hy)
    Γ hΓ hcurv hlim
  exact ⟨ℓ,Γ ℓ,hΓ ℓ,he ℓ,φ,hφ,hm,hd⟩

end PackingSufficiencySupport.CubicModel
end

end OAI
