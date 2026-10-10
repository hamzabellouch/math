import Mathlib
import OAI.Geometry.BallPacking.Hamiltonian.CartesianMomentSlices

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology BigOperators
open Set Function
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem liftedHamiltonian_compact (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : HasCompactSupport B) : HasCompactSupport (liftedHamiltonian j B) := by
  obtain ⟨r,hr,hbound⟩ := hB.isBounded.exists_pos_norm_le
  let K : Set (ℝ × PlanePhase ι) := Icc (-r) r ×ˢ pi univ (fun _ => closedRoundDisk (2*r+1))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_univ_pi (fun i =>
    closedRoundDisk_isCompact _))
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hn
  have hb := hbound (liftArgument j p) (subset_closure hn)
  have hy : ‖outerMoments j p.2‖ ≤ r := (norm_fst_le _).trans ((norm_fst_le _).trans hb)
  have ht : ‖p.1‖ ≤ r := (norm_snd_le _).trans ((norm_fst_le _).trans hb)
  have hz : ‖p.2 j‖ ≤ r := (norm_snd_le _).trans hb
  apply hp
  refine ⟨?_,?_⟩
  · exact abs_le.mp ht
  · intro i _
    change radiusSq (p.2 i) ≤ (2*r+1)^2
    by_cases hij : i=j
    · subst i
      have h₁ : |(p.2 j).1| ≤ r := (norm_fst_le _).trans hz
      have h₂ : |(p.2 j).2| ≤ r := (norm_snd_le _).trans hz
      have hs₁ := (sq_le_sq₀ (abs_nonneg _) hr.le).mpr h₁
      have hs₂ := (sq_le_sq₀ (abs_nonneg _) hr.le).mpr h₂
      simp only [sq_abs] at hs₁ hs₂
      dsimp [radiusSq]
      nlinarith
    · have hpi : radialArea (p.2 i) ≤ r := by
        have hh := (norm_le_pi_norm (outerMoments j p.2) i).trans hy
        rw [outerMoments_other j p.2 hij,Real.norm_of_nonneg (by dsimp [radialArea,radiusSq]; positivity)] at hh
        exact hh
      have hs : 0 ≤ radiusSq (p.2 i) := by dsimp [radiusSq]; positivity
      have hpi1 : 1 ≤ Real.pi := (by linarith [Real.pi_gt_three] : (1:ℝ) ≤ Real.pi)
      have he := mul_le_mul_of_nonneg_right hpi1 hs
      dsimp [radialArea] at hpi
      nlinarith

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem scaledPlanarHamiltonian_support (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : Continuous a) (hn : ∀ y, a y ≠ 0) {σ : ℝ}
    (hσ : ∀ p ∈ tsupport Ψ.hamiltonian, radialArea p.2 ≤ σ) :
    tsupport (scaledPlanarHamiltonian Ψ a χ) ⊆
      {p | p.1.1 ∈ tsupport χ ∧ radialArea p.2 ≤ σ*(a p.1.1)^2} := by
  apply closure_minimal
  · intro p hp
    have hc : χ p.1.1 ≠ 0 := by intro hz; apply hp; simp [scaledPlanarHamiltonian,hz]
    have hb : Ψ.hamiltonian ((p.1.1,χ p.1.1*Real.smoothTransition p.1.2),(a p.1.1)⁻¹ • p.2) ≠ 0 := by
      intro hz; apply hp; simp [scaledPlanarHamiltonian,hz]
    refine ⟨subset_tsupport χ hc,?_⟩
    have hh := mul_le_mul_of_nonneg_left (hσ _ (subset_tsupport _ hb)) (sq_nonneg (a p.1.1))
    rw [radialArea_smul] at hh
    have he : (a p.1.1)^2*((a p.1.1)⁻¹^2*radialArea p.2) = radialArea p.2 := by
      field_simp [hn p.1.1]
    rw [he] at hh
    simpa only [mul_comm] using hh
  · exact ((isClosed_tsupport χ).preimage continuous_fst.fst).inter
      (isClosed_le (radialArea_smooth.continuous.comp continuous_snd)
        (continuous_const.mul ((ha.comp continuous_fst.fst).pow 2)))

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem liftedHamiltonian_support_subset (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    : tsupport (liftedHamiltonian j B) ⊆
      {p : ℝ × PlanePhase ι | liftArgument j p ∈ tsupport B} := by
  apply closure_minimal
  · intro p hp
    exact subset_tsupport B hp
  · exact (isClosed_tsupport B).preimage (liftArgument_smooth j).continuous

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Comparison
open Set

variable {P : Type*} [PseudoMetricSpace P]

theorem exists_uniform_variable_modulus {Y : Set P} (hY : IsCompact Y)
    {L : P → ℝ} (hL : ContinuousOn L Y) (G : C(P × ℝ,ℝ)) {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Y, ∀ u ∈ Icc (0:ℝ) (L y), ∀ v ∈ Icc (0:ℝ) (L y),
      |u-v| < δ → G (y,u) < G (y,v)+ε := by
  obtain ⟨M,hM⟩ := (hY.image_of_continuousOn hL).bddAbove
  have hc := (hY.prod (isCompact_Icc : IsCompact (Icc (0:ℝ) M))).uniformContinuousOn_of_continuous
    G.continuous.continuousOn
  obtain ⟨δ,hδ,hG⟩ := Metric.uniformContinuousOn_iff.mp hc ε he
  refine ⟨δ,hδ,?_⟩
  intro y hy u hu v hv hd
  have hdist : dist (y,u) (y,v) < δ := by
    simpa only [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_right (abs_nonneg (u-v))] using hd
  have hh := hG (y,u) ⟨hy,hu.1,hu.2.trans (hM ⟨y,hy,rfl⟩)⟩
    (y,v) ⟨hy,hv.1,hv.2.trans (hM ⟨y,hy,rfl⟩)⟩ hdist
  rw [Real.dist_eq] at hh
  linarith only [(le_abs_self (G (y,u)-G (y,v))).trans_lt hh]

end PackingSufficiencySupport.Comparison

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open Comparison
open scoped BigOperators
open MeasureTheory
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_smooth_positive_shortening {Y : Set P} (hY : IsClosed Y)
    {L : P → ℝ} (hL : Continuous L) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hLY : ∀ y ∈ Y, η ≤ L y) :
    ∃ l : P → ℝ, ContDiff ℝ ∞ l ∧ (∀ y, 0 < l y) ∧
      ∀ y ∈ Y, η/2 < l y ∧ L y-δ < l y ∧ l y < L y := by
  let S : P → Set ℝ := fun y => {r | 0 < r ∧ (y ∈ Y → η/2 < r ∧ L y-δ < r ∧ r < L y)}
  have hs (r : ℝ) : IsOpen {y | r ∈ S y} := by
    by_cases hr : 0 < r
    · have he : {y | r ∈ S y} = Yᶜ ∪ {y | η/2 < r ∧ L y-δ < r ∧ r < L y} := by
        ext y; simp [S,hr,or_iff_not_imp_left]
      rw [he]
      exact hY.isOpen_compl.union ((isOpen_const).inter
        ((isOpen_lt (hL.sub continuous_const) continuous_const).inter
          (isOpen_lt continuous_const hL)))
    · simp [S,hr]
  have hc (y : P) (_ : y ∈ (univ : Set P)) : Convex ℝ (S y) := by
    by_cases hy : y ∈ Y
    · have he : S y = Ioi 0 ∩ (Ioi (η/2) ∩ (Ioi (L y-δ) ∩ Iio (L y))) := by
        ext r; simp [S,hy]
      rw [he]
      exact (convex_Ioi (0:ℝ)).inter ((convex_Ioi _).inter ((convex_Ioi _).inter (convex_Iio _)))
    · have he : S y = Ioi 0 := by ext r; simp [S,hy]
      rw [he]
      exact convex_Ioi (𝕜 := ℝ) (0:ℝ)
  have hn (y : P) (_ : y ∈ (univ : Set P)) : (S y).Nonempty := by
    by_cases hy : y ∈ Y
    · have hm : max (η/2) (L y-δ) < L y := max_lt (by linarith [hLY y hy]) (by linarith)
      obtain ⟨r,hr,hrL⟩ := exists_between hm
      exact ⟨r,by linarith [le_max_left (η/2) (L y-δ)],fun _ =>
        ⟨(le_max_left _ _).trans_lt hr,(le_max_right _ _).trans_lt hr,hrL⟩⟩
    · exact ⟨1,by norm_num,fun h => (hy h).elim⟩
  obtain ⟨l,hl,hlS⟩ := exists_smooth_convex_selection isClosed_univ S hs hc hn
  exact ⟨l,hl,fun y => (hlS y (mem_univ _)).1,fun y hy => (hlS y (mem_univ _)).2 hy⟩

theorem exists_shortening_cutoff {K : Set P} (hK : IsCompact K)
    {L l : P → ℝ} (hL : Continuous L) (hl : Continuous l) {η δ : ℝ}
    (hKbounds : ∀ y ∈ K, η < L y ∧ η/2 < l y ∧ L y-δ < l y ∧ l y < L y) :
    ∃ χ : P → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y, χ y ∈ Icc 0 1) ∧ (∀ y ∈ K, χ y = 1) ∧
      ∀ y ∈ tsupport χ, η < L y ∧ η/2 < l y ∧ L y-δ < l y ∧ l y < L y := by
  let U := {y | η < L y ∧ η/2 < l y ∧ L y-δ < l y ∧ l y < L y}
  have hU : IsOpen U := (isOpen_lt continuous_const hL).inter
    ((isOpen_lt continuous_const hl).inter ((isOpen_lt (hL.sub continuous_const) hl).inter
      (isOpen_lt hl hL)))
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hr⟩ := exists_smooth_cutoff hK hU hKbounds
  refine ⟨χ,hχ,hχc,hr,?_,hχU⟩
  intro y hy
  exact hχ1.self_of_nhdsSet y hy

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem scaledUnitFamily_convex (F : C(P × ℝ,ℝ)) (l : C(P,ℝ)) (y : P) {L : ℝ}
    (hl : 0 ≤ l y) (hlL : l y ≤ L)
    (hF : ConvexOn ℝ (Icc 0 L) (fun v => F (y,v))) :
    ConvexOn ℝ (Icc 0 1) (fun v => scaledUnitFamily F l (y,v)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro u hu v hv a b ha hb hab
  have hmul (w : ℝ) (hw : w ∈ Icc (0:ℝ) 1) : l y*w ∈ Icc (0:ℝ) L :=
    ⟨mul_nonneg hl hw.1,(mul_le_of_le_one_right hl hw.2).trans hlL⟩
  have hh := hF.2 (hmul u hu) (hmul v hv) ha hb hab
  simp only [smul_eq_mul] at hh
  change F (y,l y*(a*u+b*v)) ≤ a*F (y,l y*u)+b*F (y,l y*v)
  have hlin : l y*(a*u+b*v) = a*(l y*u)+b*(l y*v) := by ring
  rw [hlin]
  exact hh

omit [FiniteDimensional ℝ P] in

theorem scaled_trace_inner_estimate (F : C(P × ℝ,ℝ)) (l : C(P,ℝ))
    (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)) {a χ : P → ℝ}
    (y : P) (ha : 0 < a y) (hal : (a y)^2 = l y) (hχ : χ y = 1)
    {ε : ℝ}
    (hΨ : ∀ x ∈ closedRoundDisk (areaRadius 1),
      scaledUnitFamily F l (y,radialArea (Ψ.isotopy.map y 1 x)) ≤
        unitRearrange (scaledUnitFamily F l) (y,radialArea x)+ε)
    (x : Plane) (hx : radialArea x ≤ l y) :
    F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤
      intervalMinimum (fiberFunction F y) (l y) (radialArea x)+ε := by
  have hl : 0 < l y := hal ▸ sq_pos_of_pos ha
  have hs : radialArea ((a y)⁻¹ • x) = radialArea x/l y := by
    rw [radialArea_smul,←hal]
    field_simp
  have hm : (a y)⁻¹ • x ∈ closedRoundDisk (areaRadius 1) := by
    rw [mem_closedRoundDisk_areaRadius (by norm_num),hs]
    exact (div_le_one hl).mpr hx
  have hh := hΨ _ hm
  rw [hs,unitRearrange_scaled F l y hl ⟨radialArea_nonneg x,hx⟩] at hh
  rw [scaledPlanarTrace_time_one Ψ.motion y hχ,radialArea_smul,hal]
  exact hh

theorem exists_scaled_slice_rearrangement {Y : Set P} (hY : IsCompact Y)
    {L : P → ℝ} (hL : Continuous L) (hcL : ConcaveOn ℝ Y L)
    (F : C(P × ℝ,ℝ))
    (hconv : ∀ y ∈ Y, ConvexOn ℝ (Icc 0 (L y)) (fun v => F (y,v)))
    {ε : ℝ} (he : 0 < ε) :
    ∃ (a χ : P → ℝ) (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)),
      ContDiff ℝ ∞ a ∧ (∀ y, 0 < a y) ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ y, χ y ∈ Icc 0 1) ∧
      (∀ y ∈ tsupport χ, (a y)^2 < L y) ∧
      (∀ y ∈ Y, ∀ t x, radialArea x ≤ L y →
        radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L y) ∧
      (∀ y ∈ Y, ∀ x, radialArea x ≤ L y →
        F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤
          intervalMinimum (fiberFunction F y) (L y) (radialArea x)+ε) := by
  obtain ⟨δ,hδ,hm⟩ := exists_uniform_variable_modulus hY hL.continuousOn F (half_pos he)
  let η := δ/4
  have hη : 0 < η := div_pos hδ (by norm_num)
  let A := {y ∈ Y | η ≤ L y}
  have hA : IsCompact A := hY.inter_right (isClosed_le continuous_const hL)
  have hcA : Convex ℝ A := hcL.convex_ge η
  obtain ⟨l,hl,hlpos,hlA⟩ := exists_smooth_positive_shortening hA.isClosed hL hη
    (half_pos hδ) (fun y (hy : y ∈ A) => hy.2)
  let K := {y ∈ Y | 2*η ≤ L y}
  have hK : IsCompact K := hY.inter_right (isClosed_le continuous_const hL)
  have hKA : K ⊆ A := fun y hy => ⟨hy.1,by linarith [hy.2]⟩
  obtain ⟨χ,hχ,hχc,hχrange,hχone,hχfit⟩ := exists_shortening_cutoff hK hL hl.continuous
    (η := η) (δ := δ/2) (by
      intro y hy
      exact ⟨by linarith [hy.2],hlA y (hKA hy)⟩)
  let a := fun y => Real.sqrt (l y)
  have ha : ContDiff ℝ ∞ a := hl.sqrt (fun y => (hlpos y).ne')
  have hapos (y : P) : 0 < a y := Real.sqrt_pos.mpr (hlpos y)
  have hal (y : P) : (a y)^2 = l y := Real.sq_sqrt (hlpos y).le
  let lc : C(P,ℝ) := ⟨l,hl.continuous⟩
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_unit_rearrangement hA hcA (scaledUnitFamily F lc)
    (fun y hy => scaledUnitFamily_convex F lc y (hlpos y).le (hlA y hy).2.2.le
      (hconv y hy.1)) (half_pos he)
  have hfit (y : P) (hy : y ∈ tsupport χ) : (a y)^2 < L y := by
    rw [hal]; exact (hχfit y hy).2.2.2
  have hpres (y : P) (t : ℝ) (x : Plane) (hx : radialArea x ≤ L y) :
      radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L y :=
    scaled_disk_preserves_slice Ψ y (hapos y).ne' t x hx
      (fun h => (hfit y (subset_tsupport χ h)).le)
  refine ⟨a,χ,Ψ,ha,hapos,hχ,hχc,hχrange,hfit,fun y _ => hpres y,?_⟩
  intro y hy x hx
  have hxI : radialArea x ∈ Icc (0:ℝ) (L y) := ⟨radialArea_nonneg x,hx⟩
  by_cases hlarge : 2*η ≤ L y
  · have hyK : y ∈ K := ⟨hy,hlarge⟩
    have hyA : y ∈ A := hKA hyK
    have hm' (s : ℝ) (hs : s ∈ Icc (0:ℝ) (L y)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (L y))
        (hd : |s-t| ≤ L y-l y) : fiberFunction F y s ≤ fiberFunction F y t+ε/2 :=
      (hm y hy s hs t ht (by linarith [(hlA y hyA).2.1])).le
    rcases le_total (radialArea x) (l y) with hinner | houter
    · have hj := scaled_trace_inner_estimate F lc Ψ y (hapos y) (hal y) (hχone y hyK)
        (hΨ y hyA) x hinner
      dsimp only [lc,ContinuousMap.coe_mk] at hj
      have hs := intervalMinimum_shortening (fiberFunction F y) (hlpos y).le
        (hlA y hyA).2.2.le ⟨radialArea_nonneg x,hinner⟩ hm'
      linarith
    · rw [scaled_disk_fixed Ψ y (hapos y).ne' 1 x (by rw [hal]; exact houter)]
      have hs := intervalMinimum_outer_strip (fiberFunction F y) hxI houter hm'
      change F (y,radialArea x) ≤ _ at hs
      linarith
  · have hsmall : L y < 2*η := lt_of_not_ge hlarge
    have hm' (u : ℝ) (hu : u ∈ Icc (0:ℝ) (L y)) (v : ℝ) (hv : v ∈ Icc (0:ℝ) (L y)) :
        fiberFunction F y u ≤ fiberFunction F y v+ε/2 := by
      apply (hm y hy u hu v hv ?_).le
      rw [abs_lt]
      dsimp [η] at hsmall
      constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]
    have hs := intervalMinimum_small (fiberFunction F y) hxI
      ⟨radialArea_nonneg _,hpres y 1 x hx⟩ hm'
    change F (y,radialArea (scaledPlanarTrace Ψ.motion a χ y 1 x)) ≤ _ at hs
    linarith

end
section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def trajectoryAngularSpeed (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (y : ι → ℝ) (x : Plane) (i : ι) (t : ℝ) : ℝ :=
  2*Real.pi*fderiv ℝ Ψ.hamiltonian ((y,t),Ψ.trace y t x) ((Pi.single i 1,0),0)

@[fun_prop] theorem trajectoryAngularSpeed_continuous
    (Ψ : PlanarHamiltonianMotion (ι → ℝ)) (y : ι → ℝ) (x : Plane) (i : ι) :
    Continuous (trajectoryAngularSpeed Ψ y x i) := by
  have hmap : Continuous (fun t : ℝ => Ψ.trace y t x) :=
    Ψ.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hs : ContDiff ℝ ∞ (fun p => fderiv ℝ Ψ.hamiltonian p) :=
    Ψ.smooth.fderiv_right (by simp)
  exact continuous_const.mul ((hs.continuous.comp
    ((continuous_const.prodMk continuous_id).prodMk hmap)).clm_apply continuous_const)

def trajectoryAngle (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (y : ι → ℝ) (x : Plane) (i : ι) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..t, trajectoryAngularSpeed Ψ y x i s

theorem trajectoryAngle_hasDerivAt (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (y : ι → ℝ) (x : Plane) (i : ι) (t : ℝ) :
    HasDerivAt (trajectoryAngle Ψ y x i) (trajectoryAngularSpeed Ψ y x i t) t := by
  have hc := trajectoryAngularSpeed_continuous Ψ y x i
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

def liftedTrajectory (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) : PlanePhase ι := fun i =>
  if i=j then Ψ.trace (outerMoments j z) t (z j)
  else planeRotate (trajectoryAngle Ψ (outerMoments j z) (z j) i t) (z i)

@[simp] theorem liftedTrajectory_inner (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) :
    liftedTrajectory Ψ j z t j = Ψ.trace (outerMoments j z) t (z j) := by
  simp [liftedTrajectory]

@[simp] theorem liftedTrajectory_moments (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) :
    outerMoments j (liftedTrajectory Ψ j z t) = outerMoments j z := by
  funext i
  by_cases hij : i=j
  · subst i; simp
  · simp [outerMoments,liftedTrajectory,hij]

@[simp] theorem liftedTrajectory_zero (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) : liftedTrajectory Ψ j z 0 = z := by
  funext i
  by_cases hij : i=j
  · subst i
    simp [Ψ.zero]
  · simp [liftedTrajectory,hij,trajectoryAngle]

theorem liftedTrajectory_hasDerivAt (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) (t : ℝ) :
    HasDerivAt (liftedTrajectory Ψ j z)
      (hamiltonianField phaseArea (liftedHamiltonian j Ψ.hamiltonian)
        (t,liftedTrajectory Ψ j z t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  rw [liftedHamiltonian_field j Ψ.smooth,liftedTrajectory_moments]
  by_cases hij : i=j
  · subst i
    simp only [ite_true,liftedTrajectory_inner]
    exact Ψ.flow (outerMoments j z) t (z j)
  · rw [ite_eq_right hij]
    have hd := planeRotate_hasDerivAt
      (trajectoryAngle_hasDerivAt Ψ (outerMoments j z) (z j) i t) (z i)
    convert! hd using 1 <;> simp only [liftedAngularSpeed,liftArgument,
      liftedTrajectory_moments,trajectoryAngularSpeed,liftedTrajectory,hij,ite_false,ite_true]

theorem liftedTrajectory_continuous (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (z : PlanePhase ι) : Continuous (liftedTrajectory Ψ j z) :=
  continuous_iff_continuousAt.mpr (fun t => (liftedTrajectory_hasDerivAt Ψ j z t).continuousAt)

theorem exists_lifted_endpoint (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (j : ι) (T : ℝ) : ∃ Φ : PlanePhase ι ≃ₜ PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      HasCompactSupport (fun z => Φ z-z) ∧
      (∀ z v w, phaseArea (fderiv ℝ Φ z v) (fderiv ℝ Φ z w) = phaseArea v w) ∧
      (∀ z, Φ z = liftedTrajectory Ψ j z T) ∧
      (∀ z, outerMoments j (Φ z) = outerMoments j z) ∧
      (∀ z, Φ z j = Ψ.trace (outerMoments j z) T (z j)) := by
  obtain ⟨Φ,hΦ,hΦi,_,hΦc,hΦs,hΦeq⟩ := exists_hamiltonian_endpoint
    phaseArea_isInvertible phaseArea_skew (liftedHamiltonian_smooth j Ψ.smooth)
    (liftedHamiltonian_compact j Ψ.compact) 0 T
  have he (z : PlanePhase ι) : Φ z = liftedTrajectory Ψ j z T := by
    simpa using hΦeq (liftedTrajectory Ψ j z) (liftedTrajectory_continuous Ψ j z)
      (liftedTrajectory_hasDerivAt Ψ j z)
  refine ⟨Φ,hΦ,hΦi,hΦc,hΦs,he,?_,?_⟩
  · intro z; rw [he]; exact liftedTrajectory_moments Ψ j z T
  · intro z; rw [he]; exact liftedTrajectory_inner Ψ j z T

end
section

variable {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem homeomorph_family_inverse_smooth (Φ : Q → E ≃ₜ E)
    (hΦ : ContDiff ℝ ∞ (fun p : Q × E => Φ p.1 p.2))
    (hi : ∀ q, ContDiff ℝ ∞ (Φ q).symm) :
    ContDiff ℝ ∞ (fun p : Q × E => (Φ p.1).symm p.2) := by
  obtain ⟨U,g,_,hg,hU,_,hright⟩ := parametric_inverse_on
    (fun p : Q × E => Φ p.1 p.2) hΦ (D := univ) isOpen_univ
    (fun q _ _ _ _ h => (Φ q).injective h)
    (fun p _ => homeomorph_fderiv_isInvertible (Φ p.1)
      ((hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
      ((hi p.1).differentiable (by simp)) p.2)
  have hUall : U = univ := by
    rw [hU]
    apply eq_univ_of_forall
    intro p
    exact ⟨(p.1,(Φ p.1).symm p.2),mem_univ _,by simp⟩
  have he : g = fun p : Q × E => (Φ p.1).symm p.2 := by
    funext p
    apply (Φ p.1).injective
    rw [Homeomorph.apply_symm_apply]
    exact (hright p (hUall ▸ mem_univ p)).2
  rw [hUall] at hg
  rw [←he]
  exact contDiffOn_univ.mp hg

end
section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem trajectoryAngularSpeed_joint_smooth (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (i : ι) :
    ContDiff ℝ ∞ (fun p : ((ι → ℝ) × Plane) × ℝ =>
      trajectoryAngularSpeed Ψ p.1.1 p.1.2 i p.2) := by
  have hds : ContDiff ℝ ∞ (fun p => fderiv ℝ Ψ.hamiltonian p) :=
    Ψ.smooth.fderiv_right (by simp)
  unfold trajectoryAngularSpeed
  exact contDiff_const.mul ((hds.comp
    ((contDiff_fst.fst.prodMk contDiff_snd).prodMk
      (hΨ.comp ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)))).clm_apply
        contDiff_const)

theorem trajectoryAngle_joint_smooth (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (i : ι) :
    ContDiff ℝ ∞ (fun p : ((ι → ℝ) × Plane) × ℝ =>
      trajectoryAngle Ψ p.1.1 p.1.2 i p.2) :=
  contDiff_parameter_segment_integral (trajectoryAngularSpeed_joint_smooth Ψ hΨ i) 0

theorem liftedTrajectory_joint_smooth (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (j : ι) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => liftedTrajectory Ψ j p.2 p.1) := by
  apply contDiff_pi.mpr
  intro i
  have hm : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => outerMoments j p.2) :=
    (outerMoments_smooth j).comp contDiff_snd
  have hx : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => p.2 j) :=
    (contDiff_apply ℝ Plane j).comp contDiff_snd
  by_cases hij : i=j
  · subst i
    simp only [liftedTrajectory,ite_true]
    convert! hΨ.comp ((hm.prodMk contDiff_fst).prodMk hx) using 1
  · simp only [liftedTrajectory,hij,ite_false]
    have ha : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι =>
        trajectoryAngle Ψ (outerMoments j p.2) (p.2 j) i p.1) := by
      convert! (trajectoryAngle_joint_smooth Ψ hΨ i).comp
        ((hm.prodMk hx).prodMk contDiff_fst) using 1
    have hi : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => p.2 i) :=
      (contDiff_apply ℝ Plane i).comp contDiff_snd
    convert! planeRotate_smooth.comp (ha.prodMk hi) using 1

theorem exists_lifted_isotopy (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (j : ι) :
    ∃ Φ : ℝ → PlanePhase ι ≃ₜ PlanePhase ι,
      ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl _ ∧
      (∀ t z, z ∉ Prod.snd '' tsupport (liftedHamiltonian j Ψ.hamiltonian) → Φ t z = z) ∧
      (∀ t z v w, phaseArea (fderiv ℝ (Φ t) z v) (fderiv ℝ (Φ t) z w) = phaseArea v w) ∧
      (∀ t z, Φ t z = liftedTrajectory Ψ j z t) ∧
      (∀ t z, outerMoments j (Φ t z) = outerMoments j z) ∧
      (∀ t z, Φ t z j = Ψ.trace (outerMoments j z) t (z j)) := by
  have hex (t : ℝ) := exists_hamiltonian_endpoint
    phaseArea_isInvertible phaseArea_skew (liftedHamiltonian_smooth j Ψ.smooth)
    (liftedHamiltonian_compact j Ψ.compact) 0 t
  choose Φ _ hΦi hfix _ hsp hrec using hex
  have he (t : ℝ) (z : PlanePhase ι) : Φ t z = liftedTrajectory Ψ j z t := by
    simpa using hrec t (liftedTrajectory Ψ j z) (liftedTrajectory_continuous Ψ j z)
      (liftedTrajectory_hasDerivAt Ψ j z)
  have hs : ContDiff ℝ ∞ (fun p : ℝ × PlanePhase ι => Φ p.1 p.2) := by
    simpa only [he] using liftedTrajectory_joint_smooth Ψ hΨ j
  refine ⟨Φ,hs,homeomorph_family_inverse_smooth Φ hs hΦi,?_,hfix,hsp,he,?_,?_⟩
  · apply Homeomorph.ext
    intro z
    simpa using he 0 z
  · intro t z; rw [he]; exact liftedTrajectory_moments Ψ j z t
  · intro t z; rw [he]; exact liftedTrajectory_inner Ψ j z t

theorem exists_lifted_isotopy_object (Ψ : PlanarHamiltonianMotion (ι → ℝ))
    (hΨ : ContDiff ℝ ∞ (fun p : ((ι → ℝ) × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2)) (j : ι) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea ι _),
      Φ.hamiltonian = liftedHamiltonian j Ψ.hamiltonian ∧
      (∀ t z, outerMoments j (Φ.map t z) = outerMoments j z) ∧
      (∀ t z, Φ.map t z j = Ψ.trace (outerMoments j z) t (z j)) := by
  obtain ⟨φ,hφ,hφi,hzero,hfix,hsp,he,hm,hj⟩ := exists_lifted_isotopy Ψ hΨ j
  refine ⟨{ map := φ
            smooth := hφ
            inverse_smooth := hφi
            zero := hzero
            hamiltonian := liftedHamiltonian j Ψ.hamiltonian
            hamiltonian_smooth := liftedHamiltonian_smooth j Ψ.smooth
            compact := liftedHamiltonian_compact j Ψ.compact
            flow := ?_
            symplectic := hsp
            fixed := hfix },rfl,hm,hj⟩
  intro t z
  simpa only [he] using liftedTrajectory_hasDerivAt Ψ j z t

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hamiltonianField_zero_off_support (A : E →L[ℝ] E →L[ℝ] ℝ)
    (H : ℝ × E → ℝ) {p : ℝ × E} (hp : p ∉ tsupport H) : hamiltonianField A H p = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hp (hamiltonianField_support A H h))

theorem exists_hamiltonian_support_collar (A : E →L[ℝ] E →L[ℝ] ℝ)
    {H : ℝ × E → ℝ} (hH : HasCompactSupport H) {q : E → ℝ} (hq : Continuous q)
    {c : ℝ} (hbelow : ∀ p ∈ tsupport H, q p.2 < c) :
    ∃ ρ > 0, ∀ t z, c-q z < ρ → hamiltonianField A H (t,z) = 0 := by
  rcases (tsupport H).eq_empty_or_nonempty with he | hn
  · refine ⟨1,zero_lt_one,fun t z _ => hamiltonianField_zero_off_support A H ?_⟩
    simp [he]
  · obtain ⟨p,hp,hmax⟩ := hH.exists_isMaxOn hn (hq.comp continuous_snd).continuousOn
    refine ⟨c-q p.2,sub_pos.mpr (hbelow p hp),?_⟩
    intro t z hz
    apply hamiltonianField_zero_off_support A H
    intro hm
    have hh : q z ≤ q p.2 := hmax hm
    linarith

end

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def weightedMoment (b : ι → ℝ) (z : PlanePhase ι) : ℝ := ∑ i, b i*radialArea (z i)

omit [DecidableEq ι] in
@[fun_prop] theorem weightedMoment_smooth (b : ι → ℝ) : ContDiff ℝ ∞ (weightedMoment b) := by
  unfold weightedMoment
  fun_prop

omit [DecidableEq ι] in
theorem weightedMoment_fderiv (b : ι → ℝ) (z v : PlanePhase ι) :
    fderiv ℝ (weightedMoment b) z v =
      ∑ i, b i*(2*Real.pi*((z i).1*(v i).1+(z i).2*(v i).2)) := by
  have hh (i : ι) := ((radialArea_smooth.differentiable (by simp) (z i)).hasFDerivAt.comp z
    (ContinuousLinearMap.proj i : PlanePhase ι →L[ℝ] Plane).hasFDerivAt).const_mul (b i)
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hh i)
  change fderiv ℝ (fun z => ∑ i, b i*radialArea (z i)) z v = _
  have hd' : HasFDerivAt (fun z : PlanePhase ι => ∑ i, b i*radialArea (z i))
      (∑ i, b i • (fderiv ℝ radialArea (z i)).comp (ContinuousLinearMap.proj i)) z := by
    convert! hd using 1
  rw [hd'.fderiv]
  simp

theorem lifted_field_commutes (j : ι) {B : ((ι → ℝ) × ℝ) × Plane → ℝ}
    (hB : ContDiff ℝ ∞ B) (b : ι → ℝ) (hb : b j=0) (p : ℝ × PlanePhase ι) :
    fderiv ℝ (weightedMoment b) p.2 (hamiltonianField phaseArea (liftedHamiltonian j B) p) = 0 := by
  rw [weightedMoment_fderiv]
  apply Finset.sum_eq_zero
  intro i _
  rw [liftedHamiltonian_field j hB]
  by_cases hi : i=j
  · subst i; simp [hb]
  · simp only [hi,ite_false,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.MomentPolytope
open scoped ContDiff Topology BigOperators
open Set Function
open Hamiltonian
open Comparison

variable {m N : ℕ}

theorem scaled_lift_support_below (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)]
    (Ψ : HamiltonianDiskIsotopyFamily (Moments m) (areaRadius 1))
    {a χ : Moments m → ℝ} (ha : Continuous a) (han : ∀ y, a y ≠ 0)
    (hfit : ∀ y ∈ tsupport χ, (a y)^2 < fullLength b c j y)
    (ν : Active b j) {p : ℝ × PlanePhase (Fin m)}
    (hp : p ∈ tsupport (liftedHamiltonian j (scaledPlanarHamiltonian Ψ.motion a χ))) :
    weightedMoment (b ν) p.2 < c ν := by
  obtain ⟨σ,hσ,hσ1,hs⟩ := Ψ.exists_support_margin
  have hp' := scaledPlanarHamiltonian_support Ψ.motion ha han hs
    (liftedHamiltonian_support_subset j hp)
  have hfit' := hfit (outerMoments j p.2) hp'.1
  have hrad : radialArea (p.2 j) < fullLength b c j (outerMoments j p.2) :=
    hp'.2.trans_lt ((mul_le_of_le_one_left (sq_nonneg _) hσ1.le).trans_lt hfit')
  have he := hrad.trans_le (length_le b c j ν (baseProjection j (outerMoments j p.2)))
  have hh := (lt_div_iff₀ ν.property).mp he
  change radialArea (p.2 j)*b ν j < c ν-∑ i : {i : Fin m // i ≠ j},
    b ν i.val*(baseProjection j (outerMoments j p.2)) i at hh
  rw [weightedMoment,Fintype.sum_eq_add_sum_subtype_ne _ j]
  have heq : ∑ i : {i : Fin m // i ≠ j}, b ν i.val*(baseProjection j (outerMoments j p.2)) i =
      ∑ i : {i : Fin m // i ≠ j}, b ν i.val*radialArea (p.2 i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [baseProjection,i.property]
  rw [heq] at hh
  linarith

theorem scaled_lift_face_collars (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i)
    (Ψ : HamiltonianDiskIsotopyFamily (Moments m) (areaRadius 1))
    {a χ : Moments m → ℝ} (ha : ContDiff ℝ ∞ a) (han : ∀ y, a y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hfit : ∀ y ∈ tsupport χ, (a y)^2 < fullLength b c j y) (ν : Fin N) :
    ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
      fderiv ℝ (weightedMoment (b ν)) z
        (hamiltonianField phaseArea (liftedHamiltonian j (scaledPlanarHamiltonian Ψ.motion a χ)) (t,z)) = 0 := by
  let H := liftedHamiltonian j (scaledPlanarHamiltonian Ψ.motion a χ)
  have hB := scaledPlanarHamiltonian_smooth Ψ.motion ha han hχ
  by_cases hj : 0 < b ν j
  · have hc : IsCompact (tsupport H) := liftedHamiltonian_compact j
      (scaledPlanarHamiltonian_compact Ψ.motion ha.continuous han hχc)
    have hbelow : ∀ p ∈ tsupport H, weightedMoment (b ν) p.2 < c ν := fun p hp =>
      scaled_lift_support_below b c j Ψ ha.continuous han hfit ⟨ν,hj⟩ hp
    obtain ⟨ρ,hρ,hzero⟩ := exists_hamiltonian_support_collar phaseArea hc
      (weightedMoment_smooth (b ν)).continuous hbelow
    refine ⟨ρ,hρ,?_⟩
    intro t z hz
    rw [hzero t z hz,map_zero]
  · have hj0 : b ν j=0 := le_antisymm (not_lt.mp hj) (hb ν j)
    exact ⟨1,zero_lt_one,fun t z _ => lifted_field_commutes j hB (b ν) hj0 (t,z)⟩

theorem exists_cartesian_lifted_rearrangement
    (b : Fin N → Moments m) (c : Fin N → ℝ) (j : Fin m)
    [Nonempty (Active b j)] (hb : ∀ ν i, 0 ≤ b ν i) (hK : IsCompact (region b c))
    (F : C(Moments m,ℝ)) (hF : ConvexOn ℝ (region b c) F) {ε : ℝ} (he : 0 < ε) :
    ∃ Φ : CompactHamiltonianIsotopy (@phaseArea (Fin m) _),
      (∀ t z, Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c) ∧
      (∀ z (hz : z ∈ planeRegion b c), F (planeMoments (Φ.map 1 z)) ≤
        coordRearrange b c j hb (F.restrict (region b c)) ⟨planeMoments z,hz⟩+ε) ∧
      (∀ ν, ∃ ρ > 0, ∀ t z, c ν-weightedMoment (b ν) z < ρ →
        fderiv ℝ (weightedMoment (b ν)) z (hamiltonianField phaseArea Φ.hamiltonian (t,z)) = 0) := by
  obtain ⟨a,χ,Ψ,ha,hapos,hχ,hχc,hχrange,hfit,_,hest⟩ :=
    exists_scaled_slice_rearrangement (fullBase_compact b c j hb hK)
      (continuous_fullLength b c j) (concave_fullLength b c j) (globalSliceFamily F j)
      (globalSliceFamily_convex b c j hb F hF) he
  let B := Ψ.motion.scaled a χ ha (fun y => (hapos y).ne') hχ hχc
  have hBs : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × Plane => B.trace p.1.1 p.1.2 p.2) :=
    scaledPlanarTrace_smooth Ψ.motion Ψ.isotopy.smooth ha (fun y => (hapos y).ne') hχ
  obtain ⟨Φ,hH,hm,hj⟩ := exists_lifted_isotopy_object B hBs j
  have hmem (t : ℝ) (z : PlanePhase (Fin m)) :
      Φ.map t z ∈ planeRegion b c ↔ z ∈ planeRegion b c := by
    rw [planeRegion_mem_iff b c j hb,planeRegion_mem_iff b c j hb,hm,hj]
    apply and_congr_right
    intro _
    exact scaled_disk_slice_iff Ψ (outerMoments j z) (hapos _).ne' t (z j)
      (fun h => (hfit _ (subset_tsupport χ h)).le)
  refine ⟨Φ,hmem,?_,?_⟩
  · intro z hz
    have hzy := (planeRegion_mem_iff b c j hb z).mp hz
    have hh := hest (outerMoments j z) hzy.1 (z j) hzy.2
    have hfiber : fiberFunction (globalSliceFamily F j) (outerMoments j z) =
        fiberFunction (globalSliceFamily F j) (planeMoments z) := by
      apply ContinuousMap.ext
      intro h
      change F (assemble j (baseProjection j (outerMoments j z)) h) =
        F (assemble j (baseProjection j (planeMoments z)) h)
      rw [baseProjection_outerMoments]
    have hlen : fullLength b c j (outerMoments j z) = fullLength b c j (planeMoments z) := by
      unfold fullLength
      rw [baseProjection_outerMoments]
    rw [hfiber,hlen] at hh
    rw [←globalSliceFamily_at_moments F j (Φ.map 1 z),hm,hj,
      coordRearrange_eq_intervalMinimum b c j hb F ⟨planeMoments z,hz⟩]
    exact hh
  · intro ν
    rw [hH]
    exact scaled_lift_face_collars b c j hb Ψ ha (fun y => (hapos y).ne') hχ hχc hfit ν

end PackingSufficiencySupport.MomentPolytope

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hamiltonianField_add (A : E →L[ℝ] E →L[ℝ] ℝ)
    {H G : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (hG : ContDiff ℝ ∞ G) (p : ℝ × E) :
    hamiltonianField A (H+G) p = hamiltonianField A H p+hamiltonianField A G p := by
  simp only [hamiltonianField,formMoserField,spatialDifferential]
  rw [fderiv_add (hH.differentiable (by simp) p) (hG.differentiable (by simp) p)]
  simp only [ContinuousLinearMap.add_comp,map_add,neg_add]

def reparamHamiltonian (H : ℝ × E → ℝ) (a : ℝ → ℝ) (p : ℝ × E) : ℝ :=
  deriv a p.1 * H (a p.1,p.2)

theorem reparamHamiltonian_smooth {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H)
    {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (reparamHamiltonian H a) :=
  (((contDiff_infty_iff_deriv.mp ha).2).comp contDiff_fst).mul
    (hH.comp ((ha.comp contDiff_fst).prodMk contDiff_snd))

omit [NormedSpace ℝ E] in
theorem reparamHamiltonian_compact {H : ℝ × E → ℝ} (hH : HasCompactSupport H)
    (a : ℝ → ℝ) (ha : HasCompactSupport (deriv a)) : HasCompactSupport (reparamHamiltonian H a) := by
  apply HasCompactSupport.intro (ha.prod (hH.image continuous_snd))
  rintro ⟨t,x⟩ hp
  by_contra hn
  have ht : deriv a t ≠ 0 := by intro hz; apply hn; simp [reparamHamiltonian,hz]
  have hx : H (a t,x) ≠ 0 := by intro hz; apply hn; simp [reparamHamiltonian,hz]
  exact hp ⟨subset_closure ht,⟨(a t,x),subset_closure hx,rfl⟩⟩

theorem hamiltonianField_reparam (A : E →L[ℝ] E →L[ℝ] ℝ)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (t : ℝ) (x : E) :
    hamiltonianField A (reparamHamiltonian H a) (t,x) =
      deriv a t • hamiltonianField A H (a t,x) := by
  have hda := (ha.differentiable (by simp) t).hasFDerivAt.comp (t,x)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x)))
  have hdd := (((contDiff_infty_iff_deriv.mp ha).2).differentiable (by simp) t).hasFDerivAt.comp (t,x)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x)))
  have hi := hda.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,x)))
  have hd := hdd.mul ((hH.differentiable (by simp) (a t,x)).hasFDerivAt.comp (t,x) hi)
  change HasFDerivAt (fun p : ℝ × E => deriv a p.1 * H (a p.1,p.2)) _ (t,x) at hd
  have he : spatialDifferential (reparamHamiltonian H a) (t,x) =
      deriv a t • spatialDifferential H (a t,x) := by
    ext v
    unfold spatialDifferential reparamHamiltonian
    rw [hd.fderiv]
    simp
  simp only [hamiltonianField,formMoserField,he,map_smul,smul_neg]

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem hamiltonian_trajectory_fixed {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    {u : ℝ → E} (hu : Continuous u)
    (hud : ∀ s, HasDerivAt u (hamiltonianField A H (s,u s)) s)
    (hx : u 0 ∉ Prod.snd '' tsupport H) (t : ℝ) : u t = u 0 := by
  obtain ⟨Φ,_,_,hfix,_,_,hrec⟩ := exists_hamiltonian_endpoint hA hskew hH hHc 0 t
  have he := hrec u hu hud
  rw [zero_add,hfix _ hx] at he
  exact he.symm

end PackingSufficiencySupport.Hamiltonian
end

end OAI
