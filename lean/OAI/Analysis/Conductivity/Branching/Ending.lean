import Mathlib
import OAI.Analysis.Conductivity.Branching.CascadeWeakEnd

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Real Set Filter Topology MeasureTheory Matrix

def initialConnectorRate (a b K t : ℝ) : ℝ :=
  a+(b-a)*smoothTransition ((t-1)/K)

def initialConnectorProfile (a b K t : ℝ) : ℝ :=
  exp (-(∫ r in (0:ℝ)..t,initialConnectorRate a b K r))

lemma initialConnectorRate_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorRate a b K) := by
  exact contDiff_const.add (contDiff_const.mul (smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const K)))

lemma initialConnectorRate_bounds (a b K t : ℝ) :
    min a b ≤ initialConnectorRate a b K t ∧ initialConnectorRate a b K t ≤ max a b := by
  have h0 := smoothTransition.nonneg ((t-1)/K)
  have h1 := smoothTransition.le_one ((t-1)/K)
  have hamin := min_le_left a b
  have hbmin := min_le_right a b
  have hamax := le_max_left a b
  have hbmax := le_max_right a b
  dsimp only [initialConnectorRate]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hamin) (sub_nonneg.mpr h1),
      mul_nonneg (sub_nonneg.mpr hbmin) h0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hamax) (sub_nonneg.mpr h1),
      mul_nonneg (sub_nonneg.mpr hbmax) h0]

lemma initialConnectorRate_left {a b K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) :
    initialConnectorRate a b K t=a := by
  rw [initialConnectorRate,smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hK.le),mul_zero,add_zero]

lemma initialConnectorRate_right {a b K t : ℝ} (hK : 0 < K) (ht : K+1 ≤ t) :
    initialConnectorRate a b K t=b := by
  rw [initialConnectorRate,smoothTransition.one_of_one_le
    ((le_div_iff₀ hK).mpr (by linarith))]
  ring

lemma initialConnectorRate_deriv (a b K t : ℝ) :
    deriv (initialConnectorRate a b K) t=
      ((b-a)/K)*deriv smoothTransition ((t-1)/K) := by
  have h := ((smoothTransition.contDiff (n:=⊤)).differentiable (by simp) ((t-1)/K)).hasDerivAt
  have hh := ((h.comp t (((hasDerivAt_id t).sub_const 1).div_const K)).const_mul (b-a)).const_add a
  dsimp only [Function.comp_def,id_eq] at hh
  change deriv (fun t => a+(b-a)*smoothTransition ((t-1)/K)) t=_
  rw [hh.deriv]
  ring

lemma exists_initialConnector_length {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ,0 < K ∧ ∀ t,|deriv (initialConnectorRate a b K) t| ≤ (min a b)^2/2 := by
  obtain ⟨M,hM,hbound⟩ := exists_transition_derivative_bound
  let m := min a b
  have hm : 0 < m := lt_min ha hb
  let K := (2* |b-a| *M+1)/m^2
  have hMp : 0 < M := by linarith
  have hK : 0 < K := div_pos (by positivity) (sq_pos_of_pos hm)
  have hKe : K*m^2=2* |b-a| *M+1 := div_mul_cancel₀ _ (pow_ne_zero 2 hm.ne')
  refine ⟨K,hK,?_⟩
  intro t
  rw [initialConnectorRate_deriv,abs_mul,abs_div,abs_of_pos hK]
  calc
    _  ≤  (|b-a|/K)*M := mul_le_mul_of_nonneg_left (hbound _).1 (by positivity)
    _  ≤  m^2/2 := by
      rw [div_mul_eq_mul_div,div_le_iff₀ hK]
      nlinarith

lemma initialConnectorProfile_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorProfile a b K) := by
  let r : SmoothScalar ℝ := ⟨initialConnectorRate a b K,initialConnectorRate_smooth a b K⟩
  exact ((smoothScalar_contDiff (smoothPrimitive r)).neg).exp

lemma initialConnectorProfile_pos (a b K t : ℝ) : 0 < initialConnectorProfile a b K t := exp_pos _

lemma initialConnectorProfile_hasDerivAt (a b K t : ℝ) :
    HasDerivAt (initialConnectorProfile a b K)
      (-initialConnectorRate a b K t*initialConnectorProfile a b K t) t := by
  have hr := (initialConnectorRate_smooth a b K).continuous
  have h := intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable 0 t)
    (hr.stronglyMeasurableAtFilter _ _) hr.continuousAt
  change HasDerivAt (fun t => exp (-(∫ r in (0:ℝ)..t,initialConnectorRate a b K r))) _ t
  exact h.neg.exp.congr_deriv (g':= -initialConnectorRate a b K t*initialConnectorProfile a b K t)
    (by simp only [initialConnectorProfile,Pi.neg_apply]; ring)

lemma initialConnectorProfile_second (a b K t : ℝ) :
    deriv (deriv (initialConnectorProfile a b K)) t=
      ((initialConnectorRate a b K t)^2-deriv (initialConnectorRate a b K) t)*
        initialConnectorProfile a b K t := by
  have he : deriv (initialConnectorProfile a b K)=
      fun t => -initialConnectorRate a b K t*initialConnectorProfile a b K t :=
    funext fun t => (initialConnectorProfile_hasDerivAt a b K t).deriv
  rw [he]
  have h := (((initialConnectorRate_smooth a b K).differentiable (by simp) t).hasDerivAt.neg).mul
    (initialConnectorProfile_hasDerivAt a b K t)
  simp only [Pi.mul_def,Pi.neg_def] at h
  rw [h.deriv]
  ring

def initialConnectorAngular (a b K t : ℝ) : ℝ :=
  (initialConnectorRate a b K t)^2-deriv (initialConnectorRate a b K) t

lemma initialConnectorAngular_smooth (a b K : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (initialConnectorAngular a b K) :=
  ((initialConnectorRate_smooth a b K).pow 2).sub
    (smooth_deriv_infty (initialConnectorRate_smooth a b K))

lemma initialConnectorAngular_bounds {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : ∀ t,|deriv (initialConnectorRate a b K) t| ≤ (min a b)^2/2) (t : ℝ) :
    (min a b)^2/2 ≤ initialConnectorAngular a b K t ∧
      initialConnectorAngular a b K t ≤ (max a b)^2+(min a b)^2/2 := by
  have hm : 0 < min a b := lt_min ha hb
  have hr := initialConnectorRate_bounds a b K t
  have hd' := abs_le.mp (hd t)
  have hrp : 0 ≤ initialConnectorRate a b K t := hm.le.trans hr.1
  have hs1 := sq_le_sq₀ hm.le hrp |>.mpr hr.1
  have hs2 := sq_le_sq₀ hrp (hrp.trans hr.2) |>.mpr hr.2
  constructor <;> dsimp [initialConnectorAngular] <;> nlinarith

lemma initialConnectorProfile_left {a b K t : ℝ} (hK : 0 < K) (ht : t ≤ 1) :
    initialConnectorProfile a b K t=exp (-a*t) := by
  have hi : (∫ r in (0:ℝ)..t,initialConnectorRate a b K r)=a*t := by
    calc
      _=∫ _r in (0:ℝ)..t,a := intervalIntegral.integral_congr (by
        intro r hr
        apply initialConnectorRate_left hK
        exact (le_max_iff.mp hr.2).elim (by intro h; linarith) (by intro h; linarith))
      _=_ := by simp; ring
  rw [initialConnectorProfile,hi]
  congr 1
  ring

lemma initialConnectorProfile_right {a b K t : ℝ} (hK : 0 < K) (ht : K+1 ≤ t) :
    initialConnectorProfile a b K t=
      initialConnectorProfile a b K (K+2)*exp (-b*(t-(K+2))) := by
  have hi : (∫ r in (K+2)..t,initialConnectorRate a b K r)=b*(t-(K+2)) := by
    calc
      _=∫ _r in (K+2)..t,b := intervalIntegral.integral_congr (by
        intro r hr
        exact initialConnectorRate_right hK ((le_min (by linarith) ht).trans hr.1))
      _=_ := by simp; ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((initialConnectorRate_smooth a b K).continuous.intervalIntegrable 0 (K+2))
    ((initialConnectorRate_smooth a b K).continuous.intervalIntegrable (K+2) t)
  rw [hi] at hadd
  unfold initialConnectorProfile
  rw [←hadd,neg_add,exp_add]
  congr 2
  ring

lemma initialConnector_constitution (a b K : ℝ) {i : Fin 3} (hi : i ≠ 0) (x : Coord3) :
    pureModeTensor (initialConnectorAngular a b K (x 0)) i*ᵥ
      (fun j => direction (Pi.single j 1) (pureModeValue (initialConnectorProfile a b K) i) x)=
        potentialCurl (pureModePotential (initialConnectorProfile a b K) i) x := by
  apply pureMode_constitution ((initialConnectorProfile_smooth a b K).differentiable (by simp))
    ((smooth_deriv_infty (initialConnectorProfile_smooth a b K)).differentiable (by simp)) hi
  exact initialConnectorProfile_second a b K (x 0)

end

section
open Real Set Filter Topology MeasureTheory

lemma cascadeProfile_near_start {L K t : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (ht : t∈Icc (-1/4) (1/4)) : cascadeProfile L K t=exp (-t/2) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  rw [cascadeProfile,crossingOn_eq_one hLp (by linarith [ht.1]),
    crossingOff_eq_one hLp (by linarith [ht.2]),one_mul,mul_one,
    connectorProfile_left hK (by linarith [ht.2])]

lemma cascadeProfile_deriv_near_start {L K t : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (ht : t∈Ioo (-1/4) (1/4)) : deriv (cascadeProfile L K) t= -(1/2)*exp (-t/2) := by
  have he : cascadeProfile L K =ᶠ[𝓝 t] fun r => exp (-r/2) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact cascadeProfile_near_start hL hK ⟨hr.1.le,hr.2.le⟩
  rw [he.deriv_eq]
  have hd := (((hasDerivAt_id t).neg).div_const 2).exp
  dsimp only [Pi.neg_apply,id_eq] at hd
  rw [hd.deriv]
  ring

lemma cascadePhase_inactive_start {L K k t : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (ht : k*t ≤ 1/4) {j : ℕ} (hj : j ≠ 0) :
    cascadePhase (cascadeLength L K) k j t  <  -7*L/2 := by
  have hh := cascadePhase_antitone (D:=cascadeLength L K) (k:=k) (t:=t)
    (show k*t ≤ 2*cascadeLength L K by unfold cascadeLength; linarith)
    (show 1 ≤ j by omega)
  change cascadePhase (cascadeLength L K) k j t  ≤  cascadePhase (cascadeLength L K) k 1 t at hh
  rw [show (1:ℕ)=0+1 from rfl,cascadePhase_succ,cascadePhase_zero] at hh
  unfold cascadeLength at *
  linarith

lemma cascadeValue_near_start {L K k : ℝ} (hL : 1 ≤ L) (hK : 0 < K)
    (A : ℝ) (x : Coord3) (hx : k*x 0∈Icc (-1/4) (1/4)) :
    cascadeValue L K k A x=A*exp (-(k*x 0)/2)*cos (k*x 1) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hz : ∀ j : ℕ,j ≠ 0 → cascadeTerm L K k A j x=0 := by
    intro j hj
    rw [cascadeTerm,cascadeProfile_zero_left hLp
      (cascadePhase_inactive_start hL hK hx.2 hj).le,mul_zero,zero_mul]
  rw [cascadeValue,tsum_eq_single 0 hz,cascadeTerm,cascadePhase_zero,
    cascadeProfile_near_start hL hK hx]
  simp [cascadeAxis]

lemma cascadePotential_near_start {L K k : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (hk : k ≠ 0)
    (A : ℝ) (x : Coord3) (hx : k*x 0∈Ioo (-1/4) (1/4)) (i j : Fin 3) :
    cascadePotential L K k A i j x =
      wedgePotential 0 1 (fun y : Coord3 => -(A/2)*exp (-(k*y 0)/2)*sin (k*y 1)) i j x := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hz : ∀ n : ℕ,n ≠ 0 → (A*cascadeRatio L K^n)*
      cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j
        ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n))=0 := by
    intro n hn
    let y := (k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)
    have hy : y 0  <  -7*L/2 := by
      dsimp only [y]
      rw [cascade_dilation_time hk]
      exact cascadePhase_inactive_start hL hK hx.2.le hn
    have hb := cascadeBaseStream_zero (K:=K) hLp (cascadeAxis n) y (Or.inl hy)
    have hc := cascadeCrossStream_zero_left (K:=K) hLp (cascadeAxis n) (cascadeAxis (n+1)) y
      (by linarith)
    change (A*cascadeRatio L K^n)*cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j y=0
    simp [cascadePotentialMother,hb,hc]
  rw [cascadePotential,tsum_eq_single 0 hz]
  have hcenter : cascadeCenter (cascadeLength L K) k 0=0 := by
    ext a
    simp [cascadeCenter]
  simp only [pow_zero,mul_one,hcenter,sub_zero]
  have hc : cascadeCrossStream L K (cascadeAxis 0) (cascadeAxis 1) (k • x)=0 := by
    apply cascadeCrossStream_zero_left hLp
    change k*x 0  <  K+2+L/4
    linarith [hx.2]
  have hb : cascadeBaseStream L K (cascadeAxis 0) (k • x)=
      (-(1/2)*exp (-(k*x 0)/2))*sin (k*x 1) := by
    change deriv (cascadeProfile L K) (k*x 0)*sin (k*x (cascadeAxis 0))=_
    rw [cascadeProfile_deriv_near_start hL hK hx]
    rfl
  unfold cascadePotentialMother
  rw [hc,hb]
  simp only [show cascadeAxis 0=1 from rfl,ite_self,add_zero]
  unfold wedgePotential
  split <;> split <;> ring

end

section
open Set Filter Topology

lemma contDiff_axial_paste {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    {f g : E → F} {t : E → ℝ} {c δ : ℝ}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (ht : Continuous t)
    (hδ : 0 < δ) (he : ∀ x,t x∈Ioo (c-δ) (c+δ) → f x=g x) :
    ContDiff ℝ n (fun x => if t x<c then f x else g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : t x<c
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt ht continuous_const).mem_nhds hx] with y hy
    exact ite_eq_left hy
  · by_cases hx' : c<t x
    · apply hg.contDiffAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const ht).mem_nhds hx'] with y hy
      exact ite_eq_right (not_lt.mpr hy.le)
    · have hxc : t x=c := le_antisymm (le_of_not_gt hx') (le_of_not_gt hx)
      apply hf.contDiffAt.congr_of_eventuallyEq
      filter_upwards [(ht.isOpen_preimage _ isOpen_Ioo).mem_nhds
        (show t x∈Ioo (c-δ) (c+δ) by rw [hxc]; constructor <;> linarith)] with y hy
      split_ifs
      · rfl
      · exact (he y hy).symm

lemma axial_paste_eventually_left {E F : Type*} [TopologicalSpace E]
    {f g : E → F} {t : E → ℝ} {c : ℝ} (ht : Continuous t) {x : E} (hx : t x<c) :
    (fun y => if t y<c then f y else g y)=ᶠ[𝓝 x] f := by
  filter_upwards [(isOpen_lt ht continuous_const).mem_nhds hx] with y hy
  exact ite_eq_left hy

lemma axial_paste_eventually_right {E F : Type*} [TopologicalSpace E]
    {f g : E → F} {t : E → ℝ} {c : ℝ} (ht : Continuous t) {x : E} (hx : c<t x) :
    (fun y => if t y<c then f y else g y)=ᶠ[𝓝 x] g := by
  filter_upwards [(isOpen_lt continuous_const ht).mem_nhds hx] with y hy
  exact ite_eq_right (not_lt.mpr hy.le)

end

section
open Real Set Filter Topology MeasureTheory Matrix

def finiteEndingValue (a J L K : ℝ) (x : Coord3) : ℝ :=
  if x 0<J+2 then pureModeValue (initialConnectorProfile a (1/2) J) 1 x
  else cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2))
    (x-Pi.single 0 (J+2))

def finiteEndingPotential (a J L K : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  if x 0<J+2 then pureModePotential (initialConnectorProfile a (1/2) J) 1 i j x
  else cascadePotential L K 1 (initialConnectorProfile a (1/2) J (J+2)) i j
    (x-Pi.single 0 (J+2))

lemma finiteEnding_value_overlap {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (x : Coord3) (hx : x 0∈Ioo ((J+2)-1/4) ((J+2)+1/4)) :
    pureModeValue (initialConnectorProfile a (1/2) J) 1 x=
      cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2))
        (x-Pi.single 0 (J+2)) := by
  have hs : 1*((x-Pi.single 0 (J+2) : Coord3) 0)∈Icc (-1/4) (1/4) := by
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    constructor <;> linarith [hx.1,hx.2]
  rw [cascadeValue_near_start hL hK _ _ hs,pureModeValue,
    initialConnectorProfile_right hJ (show J+1 ≤ x 0 by linarith [hx.1])]
  simp only [one_mul,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1:Fin 3)≠0 by decide),sub_zero]
  congr 2
  ring_nf

lemma finiteEnding_potential_overlap {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (x : Coord3) (hx : x 0∈Ioo ((J+2)-1/4) ((J+2)+1/4)) (i j : Fin 3) :
    pureModePotential (initialConnectorProfile a (1/2) J) 1 i j x=
      cascadePotential L K 1 (initialConnectorProfile a (1/2) J (J+2)) i j
        (x-Pi.single 0 (J+2)) := by
  have hs : 1*((x-Pi.single 0 (J+2) : Coord3) 0)∈Ioo (-1/4) (1/4) := by
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    constructor <;> linarith [hx.1,hx.2]
  rw [cascadePotential_near_start hL hK (by norm_num) _ _ hs,pureModePotential,
    wedgePotential_as_mul,wedgePotential_as_mul]
  simp only [one_mul,Pi.sub_apply,Pi.single_eq_same,
    Pi.single_eq_of_ne (show (1:Fin 3)≠0 by decide),sub_zero]
  rw [(initialConnectorProfile_hasDerivAt a (1/2) J (x 0)).deriv,
    initialConnectorRate_right hJ (show J+1 ≤ x 0 by linarith [hx.1]),
    initialConnectorProfile_right hJ (show J+1 ≤ x 0 by linarith [hx.1])]
  congr 1
  ring_nf

lemma finiteEndingValue_C2 {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K) :
    ContDiff ℝ 2 (finiteEndingValue a J L K) := by
  apply contDiff_axial_paste (δ:=1/4) ?_ ?_ (continuous_apply 0) (by norm_num)
    (finiteEnding_value_overlap hJ hL hK)
  · have h := (initialConnectorProfile_smooth a (1/2) J).of_le (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast)
    unfold pureModeValue
    exact (h.comp (contDiff_apply ℝ ℝ 0)).mul ((contDiff_apply ℝ ℝ 1).cos)
  · exact (cascadeValue_C2 hL hK (by norm_num : (1:ℝ)≠0) _).comp
      (contDiff_id.sub contDiff_const)

lemma finiteEndingPotential_C2 {a J L K : ℝ} (hJ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (i j : Fin 3) : ContDiff ℝ 2 (finiteEndingPotential a J L K i j) := by
  apply contDiff_axial_paste (δ:=1/4) ?_ ?_ (continuous_apply 0) (by norm_num)
    (fun x hx => finiteEnding_potential_overlap hJ hL hK x hx i j)
  · have h := (smooth_deriv_infty (initialConnectorProfile_smooth a (1/2) J)).of_le
      (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast)
    have hs : ContDiff ℝ 2 (fun x : Coord3 => deriv (initialConnectorProfile a (1/2) J) (x 0)*sin (x 1)) :=
      (h.comp (contDiff_apply ℝ ℝ 0)).mul ((contDiff_apply ℝ ℝ 1).sin)
    unfold pureModePotential wedgePotential
    split <;> split
    · exact hs.sub hs
    · exact hs.sub contDiff_const
    · exact contDiff_const.sub hs
    · exact contDiff_const.sub contDiff_const
  · exact (cascadePotential_C2 hL hK 1 _ i j).comp (contDiff_id.sub contDiff_const)

lemma finiteEndingPotential_antisymm (a J L K : ℝ) (i j : Fin 3) :
    finiteEndingPotential a J L K i j=fun x => -finiteEndingPotential a J L K j i x := by
  funext x
  unfold finiteEndingPotential
  split_ifs
  · unfold pureModePotential wedgePotential
    ring
  · exact congrFun (cascadePotential_antisymm L K 1 _ i j) _

lemma finiteEndingValue_initial {a J L K : ℝ} (hJ : 0 < J) (x : Coord3) (hx : x 0 ≤ 1) :
    finiteEndingValue a J L K x=exp (-a*x 0)*cos (x 1) := by
  rw [finiteEndingValue,ite_eq_left (show x 0<J+2 by linarith),pureModeValue,
    initialConnectorProfile_left hJ hx]

lemma finiteEndingValue_terminal {a J L K : ℝ} (_ : 0 < J) (hL : 1 ≤ L) (hK : 0 < K)
    (x : Coord3) (hx : J+2+2*cascadeLength L K ≤ x 0) : finiteEndingValue a J L K x=0 := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hD := cascade_length_positive hLp hK
  rw [finiteEndingValue,ite_eq_right (show ¬x 0<J+2 by linarith)]
  apply cascadeValue_terminal hLp hK
  simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
  linarith

local instance endingMatrixMeasurableSpace : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance endingMatrixBorelSpace : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

def finiteEndingTensor (a J L K : ℝ) (x : Coord3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if x 0<J+2 then pureModeTensor (initialConnectorAngular a (1/2) J (x 0)) 1
  else cascadeTensor L K 1 (x-Pi.single 0 (J+2))

lemma direction_translate {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (c v x : Coord3) : direction v (fun y => f (y-c)) x=direction v f (x-c) := by
  simpa only [one_mul,one_smul] using direction_dilation hf 1 1 c v x

lemma potentialCurl_translate {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j,Differentiable ℝ (S i j)) (c x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => S i j (y-c)) x i=potentialCurl S (x-c) i := by
  simpa only [one_mul,one_smul] using potentialCurl_dilation hS 1 1 c x i

lemma finiteEndingTensor_measurable (a J L K : ℝ) : Measurable (finiteEndingTensor a J L K) := by
  apply Measurable.ite ((isOpen_lt (continuous_apply 0) continuous_const).measurableSet)
  · have h : Continuous (fun x : Coord3 => pureModeTensor (initialConnectorAngular a (1/2) J (x 0)) 1) := by
      apply continuous_matrix
      intro i j
      unfold pureModeTensor Matrix.diagonal
      simp only [Matrix.of_apply]
      split_ifs
      · exact (initialConnectorAngular_smooth a (1/2) J).continuous.comp (continuous_apply 0)
      all_goals exact continuous_const
    exact h.measurable
  · exact (cascadeTensor_measurable L K 1).comp (by fun_prop)

lemma finiteEndingTensor_symm (a J L K : ℝ) (x : Coord3) :
    (finiteEndingTensor a J L K x).IsSymm := by
  unfold finiteEndingTensor
  split_ifs
  · exact pureModeTensor_symm _ _
  · exact cascadeTensor_symm _ _ _ _

lemma finiteEndingTensor_normal (a J L K : ℝ) (x : Coord3) :
    finiteEndingTensor a J L K x*ᵥPi.single 0 1=Pi.single 0 1 := by
  unfold finiteEndingTensor
  split_ifs
  · exact pureModeTensor_normal (by decide : (1:Fin 3)≠0) _
  · exact cascadeTensor_normal _ _ _ _

lemma finiteEnding_constitution_left (a J L K : ℝ) (x : Coord3) (hx : x 0<J+2) :
    finiteEndingTensor a J L K x*ᵥ(fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      potentialCurl (finiteEndingPotential a J L K) x := by
  have hv : finiteEndingValue a J L K=ᶠ[𝓝 x] pureModeValue (initialConnectorProfile a (1/2) J) 1 :=
    axial_paste_eventually_left (continuous_apply 0) hx
  have hp (i j : Fin 3) : finiteEndingPotential a J L K i j=ᶠ[𝓝 x]
      pureModePotential (initialConnectorProfile a (1/2) J) 1 i j :=
    axial_paste_eventually_left (continuous_apply 0) hx
  have hg : (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      (fun j => direction (Pi.single j 1) (pureModeValue (initialConnectorProfile a (1/2) J) 1) x) :=
    funext fun j => direction_congr_nhds hv _
  rw [finiteEndingTensor,ite_eq_left hx,hg]
  rw [initialConnector_constitution a (1/2) J (by decide)]
  ext i
  exact (potentialCurl_congr_nhds x hp i).symm

lemma finiteEnding_constitution_right {a J L K : ℝ} (_ : 0<J) (hL : 1≤L) (hK : 0<K)
    (x : Coord3) (hx : J+2<x 0)
    (hc : cascadeTensor L K 1 (x-Pi.single 0 (J+2))*ᵥ
      (fun j => direction (Pi.single j 1) (cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)))
        (x-Pi.single 0 (J+2)))=
      cascadeFlux L K 1 (initialConnectorProfile a (1/2) J (J+2)) (x-Pi.single 0 (J+2))) :
    finiteEndingTensor a J L K x*ᵥ(fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      potentialCurl (finiteEndingPotential a J L K) x := by
  have hv : finiteEndingValue a J L K=ᶠ[𝓝 x]
      (fun y => cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)) (y-Pi.single 0 (J+2))) :=
    axial_paste_eventually_right (continuous_apply 0) hx
  have hp (i j : Fin 3) : finiteEndingPotential a J L K i j=ᶠ[𝓝 x]
      (fun y => cascadePotential L K 1 (initialConnectorProfile a (1/2) J (J+2)) i j (y-Pi.single 0 (J+2))) :=
    axial_paste_eventually_right (continuous_apply 0) hx
  have hg : (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
      (fun j => direction (Pi.single j 1) (cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)))
        (x-Pi.single 0 (J+2))) := by
    funext j
    rw [direction_congr_nhds hv _]
    exact direction_translate ((cascadeValue_C2 hL hK (by norm_num) _).differentiable (by norm_num)) _ _ _
  rw [finiteEndingTensor,ite_eq_right (not_lt.mpr hx.le),hg,hc]
  ext i
  rw [potentialCurl_congr_nhds x hp i,potentialCurl_translate
    (fun i j => (cascadePotential_C2 hL hK 1 _ i j).differentiable (by norm_num))]
  rfl

lemma finiteEnding_constitution_ae {a J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3, finiteEndingTensor a J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)=
        potentialCurl (finiteEndingPotential a J L K) x := by
  have he := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 (J+2))).quasiMeasurePreserving.ae
    (cascadeTensor_constitution_ae (lt_of_lt_of_le (by norm_num) hL) hK (by norm_num : (1:ℝ)≠0)
      (initialConnectorProfile a (1/2) J (J+2)))
  simp only [←sub_eq_add_neg] at he
  filter_upwards [he,ae_coord3_ne 0 (J+2)] with x hx hn
  rcases lt_or_gt_of_ne hn with hl|hr
  · exact finiteEnding_constitution_left a J L K x hl
  · apply finiteEnding_constitution_right hJ hL hK x hr (hx ?_)
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    linarith

lemma finiteEndingFlux_C1 {a J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => potentialCurl (finiteEndingPotential a J L K) x i) := by
  apply ContDiff.sum
  intro j _
  exact direction_C1 (finiteEndingPotential_C2 hJ hL hK i j) _

lemma finiteEndingFlux_divergence {a J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3) :
    ∑ i, direction (Pi.single i 1) (fun y => potentialCurl (finiteEndingPotential a J L K) y i) x=0 :=
  antisymmetric_potential_divergence (fun i => Pi.single i 1) (finiteEndingPotential a J L K)
    (finiteEndingPotential_C2 hJ hL hK) (finiteEndingPotential_antisymm a J L K) x

theorem finiteEnding_weak_equation {a J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val) :
    Integrable (fun x => ∑ i, (finiteEndingTensor a J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)) i*
        (smoothDirection (Pi.single i 1) ψ).val x) ∧
    (∫ x, ∑ i, (finiteEndingTensor a J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)) i*
        (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  have he : (fun x => ∑ i, (finiteEndingTensor a J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)) i*
        (smoothDirection (Pi.single i 1) ψ).val x)=ᵐ[volume]
      (fun x => ∑ i, potentialCurl (finiteEndingPotential a J L K) x i*
        (smoothDirection (Pi.single i 1) ψ).val x) := by
    filter_upwards [finiteEnding_constitution_ae hJ hL hK] with x hx
    rw [hx]
  constructor
  · apply Integrable.congr _ he.symm
    apply integrable_finsetSum
    intro i _
    exact ((finiteEndingFlux_C1 hJ hL hK i).continuous.mul
      (smoothScalar_contDiff (smoothDirection (Pi.single i 1) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (Pi.single i 1) hc).mul_left
  · rw [integral_congr_ae he]
    exact C1_divergence_zero_test volume (fun i : Fin 3 => Pi.single i 1)
      (fun i x => potentialCurl (finiteEndingPotential a J L K) x i) (finiteEndingFlux_C1 hJ hL hK)
      (finiteEndingFlux_divergence hJ hL hK) ψ hc

end

open Real Set Filter Topology MeasureTheory Matrix

lemma pureModeTensor_general_bounds {q c C : ℝ} (hc : c≤1) (hC : 1≤C)
    (hcq : c≤q) (hqC : q≤C) (i : Fin 3) (v : Coord3) :
    c*(v ⬝ᵥ v)≤v ⬝ᵥ (pureModeTensor q i*ᵥv) ∧
      v ⬝ᵥ (pureModeTensor q i*ᵥv)≤C*(v ⬝ᵥ v) := by
  rw [pureModeTensor_quadratic]
  simp only [dotProduct,Finset.mul_sum,←sq]
  constructor <;> apply Finset.sum_le_sum <;> intro j _
  · exact mul_le_mul_of_nonneg_right (by split <;> assumption) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (by split <;> assumption) (sq_nonneg _)

theorem exists_finiteEnding_parameters {a : ℝ} (ha : 0<a) :
    ∃ J L K c C : ℝ,0<J ∧ 1≤L ∧ 0<K ∧ 0<c ∧ c≤C ∧
      ∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (finiteEndingTensor a J L K x*ᵥv) ∧
        v ⬝ᵥ (finiteEndingTensor a J L K x*ᵥv)≤C*(v ⬝ᵥ v) := by
  obtain ⟨J,hJ,hd⟩ := exists_initialConnector_length ha (by norm_num : (0:ℝ)<1/2)
  obtain ⟨L,K,hL,hK,hLK⟩ := exists_cascade_parameters
  let c := min (1/8) ((min a (1/2))^2/2)
  let C := max 10 ((max a (1/2))^2+(min a (1/2))^2/2)
  have hmin : 0 < min a (1/2) := lt_min ha (by norm_num)
  have hc : 0<c := lt_min (by norm_num) (div_pos (sq_pos_of_pos hmin) (by norm_num))
  have hc8 : c≤1/8 := min_le_left _ _
  have hcq : c≤(min a (1/2))^2/2 := min_le_right _ _
  have hC10 : 10≤C := le_max_left _ _
  have hCq : (max a (1/2))^2+(min a (1/2))^2/2≤C := le_max_right _ _
  refine ⟨J,L,K,c,C,hJ,hL,hK,hc,by linarith,?_⟩
  intro x v
  unfold finiteEndingTensor
  split_ifs
  · have hq := initialConnectorAngular_bounds ha (by norm_num : (0:ℝ)<1/2) hd (x 0)
    exact pureModeTensor_general_bounds (by linarith) (by linarith) (hcq.trans hq.1) (hq.2.trans hCq) _ _
  · have hb := hLK 1 (x-Pi.single 0 (J+2)) v
    have hv : 0≤v ⬝ᵥ v := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact ⟨(mul_le_mul_of_nonneg_right hc8 hv).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right hC10 hv)⟩

theorem positive_rate_finite_ending {a : ℝ} (ha : 0<a) :
    ∃ J L K T c C : ℝ,0<J ∧ 1≤L ∧ 0<K ∧ 1<T ∧ 0<c ∧ c≤C ∧
      ContDiff ℝ 2 (finiteEndingValue a J L K) ∧
      (∀ x v : Coord3,c*(v ⬝ᵥ v)≤v ⬝ᵥ (finiteEndingTensor a J L K x*ᵥv) ∧
        v ⬝ᵥ (finiteEndingTensor a J L K x*ᵥv)≤C*(v ⬝ᵥ v)) ∧
      (∀ x : Coord3,x 0≤1 → finiteEndingValue a J L K x=exp (-a*x 0)*cos (x 1)) ∧
      (∀ x : Coord3,T≤x 0 → finiteEndingValue a J L K x=0) ∧
      (∀ x : Coord3,finiteEndingTensor a J L K x*ᵥPi.single 0 1=Pi.single 0 1) ∧
      ∀ (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
        Integrable (fun x => ∑ i, (finiteEndingTensor a J L K x*ᵥ
          (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)) i*
            (smoothDirection (Pi.single i 1) ψ).val x) ∧
        (∫ x, ∑ i, (finiteEndingTensor a J L K x*ᵥ
          (fun j => direction (Pi.single j 1) (finiteEndingValue a J L K) x)) i*
            (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  obtain ⟨J,L,K,c,C,hJ,hL,hK,hc,hcC,hbound⟩ := exists_finiteEnding_parameters ha
  have hD := cascade_length_positive (lt_of_lt_of_le (by norm_num) hL) hK
  exact ⟨J,L,K,J+2+2*cascadeLength L K,c,C,hJ,hL,hK,by linarith,hc,hcC,
    finiteEndingValue_C2 hJ hL hK,hbound,finiteEndingValue_initial hJ,
    finiteEndingValue_terminal hJ hL hK,finiteEndingTensor_normal a J L K,
    finiteEnding_weak_equation hJ hL hK⟩

end ScalarConductivity

end

end OAI
