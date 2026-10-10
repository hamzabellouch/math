import Mathlib
import OAI.Geometry.BallPacking.Fredholm.SurjectiveParametricReduction

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology
open Set Function Filter
variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [MetricSpace Z]

def cappedTime (N j : ℕ) (t : ℝ) : ℝ := min t ((j:ℝ)/N)

lemma cappedTime_continuous (N j : ℕ) : Continuous (cappedTime N j) :=
  continuous_id.min continuous_const

lemma cappedTime_mem (N j : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    cappedTime N j t∈Icc (0:ℝ) 1 :=
  ⟨le_min ht.1 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),(min_le_left _ _).trans ht.2⟩

lemma cappedTime_zero (N : ℕ) {t : ℝ} (ht : 0≤t) : cappedTime N 0 t=0 := by
  simp only [cappedTime,Nat.cast_zero,zero_div,min_eq_right ht]

lemma cappedTime_last {N : ℕ} (hN : 0<N) {t : ℝ} (ht : t≤1) : cappedTime N N t=t := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  simp only [cappedTime,div_self hNr,min_eq_left ht]

lemma cappedTime_step (N j : ℕ) (t : ℝ) :
    dist (cappedTime N j t) (cappedTime N (j+1) t)≤1/(N:ℝ) := by
  have hN : (0:ℝ)≤N := Nat.cast_nonneg N
  have hi : (j:ℝ)/(N:ℝ)≤(j+1:ℕ)/(N:ℝ) := div_le_div_of_nonneg_right (by norm_num) hN
  have hmono : cappedTime N j t≤cappedTime N (j+1) t := min_le_min_left t hi
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hmono)]
  change -(min t ((j:ℝ)/N)-min t ((j+1:ℕ)/N))≤_
  have hg : (j+1:ℕ)/(N:ℝ)=(j:ℝ)/(N:ℝ)+1/(N:ℝ) := by rw [Nat.cast_add,Nat.cast_one,add_div]
  rw [hg]
  have hnon : 0≤1/(N:ℝ) := div_nonneg zero_le_one hN
  by_cases hj : t≤(j:ℝ)/(N:ℝ)
  · rw [min_eq_left hj,min_eq_left (hj.trans (le_add_of_nonneg_right hnon))]
    linarith
  · have hj' := le_of_not_ge hj
    rw [min_eq_right hj']
    have hh := min_le_right t ((j:ℝ)/N+1/(N:ℝ))
    linarith

def projectionTimeChain (P : ℝ × Z → X →L[ℝ] X) (N : ℕ) : ℕ → (ℝ × Z) → X →L[ℝ] X
  | 0,_ => 1
  | j+1,v => projectionTransport (P (cappedTime N j v.1,v.2))
      (P (cappedTime N (j+1) v.1,v.2))*projectionTimeChain P N j v

lemma projectionTimeChain_continuousOn {P : ℝ × Z → X →L[ℝ] X} {K : Set Z}
    (hP : ContinuousOn P (Icc (0:ℝ) 1 ×ˢ K)) (N j : ℕ) :
    ContinuousOn (projectionTimeChain P N j) (Icc (0:ℝ) 1 ×ˢ K) := by
  induction j with
  | zero => exact continuousOn_const
  | succ j ih =>
    apply ContinuousOn.mul _ ih
    apply projectionTransport_continuousOn
    · exact hP.comp (((cappedTime_continuous N j).comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun v hv => ⟨cappedTime_mem N j hv.1,hv.2⟩)
    · exact hP.comp (((cappedTime_continuous N (j+1)).comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun v hv => ⟨cappedTime_mem N (j+1) hv.1,hv.2⟩)

omit [MetricSpace Z] in
lemma projectionTimeChain_intertwines [MetricSpace Z] {P : ℝ × Z → X →L[ℝ] X} {K : Set Z}
    (hp : ∀ v∈Icc (0:ℝ) 1 ×ˢ K,P v*P v=P v) (N j : ℕ)
    {v : ℝ × Z} (hv : v∈Icc (0:ℝ) 1 ×ˢ K) :
    projectionTimeChain P N j v*P (0,v.2)=P (cappedTime N j v.1,v.2)*projectionTimeChain P N j v := by
  induction j with
  | zero => simp only [projectionTimeChain,one_mul,mul_one,cappedTime_zero N hv.1.1]
  | succ j ih =>
    rw [projectionTimeChain,mul_assoc,ih,←mul_assoc,
      projectionTransport_intertwines (hp (cappedTime N j v.1,v.2) ⟨cappedTime_mem N j hv.1,hv.2⟩)
        (hp (cappedTime N (j+1) v.1,v.2) ⟨cappedTime_mem N (j+1) hv.1,hv.2⟩),mul_assoc]

omit [CompleteSpace X] in
lemma projectionTimeChain_invertible [CompleteSpace X] {P : ℝ × Z → X →L[ℝ] X} {K : Set Z} {δ : ℝ}
    (hs : ∀ z∈Icc (0:ℝ) 1 ×ˢ K,∀ w∈Icc (0:ℝ) 1 ×ˢ K,dist z w<δ →
      (projectionTransport (P z) (P w)).IsInvertible)
    {N : ℕ} (hN : 1/(N:ℝ)<δ) (j : ℕ) {v : ℝ × Z} (hv : v∈Icc (0:ℝ) 1 ×ˢ K) :
    (projectionTimeChain P N j v).IsInvertible := by
  induction j with
  | zero => exact ⟨ContinuousLinearEquiv.refl ℝ X,rfl⟩
  | succ j ih =>
    change (projectionTransport _ _ * _).IsInvertible
    apply ContinuousLinearMap.IsInvertible.comp _ ih
    apply hs (cappedTime N j v.1,v.2) ⟨cappedTime_mem N j hv.1,hv.2⟩
      (cappedTime N (j+1) v.1,v.2) ⟨cappedTime_mem N (j+1) hv.1,hv.2⟩
    simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)] using (cappedTime_step N j v.1).trans_lt hN

lemma compact_projection_time_transport {P : ℝ × Z → X →L[ℝ] X} {K : Set Z}
    (hK : IsCompact K) (hP : ContinuousOn P (Icc (0:ℝ) 1 ×ˢ K))
    (hp : ∀ v∈Icc (0:ℝ) 1 ×ˢ K,P v*P v=P v) :
    ∃ T : (ℝ × Z) → X →L[ℝ] X,ContinuousOn T (Icc (0:ℝ) 1 ×ˢ K) ∧
      ∀ v∈Icc (0:ℝ) 1 ×ˢ K,(T v).IsInvertible ∧ T v*P (0,v.2)=P v*T v := by
  obtain ⟨δ,hδ,hstep⟩ := compact_projection_transport (isCompact_Icc.prod hK) hP hp
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hδ
  let M := N+1
  have hM : 0<M := Nat.succ_pos N
  have hNM : 1/(M:ℝ)<δ := by simpa only [M,Nat.cast_add,Nat.cast_one] using hN
  refine ⟨projectionTimeChain P M M,projectionTimeChain_continuousOn hP M M,?_⟩
  intro v hv
  refine ⟨projectionTimeChain_invertible hstep hNM M hv,?_⟩
  simpa only [cappedTime_last hM hv.1.2,Prod.mk.eta] using projectionTimeChain_intertwines hp M M hv


def cappedTimeMap (N j : ℕ) (v : ℝ × Z) : ℝ × Z := (cappedTime N j v.1,v.2)

lemma cappedTimeMap_continuous (N j : ℕ) : Continuous (cappedTimeMap (Z := Z) N j) :=
  ((cappedTime_continuous N j).comp continuous_fst).prodMk continuous_snd

def gridDomain (V : Set (ℝ × Z)) (N : ℕ) : Set (ℝ × Z) :=
  V ∩ (fun v : ℝ × Z => (0,v.2)) ⁻¹' V ∩ ⋂ j : Fin (N+1),cappedTimeMap N j.val ⁻¹' V

lemma gridDomain_open {V : Set (ℝ × Z)} (hV : IsOpen V) (N : ℕ) : IsOpen (gridDomain V N) :=
  (hV.inter (hV.preimage (continuous_const.prodMk continuous_snd))).inter
    (isOpen_iInter_of_finite (fun j => hV.preimage (cappedTimeMap_continuous N j.val)))

omit [MetricSpace Z] in
lemma gridDomain_time_mem [MetricSpace Z] {V : Set (ℝ × Z)} {N j : ℕ} (hj : j≤N)
    {v : ℝ × Z} (hv : v∈gridDomain V N) : cappedTimeMap N j v∈V :=
  mem_iInter.mp hv.2 ⟨j,Nat.lt_succ_of_le hj⟩

omit [MetricSpace Z] in
lemma gridDomain_contains [MetricSpace Z] {V : Set (ℝ × Z)} {K : Set Z}
    (hVK : Icc (0:ℝ) 1 ×ˢ K⊆V) (N : ℕ) :
    Icc (0:ℝ) 1 ×ˢ K⊆gridDomain V N := by
  intro v hv
  refine ⟨⟨hVK hv,hVK ⟨by constructor <;> norm_num,hv.2⟩⟩,mem_iInter.mpr ?_⟩
  intro j
  exact hVK ⟨cappedTime_mem N j.val hv.1,hv.2⟩

lemma projectionTimeChain_continuousOn_grid {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hP : ContinuousOn P V) (N j : ℕ) (hj : j≤N) :
    ContinuousOn (projectionTimeChain P N j) (gridDomain V N) := by
  induction j with
  | zero => exact continuousOn_const
  | succ j ih =>
    apply ContinuousOn.mul _ (ih (Nat.le_trans (Nat.le_succ j) hj))
    apply projectionTransport_continuousOn
    · exact hP.comp (cappedTimeMap_continuous N j).continuousOn
        (fun v hv => gridDomain_time_mem (Nat.le_trans (Nat.le_succ j) hj) hv)
    · exact hP.comp (cappedTimeMap_continuous N (j+1)).continuousOn
        (fun v hv => gridDomain_time_mem hj hv)

lemma projectionTimeChain_intertwines_grid {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hp : ∀ v∈V,P v*P v=P v) (N j : ℕ) (hj : j≤N)
    {v : ℝ × Z} (hv : v∈gridDomain V N) :
    projectionTimeChain P N j v*P (cappedTimeMap N 0 v)=
      P (cappedTimeMap N j v)*projectionTimeChain P N j v := by
  induction j with
  | zero => simp only [projectionTimeChain,one_mul,mul_one]
  | succ j ih =>
    have hj' : j≤N := Nat.le_trans (Nat.le_succ j) hj
    change (projectionTransport (P (cappedTimeMap N j v)) (P (cappedTimeMap N (j+1) v))*
      projectionTimeChain P N j v)*P (cappedTimeMap N 0 v)=_
    rw [mul_assoc,ih hj',←mul_assoc,
      projectionTransport_intertwines (hp _ (gridDomain_time_mem hj' hv))
        (hp _ (gridDomain_time_mem hj hv)),mul_assoc]
    rfl

def extendedTimeTransport (P : ℝ × Z → X →L[ℝ] X) (N : ℕ) (v : ℝ × Z) : X →L[ℝ] X :=
  projectionTransport (P (cappedTimeMap N N v)) (P v)*projectionTimeChain P N N v*
    projectionTransport (P (0,v.2)) (P (cappedTimeMap N 0 v))

lemma extendedTimeTransport_continuousOn {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hP : ContinuousOn P V) (N : ℕ) : ContinuousOn (extendedTimeTransport P N) (gridDomain V N) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact projectionTransport_continuousOn
        (hP.comp (cappedTimeMap_continuous N N).continuousOn (fun v hv => gridDomain_time_mem le_rfl hv))
        (hP.mono (fun v hv => hv.1.1))
    · exact projectionTimeChain_continuousOn_grid hP N N le_rfl
  · exact projectionTransport_continuousOn
      (hP.comp (continuous_const.prodMk continuous_snd).continuousOn (fun v hv => hv.1.2))
      (hP.comp (cappedTimeMap_continuous N 0).continuousOn (fun v hv => gridDomain_time_mem (Nat.zero_le N) hv))

lemma extendedTimeTransport_intertwines {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hp : ∀ v∈V,P v*P v=P v) (N : ℕ) {v : ℝ × Z} (hv : v∈gridDomain V N) :
    extendedTimeTransport P N v*P (0,v.2)=P v*extendedTimeTransport P N v := by
  have h0 : P (0,v.2)*P (0,v.2)=P (0,v.2) := hp _ hv.1.2
  have hvp := hp v hv.1.1
  have hs := hp _ (gridDomain_time_mem (Nat.zero_le N) hv)
  have hf := hp _ (gridDomain_time_mem (N := N) le_rfl hv)
  unfold extendedTimeTransport
  rw [mul_assoc,projectionTransport_intertwines h0 hs,←mul_assoc, mul_assoc
    (projectionTransport _ _) (projectionTimeChain P N N v),
    projectionTimeChain_intertwines_grid hp N N le_rfl hv,←mul_assoc
      (projectionTransport _ _),projectionTransport_intertwines hf hvp]
  simp only [mul_assoc]

omit [MetricSpace Z] in
lemma extendedTimeTransport_eq_chain [MetricSpace Z] {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hp : ∀ v∈V,P v*P v=P v) {N : ℕ} (hN : 0<N) {v : ℝ × Z}
    (ht : v.1∈Icc (0:ℝ) 1) (hv : v∈gridDomain V N) :
    extendedTimeTransport P N v=projectionTimeChain P N N v := by
  have h0 : P (0,v.2)*P (0,v.2)=P (0,v.2) := hp _ hv.1.2
  have hvp := hp v hv.1.1
  simp only [extendedTimeTransport,cappedTimeMap,cappedTime_last hN ht.2,
    cappedTime_zero N ht.1,Prod.mk.eta,projectionTransport_self hvp,projectionTransport_self h0,one_mul,mul_one]

lemma compact_kernel_transport_neighborhood {V : Set (ℝ × Z)} {K : Set Z}
    {P : ℝ × Z → X →L[ℝ] X} (hK : IsCompact K) (hV : IsOpen V)
    (hVK : Icc (0:ℝ) 1 ×ˢ K⊆V) (hP : ContinuousOn P V) (hp : ∀ v∈V,P v*P v=P v) :
    ∃ W : Set (ℝ × Z),IsOpen W ∧ Icc (0:ℝ) 1 ×ˢ K⊆W ∧ W⊆V ∧
      (∀ v∈W,(0,v.2)∈V) ∧ ∃ T : ℝ × Z → X →L[ℝ] X,ContinuousOn T W ∧
        ∀ v∈W,(T v).IsInvertible ∧ T v*P (0,v.2)=P v*T v := by
  obtain ⟨δ,hδ,hstep⟩ := compact_projection_transport (isCompact_Icc.prod hK) (hP.mono hVK)
    (fun v hv => hp v (hVK hv))
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hδ
  let M := N+1
  have hM : 0<M := Nat.succ_pos N
  have hNM : 1/(M:ℝ)<δ := by simpa only [M,Nat.cast_add,Nat.cast_one] using hN
  let T := extendedTimeTransport P M
  let G := gridDomain V M
  have hGs : IsOpen G := gridDomain_open hV M
  have hGc : Icc (0:ℝ) 1 ×ˢ K⊆G := gridDomain_contains hVK M
  have hT : ContinuousOn T G := extendedTimeTransport_continuousOn hP M
  let W := G ∩ T ⁻¹' {L : X →L[ℝ] X | L.IsInvertible}
  have hW : IsOpen W := hT.isOpen_inter_preimage hGs ContinuousLinearEquiv.isOpen
  refine ⟨W,hW,?_,(fun v hv => hv.1.1.1),(fun v hv => hv.1.1.2),T,hT.mono inter_subset_left,?_⟩
  · intro v hv
    refine ⟨hGc hv,?_⟩
    change (extendedTimeTransport P M v).IsInvertible
    rw [extendedTimeTransport_eq_chain hp hM hv.1 (hGc hv)]
    exact projectionTimeChain_invertible hstep hNM M hv
  · intro v hv
    exact ⟨hv.2,extendedTimeTransport_intertwines hp M hv.1⟩


end
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma pathSpatialDerivative_initial {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F)
    {L : X ≃L[ℝ] Y} (hL : ∀ x,F (0,x)=L x) (x : X) :
    pathSpatialDerivative F (0,x)=L.toContinuousLinearMap := by
  rw [pathSpatialDerivative_eq hF]
  have he : (fun y => F (0,y))=L := funext hL
  rw [he]
  exact L.hasFDerivAt.fderiv

def initialKernelGraph (L : X ≃L[ℝ] Y) (E : Submodule ℝ Y) : E →L[ℝ] (X × E) :=
  (-(L.symm.toContinuousLinearMap.comp E.subtypeL)).prod (ContinuousLinearMap.id ℝ E)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma initialKernelGraph_apply [CompleteSpace X] [CompleteSpace Y]
    (L : X ≃L[ℝ] Y) (E : Submodule ℝ Y) (e : E) :
    initialKernelGraph L E e=(-L.symm (e:Y),e) := rfl

lemma initialKernelGraph_kernel {L : X ≃L[ℝ] Y} {E : Submodule ℝ Y} (v : X × E) :
    L v.1+(v.2:Y)=0 ↔ initialKernelGraph L E v.2=v := by
  constructor
  · intro hv
    rw [initialKernelGraph_apply]
    refine Prod.ext ?_ (rfl : (v.2:E)=v.2)
    change -L.symm (v.2:Y)=v.1
    apply L.injective
    rw [map_neg,L.apply_symm_apply]
    exact (eq_neg_of_add_eq_zero_left hv).symm
  · intro hv
    rw [←hv]
    simp only [initialKernelGraph_apply,map_neg,L.apply_symm_apply,neg_add_cancel]

omit [CompleteSpace X] in
lemma projection_fixed_iff_range [CompleteSpace X] {Q : X →L[ℝ] X} (hQ : Q.comp Q=Q) (x : X) :
    Q x=x ↔ x∈Q.range := by
  constructor
  · intro hx; exact ⟨x,hx⟩
  · rintro ⟨y,rfl⟩
    exact congrArg (fun A : X →L[ℝ] X => A y) hQ

structure StabilizedKernelFrame (F : ℝ × X → Y) (E : Submodule ℝ Y)
    (V : Set (ℝ × X)) where
  frame : (ℝ × X) → E →L[ℝ] (X × E)
  coordinate : (ℝ × X) → (X × E) →L[ℝ] E
  frame_continuous : ContinuousOn frame V
  coordinate_continuous : ContinuousOn coordinate V
  kernel : ∀ v∈V,∀ e : E,((pathSpatialDerivative F v).coprod E.subtypeL) (frame v e)=0
  left_inv : ∀ v∈V,∀ e : E,coordinate v (frame v e)=e
  right_inv : ∀ v∈V,∀ w : X × E,((pathSpatialDerivative F v).coprod E.subtypeL) w=0 →
    frame v (coordinate v w)=w

lemma ProperIndexZeroPath.stabilized_kernel_frame {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ K : Set X,IsCompact K ∧ K⊆U ∧ (0:X)∈K ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →x∈K) ∧
      ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
        ∃ V : Set (ℝ × X),IsOpen V ∧ Icc (0:ℝ) 1 ×ˢ K⊆V ∧
          (∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) ∧
          Nonempty (StabilizedKernelFrame F E V) := by
  obtain ⟨K,hK,hKU,h0K,hZ,E,hE,V,hVo,hKV,P,hP,hproj⟩ := h.cylinder_kernel_projection
  let := hE
  have hp : ∀ v∈V,P v*P v=P v := fun v hv => (hproj v hv).2.1
  obtain ⟨W,hWo,hKW,hWV,hW0,T,hT,hTi⟩ := compact_kernel_transport_neighborhood hK hVo hKV hP hp
  obtain ⟨L,hL⟩ := h.initial
  let B := initialKernelGraph L E
  have hB (e : E) : L (B e).1+((B e).2:Y)=0 := by
    simp only [B,initialKernelGraph_apply,map_neg,L.apply_symm_apply,neg_add_cancel]
  have hPf {v : ℝ × X} (hv : v∈V) (w : X × E) :
      P v w=w ↔ ((pathSpatialDerivative F v).coprod E.subtypeL) w=0 := by
    rw [projection_fixed_iff_range (hproj v hv).2.1,(hproj v hv).2.2]
    rfl
  have hP0 {v : ℝ × X} (hv : v∈W) (e : E) : P (0,v.2) (B e)=B e := by
    apply (hPf (hW0 v hv) (B e)).mpr
    rw [pathSpatialDerivative_initial h.smooth hL]
    exact hB e
  let Q : (ℝ × X) → E →L[ℝ] (X × E) := fun v => (T v).comp B
  let C : (ℝ × X) → (X × E) →L[ℝ] E := fun v =>
    (ContinuousLinearMap.snd ℝ X E).comp (T v).inverse
  have hcT : ContinuousOn (fun v => (T v).inverse) W := by
    intro v hv
    exact ((hTi v hv).1.contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt (hT v hv)
  refine ⟨K,hK,hKU,h0K,hZ,E,hE,W,hWo,hKW,(fun v hv => (hproj v (hWV hv)).1),⟨{
    frame := Q
    coordinate := C
    frame_continuous := hT.clm_comp continuousOn_const
    coordinate_continuous := continuousOn_const.clm_comp hcT
    kernel := ?_
    left_inv := ?_
    right_inv := ?_ }⟩⟩
  · intro v hv e
    apply (hPf (hWV hv) (Q v e)).mp
    have hh := congrArg (fun A : (X × E) →L[ℝ] (X × E) => A (B e)) (hTi v hv).2
    change T v (P (0,v.2) (B e))=P v (T v (B e)) at hh
    rw [hP0 hv e] at hh
    exact hh.symm
  · intro v hv e
    change ((T v).inverse (T v (B e))).2=e
    rw [(hTi v hv).1.inverse_apply_self]
    rfl
  · intro v hv w hw
    have hPw := (hPf (hWV hv) w).mpr hw
    have hTiw := (hTi v hv).1.self_apply_inverse w
    have hh := congrArg (fun A : (X × E) →L[ℝ] (X × E) => A ((T v).inverse w)) (hTi v hv).2
    change T v (P (0,v.2) ((T v).inverse w))=P v (T v ((T v).inverse w)) at hh
    rw [hTiw,hPw] at hh
    have hp0 : P (0,v.2) ((T v).inverse w)=(T v).inverse w :=
      (hTi v hv).1.injective (hh.trans hTiw.symm)
    have hk0 := (hPf (hW0 v hv) ((T v).inverse w)).mp hp0
    rw [pathSpatialDerivative_initial h.smooth hL] at hk0
    have hb0 := (initialKernelGraph_kernel ((T v).inverse w)).mp hk0
    change T v (B (((T v).inverse w).2))=w
    rw [show B (((T v).inverse w).2)=(T v).inverse w from hb0]
    exact hTiw



end HigherDimensionalBallPacking.Rigidity
end

end OAI
