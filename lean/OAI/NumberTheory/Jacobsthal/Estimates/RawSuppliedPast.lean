import OAI.NumberTheory.Jacobsthal.Paths.RawStableHistory
import OAI.NumberTheory.Jacobsthal.Probability.ArrivalKernelGeometry

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

variable (F : CostState → ℝ) (hF : Measurable F)
variable (hStep : ∀ z, ∀ᵐ y ∂costKernel z, F z ≤ F y)

noncomputable def scalarHistory (b : ℕ) (h : RawHistory b) : RawHistory b := fun i => ((h i).1,F (h i))
include hF in
lemma scalarHistory_measurable (b : ℕ) : Measurable (scalarHistory F b) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_fst.comp (measurable_pi_apply i)).prodMk (hF.comp (measurable_pi_apply i)))

noncomputable def scalarIncreasing (a b : ℕ) : Set (RawHistory b) :=
  scalarHistory F b ⁻¹' increasingCosts a b

include hF in
lemma scalarIncreasing_measurable (a b : ℕ) : MeasurableSet (scalarIncreasing F a b) :=
  (increasingCosts_measurable a b).preimage (scalarHistory_measurable F hF b)

include hF hStep in
lemma rawExtension_scalar_step (k : ℕ) (h : RawHistory k) :
    ∀ᵐ y ∂rawExtension k (k+1) h,
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (rawLast (k+1) y) := by
  have hs : ∀ᵐ y ∂rawExtension k (k+1) h, F (rawLast k h) ≤ F (rawLast (k+1) y) := by
    apply (ae_map_iff (rawLast_measurable (k+1)).aemeasurable
      (measurableSet_le measurable_const hF)).mp
    rw [rawExtension_last_step]
    exact hStep _
  filter_upwards [hs,rawExtension_retains_prefix (show k ≤ k+1 by omega) h] with y hy hp
  have he := congrFun hp (⟨k,by simp⟩ : Finset.Iic k)
  change y ⟨k,_⟩=rawLast k h at he
  rw [he]
  exact hy

include hF hStep in
lemma rawExtension_scalar_coordinate {a b k : ℕ} (hak : a ≤ k) (hkb : k < b) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h,
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (y ⟨k+1,Finset.mem_Iic.mpr (by omega)⟩) := by
  have hm : MeasurableSet {y : RawHistory (k+1) |
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (rawLast (k+1) y)} :=
    measurableSet_le (hF.comp (measurable_pi_apply _)) (hF.comp (rawLast_measurable _))
  have he : (rawExtension a b h).map (rawPrefix (show k+1 ≤ b by omega))=rawExtension a (k+1) h :=
    Kernel.partialTraj_map_frestrictLe₂_apply (X := fun _ => CostState) (κ := historyKernel) h (show k+1 ≤ b by omega)
  have ht : ∀ᵐ y ∂rawExtension a (k+1) h,
      F (y ⟨k,Finset.mem_Iic.mpr (by omega)⟩) ≤ F (rawLast (k+1) y) := by
    have hc : rawExtension a (k+1)=rawExtension k (k+1) ∘ₖ rawExtension a k :=
      (Kernel.partialTraj_comp_partialTraj hak (by omega)).symm
    rw [hc]
    exact Kernel.ae_comp_of_ae_ae hm (Eventually.of_forall (rawExtension_scalar_step F hF hStep k))
  rw [← he] at ht
  exact (ae_map_iff (rawPrefix_measurable (show k+1 ≤ b by omega)).aemeasurable hm).mp ht

include hF hStep in
lemma rawExtension_scalarIncreasing (a b : ℕ) (h : RawHistory a) :
    ∀ᵐ y ∂rawExtension a b h, y ∈ scalarIncreasing F a b := by
  have hs : ∀ᵐ y ∂rawExtension a b h, ∀ k : Fin b, a ≤ k.1 →
      F (y ⟨k.1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩) ≤
        F (y ⟨k.1+1,Finset.mem_Iic.mpr (by have hk:=k.2; omega)⟩) := by
    rw [ae_all_iff]
    intro k
    by_cases hak : a ≤ k.1
    · filter_upwards [rawExtension_scalar_coordinate F hF hStep hak k.2 h] with y hy
      exact fun _ => hy
    · exact Eventually.of_forall (fun _ hy => (hak hy).elim)
  filter_upwards [hs] with y hy
  exact increasingCosts_of_steps (scalarHistory F b y) hy

include hF hStep in
lemma rawExtension_preserves_scalar {a b c : ℕ} (hbc : b ≤ c) (h : RawHistory b)
    (hh : h ∈ scalarIncreasing F a b) :
    ∀ᵐ y ∂rawExtension b c h, y ∈ scalarIncreasing F a c := by
  filter_upwards [rawExtension_scalarIncreasing F hF hStep b c h,rawExtension_retains_prefix hbc h] with y hy hp
  apply increasingCosts_extend hbc (scalarHistory F b h) (scalarHistory F c y) hh hy
  have he := congrArg (scalarHistory F b) hp
  exact he

include hF hStep in
theorem rawEvenHit_scalarIncreasing (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a v H h,
      rawEvenFinalCycle a z ∈ selectedHistoryProperty (scalarIncreasing F a) := by
  apply rawEvenHit_historyProperty (scalarIncreasing F a) (scalarIncreasing_measurable F hF a)
  · intro b c hbc past hp
    exact rawExtension_preserves_scalar F hF hStep hbc past hp
  · exact increasingCosts_at_start a (scalarHistory F a h)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels NumberTheoryLean.RegeneratingInverseBands
open NumberTheoryLean.ArrivalKernelGeometry

lemma gapValue_log_eq_gapAt {r : ℝ} (hr : 0 < r) (z : CostState) :
    gapValue (Real.log r) z=gapAt r z.2 := by
  unfold gapValue gapAt
  rw [Real.exp_sub,Real.exp_log hr,Real.exp_neg,div_eq_mul_inv]

lemma record_currentExponent {r : ℝ} (hr : 0 < r) {c : CycleInputSignature} {tau : EvenState}
    (hF : recordFirst c=(Sum.inl tau,c.1+cost tau.1)) :
    currentExponent (Real.log r) (recordFirst c)=nextExponent (gapAt r c.1) tau.1 := by
  unfold currentExponent
  rw [gapValue_log_eq_gapAt hr,hF]
  change gapAt r (c.1+cost tau.1)/tau.1=nextExponent (gapAt r c.1) tau.1
  have ht : 0 < tau.1 := by have h := tau.2; change (198/100:ℝ) ≤ tau.1 at h; linarith
  rw [gapAt_add_cost r c.1 tau.1 ht,nextGap_div_ratio ht]

theorem rawEvenHit_before_cutoff {r b0 b1 ell : ℝ} (hr : 0 < r) (hb0 : 0 < b0)
    (hb1 : 0 < b1) (hell : ell < 2*b0) (a : ℕ) (h0 : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a (Real.log (r/b1)) (Real.log (b1/(10*b0))) h0,
      let q := rawEvenFinalCycle a z
      ∀ j : Finset.Iic (q.1+2*(q.2.1+1)), a ≤ j.1 → j.1 ≤ q.1+1 →
        q.2.2 j ∈ arrivalSet (Real.log r) ell := by
  have hF : Measurable (fun z => -currentExponent (Real.log r) z) := (currentExponent_measurable _).neg
  have hStep (z : CostState) : ∀ᵐ y ∂costKernel z,
      -currentExponent (Real.log r) z ≤ -currentExponent (Real.log r) y := by
    filter_upwards [costKernel_exponent_nonincreasing (Real.log r) z] with y hy
    exact neg_le_neg hy
  filter_upwards [rawEvenHit_ae_geometric hr hb0 hb1 a h0,
    rawEvenHit_scalarIncreasing (fun z => -currentExponent (Real.log r) z) hF hStep a
      (Real.log (r/b1)) (Real.log (b1/(10*b0))) h0] with z hG hI
  obtain ⟨tau,_ht0,_ht1,hFirst,_hg0,_hg1,_hx0,_hx1,hx2,_hx3,_hgap,_hratio⟩ := hG
  have hX : 2*b0 ≤ currentExponent (Real.log r) (recordFirst (rawEvenHitRecord a z)) := by
    rw [record_currentExponent hr hFirst]
    exact hx2
  have hR := rawEvenFinalCycle_record a z
  rw [hR] at hX
  rcases he : rawEvenFinalCycle a z with ⟨t,n,h⟩
  rw [he] at hI hX
  change ∀ i j : Finset.Iic (t+2*(n+1)), a ≤ i.1 → i.1 ≤ j.1 →
    -currentExponent (Real.log r) (h i) ≤ -currentExponent (Real.log r) (h j) at hI
  change 2*b0 ≤ currentExponent (Real.log r) (h ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩) at hX
  change ∀ j : Finset.Iic (t+2*(n+1)), a ≤ j.1 → j.1 ≤ t+1 → h j ∈ arrivalSet (Real.log r) ell
  intro j haj hj
  have hle := hI j ⟨t+1,Finset.mem_Iic.mpr (by omega)⟩ haj hj
  change ell < currentExponent (Real.log r) (h j)
  linarith

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures

local instance : MeasurableSingletonClass State := by
  constructor
  intro x
  cases x with
  | inl e => simpa only [image_singleton] using ((measurableSet_singleton e).inl_image : MeasurableSet (Sum.inl '' {e} : Set State))
  | inr o => simpa only [image_singleton] using ((measurableSet_singleton o).inr_image : MeasurableSet (Sum.inr '' {o} : Set State))

noncomputable def suppliedPastEvent (a : ℕ) (past : RawHistory a) (b : ℕ) : Set (RawHistory b) :=
  {h | ∃ hab : a ≤ b, rawPrefix hab h=past}

lemma suppliedPastEvent_measurable (a : ℕ) (past : RawHistory a) (b : ℕ) :
    MeasurableSet (suppliedPastEvent a past b) := by
  unfold suppliedPastEvent
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro hab
  exact (rawPrefix_measurable hab) (measurableSet_singleton past)

lemma suppliedPastEvent_self (a : ℕ) (past : RawHistory a) : past ∈ suppliedPastEvent a past a :=
  ⟨le_rfl,rfl⟩

lemma rawExtension_preserves_suppliedPast (a : ℕ) (past : RawHistory a) (b c : ℕ)
    (hbc : b ≤ c) (h : RawHistory b) (hh : h ∈ suppliedPastEvent a past b) :
    ∀ᵐ y ∂rawExtension b c h, y ∈ suppliedPastEvent a past c := by
  obtain ⟨hab,hp⟩ := hh
  filter_upwards [rawExtension_retains_prefix hbc h] with y hy
  refine ⟨hab.trans hbc,?_⟩
  calc
    rawPrefix (hab.trans hbc) y=rawPrefix hab (rawPrefix hbc y) := rfl
    _=rawPrefix hab h := congrArg (rawPrefix hab) hy
    _=past := hp

theorem rawEvenHit_retains_suppliedPast (a : ℕ) (v H : ℝ) (past : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a v H past,
      rawEvenFinalCycle a z ∈ selectedHistoryProperty (suppliedPastEvent a past) := by
  exact rawEvenHit_historyProperty (suppliedPastEvent a past) (suppliedPastEvent_measurable a past)
    (rawExtension_preserves_suppliedPast a past) a v H past (suppliedPastEvent_self a past)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
