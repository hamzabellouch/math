import OAI.Dynamics.StandardMap.ClosedEligibility

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma cosine_periodic : Function.Periodic (fun x : ℝ => Real.cos (2*Real.pi*x)) 1 := by
  intro x
  dsimp only
  rw [show 2*Real.pi*(x+1)=2*Real.pi*x+2*Real.pi by ring]
  exact Real.cos_add_two_pi _
noncomputable def cosine (x : Circle) : ℝ := cosine_periodic.lift x
@[simp] lemma cosine_coe (x : ℝ) : cosine (x : Circle)=Real.cos (2*Real.pi*x) :=
  cosine_periodic.lift_coe x
lemma continuous_cosine : Continuous cosine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => cosine (x : Circle))
  simpa only [cosine_coe,Function.comp_def,Pi.mul_apply,id_eq] using
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
noncomputable def torusPotential (k : ℝ) (x : Circle) : ℝ := 2+(2*Real.pi*k)*cosine x
@[simp] lemma torusPotential_coe (k x : ℝ) : torusPotential k (x : Circle)=potential k x := rfl
lemma continuous_torusPotential (k : ℝ) : Continuous (torusPotential k) :=
  continuous_const.add (continuous_const.mul continuous_cosine)
noncomputable def torusSegmentCoefficient (k : ℝ) (z : Torus) (a : ℤ) (i : ℕ) : ℝ :=
  torusPotential k (torusIter k (a+(i:ℤ)-1) z).1
noncomputable def torusSegmentTransfer (k : ℝ) (z : Torus) (a : ℤ) (n : ℕ) : ℂ →L[ℝ] ℂ :=
  transferProduct (torusSegmentCoefficient k z a) n
noncomputable def torusShortfall (k : ℝ) (z : Torus) (a : ℤ) (n : ℕ) : ℝ :=
  1-Real.log ‖torusSegmentTransfer k z a n‖/((n:ℝ)*Real.log (growthBase k))
@[simp] lemma torusSegmentCoefficient_lift (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (i : ℕ) :
    torusSegmentCoefficient k (liftProjection z) a i=liftSegmentCoefficient k z a i := by
  unfold torusSegmentCoefficient liftSegmentCoefficient
  rw [← liftProjection_iter]
  rfl
@[simp] lemma torusSegmentTransfer_lift (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    torusSegmentTransfer k (liftProjection z) a n=liftSegmentTransfer k z a n := by
  unfold torusSegmentTransfer liftSegmentTransfer
  congr 1
  funext i
  exact torusSegmentCoefficient_lift k z a i
@[simp] lemma torusShortfall_lift (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    torusShortfall k (liftProjection z) a n=liftShortfall k z a n := by
  simp only [torusShortfall,liftShortfall,torusSegmentTransfer_lift]
lemma continuous_torusSegmentCoefficient (k : ℝ) (a : ℤ) (i : ℕ) :
    Continuous (fun z => torusSegmentCoefficient k z a i) :=
  (continuous_torusPotential k).comp (continuous_fst.comp (continuous_torusIter k _))
lemma continuous_torusSegmentTransfer (k : ℝ) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusSegmentTransfer k z a n) :=
  continuous_transferProduct_params (fun z i => torusSegmentCoefficient k z a i)
    (fun i => continuous_torusSegmentCoefficient k a i) n
lemma torusSegmentTransfer_norm_bounds (k : ℝ) (hk : 0 ≤ k) (z : Torus) (a : ℤ) (n : ℕ) :
    1 ≤ ‖torusSegmentTransfer k z a n‖ ∧ ‖torusSegmentTransfer k z a n‖ ≤ growthBase k^n := by
  obtain ⟨w,rfl⟩ := liftProjection_surjective z
  rw [torusSegmentTransfer_lift]
  exact liftSegmentTransfer_norm_bounds k hk w a n
lemma continuous_torusShortfall (k : ℝ) (hk : 0 ≤ k) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusShortfall k z a n) := by
  apply continuous_const.sub
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k a n).norm.log
    (fun z => by have := (torusSegmentTransfer_norm_bounds k hk z a n).1; linarith)
lemma torusShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : Torus) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    torusShortfall k z a n ∈ Icc 0 1 := by
  obtain ⟨w,rfl⟩ := liftProjection_surjective z
  rw [torusShortfall_lift]
  exact liftShortfall_mem k hk w a n hn
lemma torusShortfall_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusShortfall k (torusIter k b z) a n=torusShortfall k z (a+b) n := by
  have he : torusSegmentCoefficient k (torusIter k b z) a=torusSegmentCoefficient k z (a+b) := by
    funext i
    unfold torusSegmentCoefficient
    rw [← torusIter_add]
    congr 3
    ring
  simp only [torusShortfall,torusSegmentTransfer,he]
lemma shortfall_observation_transport (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (hn : ∀ i, 0 < n i)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F)
    (b : ℤ) (r : ℕ) (hlen : ∀ i, n i ≤ 2*r)
    (hwin : ∀ i j, 1 ≤ j → j ≤ n i → (a i+(j:ℤ)-1-b).natAbs ≤ r)
    (z w : ℝ × ℝ) :
    |F (fun i => torusShortfall k (liftProjection z) (a i) (n i))-
      F (fun i => torusShortfall k (liftProjection w) (a i) (n i))| ≤
    L*(((2*Real.pi*growthBase k)/Real.log (growthBase k))*growthBase k^(3*r)*
        dist (liftIter k b z) (liftIter k b w)) := by
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have hcoeff : 0 ≤ (2*Real.pi*growthBase k)/Real.log (growthBase k) := by
    have := Real.log_pos (by have := growthBase_ge_four k hk; linarith : 1 < growthBase k)
    positivity
  have hd : dist (fun i => torusShortfall k (liftProjection z) (a i) (n i))
      (fun i => torusShortfall k (liftProjection w) (a i) (n i)) ≤
      ((2*Real.pi*growthBase k)/Real.log (growthBase k))*growthBase k^(3*r)*
        dist (liftIter k b z) (liftIter k b w) := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    rw [Real.dist_eq,torusShortfall_lift,torusShortfall_lift]
    apply (liftShortfall_transport k hk z w (a i) b (n i) r (hn i) (hwin i)).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hM (by have := hlen i; omega)) hcoeff) dist_nonneg
  rw [← Real.dist_eq]
  exact (hF.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
lemma continuous_shortfall_observation (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun z => F (fun i => torusShortfall k z (a i) (n i))) :=
  hF.comp (continuous_pi (fun i => continuous_torusShortfall k hk (a i) (n i)))
end StandardMapEntropy

end OAI
