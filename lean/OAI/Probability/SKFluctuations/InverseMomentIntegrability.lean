import Mathlib
import OAI.Probability.SKFluctuations.RealSKPressureL1

namespace OAI

/-! Inverse Moment Integrability. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem inverse_bounded_integrable {a b c d K : ℝ} {α R f : ℝ → ℝ} {C : ℝ≥0}
    (hab : a ≤ b) (hα : Measurable α) (hR : LipschitzOnWith C R (Icc c d))
    (hmap : MapsTo α (Icc a b) (Icc c d)) (hback : ∀ x ∈ Icc a b, R (α x)=x)
    (hf : IntegrableOn f (Icc c d))
    (hb : ∀ᵐ u, u ∈ Icc c d → |f u| ≤ K) :
    IntervalIntegrable (fun x => f (α x)) volume a b := by
  have hm := hf.aestronglyMeasurable
  have hea : ∀ᵐ u, u ∈ Icc c d → f u=hm.mk f u :=
    (ae_restrict_iff' measurableSet_Icc).mp hm.ae_eq_mk
  have hea' := ae_inverse_pullback hR hmap hback hea
  have hba := ae_inverse_pullback hR hmap hback hb
  have hcomp : AEStronglyMeasurable (fun x => f (α x)) (volume.restrict (Icc a b)) := by
    apply ((hm.stronglyMeasurable_mk.comp_measurable hα).aestronglyMeasurable).congr
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mpr hea'] with x hx
    exact hx.symm
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply (integrable_const K).mono' hcomp
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mpr hba] with x hx
  simpa only [Real.norm_eq_abs] using hx

 theorem constrained_inverse_bounded_integrable {r₀ u₀ c K : ℝ} {k M f : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (hf : IntervalIntegrable f volume 0 1)
    (hb : ∀ᵐ u, u ∈ Icc (0:ℝ) 1 → |f u| ≤ K) :
    IntervalIntegrable (fun r => f (α.val.val r)) volume r₀ 1 := by
  let R := fun u => (constrainedQuantile hr hc hk hkc hm hM α (projIcc u₀ 1 hu.2 u)).val
  have hR : LipschitzWith ⟨1/c,by positivity⟩ R := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have h₁ := (constrainedQuantile_lipschitz hr hc hk hkc hm hM α).dist_le_mul
      (projIcc u₀ 1 hu.2 u) (projIcc u₀ 1 hu.2 v)
    have h₂ := (LipschitzWith.projIcc hu.2).dist_le_mul u v
    simp only [NNReal.coe_one,one_mul] at h₂
    exact h₁.trans (mul_le_mul_of_nonneg_left h₂ (by change 0 ≤ 1/c; exact div_nonneg zero_le_one hc.le))
  have hmap : MapsTo α.val.val (Icc r₀ 1) (Icc u₀ 1) := fun r hri =>
    (inverseConstraintMap α ⟨r,hri⟩).property
  have hback : ∀ r ∈ Icc r₀ 1, R (α.val.val r)=r := by
    intro r hri
    apply (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
      (constrainedQuantile hr hc hk hkc hm hM α _).property hri
    rw [constrainedQuantile_spec,projIcc_of_mem hu.2 (hmap hri)]
  apply inverse_bounded_integrable hr α.val.property.2.measurable hR.lipschitzOnWith hmap hback
  · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp hf).mono_set
      (fun u h => ⟨hu.1.trans h.1,h.2⟩)
  · exact hb.mono fun u h hmu => h ⟨hu.1.trans hmu.1,hmu.2⟩

 theorem pathPairMoment_bounded {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) : ∃ K, ∀ᵐ u, u ∈ Icc (0:ℝ) 1 → |pathPairMoment w φ q P u| ≤ K := by
  classical
  let D : ι → ℝ := fun i => ∑ σ, |φ σ (Pi.single i 1)|
  have hD : ∀ i, 0≤D i := by intro i; exact Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i := by
    intro σ i
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ (Pi.single i 1))) (Finset.mem_univ σ)
  let K : ℝ := ∑ σ, ∑ τ, |P σ τ|
  have hK : 0≤K := by dsimp [K]; positivity
  have hP (σ τ : S) : |P σ τ|≤K := by
    exact (Finset.single_le_sum (fun ρ _ => abs_nonneg (P σ ρ)) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg fun η _ => abs_nonneg (P ρ η)) (Finset.mem_univ σ))
  refine ⟨K,?_⟩
  filter_upwards [(volume : Measure ℝ).ae_ne (0:ℝ)] with u hu hui
  exact pathPairMoment_bound hw φ D hD hφ q hq P hK hP ⟨lt_of_le_of_ne hui.1 hu.symm,hui.2⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem orderedPathPair_inverse_integrable {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (P : Spin n → Spin n → ℝ) :
    IntervalIntegrable (fun r => orderedPathPair n b h P (α.val.val r)) volume r₀ 1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨K,hK⟩ := pathPairMoment_bounded (uniformWeight_pos n) (orderedFeature n)
    (orderedPathClock n b h) (orderedPathClock_monotone n hb hh) P
  apply constrained_inverse_bounded_integrable hr hu hc hk hkc hm hM α
    (pathPairMoment_intervalIntegrable_all (uniformWeight_pos n) (orderedFeature n)
      (orderedPathClock n b h) (orderedPathClock_monotone n hb hh) P) hK

 theorem source_radius_gradient_integrable {r₀ u₀ c : ℝ} {k M g : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ∈ Icc (0:ℝ) 1) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ r ∈ Icc r₀ 1, c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g) (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    IntervalIntegrable (radiusComparisonGradient g α.val.val (orderedPathS n b h)
      (orderedPathB n b h)) volume r₀ 1 := by
  have hiS := orderedPathPair_inverse_integrable hr hu hc hk hkc hm hM α n hn b h hb hh (orderedOverlap n)
  have hiB := orderedPathPair_inverse_integrable hr hu hc hk hkc hm hM α n hn b h hb hh
    (fun σ τ => (orderedOverlap n σ τ)^2)
  have hgd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have h₁ := hiB.continuousOn_mul hgd.continuousOn
  have h₂ := (hiS.continuousOn_mul ((hgd.mul continuous_id).add hg.continuous).continuousOn).const_mul 2
  have h₃ : IntervalIntegrable (fun r => deriv g r*r^2) volume r₀ 1 :=
    (hgd.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have h₄ : IntervalIntegrable (fun r => 2*g r*r) volume r₀ 1 :=
    ((continuous_const.mul hg.continuous).mul continuous_id).intervalIntegrable _ _
  convert ((h₁.sub h₂).add h₃).add h₄ using 1
  ext r
  dsimp [radiusComparisonGradient,orderedPathS,orderedPathB]
  ring

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def comparisonCapSlope (N δ U L E d u : ℝ) : ℝ :=
   N^δ*(1/L+2*(d^3/E)*(u+U))

 theorem comparisonCap_tangent {N δ U L E d u v : ℝ}
    (hN : 0<N) (hE : 0<E) (hd : 0 ≤ d) :
    comparisonCap N δ U L E d u+comparisonCapSlope N δ U L E d u*(v-u) ≤ 
      comparisonCap N δ U L E d v := by
  have he : comparisonCap N δ U L E d v-
      (comparisonCap N δ U L E d u+comparisonCapSlope N δ U L E d u*(v-u))=
      N^δ*(d^3/E)*(v-u)^2 := by
    unfold comparisonCap comparisonCapSlope
    ring
  have hh : 0 ≤ N^δ*(d^3/E)*(v-u)^2 := by positivity
  linarith

 theorem control_cone_bounds {w m P a b t : ℝ}
    (hw : w ∈ Icc (0:ℝ) 1) (hm : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hA : 0 ≤ m+t*P-t*m*a) (hB : 0 ≤ m+t*P-t*m*b) :
    0 ≤ w*m+t*(w*P+m*((1-w)*a-w*b)) ∧
    w*m+t*(w*P+m*((1-w)*a-w*b)) ≤ m+t*P := by
  constructor
  · have he : w*m+t*(w*P+m*((1-w)*a-w*b))=
        w*(m+t*P-t*m*b)+t*(1-w)*m*a := by ring
    rw [he]
    exact add_nonneg (mul_nonneg hw.1 hB)
      (mul_nonneg (mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hw.2)) hm) ha)
  · have he : m+t*P-(w*m+t*(w*P+m*((1-w)*a-w*b)))=
        (1-w)*(m+t*P-t*m*a)+t*w*m*b := by ring
    have hh : 0 ≤ m+t*P-(w*m+t*(w*P+m*((1-w)*a-w*b))) := by
      rw [he]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hw.2) hA)
        (mul_nonneg (mul_nonneg (mul_nonneg ht hw.1) hm) hb)
    linarith

 theorem control_cone_small {w m P a b t g B U A : ℝ}
    (hw : w ∈ Icc (0:ℝ) 1) (hg : 0 ≤ g) (hmg : g ≤ m) (hmU : m ≤ U)
    (hP : |P| ≤ B) (ha : a ∈ Icc (0:ℝ) A) (hb : b ∈ Icc (0:ℝ) A)
    (ht : 0 ≤ t) (hsmall : t*(B+U*A) ≤ g) :
    0 ≤ w*m+t*(w*P+m*((1-w)*a-w*b)) ∧
    w*m+t*(w*P+m*((1-w)*a-w*b)) ≤ m+t*P := by
  have hm := hg.trans hmg
  have hU := hm.trans hmU
  have hpa : m*a ≤ U*A := mul_le_mul hmU ha.2 ha.1 hU
  have hpb : m*b ≤ U*A := mul_le_mul hmU hb.2 hb.1 hU
  have hlow : -B ≤ P := (abs_le.mp hP).1
  have htP := mul_le_mul_of_nonneg_left hlow ht
  have hta := mul_le_mul_of_nonneg_left hpa ht
  have htb := mul_le_mul_of_nonneg_left hpb ht
  apply control_cone_bounds hw hm ha.1 hb.1 ht <;> nlinarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem inverse_control_feasible {r₀ u₀ t g B U A : ℝ} {k M M' α ψ w a b : ℝ → ℝ}
    (hr : r₀ ≤ 1) {C D : ℝ≥0}
    (hα : LipschitzOnWith C α (Icc r₀ 1)) (hψ : LipschitzOnWith D ψ (Icc r₀ 1))
    (hα₀ : α r₀=u₀) (hα₁ : α 1=1) (hψ₀ : ψ r₀=0) (hψ₁ : ψ 1=0)
    (hconv : ∀ u v, M u+M' u*(v-u) ≤ M v)
    (hg : 0 ≤ g) (ht : 0 ≤ t) (hsmall : t*(B+U*A) ≤ g)
    (heq : ∀ᵐ r, r ∈ Icc r₀ 1 →
      deriv α r=k r+w r*(M (α r)-k r) ∧
      deriv ψ r=w r*M' (α r)*ψ r+(M (α r)-k r)*((1-w r)*a r-w r*b r))
    (hbd : ∀ᵐ r, r ∈ Icc r₀ 1 → w r ∈ Icc (0:ℝ) 1 ∧
      g ≤ M (α r)-k r ∧ M (α r)-k r ≤ U ∧ |M' (α r)*ψ r| ≤ B ∧
      a r ∈ Icc (0:ℝ) A ∧ b r ∈ Icc (0:ℝ) A) :
    sourceInverseConstraints r₀ u₀ k M (fun r => α r+t*ψ r) := by
  refine ⟨by simp [hα₀,hψ₀],by simp [hα₁,hψ₁],C+‖t‖₊*D,?_,?_⟩
  · apply hα.add
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have hh := hψ.dist_le_mul x hx y hy
    simpa only [Real.dist_eq,← mul_sub,abs_mul,Real.norm_eq_abs,NNReal.coe_mul,coe_nnnorm,
      mul_assoc] using mul_le_mul_of_nonneg_left hh (norm_nonneg t)
  have hacα : AbsolutelyContinuousOnInterval α r₀ 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le hr] using hα
  have hacψ : AbsolutelyContinuousOnInterval ψ r₀ 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
    simpa only [uIcc_of_le hr] using hψ
  have hdα : ∀ᵐ r, r ∈ Icc r₀ 1 → DifferentiableAt ℝ α r := by
    simpa only [uIcc_of_le hr] using hacα.ae_differentiableAt
  have hdψ : ∀ᵐ r, r ∈ Icc r₀ 1 → DifferentiableAt ℝ ψ r := by
    simpa only [uIcc_of_le hr] using hacψ.ae_differentiableAt
  filter_upwards [heq,hbd,hdα,hdψ] with r he hb hd₁ hd₂ hri
  have hh := control_cone_small (hb hri).1 hg (hb hri).2.1 (hb hri).2.2.1
    (hb hri).2.2.2.1 (hb hri).2.2.2.2.1 (hb hri).2.2.2.2.2 ht hsmall
  have hd := ((hd₁ hri).hasDerivAt.add ((hd₂ hri).hasDerivAt.const_mul t)).deriv
  change deriv (fun r => α r+t*ψ r) r=deriv α r+t*deriv ψ r at hd
  rw [hd,(he hri).1,(he hri).2]
  have hc := hconv (α r) (α r+t*ψ r)
  constructor <;> nlinarith [hh.1,hh.2]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem integral_primitive_lipschitz {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) {C : ℝ≥0}
    (hC : ∀ᵐ x, x ∈ Icc a b → |f x| ≤ C) :
    LipschitzOnWith C (fun x => ∫ t in a..x, f t) (Icc a b) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hsub (z) (hz : z ∈ Icc a b) : uIcc a z ⊆ uIcc a b := by
    rw [uIcc_of_le hz.1,uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hz.2
  rw [Real.dist_eq,intervalIntegral.integral_interval_sub_left
    (hf.mono_set (hsub x hx)) (hf.mono_set (hsub y hy)),Real.dist_eq]
  have hbnd : ∀ᵐ t, t ∈ uIoc y x → ‖f t‖ ≤ C := by
    filter_upwards [hC] with t ht hti
    apply ht
    have hti' : t ∈ uIcc y x := uIoc_subset_uIcc hti
    exact ⟨(le_min hy.1 hx.1).trans hti'.1,hti'.2.trans (max_le hy.2 hx.2)⟩
  simpa only [Real.norm_eq_abs,abs_sub_comm] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hbnd

 theorem lipschitzOn_real_mul {s : Set ℝ} {f g : ℝ → ℝ} {C D A B : ℝ≥0}
    (hf : LipschitzOnWith C f s) (hg : LipschitzOnWith D g s)
    (hA : ∀ x ∈ s, |f x| ≤ A) (hB : ∀ x ∈ s, |g x| ≤ B) :
    LipschitzOnWith (A*D+B*C) (fun x => f x*g x) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have he : f x*g x-f y*g y=f x*(g x-g y)+g y*(f x-f y) := by ring
  have h₁ := hf.dist_le_mul x hx y hy
  have h₂ := hg.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at h₁ h₂ ⊢
  rw [he]
  calc
    _ ≤ |f x*(g x-g y)|+|g y*(f x-f y)| := abs_add_le _ _
    _ = |f x| *|g x-g y|+|g y| *|f x-f y| := by rw [abs_mul,abs_mul]
    _ ≤ A*(D*|x-y|)+B*(C*|x-y|) := add_le_add
      (mul_le_mul (hA x hx) h₂ (abs_nonneg _) (NNReal.coe_nonneg _))
      (mul_le_mul (hB y hy) h₁ (abs_nonneg _) (NNReal.coe_nonneg _))
    _ = _ := by push_cast; ring

 theorem lipschitzOn_exp_primitive {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) {C : ℝ≥0}
    (hC : ∀ᵐ x, x ∈ Icc a b → |f x| ≤ C) :
    ∃ D, LipschitzOnWith D (fun x => Real.exp (∫ t in a..x, f t)) (Icc a b) := by
  have hP := integral_primitive_lipschitz hab hf hC
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hP.continuousOn
  obtain ⟨D,hD⟩ := (show ContDiffOn ℝ 1 Real.exp (Icc (-B) B) from
    Real.contDiff_exp.contDiffOn).exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨D*C,?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hb (z) (hz : z ∈ Icc a b) : (∫ t in a..z, f t) ∈ Icc (-B) B := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hB z hz)
  exact (hD.dist_le_mul _ (hb x hx) _ (hb y hy)).trans (by
    simpa only [NNReal.coe_mul,mul_assoc] using
      mul_le_mul_of_nonneg_left (hP.dist_le_mul x hx y hy) (NNReal.coe_nonneg D))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def inverseControlFactor (a : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
   Real.exp (∫ t in a..r, A t)
 def inverseControlTangent (a : ℝ) (A F : ℝ → ℝ) (r : ℝ) : ℝ :=
   inverseControlFactor a A r * ∫ t in a..r, F t*Real.exp (-(∫ s in a..t, A s))

 theorem inverseControlFactor_pos (a : ℝ) (A : ℝ → ℝ) (r : ℝ) :
    0 < inverseControlFactor a A r := Real.exp_pos _

 theorem inverseControlTangent_initial (a : ℝ) (A F : ℝ → ℝ) :
    inverseControlTangent a A F a=0 := by simp [inverseControlTangent]

 theorem inverseControlTangent_terminal {a b : ℝ} {A F : ℝ → ℝ}
    (h : (∫ t in a..b, F t/inverseControlFactor a A t)=0) :
    inverseControlTangent a A F b=0 := by
  simpa only [inverseControlTangent,inverseControlFactor,Real.exp_neg,div_eq_mul_inv,mul_zero]
    using congrArg (fun z => inverseControlFactor a A b*z) h

 theorem inverseControlTangent_ae_derivative {a b : ℝ} (hab : a ≤ b)
    {A F : ℝ → ℝ} (hA : IntervalIntegrable A volume a b)
    (hF : IntervalIntegrable F volume a b) {C : ℝ≥0}
    (hC : ∀ᵐ x, x ∈ Icc a b → |A x| ≤ C) :
    ∀ᵐ r, r ∈ Icc a b → HasDerivAt (inverseControlTangent a A F)
      (A r*inverseControlTangent a A F r+F r) r := by
  have hP := integral_primitive_lipschitz hab hA hC
  have hEc : ContinuousOn (fun t => Real.exp (-(∫ s in a..t, A s))) (Icc a b) :=
    Real.continuous_exp.comp_continuousOn hP.continuousOn.neg
  have hFi : IntervalIntegrable (fun t => F t*Real.exp (-(∫ s in a..t, A s))) volume a b :=
    hF.mul_continuousOn (by simpa only [uIcc_of_le hab] using hEc)
  have h₁ := hA.ae_hasDerivAt_integral
  have h₂ := hFi.ae_hasDerivAt_integral
  simp only [uIcc_of_le hab] at h₁ h₂
  filter_upwards [h₁,h₂] with r hr₁ hr₂ hri
  have hd := ((hr₁ hri a ⟨le_rfl,hab⟩).exp).mul (hr₂ hri a ⟨le_rfl,hab⟩)
  change HasDerivAt (inverseControlTangent a A F) _ r at hd
  convert hd using 1
  unfold inverseControlTangent inverseControlFactor
  rw [Real.exp_neg]
  have hne := (Real.exp_pos (∫ t in a..r, A t)).ne'
  field_simp

 theorem inverseControlTangent_lipschitz {a b : ℝ} (hab : a ≤ b)
    {A F : ℝ → ℝ} (hA : IntervalIntegrable A volume a b)
    (hF : IntervalIntegrable F volume a b) {C D : ℝ≥0}
    (hC : ∀ᵐ x, x ∈ Icc a b → |A x| ≤ C)
    (hD : ∀ᵐ x, x ∈ Icc a b → |F x| ≤ D) :
    ∃ K, LipschitzOnWith K (inverseControlTangent a A F) (Icc a b) := by
  have hP := integral_primitive_lipschitz hab hA hC
  obtain ⟨KJ,hJ⟩ := lipschitzOn_exp_primitive hab hA hC
  have hEc : ContinuousOn (fun t => Real.exp (-(∫ s in a..t, A s))) (Icc a b) :=
    Real.continuous_exp.comp_continuousOn hP.continuousOn.neg
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hEc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl,hab⟩)
  have hFi : IntervalIntegrable (fun t => F t*Real.exp (-(∫ s in a..t, A s))) volume a b :=
    hF.mul_continuousOn (by simpa only [uIcc_of_le hab] using hEc)
  have hbd : ∀ᵐ x, x ∈ Icc a b → |F x*Real.exp (-(∫ s in a..x, A s))| ≤ ((D*Real.toNNReal B : ℝ≥0) : ℝ) := by
    filter_upwards [hD] with x hx hxi
    rw [abs_mul,NNReal.coe_mul,Real.coe_toNNReal B hB0]
    exact mul_le_mul (hx hxi) (by simpa only [Real.norm_eq_abs] using hB x hxi)
      (abs_nonneg _) (NNReal.coe_nonneg D)
  have hQ := integral_primitive_lipschitz hab hFi hbd
  obtain ⟨B₁,hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hJ.continuousOn
  obtain ⟨B₂,hB₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hQ.continuousOn
  have h₁ : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ a ⟨le_rfl,hab⟩)
  have h₂ : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂ a ⟨le_rfl,hab⟩)
  have hh := lipschitzOn_real_mul (A := Real.toNNReal B₁) (B := Real.toNNReal B₂) hJ hQ
    (fun x hx => by simpa only [Real.norm_eq_abs,Real.coe_toNNReal B₁ h₁] using hB₁ x hx)
    (fun x hx => by simpa only [Real.norm_eq_abs,Real.coe_toNNReal B₂ h₂] using hB₂ x hx)
  exact ⟨_,hh⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem control_difference_bound {w p q A : ℝ}
    (hw : w ∈ Icc (0:ℝ) 1) (hp : p ∈ Icc (0:ℝ) A) (hq : q ∈ Icc (0:ℝ) A) :
    |(1-w)*p-w*q| ≤ A := by
  have hwp := mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr hw.2)
  have hwq := mul_le_mul_of_nonneg_left hq.2 hw.1
  have hp0 := mul_nonneg (sub_nonneg.mpr hw.2) hp.1
  have hq0 := mul_nonneg hw.1 hq.1
  have hA : 0 ≤ A := hp.1.trans hp.2
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hw.1 hA,mul_nonneg (sub_nonneg.mpr hw.2) hA]

 theorem bounded_control_competitors {r₀ u₀ gap U L A : ℝ} {α k M M' w p q : ℝ → ℝ}
    (hr : r₀ ≤ 1) {C : ℝ≥0} (hα : LipschitzOnWith C α (Icc r₀ 1))
    (hα₀ : α r₀=u₀) (hα₁ : α 1=1)
    (hαm : Measurable α) (hkm : Measurable k) (hMm : Measurable M) (hM'm : Measurable M')
    (hw : Measurable w) (hp : Measurable p) (hq : Measurable q)
    (hconv : ∀ u v, M u+M' u*(v-u) ≤ M v)
    (hg : 0<gap) (hU : 0 ≤ U) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (heq : ∀ᵐ r, r ∈ Icc r₀ 1 → deriv α r=k r+w r*(M (α r)-k r))
    (hbd : ∀ r ∈ Icc r₀ 1, w r ∈ Icc (0:ℝ) 1 ∧
      gap ≤ M (α r)-k r ∧ M (α r)-k r ≤ U ∧ |M' (α r)| ≤ L ∧
      p r ∈ Icc (0:ℝ) A ∧ q r ∈ Icc (0:ℝ) A)
    (hendpoint : (∫ r in r₀..1, ((M (α r)-k r)*((1-w r)*p r-w r*q r))/
      inverseControlFactor r₀ (fun r => w r*M' (α r)) r)=0) :
    let ψ := inverseControlTangent r₀ (fun r => w r*M' (α r))
      (fun r => (M (α r)-k r)*((1-w r)*p r-w r*q r))
    ∃ T B : ℝ, ∃ D : ℝ≥0, 0<T ∧ 0 ≤ B ∧ LipschitzOnWith D ψ (Icc r₀ 1) ∧
      (∀ r ∈ Icc r₀ 1, |ψ r| ≤ B) ∧
      ∀ t ∈ Icc (0:ℝ) T, sourceInverseConstraints r₀ u₀ k M (fun r => α r+t*ψ r) := by
  dsimp only
  let a := fun r => w r*M' (α r)
  let f := fun r => (M (α r)-k r)*((1-w r)*p r-w r*q r)
  let ψ := inverseControlTangent r₀ a f
  have ham : Measurable a := hw.mul (hM'm.comp hαm)
  have hfm : Measurable f := ((hMm.comp hαm).sub hkm).mul
    (((measurable_const.sub hw).mul hp).sub (hw.mul hq))
  have hab : ∀ᵐ r, r ∈ Icc r₀ 1 → |a r| ≤ L := Eventually.of_forall fun r hr' => by
    dsimp only [a]
    rw [abs_mul,abs_of_nonneg (hbd r hr').1.1]
    exact (mul_le_mul_of_nonneg_left (hbd r hr').2.2.2.1 (hbd r hr').1.1).trans
      (by nlinarith [(hbd r hr').1.2])
  have hfb : ∀ᵐ r, r ∈ Icc r₀ 1 → |f r| ≤ U*A := Eventually.of_forall fun r hr' => by
    dsimp only [f]
    rw [abs_mul,abs_of_nonneg (hg.le.trans (hbd r hr').2.1)]
    exact mul_le_mul (hbd r hr').2.2.1
      (control_difference_bound (hbd r hr').1 (hbd r hr').2.2.2.2.1 (hbd r hr').2.2.2.2.2)
      (abs_nonneg _) hU
  have hai := bounded_measurable_intervalIntegrable hr ham hab
  have hfi := bounded_measurable_intervalIntegrable hr hfm hfb
  have hab' : ∀ᵐ r, r ∈ Icc r₀ 1 → |a r| ≤ (Real.toNNReal L : ℝ) := by
    simpa only [Real.coe_toNNReal L hL] using hab
  have hfb' : ∀ᵐ r, r ∈ Icc r₀ 1 → |f r| ≤ (Real.toNNReal (U*A) : ℝ) := by
    simpa only [Real.coe_toNNReal (U*A) (mul_nonneg hU hA)] using hfb
  obtain ⟨D,hψ⟩ := inverseControlTangent_lipschitz hr hai hfi hab' hfb'
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB r₀ ⟨le_rfl,hr⟩)
  have hψb : ∀ r ∈ Icc r₀ 1, |ψ r| ≤ B := fun r hr' => by
    simpa only [Real.norm_eq_abs,ψ] using hB r hr'
  let T := gap/(L*B+U*A+1)
  have hden : 0<L*B+U*A+1 := by positivity
  have hT : 0<T := div_pos hg hden
  refine ⟨T,B,D,hT,hB0,hψ,hψb,?_⟩
  intro t ht
  have hsmall : t*(L*B+U*A) ≤ gap := by
    have hh : t*(L*B+U*A+1) ≤ gap := (le_div_iff₀ hden).mp ht.2
    nlinarith [ht.1]
  apply inverse_control_feasible hr hα hψ hα₀ hα₁
    (inverseControlTangent_initial _ _ _) (inverseControlTangent_terminal hendpoint)
    hconv hg.le ht.1 hsmall
  · have hd := inverseControlTangent_ae_derivative hr hai hfi hab'
    filter_upwards [heq,hd] with r he hd' hri
    exact ⟨he hri,(hd' hri).deriv⟩
  · exact Eventually.of_forall fun r hri => ⟨(hbd r hri).1,(hbd r hri).2.1,
      (hbd r hri).2.2.1,by
        rw [abs_mul]
        exact mul_le_mul (hbd r hri).2.2.2.1 (hψb r hri) (abs_nonneg _) hL,
      (hbd r hri).2.2.2.2.1,(hbd r hri).2.2.2.2.2⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology ENNReal

 theorem control_support_order (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Q : ℝ → ℝ} (hQ : Continuous Q) (hμ : Integrable Q μ) (hν : Integrable Q ν)
    (hopt : ∀ U V : Set ℝ, MeasurableSet U → MeasurableSet V →
      μ.real U*(∫ x in V, Q x ∂ν) ≤ ν.real V*(∫ x in U, Q x ∂μ))
    {x y : ℝ} (hx : x ∈ μ.support) (hy : y ∈ ν.support) : Q y ≤ Q x := by
  by_contra hxy
  have hlt : Q x < Q y := lt_of_not_ge hxy
  obtain ⟨c,hxc,hcy⟩ := exists_between hlt
  obtain ⟨d,hcd,hdy⟩ := exists_between hcy
  let U := {z | Q z<c}
  let V := {z | d<Q z}
  have hU : IsOpen U := isOpen_lt hQ continuous_const
  have hV : IsOpen V := isOpen_lt continuous_const hQ
  have hmU : 0<μ U := (μ.mem_support_iff_forall x).mp hx U (hU.mem_nhds hxc)
  have hnV : 0<ν V := (ν.mem_support_iff_forall y).mp hy V (hV.mem_nhds hdy)
  have hmr : 0<μ.real U := ENNReal.toReal_pos hmU.ne' (measure_ne_top μ U)
  have hnr : 0<ν.real V := ENNReal.toReal_pos hnV.ne' (measure_ne_top ν V)
  have hiU : (∫ z in U, Q z ∂μ) ≤ c*μ.real U := by
    calc
      (∫ z in U, Q z ∂μ) ≤ ∫ z in U, c ∂μ :=
        setIntegral_mono_on hμ.integrableOn (integrableOn_const (measure_ne_top μ U))
          hU.measurableSet (fun z hz => le_of_lt hz)
      _ = _ := by simp [mul_comm]
  have hiV : d*ν.real V ≤ ∫ z in V, Q z ∂ν :=
    setIntegral_ge_of_const_le_real hV.measurableSet (measure_ne_top ν V)
      (fun z hz => le_of_lt hz) hν.integrableOn
  have ho := hopt U V hU.measurableSet hV.measurableSet
  have ha := mul_le_mul_of_nonneg_left hiV hmr.le
  have hb := mul_le_mul_of_nonneg_left hiU hnr.le
  have hp : 0<μ.real U*ν.real V := mul_pos hmr hnr
  nlinarith [mul_pos (sub_pos.mpr hcd) hp]

 theorem control_scalar_multiplier (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ0 : μ≠0) (hν0 : ν≠0) {Q : ℝ → ℝ} (hQ : Continuous Q)
    (hμ : Integrable Q μ) (hν : Integrable Q ν)
    (hopt : ∀ U V : Set ℝ, MeasurableSet U → MeasurableSet V →
      μ.real U*(∫ x in V, Q x ∂ν) ≤ ν.real V*(∫ x in U, Q x ∂μ)) :
    ∃ c : ℝ, (∀ᵐ x ∂μ, c ≤ Q x) ∧ (∀ᵐ x ∂ν, Q x ≤ c) := by
  obtain ⟨x,hx⟩ := (Measure.nonempty_support hμ0)
  obtain ⟨y,hy⟩ := (Measure.nonempty_support hν0)
  have hne : (Q '' ν.support).Nonempty := ⟨Q y,mem_image_of_mem Q hy⟩
  have hbd : BddAbove (Q '' ν.support) := by
    refine ⟨Q x,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact control_support_order μ ν hQ hμ hν hopt hx hz
  refine ⟨sSup (Q '' ν.support),?_,?_⟩
  · filter_upwards [μ.support_mem_ae] with z hz
    apply csSup_le hne
    rintro _ ⟨v,hv,rfl⟩
    exact control_support_order μ ν hQ hμ hν hopt hz hv
  · filter_upwards [ν.support_mem_ae] with z hz
    exact le_csSup hbd (mem_image_of_mem Q hz)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology ENNReal

 theorem control_indicator_optimality (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Q : ℝ → ℝ)
    (hvar : ∀ a b : ℝ → ℝ, Measurable a → Measurable b →
      (∃ C : ℝ, ∀ x, a x ∈ Icc (0:ℝ) C ∧ b x ∈ Icc (0:ℝ) C) →
      (∫ x, a x ∂μ)=(∫ x, b x ∂ν) →
      (∫ x, Q x*b x ∂ν) ≤ ∫ x, Q x*a x ∂μ) :
    ∀ U V : Set ℝ, MeasurableSet U → MeasurableSet V →
      μ.real U*(∫ x in V, Q x ∂ν) ≤ ν.real V*(∫ x in U, Q x ∂μ) := by
  classical
  intro U V hU hV
  let a := U.indicator (fun _ : ℝ => ν.real V)
  let b := V.indicator (fun _ : ℝ => μ.real U)
  have ha : Measurable a := measurable_const.indicator hU
  have hb : Measurable b := measurable_const.indicator hV
  have hA : ∃ C : ℝ, ∀ x, a x ∈ Icc (0:ℝ) C ∧ b x ∈ Icc (0:ℝ) C := by
    refine ⟨μ.real U+ν.real V,?_⟩
    intro x
    have h₁ := measureReal_nonneg (μ := μ) (s := U)
    have h₂ := measureReal_nonneg (μ := ν) (s := V)
    constructor
    · by_cases hx : x ∈ U
      · rw [show a x=ν.real V by simp [a,hx]]
        exact ⟨h₂,by linarith⟩
      · rw [show a x=0 by simp [a,hx]]
        exact ⟨le_rfl,add_nonneg h₁ h₂⟩
    · by_cases hx : x ∈ V
      · rw [show b x=μ.real U by simp [b,hx]]
        exact ⟨h₁,by linarith⟩
      · rw [show b x=0 by simp [b,hx]]
        exact ⟨le_rfl,add_nonneg h₁ h₂⟩
  have hend : (∫ x, a x ∂μ)=(∫ x, b x ∂ν) := by
    dsimp [a,b]
    rw [integral_indicator hU,integral_indicator hV]
    simp [mul_comm]
  have hVa : (fun x => Q x*a x)=fun x => ν.real V*(U.indicator Q x) := by
    funext x
    by_cases hx : x ∈ U <;> simp [a,hx,mul_comm]
  have hVb : (fun x => Q x*b x)=fun x => μ.real U*(V.indicator Q x) := by
    funext x
    by_cases hx : x ∈ V <;> simp [b,hx,mul_comm]
  have hh := hvar a b ha hb hA hend
  rw [hVa,hVb,integral_const_mul,integral_const_mul,integral_indicator hU,integral_indicator hV] at hh
  exact hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology ENNReal

 def controlPlusMeasure (μ : Measure ℝ) (ρ w : ℝ → ℝ) : Measure ℝ :=
   μ.withDensity (fun x => ENNReal.ofReal (ρ x*(1-w x)))
 def controlMinusMeasure (μ : Measure ℝ) (ρ w : ℝ → ℝ) : Measure ℝ :=
   μ.withDensity (fun x => ENNReal.ofReal (ρ x*w x))

 theorem control_bang_bang (μ : Measure ℝ) (ρ w Q : ℝ → ℝ)
    [IsFiniteMeasure (controlPlusMeasure μ ρ w)] [IsFiniteMeasure (controlMinusMeasure μ ρ w)]
    (hρ : Measurable ρ) (hw : Measurable w) (hρp : ∀ᵐ x ∂μ, 0<ρ x)
    (hwb : ∀ᵐ x ∂μ, w x ∈ Icc (0:ℝ) 1)
    (hplus : controlPlusMeasure μ ρ w≠0) (hminus : controlMinusMeasure μ ρ w≠0)
    (hQ : Continuous Q) (hQi : Integrable Q (controlPlusMeasure μ ρ w))
    (hQj : Integrable Q (controlMinusMeasure μ ρ w))
    (hvar : ∀ a b : ℝ → ℝ, Measurable a → Measurable b →
      (∃ C : ℝ, ∀ x, a x ∈ Icc (0:ℝ) C ∧ b x ∈ Icc (0:ℝ) C) →
      (∫ x, a x ∂controlPlusMeasure μ ρ w)=(∫ x, b x ∂controlMinusMeasure μ ρ w) →
      (∫ x, Q x*b x ∂controlMinusMeasure μ ρ w) ≤ ∫ x, Q x*a x ∂controlPlusMeasure μ ρ w) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, (Q x-c<0 → w x=1) ∧ (0<Q x-c → w x=0) := by
  obtain ⟨c,hc₁,hc₂⟩ := control_scalar_multiplier _ _ hplus hminus hQ hQi hQj
    (control_indicator_optimality _ _ Q hvar)
  change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (ρ x*(1-w x))), c ≤ Q x at hc₁
  change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (ρ x*w x)), Q x ≤ c at hc₂
  have h₁ : Measurable (fun x => ENNReal.ofReal (ρ x*(1-w x))) :=
    (hρ.mul (measurable_const.sub hw)).ennreal_ofReal
  have h₂ : Measurable (fun x => ENNReal.ofReal (ρ x*w x)) := (hρ.mul hw).ennreal_ofReal
  rw [ae_withDensity_iff h₁] at hc₁
  rw [ae_withDensity_iff h₂] at hc₂
  refine ⟨c,?_⟩
  filter_upwards [hc₁,hc₂,hρp,hwb] with x hx₁ hx₂ hxρ hxw
  constructor
  · intro hneg
    by_contra hne
    have hp : 0<ρ x*(1-w x) := mul_pos hxρ (sub_pos.mpr (lt_of_le_of_ne hxw.2 hne))
    have hh := hx₁ (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    linarith
  · intro hpos
    by_contra hne
    have hp : 0<ρ x*w x := mul_pos hxρ (lt_of_le_of_ne hxw.1 (Ne.symm hne))
    have hh := hx₂ (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    linarith

end SKFluctuations.Hierarchy

end

end OAI
