import Mathlib
import OAI.Geometry.WeakHessian.Transport.QuadraticCost
import OAI.Geometry.WeakHessian.Sobolev.UpperGradientTendstoNorm

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open Set Filter MeasureTheory CompactlySupported
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
lemma quadratic_cost_increment {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R) (x z y : X) :
    dist z y^2/2-dist x y^2/2 ≤ (R:ℝ)*dist z x := by
  have h1 := dist_triangle z x y
  have h2 := hR z y
  have h3 := hR x y
  have h4 := dist_nonneg (x := z) (y := y)
  have h5 := dist_nonneg (x := x) (y := y)
  have h6 := dist_nonneg (x := z) (y := x)
  have H : (dist z y-dist x y)*(dist z y+dist x y) ≤ dist z x*(2*(R:ℝ)) := by
    calc
      _ ≤ dist z x*(dist z y+dist x y) := by gcongr; linarith
      _ ≤ dist z x*(2*(R:ℝ)) := by gcongr; linarith
  nlinarith

lemma hopfLax_lipschitz_diameter {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R)
    {f : X → ℝ} {B : ℝ} (hf : Continuous f) (hB : ∀ x, B ≤ f x) :
    LipschitzWith R (hopfLax f 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro z x
  have H (z x : X) : hopfLax f 1 z-hopfLax f 1 x ≤ (R:ℝ)*dist z x := by
    obtain ⟨y,hy⟩ := exists_hopf_minimizer hf hB (by norm_num : (0:ℝ)<1) x
    have hz := hopfLax_le_objective hB (by norm_num : (0:ℝ)<1) z y
    have hi := quadratic_cost_increment hR x z y
    rw [← hy]
    dsimp [hopfObjective] at *
    linarith
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by have HH := H x z; rw [dist_comm x z] at HH; linarith, H z x⟩

lemma isCompact_lipschitz_norm_ball (R : ℝ≥0) {M : ℝ} (_hM : 0 ≤ M) :
    IsCompact {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ M} := by
  let S := {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ M}
  have hS : IsClosed S :=
    ((isClosed_setOfPred_lipschitzWith R).preimage (continuous_pi fun x : X => continuous_eval_const x)).inter
      (isClosed_le continuous_norm continuous_const)
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  have hb : IsClosed (e '' S) := e.toHomeomorph.isClosedMap S hS
  have hc : IsCompact (e '' S) := by
    apply BoundedContinuousFunction.arzela_ascoli₂ (Icc (-M) M) isCompact_Icc (e '' S) hb
    · rintro f x ⟨φ,hφ,rfl⟩
      exact abs_le.mp ((φ.norm_coe_le_norm x).trans hφ.2)
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (R:ℝ)*r)
        (by simpa only [mul_zero, id_eq] using
          (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0)).const_mul (R:ℝ))
      intro x y f
      obtain ⟨φ,hφ,he⟩ := f.property
      have hed : (f.val : X → ℝ) = φ := by rw [← he]; rfl
      change dist (f.val x) (f.val y) ≤ (R:ℝ)*dist x y
      rw [congrFun hed x,congrFun hed y]
      exact hφ.1.dist_le_mul x y
  exact e.toHomeomorph.isCompact_image.mp hc

variable [MeasurableSpace X] [BorelSpace X]
lemma potential_integral_lipschitz (μ : Measure X) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (fun f : C(X,ℝ) => ∫ x, f x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hf : Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g μ := g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [NNReal.coe_one,one_mul,dist_eq_norm,← integral_sub hf hg]
  calc
    _ ≤ ∫ x, ‖f x-g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, dist f g ∂μ := integral_mono (hf.sub hg).norm (integrable_const _) (fun x => by
      simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist x (f := f) (g := g))
    _ = dist f g := by simp

lemma bounded_dual_improvement {R : ℝ≥0} (hR : ∀ x y : X, dist x y ≤ R)
    (o : X) (a b : C_c(X,ℝ)) (hab : marginalSum (a,b) ≤ quadraticCost 1) :
    ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
      ‖φ‖ ≤ (R:ℝ)^2 ∧ ‖ψ‖ ≤ (R:ℝ)^2 ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        (∫ x, a x ∂μ)+(∫ y, b y ∂ν) ≤ (∫ x, φ x ∂μ)+(∫ y, ψ y ∂ν) := by
  have hb : ∀ y, -‖b.toContinuousMap‖ ≤ -b y := fun y => by
    have H := b.toContinuousMap.norm_coe_le_norm y
    exact neg_le_neg (le_abs_self _ |>.trans H)
  let v := hopfLax (fun y => -b y) 1
  have hvL : LipschitzWith R v := hopfLax_lipschitz_diameter hR b.continuous.neg hb
  let φ : C(X,ℝ) := ⟨fun x => v x-v o,hvL.continuous.sub continuous_const⟩
  have hφL : LipschitzWith R φ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (v x-v o) (v y-v o) ≤ (R:ℝ)*dist x y
    simpa only [dist_sub_right] using hvL.dist_le_mul x y
  have hφabs (x : X) : |φ x| ≤ (R:ℝ)^2 := by
    have H := hvL.dist_le_mul x o
    change |v x-v o| ≤ _
    rw [Real.dist_eq] at H
    exact H.trans (by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (hR x o) R.coe_nonneg)
  have hφnorm : ‖φ‖ ≤ (R:ℝ)^2 := (ContinuousMap.norm_le φ (sq_nonneg _)).mpr hφabs
  have hφlower : ∀ x, -(R:ℝ)^2 ≤ -φ x := fun x => neg_le_neg (le_abs_self _ |>.trans (hφabs x))
  let w := hopfLax (fun x => -φ x) 1
  have hwL : LipschitzWith R w := hopfLax_lipschitz_diameter hR φ.continuous.neg hφlower
  let ψ : C(X,ℝ) := ⟨w,hwL.continuous⟩
  have hψabs (y : X) : |ψ y| ≤ (R:ℝ)^2 := by
    apply abs_le.mpr
    constructor
    · exact lower_le_hopfLax hφlower (by norm_num : (0:ℝ)<1) y
    · have H := hopfLax_le_objective hφlower (by norm_num : (0:ℝ)<1) y o
      have HR := hR y o
      change hopfLax _ _ _ ≤ _
      have hφo : φ o = 0 := sub_self _
      dsimp only [hopfObjective] at H
      rw [hφo] at H
      nlinarith [sq_le_sq₀ dist_nonneg R.coe_nonneg |>.mpr HR,sq_nonneg (R:ℝ)]
  refine ⟨φ,ψ,hφL,hwL,hφnorm,(ContinuousMap.norm_le ψ (sq_nonneg _)).mpr hψabs,?_,?_⟩
  · intro x y
    have H := hopfLax_le_objective hφlower (by norm_num : (0:ℝ)<1) y x
    change φ x+w y ≤ _
    dsimp [w,hopfObjective] at *
    rw [dist_comm y x] at H
    linarith
  · intro μ ν _ _
    have haφ (x : X) : a x ≤ φ x+v o := by
      suffices a x ≤ v x by dsimp [φ]; linarith
      apply le_csInf ⟨hopfObjective (fun y => -b y) 1 x x,mem_range_self x⟩
      rintro r ⟨y,rfl⟩
      have H := hab (x,y)
      change a x+b y ≤ dist x y^2/(2*1) at H
      dsimp [hopfObjective]
      linarith
    have hbψ (y : X) : b y ≤ ψ y-v o := by
      suffices b y+v o ≤ w y by change b y ≤ w y-v o; linarith
      apply le_csInf ⟨hopfObjective (fun x => -φ x) 1 y y,mem_range_self y⟩
      rintro r ⟨x,rfl⟩
      have H := hopfLax_le_objective hb (by norm_num : (0:ℝ)<1) x y
      change v x ≤ -b y+dist x y^2/(2*1) at H
      dsimp [hopfObjective,φ]
      rw [dist_comm y x]
      linarith
    have hφi : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hψi : Integrable ψ ν := ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have H := integral_mono a.integrable (hφi.add (integrable_const _)) haφ
    have I := integral_mono b.integrable (hψi.sub (integrable_const _)) hbψ
    change (∫ x,a x ∂μ) ≤ ∫ x,φ x+v o ∂μ at H
    change (∫ x,b x ∂ν) ≤ ∫ x,ψ x-v o ∂ν at I
    rw [integral_add hφi (integrable_const _),integral_const] at H
    rw [integral_sub hψi (integrable_const _),integral_const] at I
    simp only [probReal_univ,one_smul] at H I
    linarith

lemma compact_kantorovich_potentials (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {R : ℝ≥0}
    (hR : ∀ x y : X, dist x y ≤ R) (o : X) :
    ∃ q : Measure (X×X), IsProbabilityMeasure q ∧
      q.map Prod.fst = μ ∧ q.map Prod.snd = ν ∧
      (∀ q' : Measure (X×X), q'.map Prod.fst = μ → q'.map Prod.snd = ν →
        (∫ p, quadraticCost 1 p ∂q) ≤ ∫ p, quadraticCost 1 p ∂q') ∧
      ∃ φ ψ : C(X,ℝ), LipschitzWith R φ ∧ LipschitzWith R ψ ∧
        (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
        ∀ᵐ p ∂q, φ p.1+ψ p.2 = dist p.1 p.2^2/2 := by
  obtain ⟨q,hqp,hq0,hq1,hqmin,hqdual⟩ := compact_kantorovich_duality μ ν (quadraticCost 1)
  let _ := hqp
  let K := {f : C(X,ℝ) | LipschitzWith R f ∧ ‖f‖ ≤ (R:ℝ)^2}
  let A := {p : C(X,ℝ)×C(X,ℝ) | ∀ x y, p.1 x+p.2 y ≤ dist x y^2/2}
  let S := (K×ˢK) ∩ A
  have hK : IsCompact K := isCompact_lipschitz_norm_ball R (sq_nonneg _)
  have hA : IsClosed A := by
    simp only [A,ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_le ((continuous_eval_const x).comp continuous_fst |>.add
      ((continuous_eval_const y).comp continuous_snd)) continuous_const
  have hS : IsCompact S := (hK.prod hK).inter_right hA
  have happrox (ε : ℝ) (hε : 0 < ε) : ∃ p ∈ S,
      (∫ z,quadraticCost 1 z ∂q) < (∫ x,p.1 x ∂μ)+(∫ y,p.2 y ∂ν)+ε := by
    obtain ⟨⟨a,b⟩,hab,hεab⟩ := hqdual ε hε
    obtain ⟨φ,ψ,hφL,hψL,hφB,hψB,hφψ,hI⟩ := bounded_dual_improvement hR o a b hab
    refine ⟨(φ,ψ),⟨⟨⟨hφL,hφB⟩,⟨hψL,hψB⟩⟩,hφψ⟩,?_⟩
    change (∫ z,quadraticCost 1 z ∂q) < (∫ x,φ x ∂μ)+(∫ y,ψ y ∂ν)+ε
    change (∫ z,quadraticCost 1 z ∂q) < (∫ x,a x ∂μ)+(∫ y,b y ∂ν)+ε at hεab
    have HH := hI μ ν
    linarith
  have hSne : S.Nonempty := by obtain ⟨p,hp,_⟩ := happrox 1 (by norm_num); exact ⟨p,hp⟩
  let I : C(X,ℝ)×C(X,ℝ) → ℝ := fun p => (∫ x,p.1 x ∂μ)+(∫ y,p.2 y ∂ν)
  have hI : Continuous I := ((potential_integral_lipschitz μ).continuous.comp continuous_fst).add
    ((potential_integral_lipschitz ν).continuous.comp continuous_snd)
  obtain ⟨p,hp,hmax⟩ := hS.exists_isMaxOn hSne hI.continuousOn
  have hge : (∫ z,quadraticCost 1 z ∂q) ≤ I p := by
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨r,hr,hir⟩ := happrox ε hε
    have HH := hmax hr
    change (∫ x,r.1 x ∂μ)+(∫ y,r.2 y ∂ν) ≤ I p at HH
    linarith
  let φ : C_c(X,ℝ) := ⟨p.1,HasCompactSupport.of_compactSpace _⟩
  let ψ : C_c(X,ℝ) := ⟨p.2,HasCompactSupport.of_compactSpace _⟩
  have hsum : (∫ z,marginalSum (φ,ψ) z ∂q) = I p :=
    integral_marginalSum_of_marginals μ ν hq0 hq1 (φ,ψ)
  have hle : marginalSum (φ,ψ) ≤ quadraticCost 1 := by
    intro z
    simpa only [marginalSum_apply,quadraticCost_apply,mul_one,φ,ψ,CompactlySupportedContinuousMap.coe_mk] using hp.2 z.1 z.2
  have heq : ∀ᵐ z ∂q,marginalSum (φ,ψ) z = quadraticCost 1 z := by
    apply (integral_eq_iff_of_ae_le (marginalSum (φ,ψ)).integrable (quadraticCost 1).integrable
      (ae_of_all _ hle)).mp
    apply le_antisymm (integral_mono (marginalSum (φ,ψ)).integrable (quadraticCost 1).integrable hle)
    rw [hsum]
    exact hge
  refine ⟨q,hqp,hq0,hq1,hqmin,p.1,p.2,hp.1.1.1,hp.1.2.1,hp.2,?_⟩
  simpa only [marginalSum_apply,quadraticCost_apply,mul_one,φ,ψ,CompactlySupportedContinuousMap.coe_mk] using heq

end WeakHessianTransport

end
end InlinedFile0

end OAI
