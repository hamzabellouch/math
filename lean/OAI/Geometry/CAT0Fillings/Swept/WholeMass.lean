import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Summation
import OAI.Geometry.CAT0Fillings.Prism.ClosedFamily
import OAI.Geometry.CAT0Fillings.Radial.Integrability
import OAI.Geometry.CAT0Fillings.Swept.Measure

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
lemma swept_fraction_lipschitz [CompactSpace X] {g : X → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    LipschitzWith (K+1) (fun p : ClosedCylinder X => 1-p.1.val*g p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hp : |p.1.val| ≤ 1 := by rw [abs_of_nonneg p.1.2.1]; exact p.1.2.2
  have hq : |g q.2| ≤ 1 := by rw [abs_of_nonneg (hg0 _)]; exact hg1 _
  have ht : |p.1.val-q.1.val| ≤ dist p q := le_max_left _ _
  have hx : dist p.2 q.2 ≤ dist p q := le_max_right _ _
  rw [Real.dist_eq,show 1-p.1.val*g p.2-(1-q.1.val*g q.2) =
    -(p.1.val*(g p.2-g q.2)+(p.1.val-q.1.val)*g q.2) by ring,abs_neg]
  calc _ ≤ |p.1.val*(g p.2-g q.2)|+|(p.1.val-q.1.val)*g q.2| := abs_add_le _ _
    _ ≤ |g p.2-g q.2|+|p.1.val-q.1.val| := by
      simp only [abs_mul]
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hp)
        (mul_le_of_le_one_right (abs_nonneg _) hq)
    _ ≤ (K:ℝ)*dist p q+dist p q := by
      exact add_le_add ((hg.dist_le_mul p.2 q.2).trans
        (mul_le_mul_of_nonneg_left hx K.coe_nonneg)) ht
    _ = _ := by push_cast; ring

theorem exists_swept_radial_map
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    ∃ F : ClosedCylinder X → X, (∃ L, LipschitzWith L F) ∧
      (∀ p, F p = seg o p.2 (1-p.1.val*g p.2)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y,
        F (cylinderClamp (t,y)) = seg o y (1-t*g y)) := by
  let R : ℝ≥0 := ⟨Metric.diam (univ : Set X),Metric.diam_nonneg⟩
  have hl := swept_fraction_lipschitz hg hg0 hg1
  have hR : ∀ p : ClosedCylinder X, dist o p.2 ≤ R := fun p =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  have hs (p : ClosedCylinder X) : 1-p.1.val*g p.2 ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (((mul_le_mul_of_nonneg_right p.1.2.2 (hg0 _)).trans_eq
        (one_mul _)).trans (hg1 _))
    · exact sub_le_self _ (mul_nonneg p.1.2.1 (hg0 _))
  refine ⟨fun p => seg o p.2 (1-p.1.val*g p.2),⟨1+R*(K+1),?_⟩,
    fun _ => rfl,?_⟩
  · rw [←lipschitzOnWith_univ]
    exact radial_lipschitzOnWith seg hseg hcomp LipschitzWith.prod_snd.lipschitzOnWith
      hl.lipschitzOnWith (fun x _ => hs x) o (fun x _ => hR x)
  · intro t ht y
    simp only [cylinderClamp,projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) ht]

end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

theorem whole_swept_mass_le
    (C : ℕ → IntegerChart X k) (_hs : Summable (fun i => mass (C i).action))
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg KF : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (F : ClosedCylinder X → X) (hF : LipschitzWith KF F)
    (hFeq : ∀ t ∈ Icc (0:ℝ) 1, ∀ y,
      F (cylinderClamp (t,y)) = seg o y (1-t*g y))
    (p : ℕ → Euc k → Seminorm ℝ (Euc k))
    (hI : ∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z)
      (volume.restrict (C i).domain))
    (hIs : Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
      ∂volume.restrict (C i).domain))
    (hp : ∀ i, ∀ᵐ z ∂volume.restrict (C i).domain,
      (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        (C i).domain (C i).param (p i z) ⟨z,hz⟩) ∧
      (∀ u v, p i z (u+v)^2+p i z (u-v)^2 = 2*p i z u^2+2*p i z v^2) ∧
      (∀ v, p i z v = 0 ↔ v = 0)) :
    mass (pushCurrent F (closedPrismFamily C)) ≤
      ∑' i, ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
      ∂volume.restrict (C i).domain := by
  let I (i : ℕ) := ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
    ∂volume.restrict (C i).domain
  let S (i : ℕ) := pushCurrent F (C i).closedPrism.action
  have hS (i : ℕ) : IsMetricCurrent (S i) :=
    pushCurrent_isMetricCurrent (C i).closedPrism.action_isMetricCurrent hF
  have hle (i : ℕ) : mass (S i) ≤ I i := by
    dsimp only [S]
    rw [(C i).closedPrism_action,←pushCurrent_comp hF]
    exact (C i).swept_prism_mass_le seg hcomp o g hg hg0 hg1
      (F ∘ cylinderClamp) (hF.comp cylinderClamp_lipschitz) hFeq (p i) (hI i) (hp i)
  have hsum : Summable (fun i => mass (S i)) :=
    hIs.of_nonneg_of_le (fun _ => mass_nonneg _) hle
  have heq : pushCurrent F (closedPrismFamily C) = fun b π => ∑' i, S i b π := by
    funext b π
    by_cases hab : Admissible b π
    · simp only [S,pushCurrent_apply _ _ hab,closedPrismFamily_action]
    · simp only [S,pushCurrent,ite_eq_right hab,tsum_zero]
  rw [heq]
  exact (mass_tsum_le hS hsum).trans (hsum.tsum_le_tsum hle hIs)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma summable_swept_integrals [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (C : ℕ → IntegerChart X k) (p : ℕ → Euc k → Seminorm ℝ (Euc k))
    (hpm : ∀ i v, Measurable (fun z => p i z v))
    (hp : ∀ i, ∀ᵐ z ∂volume.restrict (C i).domain,
      (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        (C i).domain (C i).param (p i z) ⟨z,hz⟩) ∧
      (∀ u v, p i z (u+v)^2+p i z (u-v)^2 = 2*p i z u^2+2*p i z v^2) ∧
      (∀ v, p i z v = 0 ↔ v = 0))
    (hρ : ∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict (C i).domain))
    (hρs : Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
      ∂volume.restrict (C i).domain))
    (o : X) {g : X → ℝ} {Kg : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) {B : ℝ} (hB : ∀ y, dist o y*g y ≤ B) :
    (∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z)
      (volume.restrict (C i).domain)) ∧
    Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
      ∂volume.restrict (C i).domain) := by
  have hI i := (C i).integrable_sweptWeight (p i) (hpm i) (hp i) (hρ i) o hg hg0 hB
  refine ⟨hI,(hρs.mul_left B).of_nonneg_of_le ?_ ?_⟩
  · intro i
    apply integral_nonneg_of_ae
    exact ((C i).ae_sweptWeight_nonneg (p i) o hg0).mono fun z hz => mul_nonneg (abs_nonneg _) hz
  · intro i
    rw [←integral_const_mul]
    apply integral_mono_ae (hI i) ((hρ i).const_mul B)
    filter_upwards [(C i).ae_sweptWeight_bound (p i) (hp i) o hg0 hB] with z hz
    exact (mul_le_mul_of_nonneg_left hz (abs_nonneg _)).trans_eq (by ring)

end CAT0Fillings
end

end OAI
