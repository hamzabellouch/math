import OAI.Probability.GaussianPropeller.CapIntegral

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Coords
abbrev CS (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def split (n : ℕ) (x : CS (n+1)) : ℝ × CS n :=
  (x 0, WithLp.toLp 2 (fun i => x i.succ))
noncomputable def join (n : ℕ) (y : ℝ × CS n) : CS (n+1) :=
  WithLp.toLp 2 (Fin.cons y.1 y.2.ofLp)

lemma split_join (n : ℕ) (y : ℝ × CS n) : split n (join n y)=y := by
  rcases y with ⟨s,y⟩
  simp [split,join]

lemma join_split (n : ℕ) (x : CS (n+1)) : join n (split n x)=x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [join,split]

lemma continuous_split (n : ℕ) : Continuous (split n) := by
  unfold split
  apply Continuous.prodMk (by fun_prop)
  exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)

lemma continuous_join (n : ℕ) : Continuous (join n) := by
  unfold join
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ]
  · fun_prop
  · fun_prop

noncomputable def splitEquiv (n : ℕ) : CS (n+1) ≃ᵐ ℝ × CS n where
  toFun := split n
  invFun := join n
  left_inv := join_split n
  right_inv := split_join n
  measurable_toFun := (continuous_split n).measurable
  measurable_invFun := (continuous_join n).measurable

lemma split_measure (n : ℕ) :
    (stdGaussian (CS (n+1))).map (split n) = (gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).map_eq
  have he : (split n) ∘ WithLp.toLp 2 =
      (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0) := by
    funext x
    rfl
  rw [← map_pi_eq_stdGaussian, Measure.map_map (continuous_split n).measurable
    (PiLp.continuous_toLp 2 _).measurable, he,
    ← Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _),hm,
    ← Measure.map_prod_map _ _ measurable_id (PiLp.continuous_toLp 2 _).measurable,
    Measure.map_id,map_pi_eq_stdGaussian]

lemma measurePreserving_split (n : ℕ) : MeasurePreserving (splitEquiv n)
    (stdGaussian (CS (n+1))) ((gaussianReal 0 1).prod (stdGaussian (CS n))) :=
  ⟨(continuous_split n).measurable,split_measure n⟩

lemma integral_split (n : ℕ) (f : CS (n+1) → ℝ) :
    (∫ x, f x ∂stdGaussian (CS (n+1))) =
      ∫ y, f (join n y) ∂(gaussianReal 0 1).prod (stdGaussian (CS n)) := by
  exact ((measurePreserving_split n).symm.integral_comp (splitEquiv n).symm.measurableEmbedding f).symm

lemma norm_join_sq (n : ℕ) (y : ℝ × CS n) : ‖join n y‖^2 = y.1^2+‖y.2‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,join,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ]

lemma norm_join (n : ℕ) (y : ℝ × CS n) : ‖join n y‖ = Real.sqrt (y.1^2+‖y.2‖^2) := by
  rw [← norm_join_sq,Real.sqrt_sq (norm_nonneg _)]

lemma join_zero (n : ℕ) (y : ℝ × CS n) : join n y 0 = y.1 := by simp [join]

lemma exists_basis_zero {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (hn : Module.finrank ℝ E=n+1)
    (e : E) (he : ‖e‖=1) :
    ∃ b : OrthonormalBasis (Fin (n+1)) ℝ E, b 0=e := by
  have ho : Orthonormal ℝ (({0}:Set (Fin (n+1))).domRestrict (fun _ => e)) := by
    constructor
    · intro i; exact he
    · intro i j hij
      have hi : (i:Fin (n+1))=0 := i.2
      have hj : (j:Fin (n+1))=0 := j.2
      exact (hij (Subtype.ext (hi.trans hj.symm))).elim
  obtain ⟨b,hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (ι:=Fin (n+1)) (by simpa using hn)
  exact ⟨b,hb 0 (by simp)⟩

end GaussianPropeller.Coords

end OAI
