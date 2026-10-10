import Mathlib
import OAI.Computability.MinUncut.Analysis.SmoothingRho
import OAI.Computability.MinUncut.Games.JointInner
import OAI.Computability.MinUncut.Analysis.RowProjectedGradient

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

omit [Fintype A] in
lemma secondFailure_indicator (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) :
    secondFailure f B C σ η c p =
      (coupledAnswer f B σ η c p-coupledAnswer f C σ η c p)^2/4 := by
  have h := secondFailure_eq f B C σ η c p
  linarith

lemma secondRejection_measurable (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ) :
    Measurable (secondRejection f B C σ η) := by
  have hh (B : FaceArray A m n) : Measurable
      (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        coupledAnswer f B σ η u.1 u.2) := by
    have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
        (u.1+σ•u.2.1,u.2.2)) := by fun_prop
    exact (measurable_answer f B η).comp hm
  have hm : Measurable (fun u : (Point m n → ℝ) × ((Point m n → ℝ) × (Code m n → ℝ)) =>
      secondFailure f B C σ η u.1 u.2) := by
    simp_rw [secondFailure_indicator]
    exact ((hh B).sub (hh C)).pow_const 2 |>.div_const 4
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma secondRejection_range (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : 0≤ secondRejection f B C σ η c ∧ secondRejection f B C σ η c≤1 := by
  have hm : Measurable (secondFailure f B C σ η c) := by
    change Measurable (fun p => secondFailure f B C σ η c p)
    simp_rw [secondFailure_indicator]
    exact ((coupledAnswer_measurable f B σ η c).sub
      (coupledAnswer_measurable f C σ η c)).pow_const 2 |>.div_const 4
  have hb (p : (Point m n → ℝ) × (Code m n → ℝ)) :
      0≤ secondFailure f B C σ η c p ∧ secondFailure f B C σ η c p≤1 := by
    unfold secondFailure; split_ifs <;> norm_num
  have hi : Integrable (secondFailure f B C σ η c)
      ((gauss (Point m n)).prod (gauss (Code m n))) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb p).1]; exact (hb p).2))
  constructor
  · exact integral_nonneg (fun p => (hb p).1)
  · unfold secondRejection
    simpa only [integral_const,MeasureTheory.probReal_univ,one_smul] using
      integral_mono hi (integrable_const 1) (fun p => (hb p).2)

lemma secondRejection_integrable (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ) :
    Integrable (secondRejection f B C σ η) (gauss (Point m n)) :=
  Integrable.of_bound (secondRejection_measurable f B C σ η).aestronglyMeasurable 1
    (ae_of_all _ (fun c => by
      rw [Real.norm_eq_abs,abs_of_nonneg (secondRejection_range f B C σ η c).1]
      exact (secondRejection_range f B C σ η c).2))

lemma rowProjectedGradient_memLp (D : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) (x : Point m n) :
    MemLp (fun c => rowProjectedGradient D f σ η B c x) 2 (gauss (Point m n)) := by
  unfold rowProjectedGradient RowNoise.project
  apply memLp_finsetSum
  intro α _
  apply MemLp.mul_const
  unfold BinaryFourier.coefficient
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  exact (memLp_finsetSum _ (fun C _ => (gradient_memLp f C hσ η x).mul_const _)).mul_const _

lemma rowResidualEnergy_integrable (D : ℕ) (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ≠0) (η : ℝ) :
    Integrable (fun c => spatialEnergy (fun x => gradient f B σ η c x-
      rowProjectedGradient D f σ η B c x)) (gauss (Point m n)) := by
  unfold spatialEnergy
  exact (integrable_finsetSum _ (fun x _ =>
    ((gradient_memLp f B hσ η x).sub (rowProjectedGradient_memLp D f B hσ η x)).integrable_sq)).const_mul _

theorem gradient_row_tail_average (f : FoldedProof A) (hn : 0 < n)
    {σ a : ℝ} (hσ : σ≠0) (ha : 0≤a) (ha1 : a≤1) (η : ℝ) (D : ℕ)
    (hD : ∀ k : ℕ, D < k → 1≤(k:ℝ)*a) :
    (𝔼 B : FaceArray A m n, ∫ c, spatialEnergy (fun x =>
      gradient f B σ η c x-rowProjectedGradient D f σ η B c x) ∂gauss (Point m n)) ≤
    4*σ⁻¹^2*(𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
      RowNoise.density a B C*(∫ c, secondRejection f B C σ η c ∂gauss (Point m n))) := by
  have hl : Integrable (fun c => 𝔼 B : FaceArray A m n, spatialEnergy (fun x =>
      gradient f B σ η c x-rowProjectedGradient D f σ η B c x)) (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun B _ => rowResidualEnergy_integrable D f B hσ η)).div_const _
  have hr : Integrable (fun c => 4*σ⁻¹^2*(𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
      RowNoise.density a B C*secondRejection f B C σ η c)) (gauss (Point m n)) := by
    simp only [Fintype.expect_eq_sum_div_card]
    apply Integrable.const_mul
    apply Integrable.div_const
    apply integrable_finsetSum
    intro B _
    exact (integrable_finsetSum _ (fun C _ =>
      (secondRejection_integrable f B C σ η).const_mul _)).div_const _
  have h := integral_mono hl hr (fun c => gradient_row_tail f hn hσ ha ha1 η D hD c)
  simpa only [Fintype.expect_eq_sum_div_card,integral_div,integral_const_mul,
    integral_finsetSum _ (fun B _ => rowResidualEnergy_integrable D f B hσ η),
    integral_finsetSum _ (fun B _ =>
      (integrable_finsetSum _ (fun C _ => (secondRejection_integrable f B C σ η).const_mul _)).div_const _),
    integral_finsetSum _ (fun C _ => (secondRejection_integrable f _ C σ η).const_mul _)] using h
end MinUncut.Inner
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance secondFailureDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι] [DecidableEq ι]

lemma project_eq_mask_sum (D : ℕ) (f : (R → W) → ℝ) (B : R → W) :
    project D f B = ∑ S ∈ Finset.univ.filter (fun S : Finset R => S.card ≤ D), maskProject S f B := by
  simp only [maskProject_expansion]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]
  unfold project
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_eq_single (mask α)]
  · simp [degree]
    rfl
  · intro S _ hS
    simp [Ne.symm hS]
  · simp

omit [DecidableEq W] in
lemma project_sum {T : Type*} (s : Finset T) (D : ℕ) (u : T → (R → W) → ℝ) (B : R → W) :
    project D (fun C => ∑ t ∈ s, u t C) B = ∑ t ∈ s, project D (u t) B := by
  unfold project BinaryFourier.coefficient
  simp only [Finset.sum_mul,Finset.expect_sum_comm]
  rw [Finset.sum_comm]

omit [DecidableEq W] in
lemma project_sub (D : ℕ) (f g : (R → W) → ℝ) (B : R → W) :
    project D (fun C => f C-g C) B = project D f B-project D g B := by
  simp only [project,BinaryFourier.coefficient,sub_mul,Finset.expect_sub_distrib,Finset.sum_sub_distrib]

omit [DecidableEq W] in
lemma project_energy_le (D : ℕ) (f : (R → W) → ℝ) :
    (𝔼 B, (project D f B)^2) ≤ 𝔼 B, (f B)^2 := by
  rw [← BinaryFourier.parseval,← BinaryFourier.parseval]
  simp only [coefficient_project]
  apply Finset.sum_le_sum
  intro α _
  split_ifs <;> simp [sq_nonneg]

omit [DecidableEq ι] in
lemma project_memLp (D : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (B : R → W) :
    MemLp (fun c => project D (fun C => u C c) B) 2 (γpi ι) := by
  simp_rw [project_eq_mask_sum]
  exact memLp_finsetSum _ (fun S _ => memLp_maskProject S u hu B)

def rectangle (D s : ℕ) : Finset (Finset R × (ι → ℕ)) :=
  (Finset.univ.filter (fun S : Finset R => S.card≤D)).product (GaussianHermite.low s)

lemma rectangle_eq_composition (D s : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) :
    selectedProject (rectangle D s) u B c =
      project D (fun C => GaussianHermite.project s (u C) c) B := by
  unfold selectedProject rectangle
  have he := Finset.sum_product
    (Finset.univ.filter (fun S : Finset R => S.card≤D)) (GaussianHermite.low s)
    (fun j => maskHermite j.1 j.2 u B c)
  change (∑ j ∈ (Finset.univ.filter (fun S : Finset R => S.card≤D)) ×ˢ
    (GaussianHermite.low s), maskHermite j.1 j.2 u B c) = _
  rw [he]
  simp only [GaussianHermite.project]
  rw [project_sum]
  simp only [project_eq_mask_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro S _
  simp only [maskHermite,hermiteComponent,mul_comm]

omit [DecidableEq ι] in
lemma jointEnergy_project_le (D : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (fun B c => project D (fun C => u C c) B) ≤ jointEnergy u := by
  unfold jointEnergy
  rw [← integral_expect _ (fun B => (project_memLp D u hu B).integrable_sq),
    ← integral_expect _ (fun B => (hu B).integrable_sq)]
  apply integral_mono
  · simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun B _ => (project_memLp D u hu B).integrable_sq)).div_const _
  · simp only [Fintype.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun B _ => (hu B).integrable_sq)).div_const _
  · intro c; exact project_energy_le D (fun B => u B c)

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] [DecidableEq ι] in
lemma jointEnergy_add_le (u v : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι)) :
    jointEnergy (fun B c => u B c+v B c) ≤ 2*jointEnergy u+2*jointEnergy v := by
  have hB (B : R → W) : (∫ c, (u B c+v B c)^2 ∂γpi ι) ≤
      2*(∫ c, (u B c)^2 ∂γpi ι)+2*(∫ c, (v B c)^2 ∂γpi ι) := by
    calc
      _ ≤ ∫ c, 2*(u B c)^2+2*(v B c)^2 ∂γpi ι :=
        integral_mono ((hu B).add (hv B)).integrable_sq
          (((hu B).integrable_sq.const_mul 2).add ((hv B).integrable_sq.const_mul 2))
          (fun c => by
            change (u B c+v B c)^2 ≤ 2*(u B c)^2+2*(v B c)^2
            nlinarith [sq_nonneg (u B c-v B c)])
      _ = _ := by rw [integral_add ((hu B).integrable_sq.const_mul 2) ((hv B).integrable_sq.const_mul 2),integral_const_mul,integral_const_mul]
  simpa only [jointEnergy,Finset.expect_add_distrib,← Finset.mul_expect] using
    Finset.expect_le_expect (s := Finset.univ) (fun B _ => hB B)

theorem rectangle_residual_le (D s : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (fun B c => u B c-selectedProject (rectangle D s) u B c) ≤
      2*jointEnergy (fun B c => u B c-project D (fun C => u C c) B)+
      2*jointEnergy (fun B c => u B c-GaussianHermite.project s (u B) c) := by
  let v := fun B c => u B c-project D (fun C => u C c) B
  let w := fun B c => u B c-GaussianHermite.project s (u B) c
  have hv (B) : MemLp (v B) 2 (γpi ι) := (hu B).sub (project_memLp D u hu B)
  have hw (B) : MemLp (w B) 2 (γpi ι) := (hu B).sub (GaussianHermite.memLp_project s (u B))
  have he (B c) : u B c-selectedProject (rectangle D s) u B c =
      v B c+project D (fun C => w C c) B := by
    rw [rectangle_eq_composition]
    simp only [v,w,project_sub]
    ring
  simp_rw [he]
  exact (jointEnergy_add_le v (fun B c => project D (fun C => w C c) B) hv
    (project_memLp D w hw)).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (jointEnergy_project_le D w hw) (show (0 : ℝ) ≤ 2 by norm_num)) _)

lemma rectangle_energy_identity (D s : ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (selectedProject (rectangle D s) u) = jointEnergy u-
      jointEnergy (fun B c => u B c-selectedProject (rectangle D s) u B c) := by
  rw [jointEnergy_sub u _ hu (memLp_selectedProject _ _),
    selectedProject_source_inner _ u hu,← selectedProject_energy]
  ring
end MinUncut.RowNoise

end

end OAI
