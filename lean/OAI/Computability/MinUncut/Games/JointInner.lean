import Mathlib
import OAI.Computability.MinUncut.Estimates.SelectedProject

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
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite
open scoped BigOperators
local instance jointInnerDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W ι : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W] [Fintype ι]

lemma maskProject_selfadjoint (S : Finset R) (f g : (R → W) → ℝ) :
    (𝔼 B, f B * maskProject S g B) = 𝔼 B, maskProject S f B * g B := by
  rw [← parseval_inner, ← parseval_inner]
  simp only [coefficient_maskProject]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs <;> ring

lemma maskProject_idempotent (S T : Finset R) (f : (R → W) → ℝ) (B : R → W) :
    maskProject S (maskProject T f) B = if S=T then maskProject S f B else 0 := by
  rw [maskProject_expansion]
  simp only [coefficient_maskProject]
  by_cases h : S=T
  · subst T
    simp only [↓reduceIte]
    rw [maskProject_expansion]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs <;> simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro α _
    split_ifs with hS hT
    · exact (h (hS.symm.trans hT)).elim
    · simp
    · rfl

lemma maskProject_inner (S T : Finset R) (f g : (R → W) → ℝ) :
    (𝔼 B, maskProject S f B * maskProject T g B) =
      if S=T then (𝔼 B, f B * maskProject S g B) else 0 := by
  rw [← maskProject_selfadjoint]
  simp_rw [maskProject_idempotent]
  split_ifs with h
  · rfl
  · simp

omit [AddCommGroup W] [Module F₂ W] in
lemma maskHermite_eq (S : Finset R) (I : ι → ℕ) (u : (R → W) → (ι → ℝ) → ℝ)
    (B : R → W) (c : ι → ℝ) :
    maskHermite S I u B c = psi I c * maskProject S (fun D => GaussianHermite.coeff (u D) I) B := by
  unfold maskHermite maskProject hermiteComponent GaussianHermite.coeff
  simp only [mul_left_comm _ (psi I c), ← Finset.mul_expect]

def jointInner (u v : (R → W) → (ι → ℝ) → ℝ) : ℝ :=
  𝔼 B, ∫ c, u B c * v B c ∂γpi ι

def jointEnergy (u : (R → W) → (ι → ℝ) → ℝ) : ℝ :=
  𝔼 B, ∫ c, (u B c)^2 ∂γpi ι

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointEnergy_nonneg (u : (R → W) → (ι → ℝ) → ℝ) : 0 ≤ jointEnergy u :=
  Finset.expect_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_self (u : (R → W) → (ι → ℝ) → ℝ) : jointInner u u = jointEnergy u := by
  simp only [jointInner, jointEnergy, pow_two]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_symm (u v : (R → W) → (ι → ℝ) → ℝ) : jointInner u v = jointInner v u := by
  simp only [jointInner, mul_comm]

lemma jointInner_maskHermite (S T : Finset R) (I J : ι → ℕ)
    (u v : (R → W) → (ι → ℝ) → ℝ) :
    jointInner (maskHermite S I u) (maskHermite T J v) =
      if I=J then if S=T then
        (𝔼 B, GaussianHermite.coeff (u B) I * maskProject S (fun D => GaussianHermite.coeff (v D) J) B) else 0 else 0 := by
  classical
  unfold jointInner
  simp only [maskHermite_eq]
  have h (B : R → W) : (∫ c, (psi I c * maskProject S (fun D => GaussianHermite.coeff (u D) I) B) *
      (psi J c * maskProject T (fun D => GaussianHermite.coeff (v D) J) B) ∂γpi ι) =
      (if I=J then 1 else 0) * (maskProject S (fun D => GaussianHermite.coeff (u D) I) B *
        maskProject T (fun D => GaussianHermite.coeff (v D) J) B) := by
    simp_rw [mul_mul_mul_comm (psi I _) _ (psi J _) _]
    rw [integral_mul_const, psi_product]
  simp_rw [h, ← Finset.mul_expect, maskProject_inner]
  split_ifs <;> simp_all

lemma jointInner_source_component (S : Finset R) (I : ι → ℕ)
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointInner u (maskHermite S I u) = jointEnergy (maskHermite S I u) := by
  rw [← jointInner_self, jointInner_maskHermite]
  simp only [↓reduceIte]
  unfold jointInner
  apply Finset.expect_congr rfl
  intro B _
  simp only [maskHermite_eq, ← mul_assoc, integral_mul_const]
  congr 1
  unfold GaussianHermite.coeff
  simp only [mul_comm]

lemma components_orthogonal (a b : Finset R × (ι → ℕ)) (hab : a ≠ b)
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointInner (maskHermite a.1 a.2 u) (maskHermite b.1 b.2 u) = 0 := by
  rw [jointInner_maskHermite]
  split_ifs with hI hS
  · exact (hab (Prod.ext hS hI)).elim
  · rfl
  · rfl

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_sum_right {T : Type*} (s : Finset T)
    (u : (R → W) → (ι → ℝ) → ℝ) (v : T → (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ t ∈ s, ∀ B, MemLp (v t B) 2 (γpi ι)) :
    jointInner u (fun B c => ∑ t ∈ s, v t B c) = ∑ t ∈ s, jointInner u (v t) := by
  unfold jointInner
  simp only [Finset.mul_sum]
  have hh (B) : (∫ c, ∑ t ∈ s, u B c * v t B c ∂γpi ι) =
      ∑ t ∈ s, ∫ c, u B c * v t B c ∂γpi ι :=
    integral_finsetSum s (fun t ht => (hu B).integrable_mul (hv t ht B))
  simp_rw [hh]
  rw [Finset.expect_sum_comm]

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointInner_sum_left {T : Type*} (s : Finset T)
    (u : T → (R → W) → (ι → ℝ) → ℝ) (v : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ t ∈ s, ∀ B, MemLp (u t B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι)) :
    jointInner (fun B c => ∑ t ∈ s, u t B c) v = ∑ t ∈ s, jointInner (u t) v := by
  rw [jointInner_symm, jointInner_sum_right s v u hv hu]
  exact Finset.sum_congr rfl (fun t _ => jointInner_symm _ _)

lemma selectedProject_source_inner (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointInner u (selectedProject J u) = ∑ j ∈ J, jointEnergy (maskHermite j.1 j.2 u) := by
  change jointInner u (fun B c => ∑ j ∈ J, maskHermite j.1 j.2 u B c) = _
  rw [jointInner_sum_right J u _ hu (fun j _ B => memLp_maskHermite _ _ _ B)]
  exact Finset.sum_congr rfl (fun j _ => jointInner_source_component j.1 j.2 u)

lemma selectedProject_energy (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointEnergy (selectedProject J u) = ∑ j ∈ J, jointEnergy (maskHermite j.1 j.2 u) := by
  classical
  rw [← jointInner_self]
  change jointInner (fun B c => ∑ j ∈ J, maskHermite j.1 j.2 u B c) (selectedProject J u) = _
  rw [jointInner_sum_left J _ _ (fun j _ B => memLp_maskHermite _ _ _ B) (memLp_selectedProject J u)]
  apply Finset.sum_congr rfl
  intro j hj
  change jointInner (maskHermite j.1 j.2 u) (fun B c => ∑ k ∈ J, maskHermite k.1 k.2 u B c) = _
  rw [jointInner_sum_right J _ _ (memLp_maskHermite _ _ _) (fun k _ B => memLp_maskHermite _ _ _ B)]
  rw [Finset.sum_eq_single j]
  · exact jointInner_self _
  · intro k hk hkj
    exact components_orthogonal j k hkj.symm u
  · exact fun hjn => (hjn hj).elim

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma jointEnergy_sub (u v : (R → W) → (ι → ℝ) → ℝ)
    (hu : ∀ B, MemLp (u B) 2 (γpi ι)) (hv : ∀ B, MemLp (v B) 2 (γpi ι)) :
    jointEnergy (fun B c => u B c-v B c) = jointEnergy u - 2*jointInner u v + jointEnergy v := by
  have h (B) : (∫ c, (u B c-v B c)^2 ∂γpi ι) =
      (∫ c, (u B c)^2 ∂γpi ι) - 2*(∫ c, u B c*v B c ∂γpi ι) + ∫ c, (v B c)^2 ∂γpi ι := by
    simp only [sub_sq, mul_assoc]
    have huv : Integrable (fun c => 2*(u B c*v B c)) (γpi ι) := ((hu B).integrable_mul (hv B)).const_mul 2
    have hsub : Integrable (fun c => (u B c)^2-2*(u B c*v B c)) (γpi ι) := (hu B).integrable_sq.sub huv
    rw [integral_add hsub (hv B).integrable_sq, integral_sub (hu B).integrable_sq huv, integral_const_mul]
  simp only [jointEnergy, jointInner, h, Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect]

theorem selectedProject_energy_le (J : Finset (Finset R × (ι → ℕ)))
    (u : (R → W) → (ι → ℝ) → ℝ) (hu : ∀ B, MemLp (u B) 2 (γpi ι)) :
    jointEnergy (selectedProject J u) ≤ jointEnergy u := by
  have h := jointEnergy_nonneg (fun B c => u B c-selectedProject J u B c)
  rw [jointEnergy_sub u _ hu (memLp_selectedProject J u), selectedProject_source_inner J u hu,
    ← selectedProject_energy] at h
  linarith

omit [AddCommGroup W] [Module F₂ W] in
lemma selectedProject_sdiff (J K : Finset (Finset R × (ι → ℕ))) (hK : K ⊆ J)
    (u : (R → W) → (ι → ℝ) → ℝ) (B : R → W) (c : ι → ℝ) :
    selectedProject J u B c-selectedProject K u B c = selectedProject (J\K) u B c := by
  classical
  unfold selectedProject
  have h := Finset.sum_sdiff hK (f := fun j => maskHermite j.1 j.2 u B c)
  linarith

lemma selectedProject_loss_energy (J K : Finset (Finset R × (ι → ℕ))) (hK : K ⊆ J)
    (u : (R → W) → (ι → ℝ) → ℝ) :
    jointEnergy (fun B c => selectedProject J u B c-selectedProject K u B c) =
      ∑ j ∈ J\K, jointEnergy (maskHermite j.1 j.2 u) := by
  simp_rw [selectedProject_sdiff J K hK]
  exact selectedProject_energy _ u
end MinUncut.RowNoise

end

end OAI
