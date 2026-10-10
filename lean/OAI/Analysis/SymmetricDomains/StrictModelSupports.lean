import Mathlib

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Filter Metric Complex
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma injective_squared_lower_bound [FiniteDimensional ℂ E]
    (J : E →ₗ[ℂ] F) (hJ : Function.Injective J) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, c*‖z‖^2 ≤ ‖J z‖^2 := by
  obtain ⟨K,hK,hbound⟩ := J.injective_iff_antilipschitz.mp hJ
  have hK' : 0 < (K : ℝ) := hK
  refine ⟨((K:ℝ)^2)⁻¹,inv_pos.mpr (sq_pos_of_pos hK'),fun z => ?_⟩
  have h := ZeroHomClass.bound_of_antilipschitz J hbound z
  have hsq : ‖z‖^2 ≤ (K:ℝ)^2*‖J z‖^2 := by
    nlinarith [norm_nonneg z,norm_nonneg (J z)]
  exact (inv_mul_le_iff₀ (sq_pos_of_pos hK')).mpr hsq

lemma cancel_quadratic_support {W : Type*} {D : Set (E × W)}
    (hinv : ∀ x ∈ D, (I • x.1,x.2) ∈ D)
    (J : E →ₗ[ℂ] F) (a : W → ℝ) (P : E → ℂ)
    (hP : ∀ z, P (I • z) = -P z)
    (hbound : ∀ x ∈ D, ‖J x.1‖^2 ≤ a x.2+(P x.1).re) :
    ∀ x ∈ D, ‖J x.1‖^2 ≤ a x.2 := by
  intro x hx
  have h1 := hbound x hx
  have h2 := hbound (I • x.1,x.2) (hinv x hx)
  simp only [map_smul,norm_smul,norm_I,one_mul,hP,neg_re] at h2
  linarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma positive_on_open_of_nonnegative (ℓ : V →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {C : Set V} (hC : IsOpen C) (hnonneg : ∀ y ∈ C, 0 ≤ ℓ y) :
    ∀ y ∈ C, 0 < ℓ y := by
  intro y hy
  have h0 := hnonneg y hy
  by_contra h
  have hzero : ℓ y = 0 := by linarith
  have hex : ∃ v : V, ℓ v ≠ 0 := by
    by_contra hv
    push Not at hv
    apply hℓ
    ext v
    exact hv v
  obtain ⟨v,hv⟩ := hex
  let w : V := -(ℓ v)⁻¹ • v
  have hw : ℓ w = -1 := by simp [w,hv]
  have ht : Tendsto (fun t : ℝ => y+t • w) (𝓝 (0:ℝ)) (𝓝 y) := by
    have hc : Continuous (fun t : ℝ => y+t • w) := by fun_prop
    simpa using hc.tendsto 0
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, y+t • w ∈ C :=
    (ht.eventually (hC.mem_nhds hy)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,htp,htC⟩ := ((show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).and hevent).exists
  have hbad := hnonneg (y+t • w) htC
  simp only [map_add,map_smul,hzero,hw,smul_eq_mul,mul_neg,mul_one,zero_add] at hbad
  exact (not_le_of_gt htp) (neg_nonneg.mp hbad)

theorem strict_model_supports [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {k : ℕ} (H : E → Fin k → ℝ) (hH0 : H 0 = 0)
    {C : Set (Fin k → ℝ)} (hC : IsOpen C) (hne : C.Nonempty)
    (hcone : ∀ r : ℝ, 0 < r → ∀ y ∈ C, r • y ∈ C)
    (ℓ : (Fin k → ℝ) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (c : ℝ)
    (hbound : ∀ (z : E) (v : Fin k → ℝ), v-H z ∈ C → c*‖z‖^2 ≤ ℓ v) :
    (∀ y ∈ C, 0 < ℓ y) ∧ ∀ z, c*‖z‖^2 ≤ ℓ (H z) := by
  constructor
  · apply positive_on_open_of_nonnegative ℓ hℓ hC
    intro y hy
    simpa only [hH0,sub_zero,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] using
      hbound 0 y (by simpa only [hH0,sub_zero] using hy)
  · intro z
    obtain ⟨y,hy⟩ := hne
    have hb : ∀ᶠ r : ℝ in 𝓝[>] 0, c*‖z‖^2 ≤ ℓ (H z+r • y) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      apply hbound
      simpa only [add_sub_cancel_left] using hcone r hr y hy
    have ht : Tendsto (fun r : ℝ => ℓ (H z+r • y)) (𝓝[>] 0) (𝓝 (ℓ (H z))) := by
      have hc : Continuous (fun r : ℝ => ℓ (H z+r • y)) := by fun_prop
      simpa using (hc.tendsto 0).mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    exact ge_of_tendsto ht hb

end Release061.Hermitian

end

end OAI
