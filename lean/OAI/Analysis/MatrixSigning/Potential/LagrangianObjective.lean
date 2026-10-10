import Mathlib
import OAI.Analysis.MatrixSigning.Potential.TightComplementarity
import OAI.Analysis.MatrixSigning.Matrices.Sandwich2

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma lagrangian_le_objective (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (P Q : H d) (hP : P ∈ psdCone d) (hQ : Q ∈ psdCone d)
    (z : Point d) (hz : z ∈ feasible S η) :
    lagrangian ε S η P Q z ≤ objective ε z := by
  have hf := (feasible_iff_cone S η z).mp hz
  have h₁ := inner_nonneg_of_psd P (-residual S η z).1 hP hf.2.1
  have h₂ := inner_nonneg_of_psd Q (-residual S η z).2 hQ hf.2.2
  simp only [Prod.fst_neg, Prod.snd_neg, inner_neg_right] at h₁ h₂
  change objective ε z + inner ℝ P (residual S η z).1 + inner ℝ Q (residual S η z).2 ≤ _
  linarith

lemma lagrangian_eq_objective_of_tight (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (P Q : H d) (z : Point d) (hz : residual S η z = 0) :
    lagrangian ε S η P Q z = objective ε z := by
  simp only [lagrangian, hz, Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]

theorem minimizer_unique [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ A ∈ psdCone d, η A ∈ psdCone d) (hηsym : SymmetricMap η)
    {ε K : ℝ} (hε : 0 < ε)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    (z w : Point d) (hz : z ∈ feasible S η) (hw : w ∈ feasible S η)
    (hmin : ∀ v ∈ feasible S η, objective ε z ≤ objective ε v)
    (heq : objective ε z = objective ε w) : z = w := by
  obtain ⟨P,Q,hP,hQ,hPle,hQle,htr,hPX,hQY,htight,hX,hY⟩ :=
    kkt S η hηpos hηsym hε hS₁ hS₂ z hz hmin
  have h₁ := inverse_trace_gap_nonneg P z.2.1 w.2.1 hP.posSemidef hz.1.1 hw.1.1
  have h₂ := inverse_trace_gap_nonneg Q z.2.2 w.2.2 hQ.posSemidef hz.1.2 hw.1.2
  rw [hX] at h₁
  rw [hY] at h₂
  have hL : lagrangian ε S η P Q w ≤ lagrangian ε S η P Q z := by
    rw [lagrangian_eq_objective_of_tight ε S η P Q z htight, heq]
    exact lagrangian_le_objective ε S η P Q hP.posSemidef hQ.posSemidef w hw
  rw [lagrangian_separate ε S η hηsym, lagrangian_separate ε S η hηsym] at hL
  have hcoef : 1-realTrace P-realTrace Q = 0 := by linarith
  rw [hcoef, mul_zero, mul_zero] at hL
  have heX : inner ℝ P (invH z.2.1) + inner ℝ (sandwich (invH z.2.1) P) z.2.1 =
      inner ℝ P (invH w.2.1) + inner ℝ (sandwich (invH z.2.1) P) w.2.1 := by
    rw [hX]
    linarith
  have heY : inner ℝ Q (invH z.2.2) + inner ℝ (sandwich (invH z.2.2) Q) z.2.2 =
      inner ℝ Q (invH w.2.2) + inner ℝ (sandwich (invH z.2.2) Q) w.2.2 := by
    rw [hY]
    linarith
  have hzx := inverse_trace_gap_zero P z.2.1 w.2.1 hP hz.1.1 hw.1.1 heX
  have hzy := inverse_trace_gap_zero Q z.2.2 w.2.2 hQ hz.1.2 hw.1.2 heY
  apply Prod.ext
  · change z.1 + ε * realTrace (z.2.1 + z.2.2) = w.1 + ε * realTrace (w.2.1+w.2.2) at heq
    rw [hzx,hzy] at heq
    linarith
  · exact Prod.ext hzx hzy

end CurrentKS.Variational

namespace CurrentKS.PositiveMap
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cone_smul_nonneg (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C)
    {a : ℝ} (ha : 0 ≤ a) {x : E} (hx : x ∈ C) : a • x ∈ C := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simpa using h0
  · exact C.smul_mem ha hx

lemma interior_absorbs (C : ConvexCone ℝ E) {p : E}
    (hp : p ∈ interior (C : Set E)) (x : E) :
    ∃ b : ℝ, 0 ≤ b ∧ x + b • p ∈ C := by
  have hc : Continuous (fun t : ℝ => p + t • x) := by fun_prop
  have hn : ∀ᶠ t : ℝ in nhds 0, p + t • x ∈ C := by
    have h : (fun t : ℝ => p + t • x) 0 ∈ interior (C : Set E) := by simpa using hp
    exact hc.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp h)
  obtain ⟨δ, hδ, hs⟩ := Metric.mem_nhds_iff.mp hn
  have ht : 0 < δ/2 := by positivity
  have htd : δ/2 ∈ Metric.ball (0 : ℝ) δ := by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]
    linarith
  have hh := C.smul_mem (inv_pos.mpr ht) (hs htd)
  refine ⟨(δ/2)⁻¹, (inv_pos.mpr ht).le, ?_⟩
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_comm] using hh

theorem mem_of_supersolution (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C)
    (hC : IsClosed (C : Set E)) (T : E →L[ℝ] E)
    (hT : ∀ x ∈ C, T x ∈ C) {p : E} (hp : p ∈ interior (C : Set E))
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hcrit : q • p - T p ∈ C)
    {x : E} (hx : x - T x ∈ C) : x ∈ C := by
  obtain ⟨b,hb,hbp⟩ := interior_absorbs C hp x
  have hn (n : ℕ) : x + (b*q^n) • p ∈ C := by
    induction n with
    | zero => simpa using hbp
    | succ n ih =>
      have h₁ := hT _ ih
      have h₂ := cone_smul_nonneg C h0 (mul_nonneg hb (pow_nonneg hq₀ n)) hcrit
      have hh := C.add_mem hx (C.add_mem h₁ h₂)
      convert hh using 1
      simp only [map_add, map_smul, pow_succ]
      module
  have ht : Tendsto (fun n : ℕ => x + (b*q^n) • p) atTop (nhds x) := by
    have hh := ((tendsto_const_nhds (x := b)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)).smul
      (tendsto_const_nhds (x := p))
    simpa using (tendsto_const_nhds (x := x)).add hh
  exact hC.mem_of_tendsto ht (Eventually.of_forall hn)

theorem positive_inverse [FiniteDimensional ℝ E]
    (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C) (hC : IsClosed (C : Set E))
    (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : E →L[ℝ] E) (hT : ∀ x ∈ C, T x ∈ C)
    {p : E} (hp : p ∈ interior (C : Set E))
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hcrit : q • p - T p ∈ C) :
    ∃ V : E ≃L[ℝ] E, (∀ x, V x = x-T x) ∧ ∀ x ∈ C, V.symm x ∈ C := by
  let N : E →ₗ[ℝ] E := LinearMap.id - T.toLinearMap
  have hker (x : E) (hx : N x = 0) : x = 0 := by
    have hx' : x-T x ∈ C := by
      change N x ∈ C
      rw [hx]
      exact h0
    have hn' : -x-T (-x) ∈ C := by
      have he : -x-T (-x) = -(x-T x) := by rw [map_neg]; abel
      rw [he, show x-T x = 0 from hx, neg_zero]
      exact h0
    exact hpoint x (mem_of_supersolution C h0 hC T hT hp hq₀ hq₁ hcrit hx')
      (mem_of_supersolution C h0 hC T hT hp hq₀ hq₁ hcrit hn')
  have hinj : Function.Injective N := by
    intro x y he
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, he, sub_self]
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective N
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let V : E ≃L[ℝ] E := e.toContinuousLinearEquiv
  refine ⟨V, fun _ => rfl, fun x hx => ?_⟩
  apply mem_of_supersolution C h0 hC T hT hp hq₀ hq₁ hcrit
  change V (V.symm x) ∈ C
  rwa [V.apply_symm_apply]

theorem positive_inverse_of_gap [FiniteDimensional ℝ E]
    (C : ConvexCone ℝ E) (h0 : (0 : E) ∈ C) (hC : IsClosed (C : Set E))
    (hpoint : ∀ x ∈ C, -x ∈ C → x = 0)
    (T : E →L[ℝ] E) (hT : ∀ x ∈ C, T x ∈ C)
    {p : E} (hp : p ∈ interior (C : Set E))
    (hgap : p-T p ∈ interior (C : Set E)) :
    ∃ V : E ≃L[ℝ] E, (∀ x, V x = x-T x) ∧ ∀ x ∈ C, V.symm x ∈ C := by
  have hc : Continuous (fun t : ℝ => p-T p-t • p) := by fun_prop
  have hn : ∀ᶠ t : ℝ in nhds 0, p-T p-t • p ∈ C := by
    have h : (fun t : ℝ => p-T p-t • p) 0 ∈ interior (C : Set E) := by simpa using hgap
    exact hc.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp h)
  obtain ⟨δ,hδ,hs⟩ := Metric.mem_nhds_iff.mp hn
  let s := min (δ/2) (1/2 : ℝ)
  have hs₀ : 0 < s := lt_min (by positivity) (by norm_num)
  have hs₁ : s ≤ 1/2 := min_le_right _ _
  have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsball : s ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs₀] using hsδ
  apply positive_inverse C h0 hC hpoint T hT hp (q := 1-s) (by linarith) (by linarith)
  have he : (1-s) • p-T p = p-T p-s • p := by module
  rw [he]
  exact hs hsball

end CurrentKS.PositiveMap

end

end OAI
