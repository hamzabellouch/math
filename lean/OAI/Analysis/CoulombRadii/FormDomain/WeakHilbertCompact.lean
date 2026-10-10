import Mathlib

namespace OAI

section
open Filter Set
open scoped Topology ComplexConjugate
noncomputable section
namespace Coulomb
variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
 [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

lemma bounded_hilbert_weak_subsequence (u:ℕ → H) (C:ℝ) (hb:∀ n,‖u n‖≤C) :
    ∃ v:H, ‖v‖≤C ∧ ∃ φ:ℕ → ℕ,StrictMono φ ∧
      ∀ w:H,Tendsto (fun n => inner ℂ w (u (φ n))) atTop (𝓝 (inner ℂ w v)) := by
  let F : ℕ → WeakDual ℂ H := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n))
  have hm (n:ℕ) : F n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0:StrongDual ℂ H) C := by
    change dist (WeakDual.toStrongDual (StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (u n)))) 0 ≤ C
    have hh (g:StrongDual ℂ H) : WeakDual.toStrongDual (StrongDual.toWeakDual g)=g := by
      ext x
      rfl
    rw [hh,dist_eq_norm]
    change ‖InnerProductSpace.toDual ℂ H (u n)-0‖≤ C
    simpa only [sub_zero,LinearIsometryEquiv.norm_map] using hb n
  obtain ⟨f,hf,φ,hφ,ht⟩ := (WeakDual.isSeqCompact_closedBall (𝕜:=ℂ) (E:=H) 0 C) hm
  let v:H := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual f)
  refine ⟨v,?_,φ,hφ,?_⟩
  · simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,
      ←(InnerProductSpace.toDual ℂ H).symm.norm_map] using hf
  · intro w
    have h := (WeakBilin.eval_continuous _ w).tendsto f |>.comp ht
    have he : WeakDual.toStrongDual f w=inner ℂ v w := by
      rw [←InnerProductSpace.toDual_apply_apply]
      exact congrArg (fun g:StrongDual ℂ H => g w)
        ((InnerProductSpace.toDual ℂ H).apply_symm_apply _).symm
    change Tendsto (fun n => inner ℂ (u (φ n)) w) atTop (𝓝 (WeakDual.toStrongDual f w)) at h
    rw [he] at h
    simpa only [Function.comp_def,inner_conj_symm] using (Complex.continuous_conj.tendsto _).comp h
end Coulomb
end

end
section
open Filter Set
open scoped Topology ComplexConjugate BigOperators
noncomputable section
namespace Coulomb
variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
 [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma bounded_finite_hilbert_weak_subsequence (u:ℕ → ι → H) (K:ℝ)
    (hb:∀ n,∑ i,‖u n i‖^2≤K) :
    ∃ v:ι → H,(∑ i,‖v i‖^2)≤K ∧ ∃ φ:ℕ → ℕ,StrictMono φ ∧
      ∀ i w,Tendsto (fun n => inner ℂ w (u (φ n) i)) atTop (𝓝 (inner ℂ w (v i))) := by
  let U:ℕ → PiLp 2 (fun _:ι => H) := fun n => WithLp.toLp 2 (u n)
  have hK:0≤K := (Finset.sum_nonneg fun i _ => sq_nonneg ‖u 0 i‖).trans (hb 0)
  have hU (n:ℕ) : ‖U n‖≤Real.sqrt K := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hK,PiLp.norm_sq_eq_of_L2]
    exact hb n
  obtain ⟨v,hv,φ,hφ,hw⟩ := bounded_hilbert_weak_subsequence U (Real.sqrt K) hU
  refine ⟨fun i => v i,?_,φ,hφ,?_⟩
  · rw [←PiLp.norm_sq_eq_of_L2 (fun _:ι => H) v]
    exact (pow_le_pow_left₀ (norm_nonneg _) hv 2).trans_eq (Real.sq_sqrt hK)
  · intro i w
    have h := hw (PiLp.single 2 i w)
    have he (z:PiLp 2 (fun _:ι => H)) : inner ℂ (PiLp.single 2 i w) z = inner ℂ w (z i) := by
      simp only [PiLp.inner_apply,PiLp.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [hji]
      · simp
    simpa only [he,U,WithLp.toLp_ofLp] using h

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma weak_tendsto_norm_le {u:ℕ → H} {v:H} {C:ℝ} (hC:0≤C)
    (hw:∀ w,Tendsto (fun n => inner ℂ w (u n)) atTop (𝓝 (inner ℂ w v)))
    (hb:∀ᶠ n in atTop,‖u n‖≤C) : ‖v‖≤C := by
  have h := (hw v).norm
  have hh : ∀ᶠ n in atTop,‖inner ℂ v (u n)‖≤‖v‖*C := by
    filter_upwards [hb] with n hn
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
  have H := le_of_tendsto h hh
  rw [← inner_self_re_eq_norm, ← norm_sq_eq_re_inner] at H
  by_cases hv:‖v‖=0
  · rwa [hv]
  · have hp:0<‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    nlinarith
end Coulomb
end

end

end OAI
