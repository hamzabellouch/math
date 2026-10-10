import OAI.Analysis.FiniteFactor.Diffuse.OperatorCesaro

namespace OAI

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Nonhyperlinear.Diffuseness
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cesaro_on_closedRange (S : H →L[ℂ] H) (hS : ‖S‖≤1) (x : H)
    (hx : x∈(1-S).range.topologicalClosure) :
    Tendsto (fun n=>cesaro S n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hcl : x∈closure ((1-S).range : Set H) := hx
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hcl (ε/2) (by positivity)
  obtain ⟨z,rfl⟩ := hy
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (cesaro_on_range S hS z) (ε/2) (by positivity)
  refine ⟨N,fun n hn=>?_⟩
  rw [dist_zero_right]
  have he : cesaro S n x = cesaro S n (x-(1-S) z)+cesaro S n ((1-S) z) := by
    rw [map_sub]; abel
  rw [he]
  have hh := hN n hn
  rw [dist_zero_right] at hh
  rw [dist_eq_norm] at hxy
  change ‖x-(1-S) z‖<ε/2 at hxy
  exact (norm_add_le _ _).trans_lt (by linarith [cesaro_apply_norm_le S hS n (x-(1-S) z)])

omit [CompleteSpace H] in
lemma cesaro_fixed [CompleteSpace H] (S : H →L[ℂ] H) (n : ℕ) (x : H) (hx : S x=x) :
    cesaro S n x=x := by
  have hp : ∀k:ℕ,(S^k) x=x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ',mul_apply_eq_comp,ih,hx]
  simp only [cesaro,smul_apply,sum_apply,hp,
    Finset.sum_const,Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n),one_smul]

/-- The Hilbert mean ergodic theorem for a selfadjoint contraction, proved
using telescoping on the dense range and the fixed-space orthogonal projection. -/
theorem cesaro_tendsto_fixedProjection (S : H →L[ℂ] H)
    (hS : ‖S‖≤1) (hstar : star S=S) (x : H) :
    Tendsto (fun n=>cesaro S n x) atTop (𝓝 ((1-S).ker.starProjection x)) := by
  let K := (1-S).ker
  let : CompleteSpace K := (1-S).isClosed_ker.completeSpace_coe
  have hP : S (K.starProjection x)=K.starProjection x := by
    have h := K.starProjection_apply_mem x
    change (K.starProjection x)-S (K.starProjection x)=0 at h
    exact (sub_eq_zero.mp h).symm
  have hk : Kᗮ=(1-S).range.topologicalClosure := by
    have hh := ContinuousLinearMap.orthogonal_ker (1-S)
    rw [←ContinuousLinearMap.star_eq_adjoint] at hh
    simpa only [star_sub,star_one,hstar] using hh
  have hr : x-K.starProjection x∈(1-S).range.topologicalClosure := by
    rw [←hk]
    exact K.sub_starProjection_mem_orthogonal x
  have ht := (cesaro_on_closedRange S hS (x-K.starProjection x) hr).add_const (K.starProjection x)
  simp only [zero_add] at ht
  convert ht using 1
  funext n
  rw [map_sub,cesaro_fixed S n _ hP,sub_add_cancel]

end Nonhyperlinear.Diffuseness

end

end OAI
