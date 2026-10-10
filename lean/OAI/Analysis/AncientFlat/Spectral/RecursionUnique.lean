import OAI.Analysis.AncientFlat.Spectral.Recursion

namespace OAI
noncomputable section
open scoped Topology BoundedContinuousFunction
namespace PeriodicResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma loop_right_identity (P : E →L[ℂ] E) {q : ℝ} (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) (t : ℝ) :
    (q:ℂ) • (osc 1 t • resolventLoop P q t)-resolventLoop P q t*P=1 := by
  have h := hc ((q:ℂ)*osc 1 t)
    (by simp [osc_norm, Complex.norm_real, Real.norm_eq_abs, hq.le])
  rw [resolventLoop, spectrum.resolvent_eq h]
  have hu := h.unit.inv_mul
  simp only [h.unit_spec, mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at hu
  simpa only [smul_smul] using hu
lemma green_right_identity (P : E →L[ℂ] E) {q : ℝ} (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P) (n : ℤ) :
    (q:ℂ) • coeff (resolventLoop P q) (n+1)-coeff (resolventLoop P q) n*P=
      if n=0 then 1 else 0 := by
  have hf := (loop_smooth P hq hc).continuous
  have hm := coeff_map ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip P)
    (resolventLoop P q) hf n
  have he := congrArg (fun f : ℝ → (E →L[ℂ] E) => coeff f n)
    (funext (loop_right_identity P hq hc))
  change coeff (fun t => resolventLoop P q t*P) n=coeff (resolventLoop P q) n*P at hm
  rw [coeff_sub (fun t => (q:ℂ) • (osc 1 t • resolventLoop P q t))
    (fun t => resolventLoop P q t*P)
    (((osc_continuous 1).smul hf).const_smul (q:ℂ))
    (hf.mul continuous_const), coeff_smul, coeff_shift, hm, coeff_const] at he
  exact he
end PeriodicResolvent
namespace FlatRecursion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
def difference (P : E →L[ℂ] E) (q : ℂ) : (ℤ →ᵇ E) →L[ℂ] (ℤ →ᵇ E) :=
  q • BoundedContinuousFunction.compContinuousCLM E ℂ (shift (-1))-
    P.compLeftContinuousBounded ℤ
omit [CompleteSpace E] in
@[simp] lemma difference_apply (P : E →L[ℂ] E) (q : ℂ) (f : ℤ →ᵇ E) (j : ℤ) :
    difference P q f j=q • f (j+1)-P (f j) := by
  change q • f (j-(-1))-P (f j)=_
  congr 3
lemma greenOperator_left_inverse (P : E →L[ℂ] E) (q : ℂ) (G : ℤ → E →L[ℂ] E)
    (hG : Summable (fun n => ‖G n‖))
    (hrec : ∀ n : ℤ, q • G (n+1)-G n*P=if n=0 then 1 else 0)
    (f : ℤ →ᵇ E) : greenOperator G (difference P q f)=f := by
  ext j
  rw [greenOperator_apply G hG]
  simp only [difference_apply, map_sub, map_smul]
  have hs : Summable (fun n : ℤ => G n (f (j+1-n))) := convolution_summable G hG f (j+1)
  have hsp : Summable (fun n : ℤ => G n (P (f (j-n)))) :=
    convolution_summable G hG (P.compLeftContinuousBounded ℤ f) j
  have hs2 : Summable (fun n : ℤ => G (n+1) (f (j-n))) := by
    convert hs.comp_injective (i := fun n : ℤ => n+1) (fun a b h => add_right_cancel h) using 1
    funext n
    dsimp
    congr 2
    omega
  have hshift : (∑' n : ℤ, q • G n (f (j-n+1)))=∑' n : ℤ, q • G (n+1) (f (j-n)) := by
    rw [← (Equiv.addRight (1:ℤ)).tsum_eq]
    congr 1
    funext n
    simp only [Equiv.coe_addRight]
    congr 3
    omega
  have hs1 : Summable (fun n : ℤ => q • G n (f (j-n+1))) := by
    convert hs.const_smul q using 1
    funext n
    congr 3
    omega
  rw [Summable.tsum_sub hs1 hsp, hshift,
    ← Summable.tsum_sub (hs2.const_smul q) hsp]
  have he : (fun n : ℤ => q • G (n+1) (f (j-n))-G n (P (f (j-n))))=
      (fun n : ℤ => if n=0 then f j else 0) := by
    funext n
    have hn := congrArg (fun L : E →L[ℂ] E => L (f (j-n))) (hrec n)
    by_cases hn0 : n=0
    · simpa [hn0] using hn
    · simpa [hn0] using hn
  rw [he, tsum_ite_eq]

theorem homogeneous_eq_zero (P : E →L[ℂ] E) (q : ℝ) (hq : 0<q)
    (hc : ∀ z : ℂ, ‖z‖=q → z ∈ resolventSet ℂ P)
    (f : ℤ →ᵇ E) (hf : ∀ j : ℤ, (q:ℂ) • f (j+1)=P (f j)) : f=0 := by
  let G := PeriodicResolvent.coeff (PeriodicResolvent.resolventLoop P q)
  have hG := PeriodicResolvent.green_summable P hq hc
  have hrec := PeriodicResolvent.green_right_identity P hq hc
  have hz : difference P (q:ℂ) f=0 := by ext j; simp [hf]
  have he := greenOperator_left_inverse P (q:ℂ) G hG hrec f
  rw [hz, map_zero] at he
  exact he.symm
end FlatRecursion

end

end OAI
