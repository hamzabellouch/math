import Mathlib
import OAI.Combinatorics.UniformKServer.AdaptiveSide

namespace OAI

                                           
section

/-! Prepared parameter jumps charged only to changed size coordinates (§04).
 Constants are independent of the number of children and of the smallest size. -/
noncomputable section
namespace UniformKServer.SideParameterChanges
open Finset UniformKServer.AdaptiveSide
open scoped Classical
variable {ι : Type*} [Fintype ι]

def size (p : Config ι) : ι → ℝ := DomainTransport.extend p.active p.a

omit [Fintype ι] in
theorem same_sizes {p q : Config ι} (hp : valid p) (hq : valid q)
    (hA : p.A=q.A) (hl : p.ell=q.ell) (hc : p.cw=q.cw) (i : ι)
    (hs : size p i=size q i) : theta p i=theta q i ∧ offset p i=offset q i := by
  by_cases hi : i ∈ p.active
  · have hj : i ∈ q.active := by
      by_contra hn
      have he : p.a ⟨i,hi⟩=0 := by
        simpa [size,DomainTransport.extend,hi,hn] using hs
      linarith [(hp.2.2.2.2.1 ⟨i,hi⟩).1]
    have ha : p.a ⟨i,hi⟩=q.a ⟨i,hj⟩ := by
      simpa [size,DomainTransport.extend,hi,hj] using hs
    simp only [theta,offset,DomainTransport.extend,hi,hj,dite_true,ha,hA,hl,hc,and_self]
  · have hj : i ∉ q.active := by
      intro hj
      have he : 0=q.a ⟨i,hj⟩ := by
        simpa [size,DomainTransport.extend,hi,hj] using hs
      linarith [(hq.2.2.2.2.1 ⟨i,hj⟩).1]
    simp [theta,offset,DomainTransport.extend,hi,hj]

omit [Fintype ι] in
theorem coordinate_bound_all {p : Config ι} (hp : valid p) (i : ι) {w B D : ℝ}
    (hw : 0 ≤ w) (hwW : w ≤ 11) :
    |SideTracker.coordinate p.b (theta p i) (offset p i) 28 B D w| ≤
      slope p*(|D| *w+|B|) := by
  by_cases hi : i ∈ p.active
  · exact coordinate_bound hp ⟨i,hi⟩ hw hwW
  · simp only [theta,offset,DomainTransport.extend,hi,dite_false]
    simp only [SideTracker.coordinate,div_zero,mul_zero,zero_mul,add_zero,sub_zero,zero_div,abs_zero]
    exact mul_nonneg (slope_nonneg hp) (add_nonneg (mul_nonneg (abs_nonneg D) hw) (abs_nonneg B))

theorem parameter_jump {p q : Config ι} (hp : valid p) (hq : valid q)
    (hA : p.A=q.A) (hl : p.ell=q.ell) (hc : p.cw=q.cw) (hb : p.b=q.b)
    (B w : ι → ℝ) {D : ℝ} (hD : 0 ≤ D) (hB : ∀ i, 0 ≤ B i)
    (hw : DomainTransport.domain q.active 11 w)
    (hprep : ∀ i, D*w i ≤ 5*B i) :
    |potential q B D w-potential p B D w| ≤
      6*(slope p+slope q)*(∑ i, if size p i=size q i then 0 else B i) := by
  unfold potential SideTracker.potential
  rw [←sum_sub_distrib,mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  by_cases hs : size p i=size q i
  · obtain ⟨ht,hz⟩ := same_sizes hp hq hA hl hc i hs
    simp only [ite_eq_left hs,hb,ht,hz,sub_self,abs_zero,mul_zero,le_refl]
  · rw [ite_eq_right hs]
    have hp' := coordinate_bound_all hp i (hw.1 i) (coordinate_le_sum hw i) (B:=B i) (D:=D)
    have hq' := coordinate_bound_all hq i (hw.1 i) (coordinate_le_sum hw i) (B:=B i) (D:=D)
    rw [abs_of_nonneg hD,abs_of_nonneg (hB i)] at hp' hq'
    have hp'' := mul_le_mul_of_nonneg_left (hprep i) (slope_nonneg hp)
    have hq'' := mul_le_mul_of_nonneg_left (hprep i) (slope_nonneg hq)
    exact (abs_sub _ _).trans (by nlinarith)

omit [Fintype ι] in
theorem prepared_upper {p : Config ι} (hp : valid p) (B w : ι → ℝ) (D : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hf : ∀ i, D*w i ≤ (p.b+theta p i)*B i) :
    ∀ i, D*w i ≤ 5*B i := by
  intro i
  have hθ : theta p i ≤ 1 := by
    by_cases hi : i ∈ p.active
    · exact theta_le hp ⟨i,hi⟩
    · rw [theta,DomainTransport.extend_supported _ _ i hi]; norm_num
  exact (hf i).trans (mul_le_mul_of_nonneg_right (by linarith [hp.2.2.2.1]) (hB i))

end UniformKServer.SideParameterChanges

end


end

end OAI
