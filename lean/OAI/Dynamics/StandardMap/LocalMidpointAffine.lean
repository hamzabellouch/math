import OAI.Dynamics.StandardMap.LocalMidpointGrid

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
lemma midpoint_interval_affine {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (fun p : ℝ × ℝ => d p.1 p.2))
    (a b : ℝ) (hab : a< b) (hm : MidpointAffineOn d (Icc a b)) :
    ∀x∈Ioo a b,∀y∈Ioo a b,d x y=(d a b/(b-a))*|y-x| := by
  let f : ℝ → ℝ := fun t => a+t*(b-a)
  have hf : Continuous f := continuous_const.add (continuous_id.mul continuous_const)
  have hgrid (s t : DyadicTime) (hs : (s:ℝ)∈Ioo (0:ℝ) 1) (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
      d (f s) (f t)=(d a b/(b-a))*|f t-f s| := by
    obtain ⟨m,i,j,hi,hj⟩ := dyadic_common_grid s t
    have hsc : (s:ℝ)=(i:ℝ)/(2:ℝ)^m := by rw [hi,dyadic_zsmul_val,dyadicUnit_val]; ring
    have htc : (t:ℝ)=(j:ℝ)/(2:ℝ)^m := by rw [hj,dyadic_zsmul_val,dyadicUnit_val]; ring
    have hp : (0:ℝ)<(2:ℝ)^m := by positivity
    have hiR : 0≤(i:ℝ) ∧ (i:ℝ)≤(2:ℝ)^m := by
      rw [hsc] at hs
      exact ⟨by simpa only [zero_mul] using (le_div_iff₀ hp).mp hs.1.le,by have := (div_le_one hp).mp hs.2.le; exact this⟩
    have hjR : 0≤(j:ℝ) ∧ (j:ℝ)≤(2:ℝ)^m := by
      rw [htc] at ht
      exact ⟨by simpa only [zero_mul] using (le_div_iff₀ hp).mp ht.1.le,by have := (div_le_one hp).mp ht.2.le; exact this⟩
    have hi0 : 0≤ i := by exact_mod_cast hiR.1
    have hj0 : 0≤ j := by exact_mod_cast hjR.1
    have hiB : i≤((2^m:ℕ):ℤ) := by exact_mod_cast hiR.2
    have hjB : j≤((2^m:ℕ):ℤ) := by exact_mod_cast hjR.2
    have hiN : i.toNat≤2^m := by omega
    have hjN : j.toNat≤2^m := by omega
    have hei : (i.toNat:ℝ)=(i:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hi0
    have hej : (j.toNat:ℝ)=(j:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
    have he1 : f s=a+(i.toNat:ℝ)*((b-a)/(2^m:ℕ)) := by
      dsimp [f]
      rw [hsc,hei]
      push_cast; ring
    have he2 : f t=a+(j.toNat:ℝ)*((b-a)/(2^m:ℕ)) := by
      dsimp [f]
      rw [htc,hej]
      push_cast; ring
    rw [he1,he2]
    exact midpoint_grid_affine hd a b hab hm (2^m) (by positivity) i.toNat j.toNat hiN hjN
  have hall : ∀ s t : ℝ,s∈Ioo (0:ℝ) 1 → t∈Ioo (0:ℝ) 1 →
      d (f s) (f t)=(d a b/(b-a))*|f t-f s| := by
    apply isClosed_property2 (p := fun s t => s∈Ioo (0:ℝ) 1 → t∈Ioo (0:ℝ) 1 →
      d (f s) (f t)=(d a b/(b-a))*|f t-f s|) dyadicTime_dense
    · apply isClosed_imp (isOpen_Ioo.preimage continuous_fst)
      apply isClosed_imp (isOpen_Ioo.preimage continuous_snd)
      exact isClosed_eq (hc.comp ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd)))
        (continuous_const.mul (((hf.comp continuous_snd).sub (hf.comp continuous_fst)).abs))
    · exact hgrid
  intro x hx y hy
  let s := (x-a)/(b-a)
  let t := (y-a)/(b-a)
  have hs : s∈Ioo (0:ℝ) 1 := ⟨div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hab),
    (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])⟩
  have ht : t∈Ioo (0:ℝ) 1 := ⟨div_pos (sub_pos.mpr hy.1) (sub_pos.mpr hab),
    (div_lt_one (sub_pos.mpr hab)).mpr (by linarith [hy.2])⟩
  have hfx : f s=x := by dsimp [f,s]; rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]; ring
  have hfy : f t=y := by dsimp [f,t]; rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]; ring
  simpa only [hfx,hfy] using hall s t hs ht
lemma midpoint_ball_locallyAffine {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
    (hc : Continuous (fun p : ℝ × ℝ => d p.1 p.2)) (x r : ℝ) (hr : 0< r)
    (hm : MidpointAffineOn d (ball x r)) : ∃w,LocallyAffineAt d x w := by
  let a := x-r/2
  let b := x+r/2
  have hab : a< b := by dsimp [a,b]; linarith
  have hI : Icc a b⊆ball x r := by
    intro y hy
    rw [mem_ball,Real.dist_eq,abs_lt]
    dsimp [a,b] at hy
    constructor <;> linarith [hy.1,hy.2]
  have hs : MidpointAffineOn d (Icc a b) := fun s hs t ht hst => hm s (hI hs) t (hI ht) hst
  have hh := midpoint_interval_affine hd hc a b hab hs
  refine ⟨d a b/(b-a),r/2,by positivity,?_⟩
  intro u hu v hv
  have hu' : u∈Ioo a b := by simpa only [Real.ball_eq_Ioo] using hu
  have hv' : v∈Ioo a b := by simpa only [Real.ball_eq_Ioo] using hv
  exact hh u hu' v hv'
end StandardMapEntropy

end OAI
