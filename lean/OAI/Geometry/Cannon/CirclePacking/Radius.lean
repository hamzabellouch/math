import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
open Filter Topology

namespace CannonNode

def radius (ell : ℝ) (k : ℕ) : ℝ := Real.exp (-ell*k)

lemma radius_pos (ell : ℝ) (k : ℕ) : 0 < radius ell k := Real.exp_pos _

lemma radius_add (ell : ℝ) (k d : ℕ) : radius ell (k+d) = radius ell d*radius ell k := by
  simp only [radius,Nat.cast_add, mul_add,Real.exp_add]
  ring

lemma radius_ratio (ell : ℝ) (k d : ℕ) : radius ell k/radius ell (k+d) = Real.exp (ell*d) := by
  simp only [radius, ← Real.exp_sub, Nat.cast_add]
  congr 1
  ring

lemma radius_sub_ratio (ell : ℝ) (k d e : ℕ) (hed : e ≤ d) :
    radius ell (k+d)/radius ell (k+e) = radius ell (d-e) := by
  simp only [radius,← Real.exp_sub,Nat.cast_add,Nat.cast_sub hed]
  congr 1
  ring

lemma radius_antitone {ell : ℝ} (hell : 0 ≤ ell) : Antitone (radius ell) := by
  intro i j hij
  apply Real.exp_le_exp.mpr
  have hh : (i:ℝ) ≤ j := by exact_mod_cast hij
  exact mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr hell)

lemma radius_eq_power (ell : ℝ) (k : ℕ) : radius ell k = (Real.exp ell^k)⁻¹ := by
  rw [← Real.exp_nat_mul,← Real.exp_neg]
  unfold radius
  congr 1
  ring

lemma radius_tendsto {ell : ℝ} (hell : 0 < ell) : Tendsto (radius ell) atTop (𝓝 0) := by
  have he : Real.exp (-ell) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hell)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-ell)).le he
  change Tendsto (fun n : ℕ => Real.exp (-ell*n)) atTop (𝓝 0)
  simpa only [radius,← Real.exp_nat_mul, mul_comm] using ht

lemma nat_mul_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun n : ℕ => d*n) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n)
  · intro n
    exact Nat.le_mul_of_pos_left n hd
  · exact tendsto_id

theorem eventually_flow_scales (qdim : ℕ) (ell c₀ H C : ℝ) (hell : 0 < ell) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ radius ell (160*(qdim+1)*n) < 1/4 ∧
      c₀*radius ell (160*(qdim+1)*n) ≤ 1 ∧
      2*(H+3)*radius ell (160*(qdim+1)*n) ≤ 1 ∧
      radius ell (2*n) ≤ 1/4 ∧
      C*radius ell ((160*(qdim+1)-2)*n) ≤ 1 := by
  have hd : 0 < 160*(qdim+1) := by omega
  have he : 0 < 160*(qdim+1)-2 := by omega
  have hdl : Tendsto (fun n : ℕ => radius ell (160*(qdim+1)*n)) atTop (𝓝 0) :=
    (radius_tendsto hell).comp (nat_mul_tendsto hd)
  have hel : Tendsto (fun n : ℕ => radius ell ((160*(qdim+1)-2)*n)) atTop (𝓝 0) :=
    (radius_tendsto hell).comp (nat_mul_tendsto he)
  have h₂l : Tendsto (fun n : ℕ => radius ell (2*n)) atTop (𝓝 0) :=
    (radius_tendsto hell).comp (nat_mul_tendsto (by norm_num : 0 < (2:ℕ)))
  have hcl : Tendsto (fun n : ℕ => c₀*radius ell (160*(qdim+1)*n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdl.const_mul c₀
  have hHl : Tendsto (fun n : ℕ => 2*(H+3)*radius ell (160*(qdim+1)*n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdl.const_mul (2*(H+3))
  have hCl : Tendsto (fun n : ℕ => C*radius ell ((160*(qdim+1)-2)*n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hel.const_mul C
  filter_upwards [eventually_gt_atTop (0:ℕ),
    hdl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hcl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hHl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    h₂l.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)),
    hCl.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn hdn hcn hHn h₂n hCn
  exact ⟨hn,hdn,hcn.le,hHn.le,h₂n.le,hCn.le⟩

end CannonNode

end

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
