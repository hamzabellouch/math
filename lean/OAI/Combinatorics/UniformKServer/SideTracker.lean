import Mathlib

namespace OAI

                                  
section

                                                                          
                                                                       
noncomputable section
namespace UniformKServer.SideTracker
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def domain (W : ℝ) (w : ι → ℝ) : Prop := (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ W

def coordinate (b θ z C B D s : ℝ) : ℝ :=
  C*(D/θ*(s-z*Real.log (1+s/z)) + D*z*Real.log (1+s/z)/2 -
    (b+θ/2)*B*Real.log (1+s/z)/θ)

def potential (b C D : ℝ) (θ z B w : ι → ℝ) : ℝ :=
  ∑ i, coordinate b (θ i) (z i) C (B i) D (w i)

def movement (w v : ι → ℝ) : ℝ := ∑ i, |w i-v i|

-- CANDIDATE PROOFS
theorem right_derivative_nonneg {f : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hf : HasDerivAt f d 0) (hmin : ∀ s, 0 < s → s < δ → f 0 ≤ f s) : 0 ≤ d := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with s hs hsδ
  simp only [Set.mem_Ioi, Set.mem_Iio] at hs hsδ
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr (hmin s hs hsδ))

omit [DecidableEq ι] in
theorem domain_compact (W : ℝ) : IsCompact {w : ι → ℝ | domain W w} := by
  have h₁ : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h₂ : IsClosed {w : ι → ℝ | ∑ i, w i ≤ W} := isClosed_le (by fun_prop) continuous_const
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => W))).of_isClosed_subset (h₁.inter h₂)
  intro w hw
  refine ⟨hw.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)).trans hw.2

theorem coordinate_continuous {b θ z C B D s : ℝ} (hz : 0 < z) (hs : 0 ≤ s) :
    ContinuousAt (coordinate b θ z C B D) s := by
  have hl : ContinuousAt (fun s : ℝ => Real.log (1+s/z)) s := by
    apply ContinuousAt.log (by fun_prop)
    have : 0 ≤ s/z := div_nonneg hs hz.le
    linarith
  unfold coordinate
  fun_prop

theorem coordinate_deriv {b θ z C B D s : ℝ} (hθ : 0 < θ) (hz : 0 < z) (hs : 0 ≤ s) :
    HasDerivAt (coordinate b θ z C B D)
      (C*(D*s-(b+θ/2)*B+D*θ*z/2)/(θ*(s+z))) s := by
  have he : 1+s/z ≠ 0 := by have := div_nonneg hs hz.le; linarith
  have hl : HasDerivAt (fun s : ℝ => Real.log (1+s/z)) (1/(s+z)) s := by
    convert! (((hasDerivAt_id s).div_const z).const_add 1).log he using 1
    simp only [id_eq]
    field_simp [hz.ne', (add_pos_of_nonneg_of_pos hs hz).ne']
    ring
  have hh := (((hasDerivAt_id s).sub (hl.const_mul z)).const_mul (D/θ)).add
    ((hl.const_mul (D*z)).div_const 2)
  have hh' := (hh.sub ((hl.const_mul ((b+θ/2)*B)).div_const θ)).const_mul C
  convert! hh' using 1
  field_simp [hθ.ne', (add_pos_of_nonneg_of_pos hs hz).ne']
  ring

theorem sum_update (w : ι → ℝ) (i : ι) (s : ℝ) :
    ∑ j, Function.update w i (w i+s) j = (∑ j, w j)+s := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

theorem potential_update (g : ι → ℝ → ℝ) (w : ι → ℝ) (i : ι) (s : ℝ) :
    (∑ j, g j (Function.update w i (w i+s) j)) =
    (∑ j, g j (w j))+g i (w i+s)-g i (w i) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ (fun j => g j (w j)) (Finset.mem_univ i)]
  have he : ∑ j ∈ Finset.univ.erase i, g j (Function.update w i (w i+s) j) =
      ∑ j ∈ Finset.univ.erase i, g j (w j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he, Function.update_self]
  ring

theorem movement_update_le (w v : ι → ℝ) (i : ι) (s : ℝ) :
    movement (Function.update w i (w i+s)) v ≤ movement w v+|s| := by
  unfold movement
  rw [potential_update (fun j t => |t-v j|)]
  have hh := abs_add_le (w i-v i) s
  have he : w i+s-v i = (w i-v i)+s := by ring
  rw [he]
  linarith

theorem gradient_upper (g : ι → ℝ → ℝ) (W D : ℝ) (w₀ w : ι → ℝ)
    (hD : 0 ≤ D) (hw : domain W w)
    (hmin : ∀ v, domain W v → (∑ i, g i (w i))+D*movement w w₀ ≤
      (∑ i, g i (v i))+D*movement v w₀)
    (i : ι) (hwpos : 0 < w i) {d : ℝ} (hg : HasDerivAt (g i) d (w i)) : d ≤ D := by
  have hd : HasDerivAt (fun s => g i (w i-s)+D*s) (-d+D) 0 := by
    have hgi : HasDerivAt (g i) d (w i-id 0) := by simpa using hg
    have hh := hgi.comp 0 ((hasDerivAt_id 0).const_sub (w i))
    convert! hh.add ((hasDerivAt_id 0).const_mul D) using 1 ; simp
  have hge := right_derivative_nonneg hwpos hd (fun s hs hsδ => ?_)
  · linarith
  have hv : domain W (Function.update w i (w i + -s)) := by
    refine ⟨?_, ?_⟩
    · intro j
      by_cases he : j = i
      · subst j; simp only [Function.update_self]; linarith
      · rw [Function.update_of_ne he]; exact hw.1 j
    · rw [sum_update]; linarith [hw.2]
  have hh := hmin _ hv
  rw [potential_update] at hh
  have hm := mul_le_mul_of_nonneg_left (movement_update_le w w₀ i (-s)) hD
  rw [abs_neg, abs_of_nonneg hs.le] at hm
  simp only [sub_zero, mul_zero, add_zero]
  simp only [← sub_eq_add_neg] at hh hm
  linarith

theorem gradient_lower (g : ι → ℝ → ℝ) (W D : ℝ) (w₀ w : ι → ℝ)
    (hD : 0 ≤ D) (hw : domain W w) (hroom : ∑ i, w i < W)
    (hmin : ∀ v, domain W v → (∑ i, g i (w i))+D*movement w w₀ ≤
      (∑ i, g i (v i))+D*movement v w₀)
    (i : ι) {d : ℝ} (hg : HasDerivAt (g i) d (w i)) : -D ≤ d := by
  have hd : HasDerivAt (fun s => g i (w i+s)+D*s) (d+D) 0 := by
    have hgi : HasDerivAt (g i) d (w i+id 0) := by simpa using hg
    have hh := hgi.comp 0 ((hasDerivAt_id 0).const_add (w i))
    convert! hh.add ((hasDerivAt_id 0).const_mul D) using 1 ; simp
  have hge := right_derivative_nonneg (sub_pos.mpr hroom) hd (fun s hs hsδ => ?_)
  · linarith
  have hv : domain W (Function.update w i (w i+s)) := by
    refine ⟨?_, ?_⟩
    · intro j
      by_cases he : j = i
      · subst j; simp only [Function.update_self]; linarith [hw.1 i]
      · rw [Function.update_of_ne he]; exact hw.1 j
    · rw [sum_update]; linarith
  have hh := hmin _ hv
  rw [potential_update] at hh
  have hm := mul_le_mul_of_nonneg_left (movement_update_le w w₀ i s) hD
  rw [abs_of_nonneg hs.le] at hm
  simp only [add_zero, mul_zero]
  linarith


theorem upper_violation {b θ z C B D s : ℝ}
    (hb : 0 < b) (hθ : 0 < θ) (hz : 0 < z) (hB : 0 ≤ B) (hD : 0 < D)
    (hs : 0 ≤ s) (hC : 4*(b+θ+1) ≤ C) (hv : (b+θ)*B < D*s) :
    D < C*(D*s-(b+θ/2)*B+D*θ*z/2)/(θ*(s+z)) := by
  let N := D*s-(b+θ/2)*B+D*θ*z/2
  let e := D*s-(b+θ)*B
  have he : 0 < e := sub_pos.mpr hv
  have heN : N = e+θ*B/2+D*θ*z/2 := by dsimp [N,e]; ring
  have hN : 0 < N := by rw [heN]; positivity
  have hq : 0 < 2*(b+θ+1)-θ := by linarith
  have hid : 2*(b+θ+1)*N-D*θ*(s+z) =
      (2*(b+θ+1)-θ)*e+θ*B+D*θ*(b+θ)*z := by dsimp [N,e]; ring
  have hstrict : D*θ*(s+z) < 2*(b+θ+1)*N := by
    apply sub_pos.mp
    rw [hid]
    positivity
  have hlarge : 2*(b+θ+1) ≤ C := by linarith
  apply (lt_div_iff₀ (mul_pos hθ (add_pos_of_nonneg_of_pos hs hz))).mpr
  change D*(θ*(s+z)) < C*N
  calc
    D*(θ*(s+z)) = D*θ*(s+z) := by ring
    _ < 2*(b+θ+1)*N := hstrict
    _ ≤ C*N := mul_le_mul_of_nonneg_right hlarge hN.le

theorem lower_violation {b θ z C B D s : ℝ}
    (hb : 0 < b) (hθ : 0 < θ) (hz : 0 < z) (hB : 0 ≤ B) (hD : 0 < D)
    (hs : 0 ≤ s) (hC : 4*(b+θ+1) ≤ C) (hv : D*s < b*B-θ*z*D) :
    C*(D*s-(b+θ/2)*B+D*θ*z/2)/(θ*(s+z)) < -D := by
  let N := D*s-(b+θ/2)*B+D*θ*z/2
  let e := b*B-D*s-D*θ*z
  have he : 0 < e := by dsimp [e]; nlinarith
  have heN : -N = e+θ*B/2+D*θ*z/2 := by dsimp [N,e]; ring
  have hN : 0 < -N := by rw [heN]; positivity
  have hq : 0 < 2*(b+1)+θ := by linarith
  have hid : 2*(b+1)*(-N)-D*θ*(s+z) =
      (2*(b+1)+θ)*e+θ*B+D*θ^2*z+D*θ*b*z := by dsimp [N,e]; ring
  have hstrict : D*θ*(s+z) < 2*(b+1)*(-N) := by
    apply sub_pos.mp
    rw [hid]
    positivity
  have hlarge : 2*(b+1) ≤ C := by linarith
  have hh := hstrict.trans_le (mul_le_mul_of_nonneg_right hlarge hN.le)
  apply (div_lt_iff₀ (mul_pos hθ (add_pos_of_nonneg_of_pos hs hz))).mpr
  change C*N < -D*(θ*(s+z))
  nlinarith


theorem side_update (b C D W m S : ℝ) (θ z B w₀ : ι → ℝ)
    (hb : 0 < b) (hD : 0 ≤ D) (hm : 0 ≤ m) (hW : 2*m < W)
    (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i) (hB : ∀ i, 0 ≤ B i)
    (hS : ∑ i, B i ≤ S) (hbound : ∀ i, b+θ i ≤ m)
    (hC : ∀ i, 4*(b+θ i+1) ≤ C) (hw₀ : domain W w₀) :
    ∃ w, domain W w ∧
      (∀ i, D*w i ≤ (b+θ i)*B i) ∧
      (S ≤ 2*D → ∀ i, b*B i-θ i*z i*D ≤ D*w i) ∧
      D*movement w w₀ ≤ potential b C D θ z B w₀-potential b C D θ z B w := by
  have hc : ContinuousOn (fun w => potential b C D θ z B w+D*movement w w₀)
      {w | domain W w} := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.add
    · unfold potential
      apply tendsto_finsetSum
      intro i hi
      exact (coordinate_continuous (hz i) (hw.1 i)).comp' (f := fun v : ι → ℝ => v i) (continuous_apply i).continuousAt
    · exact (show Continuous (fun w => D*movement w w₀) by unfold movement; fun_prop).continuousAt
  obtain ⟨w, hw, hwmin⟩ := (domain_compact (ι := ι) W).exists_isMinOn ⟨w₀, hw₀⟩ hc
  have hmin : ∀ v, domain W v →
      (∑ i, coordinate b (θ i) (z i) C (B i) D (w i))+D*movement w w₀ ≤
      (∑ i, coordinate b (θ i) (z i) C (B i) D (v i))+D*movement v w₀ := by
    intro v hv
    exact hwmin hv
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · intro i
    by_cases he : D = 0
    · subst D
      simp only [zero_mul]
      exact mul_nonneg (add_pos hb (hθ i)).le (hB i)
    have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm he)
    by_contra hn
    have hv := lt_of_not_ge hn
    have hwi : 0 < w i := by
      have hbB := mul_nonneg (add_pos hb (hθ i)).le (hB i)
      by_contra hnw
      have := mul_nonpos_of_nonneg_of_nonpos hD (le_of_not_gt hnw)
      linarith
    have hu := gradient_upper _ W D w₀ w hD hw hmin i hwi
      (coordinate_deriv (hθ i) (hz i) (hw.1 i))
    have hv' := upper_violation hb (hθ i) (hz i) (hB i) hDp (hw.1 i) (hC i) hv
    linarith
  · intro hSD i
    by_cases he : D = 0
    · subst D
      have hzero : B i = 0 := by
        have hle := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
        have : S ≤ 0 := by simpa using hSD
        linarith [hB i]
      simp [hzero]
    have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm he)
    have hu : ∀ j, D*w j ≤ (b+θ j)*B j := by
      intro j
      by_contra hn
      have hv := lt_of_not_ge hn
      have hwj : 0 < w j := by
        have hbB := mul_nonneg (add_pos hb (hθ j)).le (hB j)
        by_contra hnw
        have := mul_nonpos_of_nonneg_of_nonpos hD (le_of_not_gt hnw)
        linarith
      have hh := gradient_upper _ W D w₀ w hD hw hmin j hwj
        (coordinate_deriv (hθ j) (hz j) (hw.1 j))
      have hv' := upper_violation hb (hθ j) (hz j) (hB j) hDp (hw.1 j) (hC j) hv
      linarith
    have hsum : D*(∑ j, w j) ≤ m*(2*D) := by
      calc
        D*(∑ j, w j) = ∑ j, D*w j := Finset.mul_sum ..
        _ ≤ ∑ j, (b+θ j)*B j := Finset.sum_le_sum fun j _ => hu j
        _ ≤ ∑ j, m*B j := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hbound j) (hB j)
        _ = m*(∑ j, B j) := (Finset.mul_sum ..).symm
        _ ≤ m*S := mul_le_mul_of_nonneg_left hS hm
        _ ≤ m*(2*D) := mul_le_mul_of_nonneg_left hSD hm
    have hroom : ∑ j, w j < W := by nlinarith
    by_contra hn
    have hv := lt_of_not_ge hn
    have hl := gradient_lower _ W D w₀ w hD hw hroom hmin i
      (coordinate_deriv (hθ i) (hz i) (hw.1 i))
    have hv' := lower_violation hb (hθ i) (hz i) (hB i) hDp (hw.1 i) (hC i) hv
    linarith
  · have hh : potential b C D θ z B w+D*movement w w₀ ≤
        potential b C D θ z B w₀+D*movement w₀ w₀ := hwmin hw₀
    have hm₀ : movement w₀ w₀ = 0 := by simp [movement]
    rw [hm₀, mul_zero, add_zero] at hh
    linarith

end UniformKServer.SideTracker

end


end

end OAI
