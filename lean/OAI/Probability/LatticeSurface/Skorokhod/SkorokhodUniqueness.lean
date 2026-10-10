import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodUniquenessSupport

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem normal_partition_contraction (B : Body E) (u v k l : ℝ → E)
    (hu : ContinuousOn u (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hBu : ∀ t ∈ Icc (0:ℝ) 1, u t ∈ B.carrier)
    (hBv : ∀ t ∈ Icc (0:ℝ) 1, v t ∈ B.carrier)
    (Ck Cl : ℝ) (hCk : 0 ≤ Ck) (hCl : 0 ≤ Cl)
    (hk : eVariationOn k (Icc (0:ℝ) 1) ≤ ENNReal.ofReal Ck)
    (hl : eVariationOn l (Icc (0:ℝ) 1) ≤ ENNReal.ofReal Cl)
    (hku : NormalPartitionCondition B u k) (hlv : NormalPartitionCondition B v l)
    (hdriver : ∀ t ∈ Icc (0:ℝ) 1,
      u t-v t=(u 0-v 0)+(k t-k 0)-(l t-l 0)) :
    ∀ t ∈ Icc (0:ℝ) 1, ‖u t-v t‖ ≤ ‖u 0-v 0‖ := by
  let d : ℝ → E := fun s => u s-v s
  have hdc : ContinuousOn d (Icc (0:ℝ) 1) := hu.sub hv
  have hduc := isCompact_Icc.uniformContinuousOn_of_continuous hdc
  let C := Ck+Cl
  have hC : 0 ≤ C := add_nonneg hCk hCl
  intro t ht
  have hs : ‖d t‖^2 ≤ ‖d 0‖^2 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε/(2*(C+1))
    have hδ : 0 < δ := div_pos hε (by linarith)
    have hδC : δ*C < ε/2 := by
      have hh : δ*(2*(C+1))=ε := div_mul_cancel₀ _ (by linarith)
      nlinarith
    obtain ⟨Mu,hMu⟩ := hku (ε/16) (by positivity)
    obtain ⟨Mv,hMv⟩ := hlv (ε/16) (by positivity)
    obtain ⟨η,hη,hηd⟩ := Metric.uniformContinuousOn_iff.mp hduc δ hδ
    have hevent : ∀ᶠ n : ℕ in atTop,(1:ℝ)/((n+1:ℕ):ℝ) < η := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds hη)
      simpa only [Nat.cast_add,Nat.cast_one] using hh
    have htend := (hdc t ht).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨sample_floor_tendsto t ht.1,Eventually.of_forall fun n => sample_floor_mem (n+1) (Nat.succ_pos _) t ht⟩)
    have hE := htend.norm.pow 2
    have hbound : ‖d t‖^2 ≤ ‖d 0‖^2+4*(ε/16)+δ*C := by
      apply le_of_tendsto hE
      filter_upwards [hevent,eventually_ge_atTop Mu,eventually_ge_atTop Mv] with n hnη hnu hnv
      let m := n+1
      let N := ⌊t*(m:ℝ)⌋₊
      have hm : 0 < m := Nat.succ_pos _
      have hm' : (0:ℝ) < m := by exact_mod_cast hm
      have hNm : N ≤ m := Nat.floor_le_of_le (by nlinarith [ht.2])
      let ds : ℕ → E := fun j => d ((j:ℝ)/m)
      let ks : ℕ → E := fun j => k ((j:ℝ)/m)
      let ls : ℕ → E := fun j => l ((j:ℝ)/m)
      have hinc : ∀ j < N,ds (j+1)-ds j=(ks (j+1)-ks j)-(ls (j+1)-ls j) := by
        intro j hj
        have ht₀ := uniform_grid_mem m j hm (by omega)
        have ht₁ := uniform_grid_mem m (j+1) hm (by omega)
        change (u _-v _)-(u _-v _)=(k _-k _)-(l _-l _)
        rw [hdriver _ ht₁,hdriver _ ht₀]
        abel
      have hsmall : ∀j < N,‖ds (j+1)-ds j‖ ≤ δ := by
        intro j hj
        have ht₀ := uniform_grid_mem m j hm (by omega)
        have ht₁ := uniform_grid_mem m (j+1) hm (by omega)
        have hh : dist (((j+1:ℕ):ℝ)/m) ((j:ℝ)/m) < η := by
          rw [Real.dist_eq]
          have he : (((j+1:ℕ):ℝ)/m)-(j:ℝ)/m=1/m := by push_cast;ring
          rw [he,abs_of_nonneg (by positivity)]
          exact hnη
        simpa only [dist_eq_norm] using (hηd _ ht₁ _ ht₀ hh).le
      have hks : (∑j∈Finset.range N,inner ℝ (ds j) (ks (j+1)-ks j)) ≤ ε/16 := by
        have hh := hMu m (by omega) hm
          (fun j => if j < N then v ((j:ℝ)/m) else u ((j:ℝ)/m)) (by
            intro j hj
            split_ifs
            · exact hBv _ (uniform_grid_mem m j hm hj.le)
            · exact hBu _ (uniform_grid_mem m j hm hj.le))
        rw [normal_cutoff u v k m N hNm] at hh
        exact hh
      have hls : (∑j∈Finset.range N,inner ℝ (-ds j) (ls (j+1)-ls j)) ≤ ε/16 := by
        have hh := hMv m (by omega) hm
          (fun j => if j < N then u ((j:ℝ)/m) else v ((j:ℝ)/m)) (by
            intro j hj
            split_ifs
            · exact hBu _ (uniform_grid_mem m j hm hj.le)
            · exact hBv _ (uniform_grid_mem m j hm hj.le))
        rw [normal_cutoff v u l m N hNm] at hh
        simpa only [ds,d,ls,neg_sub] using hh
      have hvk : variation ks N ≤ Ck :=
        (variation_mono ks hNm).trans (grid_variation_le k Ck hCk hk m hm)
      have hvl : variation ls N ≤ Cl :=
        (variation_mono ls hNm).trans (grid_variation_le l Cl hCl hl m hm)
      have he := discrete_normal_contraction ds ks ls N (ε/16) δ hδ.le hinc hsmall hks hls
      have htot := mul_le_mul_of_nonneg_left (add_le_add hvk hvl) hδ.le
      simp only [ds,N,Nat.cast_zero,zero_div] at he
      exact he.trans (by linarith)
    linarith
  change ‖d t‖ ≤ ‖d 0‖
  nlinarith [norm_nonneg (d t),norm_nonneg (d 0)]

end ConvexSkorokhod

end OAI
