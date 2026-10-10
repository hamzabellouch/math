import OAI.Geometry.NodalSets.Coefficients.CutoffResidualProductLemmas

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T]

theorem uniform_finiteResidualCore_bound {s : Set T} {R : ℝ}
    (E t0 L : T → Coord → ℂ) (tj : ℕ → T → Coord → ℂ)
    (a : T → ℝ → Coord → ℂ)
    (hE : UniformSmoothBounded s R E) (ht0 : UniformSmoothBounded s R t0)
    (htj : ∀ j, UniformSmoothBounded s R (tj j)) (hL : UniformSmoothBounded s R L)
    (ha : ∀ t N, ContDiff ℝ ∞ (a t N))
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) (hR : 0 ≤ R)
    (hEz : ∀ t ∈ s, FlatAt m (E t) 0) (ht0z : ∀ t ∈ s, FlatAt m (t0 t) 0)
    (htjz : ∀ j, j < J → ∀ t ∈ s, FlatAt m (tj j t) 0)
    (hab : ∃ A > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord, ‖x‖ ≤ R →
      DerivativeBound k0 (a t N) x A) :
    ∃ C > 0, ∀ t ∈ s, ∀ N : ℝ, 1 ≤ N → ∀ x : Coord,
      ‖x‖ ≤ R * N ^ (-1/3 : ℝ) →
      DerivativeBound k0 (finiteResidualCore (E t) (a t N) (t0 t)
        (fun j ↦ tj j t) (L t) J N) x (C * N ^ (-(K : ℝ)-k0)) := by
  obtain ⟨CE, hCE, hEb⟩ := uniform_flat_derivative_decay hE hm hR hEz
  obtain ⟨C0, hC0, ht0b⟩ := uniform_flat_derivative_decay ht0 hm hR ht0z
  obtain ⟨CL, hCL, hLb⟩ := hL.2 k0
  obtain ⟨A, hA, haB⟩ := hab
  have hjs (j : Fin J) := uniform_flat_derivative_decay (htj j.val) hm hR (htjz j.val j.isLt)
  choose Cj hCj hjb using hjs
  let B := CE + C0 + CL + ∑ j, Cj j
  have hsum : 0 ≤ ∑ j, Cj j := Finset.sum_nonneg (fun j _ ↦ (hCj j).le)
  have hB : 0 < B := by dsimp [B]; positivity
  have heB : CE ≤ B := by dsimp [B]; linarith
  have h0B : C0 ≤ B := by dsimp [B]; linarith
  have hlB : CL ≤ B := by dsimp [B]; linarith
  have hjB (j : Fin J) : Cj j ≤ B := by
    have := Finset.single_le_sum (fun i _ ↦ (hCj i).le) (Finset.mem_univ j)
    dsimp [B]
    linarith
  refine ⟨2^k0*B*A + (J+2)*B, by positivity, ?_⟩
  intro t ht N hN x hx
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp : 0 ≤ N ^ (-(K : ℝ)-k0-2) := Real.rpow_nonneg hNp.le _
  have hxR : ‖x‖ ≤ R := by
    apply hx.trans
    calc
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)) hR
      _ = _ := mul_one R
  apply finiteResidualCore_bound (hE.1 t) (ha t N) (ht0.1 t) (fun j ↦ (htj j).1 t)
    (hL.1 t) k0 J x hB.le hA.le hN (by exact_mod_cast (show K+k0 ≤ J by omega))
  · exact (hEb t ht N hN x hx).enlarge (mul_le_mul_of_nonneg_right heB hp)
  · exact haB t ht N hN x hxR
  · exact (ht0b t ht N hN x hx).enlarge (mul_le_mul_of_nonneg_right h0B hp)
  · intro j hj
    exact (hjb ⟨j,hj⟩ t ht N hN x hx).enlarge
      (mul_le_mul_of_nonneg_right (hjB ⟨j,hj⟩) hp)
  · exact (hLb t ht x hxR).enlarge hlB

end
end Yau.Jets

end OAI
