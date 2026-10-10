import OAI.Probability.FreeIsing.Posterior.FilteringRepresentationClosure

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem367.FilteringRepresentationClosure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_sum_coordinate {ι : Type*} {f : ι → E} {y : E}
    (hs : HasSum f y) (ho : Pairwise fun i j => inner ℝ (f i) (f j) = 0) (i : ι) :
    inner ℝ y (f i) = ‖f i‖ ^ 2 := by
  have h := hs.mapL (innerSL ℝ (f i))
  change HasSum (fun j => inner ℝ (f i) (f j)) (inner ℝ (f i) y) at h
  have hsingle : HasSum (fun j => inner ℝ (f i) (f j)) (inner ℝ (f i) (f i)) :=
    hasSum_single i (fun j hji => ho hji.symm)
  rw [real_inner_comm, ← real_inner_self_eq_norm_sq]
  exact h.unique hsingle

theorem eq_of_orthogonal_row_limits
    {ι N : Type*} {l : Filter N} [l.NeBot]
    {f : N → ι → E} {y : N → E} {g : ι → E} {z m : E}
    (hs : ∀ n, HasSum (f n) (y n))
    (ho : ∀ n, Pairwise fun i j => inner ℝ (f n i) (f n j) = 0)
    (hf : ∀ i, Tendsto (fun n => f n i) l (𝓝 (g i)))
    (hy : Tendsto y l (𝓝 z)) (hg : HasSum g m)
    (he : ‖z‖ ^ 2 = ‖m‖ ^ 2) : z = m := by
  have hgo : Pairwise fun i j => inner ℝ (g i) (g j) = 0 := by
    intro i j hij
    have h := (hf i).inner (𝕜 := ℝ) (hf j)
    have hz : Tendsto (fun n => inner ℝ (f n i) (f n j)) l (𝓝 (0 : ℝ)) := by
      simpa only [ho _ hij] using (tendsto_const_nhds : Tendsto (fun _ : N => (0 : ℝ)) l (𝓝 0))
    exact tendsto_nhds_unique h hz
  have hcross (i : ι) : inner ℝ z (g i) = ‖g i‖ ^ 2 := by
    have hleft := hy.inner (𝕜 := ℝ) (hf i)
    have hright := (hf i).norm.pow 2
    exact tendsto_nhds_unique_of_eventuallyEq hleft hright
      (Eventually.of_forall fun n => inner_sum_coordinate (hs n) (ho n) i)
  have hzi := hg.mapL (innerSL ℝ z)
  have hmi := hg.mapL (innerSL ℝ m)
  change HasSum (fun i => inner ℝ z (g i)) (inner ℝ z m) at hzi
  change HasSum (fun i => inner ℝ m (g i)) (inner ℝ m m) at hmi
  simp only [hcross] at hzi
  simp only [inner_sum_coordinate hg hgo] at hmi
  exact eq_of_cross_energy (by simpa only [real_inner_self_eq_norm_sq] using hzi.unique hmi) he

theorem ae_eq_of_orthogonal_row_meanSquare_limits
    {Ω ι N : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {l : Filter N} [l.NeBot]
    {X : N → ι → Ω → ℝ} {Y : N → Ω → ℝ} {I : ι → Ω → ℝ} {Z M : Ω → ℝ}
    (hX : ∀ n i, MemLp (X n i) 2 P) (hY : ∀ n, MemLp (Y n) 2 P)
    (hI : ∀ i, MemLp (I i) 2 P) (hZ : MemLp Z 2 P) (hM : MemLp M 2 P)
    (hs : ∀ n, HasSum (fun i => (hX n i).toLp (X n i)) ((hY n).toLp (Y n)))
    (ho : ∀ n, Pairwise fun i j => ∫ ω, X n i ω * X n j ω ∂P = 0)
    (hc : ∀ i, Tendsto (fun n => ∫ ω, (X n i ω - I i ω) ^ 2 ∂P) l (𝓝 0))
    (hy : Tendsto (fun n => ∫ ω, (Y n ω - Z ω) ^ 2 ∂P) l (𝓝 0))
    (hi : HasSum (fun i => (hI i).toLp (I i)) (hM.toLp M))
    (he : (∫ ω, Z ω ^ 2 ∂P) = ∫ ω, M ω ^ 2 ∂P) : Z =ᵐ[P] M := by
  apply (hZ.toLp_eq_toLp_iff hM).mp
  apply eq_of_orthogonal_row_limits hs
    (fun n => by simpa only [PredictableL2.inner_toLp] using ho n)
    (fun i => tendsto_toLp_of_integral_sq_error (fun n => hX n i) (hI i) (hc i))
    (tendsto_toLp_of_integral_sq_error hY hZ hy) hi
  simpa only [PredictableL2.norm_toLp_sq] using he

end Problem367.FilteringRepresentationClosure

end

end OAI
