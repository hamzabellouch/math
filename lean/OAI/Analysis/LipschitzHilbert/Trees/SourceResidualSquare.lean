import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualBlockGeometry

namespace OAI

/-! The actual residual coefficient is bounded by its assigned top's
mask times a negative power of that top's weight. Grouping the resulting
absolute packet envelopes by the disjoint source length bands gives the
marked residual square estimate without any angular-depth factor. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem packet_length_group_norm_bound {σ E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N)
    (I : Finset (Fin N)) (multiplier : σ → ℂ) (value : σ → E)
    (envelope : Fin N → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsupport : ∀ q ∈ Q, lengthIndex q ∈ I)
    (hmult : ∀ q ∈ Q, ‖multiplier q‖ ≤ C)
    (henvelope : ∀ k ∈ I, (∑ q ∈ Q.filter (fun q => lengthIndex q = k), ‖value q‖) ≤ envelope k) :
    ‖∑ q ∈ Q, multiplier q • value q‖ ≤ C*∑ k ∈ I, envelope k := by
  calc
    _ ≤ ∑ q ∈ Q, ‖multiplier q • value q‖ := norm_sum_le _ _
    _ = ∑ q ∈ Q, ‖multiplier q‖*‖value q‖ := by simp only [norm_smul]
    _ ≤ ∑ q ∈ Q, C*‖value q‖ := Finset.sum_le_sum (fun q hq =>
      mul_le_mul_of_nonneg_right (hmult q hq) (norm_nonneg _))
    _ = C*∑ q ∈ Q, ‖value q‖ := (Finset.mul_sum ..).symm
    _ = C*∑ k ∈ I, ∑ q ∈ Q.filter (fun q => lengthIndex q = k), ‖value q‖ := by
      rw [Finset.sum_fiberwise_of_maps_to hsupport]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum henvelope) hC

namespace AngularGrid
variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem source_packet_residual_coefficient_bound (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (mask : ι → ℂ) (C : ℝ)
    (hmask : ∀ t ∈ tops, weight t x^(-a)*‖mask t‖ ≤ C)
    (top : ι) (htop : top ∈ tops) (stop : ℕ)
    (he : g.eligible cutoff (precision top) stop) (lower : ℕ) :
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
        lower stop (slope top)*
      ((g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x^(-a):ℝ):ℂ)*mask top‖ ≤ C := by
  have hprod : ‖g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower stop (slope top)‖ ≤ 1 := by
    rw [packetPathProduct,norm_prod]
    apply Finset.prod_le_one₀
    · intro k _
      exact norm_nonneg _
    · intro k hk
      exact g.sourceTransition_norm_le_one tops slope precision cutoff weight hp hw hK gap phase
        x k top htop (g.eligible_of_le (hp top htop)
          (Nat.succ_le_of_lt (Finset.mem_Ico.mp hk).2) he) (hz k)
  have hmember : top ∈ g.cellTops tops slope precision cutoff stop (g.index stop (slope top)) :=
    (g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩
  have hm : weight top x ≤ g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x :=
    Finset.single_le_sum (fun t _ => (hw t x).le) hmember
  have hrpow := Real.rpow_le_rpow_of_nonpos (hw top x) hm (neg_nonpos.mpr ha)
  have hnonneg : 0 ≤ g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x^(-a) :=
    Real.rpow_nonneg ((hw top x).le.trans hm) _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
  calc
    _ ≤ (1*(g.mass tops slope precision cutoff weight stop (g.index stop (slope top)) x^(-a)))*‖mask top‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hnonneg) (norm_nonneg _)
    _ ≤ weight top x^(-a)*‖mask top‖ := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hrpow (norm_nonneg _)
    _ ≤ C := hmask top htop

/-- Exact assigned-top coefficients and a per-length absolute envelope
control the complete residual of an actual source node. -/
theorem source_packet_residual_norm_bound {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (packets : Finset σ) (assigned : σ → ι) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (mask : ι → ℂ) (value : σ → E)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop (lengthIndex q)))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ t ∈ tops, weight t x^(-a)*‖mask t‖ ≤ C)
    (lower upper : ℕ) (pathSlope : ℝ) (envelope : Fin N → ℝ)
    (henvelope : ∀ k ∈ residualLengthSet stop lower upper,
      (∑ q ∈ ((g.packetSet packets (fun q => slope (assigned q))
          (fun q => stop (lengthIndex q)) lower (g.index lower pathSlope)).filter
            (fun q => stop (lengthIndex q) < upper)).filter (fun q => lengthIndex q = k),
        ‖value q‖) ≤ envelope k) :
    ‖g.packetResidual packets (fun q => slope (assigned q)) (fun q => stop (lengthIndex q))
      (g.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop (lengthIndex q))
        (fun q => mask (assigned q) • value q) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower upper (g.index lower pathSlope)‖ ≤ C*∑ k ∈ residualLengthSet stop lower upper, envelope k := by
  unfold packetResidual
  simp only [sourcePacketBase,smul_smul]
  apply packet_length_group_norm_bound _ lengthIndex (residualLengthSet stop lower upper) _ value
    envelope hC
  · intro q hq
    obtain ⟨hq,hupper⟩ := Finset.mem_filter.mp hq
    have hstop := (Finset.mem_filter.mp hq).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hstop,hupper⟩
  · intro q hq
    have hqp := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have h := g.source_packet_residual_coefficient_bound tops slope precision cutoff weight hp hw hK
      gap phase hz a ha x mask C hmask (assigned q) (hassigned q hqp) (stop (lengthIndex q))
      (he q hqp) lower
    simpa only [mul_assoc] using h
  · exact henvelope

/-- The block square estimate now has the actual source residuals on
the left. All overlap and length-cardinality costs are proved above;
the remaining inputs are the positive per-length reference envelopes. -/
theorem source_packet_residual_square_sum {N : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (hz : ∀ k, 0 ≤ (phase k).re) (a : ℝ) (ha : 0 ≤ a) (x : X)
    (packets : Finset σ) (assigned : σ → ι) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (mask : ι → ℂ) (value : σ → E)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (he : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop (lengthIndex q)))
    (C : ℝ) (hC : 0 ≤ C) (hmask : ∀ t ∈ tops, weight t x^(-a)*‖mask t‖ ≤ C)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ) (pathSlope : ℝ)
    (error main : Fin N → ℝ) (herror : ∀ k, 0 ≤ error k) (hmain : ∀ k, 0 ≤ main k)
    (R : ℝ) (hR : 0 ≤ R)
    (hcard : ∀ j < count, ((residualLengthSet stop (level j) (level (j+1))).card:ℝ) ≤ R)
    (henvelope : ∀ j < count, ∀ k ∈ residualLengthSet stop (level j) (level (j+1)),
      (∑ q ∈ ((g.packetSet packets (fun q => slope (assigned q))
          (fun q => stop (lengthIndex q)) (level j) (g.index (level j) pathSlope)).filter
            (fun q => stop (lengthIndex q) < level (j+1))).filter (fun q => lengthIndex q = k),
        ‖value q‖) ≤ error k+main k) :
    (∑ j : Fin count, ‖g.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop (lengthIndex q))
      (g.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop (lengthIndex q))
        (fun q => mask (assigned q) • value q) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      (level j.val) (level (j.val+1)) (g.index (level j.val) pathSlope)‖^2) ≤
        3*C^2*((∑ k, error k)^2+R*∑ k, (main k)^2) := by
  have hd := residualLengthSet_disjoint stop level hlevel
  have h := residual_blocks_square_sum_le
    (fun j : Fin count => residualLengthSet stop (level j.val) (level (j.val+1)))
    (fun i j hij => hd (Fin.val_injective.ne hij)) error main herror hmain
    (fun j : Fin count => g.packetResidual packets (fun q => slope (assigned q))
      (fun q => stop (lengthIndex q))
      (g.sourcePacketBase tops slope precision cutoff weight assigned (fun q => stop (lengthIndex q))
        (fun q => mask (assigned q) • value q) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      (level j.val) (level (j.val+1)) (g.index (level j.val) pathSlope))
    (fun _ => 0) (C := C) (L := R) (R := 0) (fun _ => le_rfl) hC hR le_rfl
    (fun j => hcard j.val j.isLt) (by simp) ?_
  · simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] using h
  · intro j
    have hj := g.source_packet_residual_norm_bound tops slope precision cutoff weight hp hw hK gap
      phase hz a ha x packets assigned lengthIndex stop mask value hassigned he C hC hmask
      (level j.val) (level (j.val+1)) pathSlope (fun k => error k+main k)
      (henvelope j.val j.isLt)
    simpa only [Finset.sum_add_distrib,add_zero] using hj

end AngularGrid
end LipschitzHilbert

end

end OAI
