import OAI.Probability.GammaPassage.ActualWitnessScale
import OAI.Probability.GammaPassage.LoopErasure

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open Set Filter MeasureTheory
open scoped Topology

/-- The source no-corner contradiction, using actual near-optimal simple paths
and the cut-number bound. No geodesic existence or selected-path limit is assumed. -/
theorem long_paths_contradict_directional_limit (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (b m₀ a η : ℝ) (hb : |b| ≤ 1) (hη : 0 < η) (k m : ℕ)
    (hlim : Tendsto (fun n : ℕ => passageTime w 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ)) atTop (𝓝 m₀))
    (hlong : ∀ᶠ N : ℕ in atTop, ∀ blocks : List (List Step), ∀ rest : List Step,
      blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
      ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
      N*η*(2 : ℝ)^k/2 ≤ defect w b m₀ a 0 (blocks.flatten++rest)) : False := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hlong
  let A := η*(2 : ℝ)^k
  let L := (2 : ℝ)^m
  let δ := A/(8*L)
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 8*L*δ=A := by dsimp [δ]; field_simp
  have hup := hlim.eventually (gt_mem_nhds (show m₀ < m₀+δ by linarith))
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnlarge := hnat.eventually (eventually_gt_atTop (((N₀ : ℝ)+1)*2*L))
  have hnC := hnat.eventually (eventually_gt_atTop ((A/2+|a|+1)/δ))
  have hnpos := hnat.eventually (eventually_gt_atTop (0 : ℝ))
  obtain ⟨n,hnup,hnlarge,hnC,hnpos⟩ := (hup.and (hnlarge.and (hnC.and hnpos))).exists
  obtain ⟨ds,hend,hsimple,_hmin,hcost⟩ := GammaFPP.LoopErase.exists_near_optimal_simple_path w hw 0 ((n : ℤ),⌊b*(n : ℝ)⌋) 1 (by norm_num)
  have hdisp : displacement ds=((n : ℤ),⌊b*(n : ℝ)⌋) := by simpa using hend
  obtain ⟨blocks,rest,heq,hfull,hrest⟩ := spatial_chunk_decomposition b k m ds
  have hcut := spatial_chunk_displacement_bound b hb k m blocks rest hfull hrest
  rw [← heq,hdisp] at hcut
  have hcutR : (n : ℝ) ≤ 2*L*((blocks.length : ℝ)+1) := by
    have hh : (n : ℤ) ≤ 2*(2 : ℤ)^m*((blocks.length : ℤ)+1) := by simpa using hcut
    dsimp [L]
    exact_mod_cast hh
  have hN : N₀ ≤ blocks.length := by
    by_contra hh
    have hl : ((blocks.length : ℝ)+1) ≤ N₀ := by exact_mod_cast (show blocks.length+1 ≤ N₀ by omega)
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*L by positivity)
    nlinarith
  have hlow := hN₀ blocks.length hN blocks rest rfl hfull hrest (by rw [← heq]; exact hsimple)
  have hloA : (blocks.length : ℝ)*A/2 ≤ defect w b m₀ a 0 ds := by
    rw [← heq] at hlow
    simpa only [A,mul_assoc] using hlow
  have hr : |(⌊b*(n : ℝ)⌋ : ℝ)-b*n| ≤ 1 := by
    apply abs_le.mpr
    have hl := Int.floor_le (b*(n : ℝ))
    have hu := Int.lt_floor_add_one (b*(n : ℝ))
    constructor <;> linarith
  have hab : |a*((⌊b*(n : ℝ)⌋ : ℝ)-b*n)| ≤ |a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hr (abs_nonneg a)
  have hsupport : m₀*n-|a| ≤ support b m₀ a (displacement ds) := by
    rw [hdisp]
    simp only [support,transverse,Int.cast_natCast]
    linarith [(abs_le.mp hab).1]
  have hpass : passageTime w 0 ((n : ℤ),⌊b*(n : ℝ)⌋) < (m₀+δ)*n := (div_lt_iff₀ hnpos).mp hnup
  have hupper : defect w b m₀ a 0 ds < δ*n+|a|+1 := by
    unfold defect
    nlinarith
  have hcutδ := mul_le_mul_of_nonneg_left hcutR hδ.le
  have hδN := congrArg (fun x : ℝ => x*((blocks.length : ℝ)+1)) hδeq
  have hC : A/2+|a|+1 < δ*n := by
    have hh := (div_lt_iff₀ hδ).mp hnC
    nlinarith
  nlinarith

end GammaFPP.CrossingBridge

end OAI
