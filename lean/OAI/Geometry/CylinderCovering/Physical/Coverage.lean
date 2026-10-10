import OAI.Geometry.CylinderCovering.Physical.Paired
import OAI.Geometry.CylinderCovering.Radial.SqrtCap
import OAI.Geometry.CylinderCovering.Radial.CapCoverage

namespace OAI

open Set Filter
open scoped Topology

noncomputable section
namespace CylinderCovering.UnitEdgeFootprints
open TriangularCovering

lemma cap_dictionary (η q : ℝ) :
    RadialSqrtCap.cap (1 / 120) (η / 2) q = 2 * sourceCap η (q / 2) := by
  have hleft : 0 ≤ RadialSqrtCap.cap (1 / 120) (η / 2) q := Real.sqrt_nonneg _
  have hright : 0 ≤ 2 * sourceCap η (q / 2) := mul_nonneg (by norm_num) (sourceCap_pos η (q / 2)).le
  apply (sq_eq_sq₀ hleft hright).mp
  rw [RadialSqrtCap.cap_sq (by norm_num : (0 : ℝ) ≤ 1 / 120), mul_pow]
  have hs : (sourceCap η (q / 2)) ^ 2 =
      1 / 4 + η ^ 2 * ((q / 2) ^ 2 / 4 + (q / 2) ^ 4 + 1 / 960) := by
    unfold sourceCap
    exact Real.sq_sqrt (by positivity)
  rw [hs]
  unfold RadialSqrtCap.profile RadialCaps.H
  ring

theorem source_coverage : CoverageStatement := by
  obtain ⟨δ, hδ, hpad⟩ := RadialSqrtCap.exists_padding_threshold
    (by norm_num : (0 : ℝ) < 1 / 120)
  refine ⟨2 * δ, by positivity, ?_⟩
  intro η hη hsmall z hz
  obtain ⟨t, ht, hz2, hx, hy⟩ := hz
  have he : 0 < η / 2 := by positivity
  obtain ⟨hεβ, hcap⟩ := hpad (η / 2) he (by linarith)
  have hx' : |4 * z 1| ≤ 1 + (2 * t - 1) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hy' : |4 * z 0| ≤ 1 - (2 * t - 1) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hc := RadialCapCoverage.padding_coverage (eps := η / 2)
    (R := RadialCaps.linearCap (1 / 240) (η / 2)) (b := fun _ => (1 / 240 : ℝ)) he
    (fun _ _ => rfl) (fun _ _ => by norm_num)
    (fun _ _ _ _ => by linarith) hx' hy'
  rcases hc with hu | hl
  · obtain ⟨q, ρ, hq, hρ, hR, hrep, htrep⟩ := hu
    right
    have hqI := abs_le.mp hq
    have hcapq := hcap q hq
    have hρcap : ρ ≤ 2 * sourceCap η (q / 2) := by
      rw [← cap_dictionary]
      apply hR.trans
      simpa only [RadialCaps.linearCap, show (1 / 120 : ℝ) / 2 = 1 / 240 by norm_num] using hcapq
    refine ⟨q / 2, ⟨by linarith, by linarith⟩, ρ / 2,
      ⟨by positivity, by linarith⟩, z 1, ?_, ?_⟩
    · linarith [ht.2]
    · ext i
      fin_cases i
      · change z 0 = q / 2 * (ρ / 2) - η * z 1 * (1 / 4 + (q / 2) ^ 2)
        unfold RadialCaps.G at hrep
        nlinarith only [hrep]
      · rfl
      · change z 2 = height * (1 - ρ / 2 + 2 * η * z 1 * (q / 2))
        rw [hz2]
        congr 1
        nlinarith only [htrep]
  · obtain ⟨q, ρ, hq, hρ, hR, hrep, htrep⟩ := hl
    left
    have hqI := abs_le.mp hq
    have hcapq := hcap q hq
    have hρcap : ρ ≤ 2 * sourceCap η (q / 2) := by
      rw [← cap_dictionary]
      apply hR.trans
      simpa only [RadialCaps.linearCap, show (1 / 120 : ℝ) / 2 = 1 / 240 by norm_num] using hcapq
    refine ⟨q / 2, ⟨by linarith, by linarith⟩, ρ / 2,
      ⟨by positivity, by linarith⟩, z 0, ?_, ?_⟩
    · linarith [ht.1]
    · ext i
      fin_cases i
      · rfl
      · change z 1 = q / 2 * (ρ / 2) + η * z 0 * (1 / 4 + (q / 2) ^ 2)
        unfold RadialCaps.G at hrep
        nlinarith only [hrep]
      · change z 2 = height * (ρ / 2 + 2 * η * z 0 * (q / 2))
        rw [hz2]
        congr 1
        nlinarith only [htrep]

theorem finite_strict_of_coverage (hcoverage : CoverageStatement) : FiniteStrictStatement := by
  obtain ⟨δ, hδ, hcover⟩ := hcoverage
  refine ⟨min δ (1 / 40), by positivity, ?_⟩
  intro η hη hsmall
  have hc := hcover η hη (lt_of_lt_of_le hsmall (min_le_left _ _))
  have hs := source_cost_strict hη (le_trans hsmall.le (min_le_right _ _))
  obtain ⟨C₁, C₂, hspec, hpair, hlim⟩ := paired_family_realization η hη
  have hevent : ∀ᶠ N in atTop, totalArea (C₁ N) + totalArea (C₂ N) < height / 4 :=
    hlim.eventually (gt_mem_nhds hs)
  obtain ⟨N, hcost⟩ := (eventually_atTop.1 hevent)
  let M := max N 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num : 0 < 1) (le_max_right _ _)
  refine ⟨M, hM, C₁ M, C₂ M, ?_, ?_, hcost M (le_max_left _ _)⟩
  · intro i
    obtain ⟨h1, h2, h3, h4, _, _⟩ := hspec M i
    exact ⟨h1, h2, h3, h4⟩
  · intro z hz
    exact hpair M hM z (hc hz)

lemma tetrahedron_similarity : tetrahedron =
    Similarity.map (0 : Space) (1 / 2) (LinearIsometryEquiv.refl ℝ Space) '' K := by
  have hh : H / 2 = height := by
    unfold H height
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith only [hs]
  ext z
  constructor
  · rintro ⟨t, ht, hz, hx, hy⟩
    refine ⟨point (2 * z 0) (2 * z 1) t, ?_, ?_⟩
    · refine ⟨2 * z 0, 2 * z 1, t, ht.1, ht.2, ?_, ?_, rfl⟩
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
      · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
    · ext i
      fin_cases i
      · simp [Similarity.map, point]
      · simp [Similarity.map, point]
      · change 0 + (1 / 2 : ℝ) * (H * t) = z 2
        rw [hz, ← hh]
        ring
  · rintro ⟨_, ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩, rfl⟩
    refine ⟨t, ⟨ht0, ht1⟩, ?_, ?_, ?_⟩
    · change 0 + (1 / 2 : ℝ) * (H * t) = height * t
      rw [← hh]
      ring
    · change |0 + (1 / 2 : ℝ) * x| ≤ (1 - t) / 2
      rw [zero_add, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    · change |0 + (1 / 2 : ℝ) * y| ≤ t / 2
      rw [zero_add, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

theorem minimum_area : Similarity.minimumArea tetrahedron = height / 2 := by
  rw [tetrahedron_similarity, Similarity.minimumArea_map _ _
    (by norm_num : (1 / 2 : ℝ) ≠ 0) (LinearIsometryEquiv.refl ℝ Space)]
  change (1 / 2 : ℝ) ^ 2 * A_min = height / 2
  rw [projection_minimum]
  unfold H height
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  nlinarith only [hs]

theorem full_unit_edge : FullStatement :=
  ⟨local_realization, family_realization, paired_family_realization, source_cost,
    source_coverage, finite_strict_of_coverage source_coverage, minimum_area⟩

end CylinderCovering.UnitEdgeFootprints

end

end OAI
