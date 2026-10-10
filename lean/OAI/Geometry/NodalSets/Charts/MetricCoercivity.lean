import OAI.Geometry.NodalSets.Elliptic.UniformTripleBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

lemma uniform_metric_coercivity (g : T → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : Continuous g) (hp : ∀ t v, v ≠ 0 → 0 < g t v v) :
    ∃ c > 0, ∃ B > 0, ∀ t, ‖g t‖ ≤ B ∧ ∀ v, c*‖v‖^2 ≤ g t v v := by
  have hc : Continuous (fun z : T × Coord ↦ g z.1 z.2 z.2) :=
    ((hg.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c,hc0,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0:Coord) 1)) _ hc.continuousOn
    (fun z hz ↦ hp z.1 z.2 (by intro he; simpa [he] using hz.2))
  obtain ⟨B,hB,hBb⟩ := (isCompact_univ.image hg).isBounded.exists_pos_norm_le
  refine ⟨c,hc0,B,hB,?_⟩
  intro t
  refine ⟨hBb _ ⟨t,mem_univ _,rfl⟩,?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹:ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  have hh := (hbound (t,(‖v‖⁻¹:ℝ) • v)
    ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
  simp only [map_smul,smul_apply,smul_eq_mul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have he : ‖v‖^2*(‖v‖⁻¹*(‖v‖⁻¹*g t v v)) = g t v v := by field_simp
  rw [he] at hmul
  nlinarith

lemma bilinear_pairing_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (u v : Coord) :
    |g u v| ≤ ‖g‖*‖u‖*‖v‖ :=
  ((g u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (g.le_opNorm u) (norm_nonneg v))

lemma rounded_positive_pairing (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (mu B K h : ℝ) (hmu : 0 < mu) (hB : 0 ≤ B) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hg : ‖g‖ ≤ B) (hc : ∀ v, mu*‖v‖^2 ≤ g v v)
    (hlarge : 2*B+1 ≤ K*mu) (x y v : Coord)
    (hround : ‖y-(x+(K*h) • ((‖v‖⁻¹:ℝ) • v))‖ ≤ 2*h) :
    g (x-y) v ≤ -h*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  let u := (‖v‖⁻¹:ℝ) • v
  let e := y-(x+(K*h) • u)
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : mu*‖v‖ ≤ g u v := by
    have h := mul_le_mul_of_nonneg_left (hc v) (inv_nonneg.mpr hn.le)
    have he : ‖v‖⁻¹*(mu*‖v‖^2) = mu*‖v‖ := by field_simp
    rw [he] at h
    simpa [u,map_smul,smul_apply,smul_eq_mul] using h
  have he : |g e v| ≤ (2*B*h)*‖v‖ := (bilinear_pairing_bound g e v).trans (by
    have hb : ‖e‖ ≤ 2*h := hround
    calc
      ‖g‖*‖e‖*‖v‖ ≤ B*(2*h)*‖v‖ := by gcongr
      _ = _ := by ring)
  have hid : x-y = -(K*h) • u-e := by dsimp [e]; module
  rw [hid,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left hunit (mul_nonneg hK hh)
  have h2 := mul_le_mul_of_nonneg_right hlarge (mul_nonneg hh (norm_nonneg v))
  have h3 := (abs_le.mp he).1
  nlinarith

end
end Yau.Geometry

end OAI
