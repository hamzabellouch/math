import OAI.Geometry.NodalSets.Elliptic.TransverseSpanning
import OAI.Geometry.NodalSets.Elliptic.UniformContact

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

omit [CompactSpace T] in
lemma transverseEnergy_continuous
    (g : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : Continuous g)
    (q : T → Fin 3 → Coord) (hq : Continuous q) :
    Continuous (fun z : T × Coord ↦ transverseEnergy (g z.1) (q z.1) z.2) := by
  apply continuous_finsetSum
  intro j _
  exact (((hg.comp continuous_fst).clm_apply
    (((continuous_apply j).comp hq).comp continuous_fst)).clm_apply continuous_snd).pow 2

theorem uniform_transverse_spanning
    (g : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : Continuous g)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (q : T → Fin 3 → Coord) (hq : Continuous q)
    (hqi : ∀ t, LinearIndependent ℝ (q t)) (hperp : ∀ t j, g t (p t) (q t j) = 0) :
    ∃ c > 0, ∀ t v, g t (p t) v = 0 → c*‖v‖^2 ≤ transverseEnergy (g t) (q t) v := by
  let A : Set (T × Coord) := (univ ×ˢ Metric.sphere 0 1) ∩ {z | g z.1 (p z.1) z.2 = 0}
  have hcompact : IsCompact A :=
    (isCompact_univ.prod (isCompact_sphere (0:Coord) 1)).inter_right
      (isClosed_eq (((hg.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply
        continuous_snd) continuous_const)
  have hpositive : ∀ z ∈ A, 0 < transverseEnergy (g z.1) (q z.1) z.2 := by
    intro z hz
    apply transverseEnergy_pos (g z.1) (hpos z.1) (p z.1) (hp0 z.1)
      (q z.1) (hqi z.1) (hperp z.1) z.2 hz.2
    intro he
    have hn := hz.1.2
    simp [he] at hn
  obtain ⟨c,hc,C,hC,hbound⟩ := compact_positive_bounds hcompact _
    (transverseEnergy_continuous g hg q hq).continuousOn hpositive
  refine ⟨c,hc,?_⟩
  intro t v hv
  by_cases hz : v = 0
  · simp [hz,transverseEnergy]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  have hunit : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ (ne_of_gt hn)]
  have hmem : (t,(‖v‖⁻¹ : ℝ) • v) ∈ A := by
    exact ⟨⟨mem_univ t,by simpa only [Metric.mem_sphere,dist_zero_right] using hunit⟩,
      by simp [map_smul,smul_eq_mul,hv]⟩
  have hh := (hbound _ hmem).1
  rw [transverseEnergy_smul] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖v‖)
  have hn0 : ‖v‖ ≠ 0 := ne_of_gt hn
  have he : ‖v‖^2 * ((‖v‖⁻¹)^2 * transverseEnergy (g t) (q t) v) =
      transverseEnergy (g t) (q t) v := by field_simp
  rw [he] at hmul
  nlinarith

def sourceDirectionEta (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ) (p q : Coord) : ℝ :=
  (H p p+H q q)/(g p p+g q q)

theorem uniform_direction_strictness
    (g H : T → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : Continuous g) (hH : Continuous H)
    (hpos : ∀ t v, v ≠ 0 → 0 < g t v v)
    (p : T → Coord) (hp : Continuous p) (hp0 : ∀ t, p t ≠ 0)
    (d : AdmissibleFrameTriple g H p) :
    ∃ c > 0, ∃ C > 0, ∀ t j,
      c ≤ sourceDirectionEta (g t) (H t) (p t) (d.q t j) ∧
      sourceDirectionEta (g t) (H t) (p t) (d.q t j) ≤ C := by
  have hq : Continuous (fun z : T × Fin 3 ↦ d.q z.1 z.2) :=
    continuous_prod_of_discrete_right.mpr (fun j ↦ (continuous_apply j).comp d.continuous_q)
  have hgP : Continuous (fun z : T × Fin 3 ↦ g z.1 (p z.1) (p z.1)) := ((hg.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply (hp.comp continuous_fst)
  have hgQ : Continuous (fun z : T × Fin 3 ↦ g z.1 (d.q z.1 z.2) (d.q z.1 z.2)) := ((hg.comp continuous_fst).clm_apply hq).clm_apply hq
  have hHP : Continuous (fun z : T × Fin 3 ↦ H z.1 (p z.1) (p z.1)) := ((hH.comp continuous_fst).clm_apply (hp.comp continuous_fst)).clm_apply (hp.comp continuous_fst)
  have hHQ : Continuous (fun z : T × Fin 3 ↦ H z.1 (d.q z.1 z.2) (d.q z.1 z.2)) := ((hH.comp continuous_fst).clm_apply hq).clm_apply hq
  have hden (z : T × Fin 3) : 0 < g z.1 (p z.1) (p z.1)+g z.1 (d.q z.1 z.2) (d.q z.1 z.2) := by
    rw [d.length]
    have hh := hpos z.1 (p z.1) (hp0 z.1)
    linarith
  have heta : Continuous (fun z : T × Fin 3 ↦ sourceDirectionEta (g z.1) (H z.1)
      (p z.1) (d.q z.1 z.2)) := (hHP.add hHQ).div (hgP.add hgQ) (fun z ↦ ne_of_gt (hden z))
  obtain ⟨c,hc,C,hC,hb⟩ := compact_positive_bounds isCompact_univ _ heta.continuousOn
    (fun z _ ↦ div_pos (d.strict z.1 z.2) (hden z))
  exact ⟨c,hc,C,hC,fun t j ↦ hb (t,j) (mem_univ _)⟩

end
end Yau.Geometry

end OAI
