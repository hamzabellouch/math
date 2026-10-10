import OAI.Geometry.NodalSets.Elliptic.DirectionTripleAlgebra

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def transverseDirection (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord) (b eps : ℝ) (j : Fin 3) : Coord :=
  b • metricNormalize g (e (transverseTriple eps j))

lemma transverseDirection_continuous (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (e : Coord ≃L[ℝ] Coord) (b : ℝ) (j : Fin 3) :
    Continuous (fun eps : ℝ ↦ transverseDirection g e b eps j) := by
  have hz : Continuous (fun eps : ℝ ↦ e (transverseTriple eps j)) := by
    fin_cases j <;> dsimp [transverseTriple] <;> fun_prop
  exact (continuous_const (y := b)).smul (metricNormalize_continuous (fun _ : ℝ ↦ g)
    (fun eps ↦ e (transverseTriple eps j)) continuous_const hz
    (fun eps ↦ hp _ (by intro h; exact transverseTriple_ne_zero eps j (e.injective (by simpa using h)))))

lemma frame_pair_coordinate (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e : Coord ≃L[ℝ] Coord)
    (ho : ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (i : Fin 4) (v : Coord) : g (e (Pi.single i 1)) v = e.symm v i := by
  calc
    _ = g (e (Pi.single i 1)) (e (e.symm v)) := by rw [e.apply_symm_apply]
    _ = _ := by
      have hexp : e.symm v = ∑ j : Fin 4, e.symm v j • Pi.single j (1:ℝ) := by
        ext j; simp [Pi.single_apply]
      conv_lhs => rw [hexp]
      simp [map_sum,map_smul,ho,smul_eq_mul]

theorem frame_admissible_direction_triple
    (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (e : Coord ≃L[ℝ] Coord)
    (ho : ∀ i j : Fin 4, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b)
    (hstrict : 0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
      H (b • e (Pi.single 1 1)) (b • e (Pi.single 1 1))) :
    ∃ q : Fin 3 → Coord, LinearIndependent ℝ q ∧
      (∀ j, g (a • e (Pi.single 0 1)) (q j) = 0 ∧ g (q j) (q j) = b^2 ∧
        0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) + H (q j) (q j)) ∧
      ∀ v : Coord, g (a • e (Pi.single 0 1)) v = 0 → v ∈ Submodule.span ℝ (Set.range q) := by
  have hnon (eps : ℝ) (j : Fin 3) : e (transverseTriple eps j) ≠ 0 := by
    intro h
    exact transverseTriple_ne_zero eps j (e.injective (by simpa using h))
  have hz (j : Fin 3) : transverseDirection g e b 0 j = b • e (Pi.single 1 1) := by
    fin_cases j <;> simp [transverseDirection,transverseTriple,metricNormalize,ho]
  have hev (j : Fin 3) : ∀ᶠ eps : ℝ in 𝓝 0,
      0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
        H (transverseDirection g e b eps j) (transverseDirection g e b eps j) := by
    have hq := transverseDirection_continuous g hp e b j
    have hc : Continuous (fun eps : ℝ ↦
        H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
          H (transverseDirection g e b eps j) (transverseDirection g e b eps j)) :=
      continuous_const.add (((continuous_const (y := H)).clm_apply hq).clm_apply hq)
    exact hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hz] using hstrict))
  obtain ⟨d,hd,hdi⟩ := Metric.mem_nhds_iff.mp (Filter.eventually_all.mpr hev)
  let eps : ℝ := d/2
  have heps : eps ≠ 0 := by dsimp [eps]; positivity
  have hestrict := hdi (show eps ∈ Metric.ball 0 d by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by dsimp [eps]; positivity)]
    dsimp [eps]; linarith)
  let c : Fin 3 → ℝ := fun j ↦ b * (Real.sqrt (g (e (transverseTriple eps j)) (e (transverseTriple eps j))))⁻¹
  have hc (j : Fin 3) : c j ≠ 0 := mul_ne_zero (ne_of_gt hb)
    (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (hp _ (hnon eps j)))))
  have hq (j : Fin 3) : transverseDirection g e b eps j = c j • e (transverseTriple eps j) := by
    simp [transverseDirection,metricNormalize,c,smul_smul]
  have hqf : transverseDirection g e b eps = fun j ↦ c j • e (transverseTriple eps j) := funext hq
  refine ⟨transverseDirection g e b eps,?_,?_,?_⟩
  · rw [hqf]
    exact rescaled_frame_triple_independent e eps heps c hc
  · intro j
    refine ⟨?_,?_,hestrict j⟩
    · rw [hq]
      have hpair : g (e (Pi.single 0 1)) (e (transverseTriple eps j)) = 0 := by
        rw [frame_pair_coordinate g e ho, e.symm_apply_apply]
        fin_cases j <;> simp [transverseTriple]
      simp [map_smul,smul_eq_mul,hpair]
    · have hn := metricNormalize_unit g (e (transverseTriple eps j)) (hp _ (hnon eps j))
      simp only [transverseDirection,map_smul,smul_apply,smul_eq_mul,hn]
      ring
  · intro v hv
    have hzero : e.symm v 0 = 0 := by
      have hh : a * g (e (Pi.single 0 1)) v = 0 := by simpa [map_smul,smul_eq_mul] using hv
      rw [frame_pair_coordinate g e ho] at hh
      exact (mul_eq_zero.mp hh).resolve_left ha
    rw [hqf]
    exact rescaled_frame_triple_spans e eps heps c hc v hzero

theorem admissible_direction_triple
    (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u)
    (p t : Coord) (hp0 : p ≠ 0) (hpt : g p t = 0) (ht : g t t = 1)
    (hstrict : 0 < H p p + (g p p+4)*H t t) :
    ∃ q : Fin 3 → Coord, LinearIndependent ℝ q ∧
      (∀ j, g p (q j) = 0 ∧ g (q j) (q j) = g p p+4 ∧ 0 < H p p+H (q j) (q j)) ∧
      ∀ v : Coord, g p v = 0 → v ∈ Submodule.span ℝ (Set.range q) := by
  let a := Real.sqrt (g p p)
  let b := Real.sqrt (g p p+4)
  have ha : 0 < a := Real.sqrt_pos.mpr (hp p hp0)
  have hb : 0 < b := Real.sqrt_pos.mpr (by have h := hp p hp0; linarith)
  have ha2 : a^2 = g p p := Real.sq_sqrt (hp p hp0).le
  have hb2 : b^2 = g p p+4 := Real.sq_sqrt (by have h := hp p hp0; linarith)
  have hqt : g (b • t) (b • t) = b^2 := by
    simp [map_smul,smul_eq_mul,ht,pow_two]
  obtain ⟨e,he0,he1,ho⟩ := positive_coordinate_adapted_frame g hp hs p (b • t) a b ha hb ha2.symm hqt
    (by simp [hpt])
  have heP : a • e (Pi.single 0 1) = p := by simp [he0,smul_smul,ne_of_gt ha]
  have heQ : b • e (Pi.single 1 1) = b • t := by simp [he1,smul_smul,ne_of_gt hb]
  have hHq : H (b • t) (b • t) = (g p p+4)*H t t := by
    simp only [map_smul,smul_apply,smul_eq_mul]
    calc
      b*(b*H t t) = b^2*H t t := by ring
      _ = _ := by rw [hb2]
  have hstr : 0 < H (a • e (Pi.single 0 1)) (a • e (Pi.single 0 1)) +
      H (b • e (Pi.single 1 1)) (b • e (Pi.single 1 1)) := by
    rw [heP,heQ,hHq]
    exact hstrict
  obtain ⟨q,hqi,hq,hspan⟩ := frame_admissible_direction_triple g H hp e ho a b (ne_of_gt ha) hb hstr
  exact ⟨q,hqi,by simpa only [heP,hb2] using hq,by simpa only [heP] using hspan⟩

end
end Yau.Geometry

end OAI
