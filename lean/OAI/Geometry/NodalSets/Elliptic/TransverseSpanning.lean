import OAI.Geometry.NodalSets.Charts.LocalFrameTriple

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma perpendicular_span_le_ker (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (p : Coord) (q : Fin 3 → Coord) (hperp : ∀ j, g p (q j) = 0) :
    Submodule.span ℝ (range q) ≤ (g p).toLinearMap.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact hperp j

lemma perpendicular_triple_basis (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0) :
    Submodule.span ℝ (range (Fin.cons p q)) = ⊤ := by
  have hnot : p ∉ Submodule.span ℝ (range q) := by
    intro h
    have hh := perpendicular_span_le_ker g p q hperp h
    exact (ne_of_gt (hp p hp0)) hh
  have hi : LinearIndependent ℝ (Fin.cons p q) := linearIndependent_finCons.mpr ⟨hq,hnot⟩
  exact hi.span_eq_top_of_card_eq_finrank' (by simp [Coord])

theorem perpendicular_triple_spans (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0)
    (v : Coord) (hv : g p v = 0) : v ∈ Submodule.span ℝ (range q) := by
  have htop := perpendicular_triple_basis g hp p hp0 q hq hperp
  have hvtop : v ∈ Submodule.span ℝ (insert p (range q)) := by
    rw [← Fin.range_cons,htop]
    trivial
  obtain ⟨a,u,hu,rfl⟩ := Submodule.mem_span_insert.mp hvtop
  have hgu : g p u = 0 := perpendicular_span_le_ker g p q hperp hu
  have ha : a = 0 := by
    have hh : a * g p p = 0 := by simpa [map_add,map_smul,smul_eq_mul,hgu] using hv
    exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt (hp p hp0))
  simpa [ha] using hu

def transverseEnergy (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (q : Fin 3 → Coord) (v : Coord) : ℝ := ∑ j, (g (q j) v)^2

theorem transverseEnergy_pos (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (p : Coord) (hp0 : p ≠ 0)
    (q : Fin 3 → Coord) (hq : LinearIndependent ℝ q) (hperp : ∀ j, g p (q j) = 0)
    (v : Coord) (hv : g p v = 0) (hv0 : v ≠ 0) : 0 < transverseEnergy g q v := by
  have hnon : 0 ≤ transverseEnergy g q v := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro hz
  have hzero : ∀ j, g (q j) v = 0 := by
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦
      sq_nonneg (g (q j) v))).mp hz.symm
    intro j
    exact (sq_eq_zero_iff).mp (he j (Finset.mem_univ j))
  have hker : Submodule.span ℝ (range q) ≤ (g.flip v).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hzero j
  have hgv : g v v = 0 := hker (perpendicular_triple_spans g hp p hp0 q hq hperp v hv)
  exact (ne_of_gt (hp v hv0)) hgv

lemma transverseEnergy_smul (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (q : Fin 3 → Coord) (v : Coord) (a : ℝ) :
    transverseEnergy g q (a • v) = a^2 * transverseEnergy g q v := by
  simp [transverseEnergy,map_smul,smul_eq_mul,mul_pow,Finset.mul_sum]

end
end Yau.Geometry

end OAI
