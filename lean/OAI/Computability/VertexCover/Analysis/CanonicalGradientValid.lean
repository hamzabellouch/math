import Mathlib
import OAI.Computability.VertexCover.Analysis.ZeroMemIncidenceHull
import OAI.Computability.VertexCover.Analysis.DistanceMinusSelect
import OAI.Computability.VertexCover.Analysis.AeRegular

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover
open MeasureTheory

theorem separator_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (Φ.separator A hA) :=
  ((Φ.distanceTo_continuous A hA).comp continuous_neg |>.sub
    (Φ.distanceTo_continuous A hA)).div_const 2

noncomputable def batchFunction (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) : ℝ :=
  Φ.separator A hA (c0 + Φ.batchSum seed J s)

theorem batchFunction_continuous (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) :
    Continuous (Φ.batchFunction seed J c0 A hA) :=
  (Φ.separator_continuous A hA).comp
    (continuous_const.add (Φ.batchSumCLM seed J).continuous)

theorem batchFunction_hasFDerivAt (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J)
    (hs : VertexCover.AffineSelector.Regular (Φ.affineSlope seed J)
      (Φ.affineOffset c0 (A := A)) s) :
    ∃ im ip : Φ.AffineIndex A, HasFDerivAt (Φ.batchFunction seed J c0 A hA)
      ((1/2 : ℝ) • (Φ.affineSlope seed J im - Φ.affineSlope seed J ip)) s := by
  have hc : Continuous (fun s : Φ.BatchWeights J => c0 + Φ.batchSum seed J s) :=
    continuous_const.add (Φ.batchSumCLM seed J).continuous
  obtain ⟨ip, hp⟩ := VertexCover.AffineSelector.hasFDerivAt _ _
    ((Φ.distanceTo_continuous A hA).comp hc)
    (Φ.distance_plus_select seed J c0 A hA) hs
  obtain ⟨im, hm⟩ := VertexCover.AffineSelector.hasFDerivAt _ _
    ((Φ.distanceTo_continuous A hA).comp hc.neg)
    (Φ.distance_minus_select seed J c0 A hA) hs
  refine ⟨im, ip, ?_⟩
  have heq : Φ.batchFunction seed J c0 A hA = (fun y => (1/2 : ℝ) *
      (Φ.distanceTo A hA (-(c0 + Φ.batchSum seed J y)) -
        Φ.distanceTo A hA (c0 + Φ.batchSum seed J y))) := by
    funext y
    unfold batchFunction separator
    ring
  rw [heq]
  exact (hm.sub hp).const_mul (1/2 : ℝ)

def BatchGradientValid (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (g : Φ.BatchWeights J) : Prop :=
  ∃ G ∈ Φ.incidenceHull seed, ∀ (j : J) k, g j k = G j k

theorem signed_incidence_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (e : Bool) :
    affineSign e • Φ.incidence seed I ∈ Φ.incidenceHull seed := by
  apply subset_convexHull ℝ
  cases e
  · exact ⟨I, hI, Or.inr (by simp)⟩
  · exact ⟨I, hI, Or.inl (by simp)⟩

theorem neg_signed_incidence_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {I : Finset (Φ.Coordinate d)} (hI : Φ.Compatible I) (e : Bool) :
    -(affineSign e • Φ.incidence seed I) ∈ Φ.incidenceHull seed := by
  apply subset_convexHull ℝ
  cases e
  · exact ⟨I, hI, Or.inl (by simp)⟩
  · exact ⟨I, hI, Or.inr (by simp)⟩

theorem batchGradient_affineSlope (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) {A : Finset (Φ.Coordinate d → ℝ)}
    (i : Φ.AffineIndex A) (j : J) (k : Fin (Φ.WeightDimension d)) :
    Φ.batchGradient J (Φ.affineSlope seed J i) j k =
      affineSign i.2.2.2 * Φ.incidence seed i.2.1.val j k := by
  change affineSign i.2.2.2 *
    Φ.batchGradient J ((Φ.selectionForm i.2.1.val).comp (Φ.batchSumCLM seed J)) j k = _
  rw [Φ.batchGradient_form seed J ((Φ.mem_compatibleSelections _).mp i.2.1.property)]

theorem batchGradient_half_difference_valid (Φ : LabelCover) {d : ℕ}
    (seed : Φ.Seeds d) (J : Finset (Fin d)) {A : Finset (Φ.Coordinate d → ℝ)}
    (im ip : Φ.AffineIndex A) :
    Φ.BatchGradientValid seed J (Φ.batchGradient J
      ((1/2 : ℝ) • (Φ.affineSlope seed J im - Φ.affineSlope seed J ip))) := by
  let gm := affineSign im.2.2.2 • Φ.incidence seed im.2.1.val
  let gp := -(affineSign ip.2.2.2 • Φ.incidence seed ip.2.1.val)
  have hm := Φ.signed_incidence_mem seed
    ((Φ.mem_compatibleSelections _).mp im.2.1.property) im.2.2.2
  have hp := Φ.neg_signed_incidence_mem seed
    ((Φ.mem_compatibleSelections _).mp ip.2.1.property) ip.2.2.2
  refine ⟨(1/2 : ℝ) • gm + (1/2 : ℝ) • gp,
    (convex_convexHull ℝ _) hm hp (by norm_num) (by norm_num) (by norm_num), ?_⟩
  intro j k
  change (1/2 : ℝ) * (Φ.batchGradient J (Φ.affineSlope seed J im) j k -
    Φ.batchGradient J (Φ.affineSlope seed J ip) j k) = _
  rw [Φ.batchGradient_affineSlope, Φ.batchGradient_affineSlope]
  simp only [gm, gp, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

noncomputable def canonicalGradient (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    Φ.BatchWeights J := by
  classical
  exact if VertexCover.AffineSelector.Regular (Φ.affineSlope seed J)
    (Φ.affineOffset c0 (A := A)) s then
      Φ.batchGradient J (fderiv ℝ (Φ.batchFunction seed J c0 A hA) s) else 0

theorem canonicalGradient_valid (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (J : Finset (Fin d)) (c0 : Φ.Coordinate d → ℝ)
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (s : Φ.BatchWeights J) :
    Φ.BatchGradientValid seed J (Φ.canonicalGradient seed J c0 A hA s) := by
  classical
  unfold canonicalGradient
  split_ifs with hs
  · obtain ⟨im, ip, hder⟩ := Φ.batchFunction_hasFDerivAt seed J c0 A hA s hs
    rw [hder.fderiv]
    exact Φ.batchGradient_half_difference_valid seed J im ip
  · exact ⟨0, Φ.zero_mem_incidenceHull seed, fun _ _ => rfl⟩

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
