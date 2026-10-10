import OAI.NumberTheory.DukePrimeDegree.Geometry.FirstCoverCode
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuantitativeQuotientCover

namespace OAI

/-! # Finite codes for bounded transverse coordinates

Only the transverse vector is observed. Equal labels give a quantitative
coordinate bound, with the number of labels controlled by a finite grid.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_bounded_vector_code {Y : Type*} [MeasurableSpace Y]
    {d : ℕ} (f : Y → Fin d → ℝ) (hf : Measurable f)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (K : ℕ) (B : Y → Fin K), Measurable B ∧
      (K : ℝ) ≤ 1+(2*R+2)^d/δ^d ∧
      ∀ x y, (∀ i, |f x i| ≤ R) → B y=B x →
        ∀ i, |f y i-f x i| < 2*δ := by
  classical
  obtain ⟨s,_,hcard,hcover⟩ := cube_grid_cover d hR hδ hδ1
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let g (i : Fin (Fintype.card s)) (x : Y) : ℝ := dist (f x) (e i).val
  let B := firstCoverCode g (fun _ => δ)
  refine ⟨Fintype.card s+1,B,?_,?_,?_⟩
  · exact firstCoverCode_measurable (fun i => hf.dist measurable_const) _
  · push_cast
    have hc : (Fintype.card s : ℝ) ≤ (2*R+2)^d/δ^d := by
      simpa only [Fintype.card_coe] using hcard
    linarith
  · intro x y hx hxy
    obtain ⟨c,hc,hclose⟩ := hcover (f x) hx
    have hcov : ∃ i, g i x < δ := by
      refine ⟨e.symm ⟨c,hc⟩,?_⟩
      change dist (f x) ((e (e.symm ⟨c,hc⟩)).val) < δ
      simp only [Equiv.apply_symm_apply]
      apply (dist_pi_lt_iff hδ).mpr
      intro i
      simpa only [Real.dist_eq] using hclose i
    obtain ⟨i,hiy,hix⟩ := firstCoverCode_common g (fun _ => δ) hcov hxy
    have hd : dist (f y) (f x) < 2*δ :=
      (dist_triangle_right (f y) (f x) (e i).val).trans_lt (by linarith)
    intro j
    simpa only [Real.dist_eq] using (dist_pi_lt_iff (by positivity : 0 < 2*δ)).mp hd j

end DukePrimeDegree

end

end OAI
