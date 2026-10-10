import OAI.Geometry.SurfaceImmersion.Correction.CenteredPairModels

namespace OAI

/-! Either possible pair of transverse endpoint signs admits a compact
relative frame filling in every neighborhood of the whole connecting interval. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma nonzeroSign_ne_zero (a : ℝ) : nonzeroSign a ≠ 0 := by
  unfold nonzeroSign
  split <;> norm_num

lemma nonzeroSign_cases (a b : ℝ) :
    nonzeroSign a = nonzeroSign b ∨ nonzeroSign b = -nonzeroSign a := by
  unfold nonzeroSign
  split <;> split <;> norm_num

theorem signed_diagonal_filling {p q a b : ℝ} (hpq : p < q)
    {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc p q, crosscapAxis t ∈ U) :
    HasRelativeDefectFilling (diagonalDefectModel (endpointSignModel p q a b) p q) U := by
  let c := (p+q)/2
  let h := (q-p)/2
  have hh : 0 < h := by dsimp [h]; linarith
  have hleft : c-h = p := by dsimp [c,h]; ring
  have hright : c+h = q := by dsimp [c,h]; ring
  have hax : ∀ t ∈ Icc (c-h) (c+h), crosscapAxis t ∈ U := by
    simpa only [hleft,hright] using haxis
  rcases nonzeroSign_cases a b with hsame | hopp
  · have hmodel : diagonalDefectModel (endpointSignModel p q a b) p q =
        centeredOppositeNormal c h (nonzeroSign a) := by
      funext x
      rw [diagonalDefectModel_apply,endpointSignModel_same hpq.ne hsame]
      ext i
      fin_cases i
      · dsimp [centeredOppositeNormal,c,h]
        ring
      · dsimp [centeredOppositeNormal]
        ring
    rw [hmodel]
    exact centeredOppositeNormal_filling hh (nonzeroSign_ne_zero a) hU hax
  · obtain ⟨R,k,hR,hk,hbox⟩ := thin_pair_coordinates hh hU hax
    let H := centeredEqualHomotopy c h k (-nonzeroSign a)
    have h1 : H 1 = centeredEqualNormal c h k (-nonzeroSign a) := by
      funext x
      ext i
      fin_cases i <;> simp [H,centeredEqualHomotopy,centeredEqualNormal]
    have h0 : H 0 = diagonalDefectModel (endpointSignModel p q a b) p q := by
      funext x
      rw [diagonalDefectModel_apply,endpointSignModel_opposite hpq.ne hopp]
      ext i
      fin_cases i
      · dsimp [H,centeredEqualHomotopy,c,h]
        ring
      · dsimp [H,centeredEqualHomotopy,c,h]
        field_simp
        ring
    have hfill : HasRelativeDefectFilling (H 1) U := by
      rw [h1]
      exact centeredEqualNormal_filling hh hk (neg_ne_zero.mpr (nonzeroSign_ne_zero a)) hR hbox
    have hz : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
        x ∉ ({crosscapAxis p,crosscapAxis q} : Set Base) → H s x ≠ 0 := by
      intro s hs x _ hx he
      have hr := (centeredEqualHomotopy_zero_iff hh
        (neg_ne_zero.mpr (nonzeroSign_ne_zero a)) hs.1 x).mp he
      rw [hleft,hright] at hr
      exact hx (by simpa only [mem_insert_iff,mem_singleton_iff] using hr)
    have hzU : ({crosscapAxis p,crosscapAxis q} : Set Base) ⊆ U := by
      intro x hx
      rcases hx with (rfl | rfl)
      · exact haxis p (left_mem_Icc.mpr hpq.le)
      · exact haxis q (right_mem_Icc.mpr hpq.le)
    have hres := relativeDefectFilling_homotopy (centeredEqualHomotopy_smooth c h k (-nonzeroSign a))
      hU (isCompact_singleton.insert _) hzU hz hfill
    change HasRelativeDefectFilling (H 0) U at hres
    rwa [h0] at hres

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
