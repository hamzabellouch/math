import Mathlib
import OAI.Analysis.AffineBernstein.AffineBoxArea

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

def verticalScale {n : ℕ} (c : ℝ) (hc : c ≠ 0) :
    (Space n × ℝ) ≃L[ℝ] (Space n × ℝ) :=
  ({ toFun := fun z => (z.1,c*z.2)
     invFun := fun z => (z.1,c⁻¹*z.2)
     map_add' := by intro x y; ext <;> simp [mul_add]
     map_smul' := by intro t x; ext <;> simp [mul_left_comm]
     left_inv := by intro z; ext <;> simp [hc]
     right_inv := by intro z; ext <;> simp [hc] } :
    (Space n × ℝ) ≃ₗ[ℝ] (Space n × ℝ)).toContinuousLinearEquiv

@[simp] lemma verticalScale_apply {n : ℕ} (c : ℝ) (hc : c ≠ 0) (z : Space n × ℝ) :
    verticalScale c hc z = (z.1,c*z.2) := rfl

lemma det_verticalScale {n : ℕ} (c : ℝ) (hc : c ≠ 0) :
    (verticalScale (n := n) c hc).toContinuousLinearMap.det = c := by
  let V := verticalScale (n := n) c hc
  have hV : V (0,1) = (0,c) := by simp [V]
  have hbase : (triangularBaseEquiv V hV hc).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (Space n) := by
    ext x
    rfl
  rw [determinant_triangular V hV hc,hbase]
  change LinearMap.det (LinearMap.id : Space n →ₗ[ℝ] Space n)*c = c
  rw [LinearMap.det_id,one_mul]

/- The exact epsilon power in source (strip-area), for the actual area of
an affine-image boundary patch. Only this patch, not the whole transformed
cap or graph, needs to lie in the coordinate box. -/
theorem affine_image_strip_area {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (j : Fin n ⊕ Unit) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hxR : ∀ x ∈ K, ∀ i, |(L (x,u x)+v).1 i| ≤ R)
    (htR : ∀ x ∈ K, |(L (x,u x)+v).2| ≤ R)
    (hstrip : ∀ x ∈ K, |ambientCoordinates n (L (x,u x)+v) j| ≤ ε) :
    Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      (∫ x in K, affineAreaDensity u x) ≤
      (graphAreaBoxBound n (2*max R 1)).toReal * ε^((n:ℝ)/((n:ℝ)+2)) := by
  let P := ambientSwap j
  let T := verticalScale (n := n) ε⁻¹ (inv_ne_zero hε.ne')
  let M := (L.trans P).trans T
  let w := T (P v)
  have hcoord (x : Space n) : M (x,u x)+w = T (P (L (x,u x)+v)) := by
    simp only [M,w,ContinuousLinearEquiv.trans_apply,map_add]
  have hswap (z : Space n × ℝ) (i : Fin n ⊕ Unit) :
      ambientCoordinates n (P z) i = ambientCoordinates n z (Equiv.swap j (Sum.inr ()) i) :=
    ambientSwap_coordinates j z i
  have hb (x : Space n) (hx : x ∈ K) : ∀ i, |(M (x,u x)+w).1 i| ≤ max R 1 := by
    intro i
    rw [hcoord]
    change |ambientCoordinates n (P (L (x,u x)+v)) (Sum.inl i)| ≤ _
    rw [hswap]
    cases Equiv.swap j (Sum.inr ()) (Sum.inl i) with
    | inl l => exact (hxR x hx l).trans (le_max_left _ _)
    | inr l => simpa only [ambientCoordinates_inr] using (htR x hx).trans (le_max_left R 1)
  have ht (x : Space n) (hx : x ∈ K) : |(M (x,u x)+w).2| ≤ max R 1 := by
    rw [hcoord]
    change |ε⁻¹*(P (L (x,u x)+v)).2| ≤ _
    rw [← ambientCoordinates_inr (P (L (x,u x)+v)) (),hswap,
      Equiv.swap_apply_right,abs_mul,abs_inv,abs_of_pos hε]
    calc
      _ ≤ ε⁻¹*ε := mul_le_mul_of_nonneg_left (hstrip x hx) (inv_nonneg.mpr hε.le)
      _ = 1 := inv_mul_cancel₀ hε.ne'
      _ ≤ _ := le_max_right _ _
  have hi := affine_image_graph_area_in_box hΩ hcv hK hKΩ hu hp M w
    (hR.trans (le_max_left _ _)) hb ht
  have hd : |M.toContinuousLinearMap.det| = ε⁻¹*|L.toContinuousLinearMap.det| := by
    simp only [M,abs_det_trans,T,det_verticalScale,abs_inv,abs_of_pos hε,
      show |P.toContinuousLinearMap.det| = 1 from abs_det_involutive P (ambientSwap_involutive j),one_mul]
  rw [hd] at hi
  simp only [Real.rpow_eq_pow] at hi ⊢
  rw [Real.mul_rpow (inv_nonneg.mpr hε.le) (abs_nonneg _),Real.inv_rpow hε.le] at hi
  have hpow : 0 < ε^((n:ℝ)/((n:ℝ)+2)) := Real.rpow_pos_of_pos hε _
  have hm := mul_le_mul_of_nonneg_left hi hpow.le
  have heval : ε^((n:ℝ)/((n:ℝ)+2))*
      ((ε^((n:ℝ)/((n:ℝ)+2)))⁻¹*|L.toContinuousLinearMap.det|^((n:ℝ)/((n:ℝ)+2))*
        (∫ x in K, affineAreaDensity u x)) =
      |L.toContinuousLinearMap.det|^((n:ℝ)/((n:ℝ)+2))*(∫ x in K, affineAreaDensity u x) := by
    field_simp
  rw [heval] at hm
  simpa only [mul_comm] using hm

end AffineBernstein

end

end OAI
