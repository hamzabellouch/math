import OAI.Geometry.CylinderCovering.Ruled.LocalDefinitions
import OAI.Geometry.CylinderCovering.Ruled.CellGeometry
import OAI.Geometry.CylinderCovering.Convexity.CompactC1Remainder

namespace OAI

noncomputable section
open Set Metric
namespace CylinderCovering.ProductLocal
open RuledApproximation

lemma frame_apply (L : (ℝ × ℝ) ≃L[ℝ] Plane) (s : ℝ × ℝ) :
    L s = s.1 • L (1,0) + s.2 • L (0,1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

lemma frame_norm_le {A : Plane →L[ℝ] Plane} {lam : ℝ}
    {L : (ℝ × ℝ) ≃L[ℝ] Plane} (hL : IsUnitEigenframe A lam L)
    (s : ℝ × ℝ) : ‖L s‖ ≤ |s.1| + |s.2| := by
  rw [frame_apply]
  calc ‖s.1 • L (1,0) + s.2 • L (0,1)‖
      ≤ ‖s.1 • L (1,0)‖ + ‖s.2 • L (0,1)‖ := norm_add_le _ _
    _ = |s.1| + |s.2| := by rw [norm_smul,norm_smul,hL.1,hL.2.1]; simp

lemma frame_diagonal {A : Plane →L[ℝ] Plane} {lam : ℝ}
    {L : (ℝ × ℝ) ≃L[ℝ] Plane} (hL : IsUnitEigenframe A lam L)
    (s : ℝ × ℝ) : A (L s) = L (lam*s.1,-lam*s.2) := by
  rw [frame_apply L s,map_add,map_smul,map_smul,hL.2.2.1,hL.2.2.2,
    frame_apply L (lam*s.1,-lam*s.2)]
  simp only [smul_smul]
  congr 1 <;> congr 1 <;> ring

lemma affineCell_distance {A : Plane →L[ℝ] Plane} {lam tau rho : ℝ}
    {L : (ℝ × ℝ) ≃L[ℝ] Plane} (hL : IsUnitEigenframe A lam L)
    {p q : Plane} (hrho : 0 ≤ rho)
    (hq : q ∈ affineCell p rho L (ProductCells.parameterCell tau)) :
    ‖q-p‖ ≤ 2*rho := by
  obtain ⟨s,hs,rfl⟩ := hq
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hrho]
  have hb : ‖L s‖ ≤ 2 := (frame_norm_le hL s).trans (by linarith [hs.1,hs.2.1])
  nlinarith

lemma intercept_identity (v : Plane → Plane) (p : Plane) (rho x lam : ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] Plane)
    (hL : IsUnitEigenframe (fderiv ℝ v p) lam L) (hrho : rho ≠ 0)
    (s : ℝ × ℝ) :
    let q := p + rho • L s
    let e := (x/rho) • L.symm (v q-v p-fderiv ℝ v p (q-p))
    q + x • (v q-v p) =
      p + rho • L (((1+x*lam)*s.1+e.1,(1-x*lam)*s.2+e.2)) := by
  dsimp only
  have hpair : (((1+x*lam)*s.1, (1-x*lam)*s.2) : ℝ × ℝ) =
      s + x • (lam*s.1,-lam*s.2) := by ext <;> simp <;> ring
  have hepair (e : ℝ × ℝ) :
      ((1+x*lam)*s.1+e.1,(1-x*lam)*s.2+e.2) =
        ((1+x*lam)*s.1,(1-x*lam)*s.2)+e := rfl
  rw [hepair,hpair,map_add,map_add,map_smul,← frame_diagonal hL,
    map_smul,L.apply_symm_apply,smul_add,smul_add]
  simp only [smul_smul]
  rw [show rho*(x/rho)=x by field_simp]
  simp only [add_sub_cancel_left,map_smul,smul_sub,smul_smul]
  module

theorem uniform_intercept_containment
    {D U : Set Plane} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    {v : Plane → Plane} (hv : ContDiffOn ℝ 1 v U)
    {M N tau gamma : ℝ} (hM : 0 < M) (hN : 0 < N)
    (htau : 0 < tau) (hgamma : 0 < gamma) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∀ p ∈ D,
      ∀ (lam : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] Plane),
      IsUnitEigenframe (fderiv ℝ v p) lam L →
      0 ≤ lam → M*lam ≤ 1 → (∀ z, ‖L.symm z‖ ≤ N*‖z‖) →
      ∀ rho : ℝ, 0 < rho → rho < rho0 →
      ∀ q ∈ affineCell p rho L (ProductCells.parameterCell tau),
      ∀ x : ℝ, |x| ≤ M →
      q + x • (v q-v p) ∈ affineCell p rho L (ProductCells.interceptCell tau gamma) := by
  let c : ℝ := min (1/2) (gamma*tau/5) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c < 1/2 := by dsimp [c]; linarith [min_le_left (1/2:ℝ) (gamma*tau/5)]
  have hc2 : c < gamma*tau/5 := by
    dsimp [c]; linarith [min_le_right (1/2:ℝ) (gamma*tau/5), mul_pos hgamma htau]
  let delta : ℝ := c/(2*M*N)
  have hd : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨r,hr,hrem⟩ := compact_c1_remainder hD hU hDU hv hd
  refine ⟨r/3,by positivity,?_⟩
  intro p hp lam L hL hlam hML hLN rho hrho hrhor q hq x hx
  obtain ⟨s,hs,rfl⟩ := hq
  let q := p+rho • L s
  have hqdist : ‖q-p‖ ≤ 2*rho := affineCell_distance hL hrho.le ⟨s,hs,rfl⟩
  have hqr : q ∈ ball p r := by rw [mem_ball,dist_eq_norm]; linarith
  let w := v q-v p-fderiv ℝ v p (q-p)
  have hw : ‖w‖ ≤ delta*(2*rho) :=
    (hrem p hp).2 q hqr |>.trans (mul_le_mul_of_nonneg_left hqdist hd.le)
  let e : ℝ × ℝ := (x/rho) • L.symm w
  have he : ‖e‖ ≤ c := by
    calc ‖e‖ = (|x|/rho) * ‖L.symm w‖ := by
            simp only [e,norm_smul,Real.norm_eq_abs,abs_div,abs_of_pos hrho]
      _ ≤ (M/rho) * (N*(delta*(2*rho))) := by
            gcongr
            exact (hLN w).trans (mul_le_mul_of_nonneg_left hw hN.le)
      _ = c := by dsimp [delta]; field_simp
  have he1 : |e.1| ≤ c := (show |e.1| ≤ ‖e‖ by simpa only [Real.norm_eq_abs] using norm_fst_le e).trans he
  have he2 : |e.2| ≤ c := (show |e.2| ≤ ‖e‖ by simpa only [Real.norm_eq_abs] using norm_snd_le e).trans he
  have hz : |x*lam| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg hlam]
    exact (mul_le_mul_of_nonneg_right hx hlam).trans hML
  refine ⟨((1+x*lam)*s.1+e.1,(1-x*lam)*s.2+e.2),
    ProductCells.expanded_parameterCell_mem_intercept hz hs he1 he2 hc1 hc2,?_⟩
  exact (intercept_identity v p rho x lam L hL hrho.ne' s).symm

end CylinderCovering.ProductLocal

end

end OAI
