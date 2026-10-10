import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.CylinderCovering.Angular.InterceptDefinitions

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace TriangularCovering

theorem lowerIntercept_eq_convexHull {a b T : ℝ} (hab : a < b) (hT : 0 < T) :
    lowerIntercept a b T = convexHull ℝ (Set.range (lowerVertices a b T)) := by
  change lowerIntercept a b T =
    triangle (lowerVertices a b T 0) (lowerVertices a b T 1) (lowerVertices a b T 2)
  ext z
  constructor
  · rintro ⟨y,t,ht0,htT,hay,hyb,rfl⟩
    exact lower_triangle_mem hab hT ht0 htT hay hyb
  · rw [mem_triangle_iff]
    rintro ⟨r,s,hr,hs,hrs,rfl⟩
    refine ⟨r*(a*T)+s*(b*T), r*T+s*T, ?_, ?_, ?_, ?_, ?_⟩
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_right hrs hT.le]
    · nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hab.le hT.le) hs]
    · nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hab.le hT.le) hr]
    · ext i
      fin_cases i <;> simp [lowerVertices, point]
      ring

theorem upperIntercept_eq_convexHull {a b T : ℝ} (hab : a < b) (hT : 0 < T) :
    upperIntercept a b T = convexHull ℝ (Set.range (upperVertices a b T)) := by
  change upperIntercept a b T =
    triangle (upperVertices a b T 0) (upperVertices a b T 1) (upperVertices a b T 2)
  ext z
  constructor
  · rintro ⟨x,t,ht0,htT,hax,hxb,rfl⟩
    exact upper_triangle_mem hab hT ht0 htT hax hxb
  · rw [mem_triangle_iff]
    rintro ⟨r,s,hr,hs,hrs,rfl⟩
    refine ⟨r*(a*T)+s*(b*T), r*T+s*T, ?_, ?_, ?_, ?_, ?_⟩
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_right hrs hT.le]
    · nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hab.le hT.le) hs]
    · nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hab.le hT.le) hr]
    · ext i
      fin_cases i <;> simp [upperVertices, point]
      ring

theorem projectedCylinder_carrier_direction (v : Space) (hv : v ≠ 0)
    (a b c : Space)
    (h : inner ℝ (unit v) (cross3 (b-a) (c-a)) ≠ 0) :
    (projectedCylinder (unit v) (unit_norm hv) a b c h).carrier =
      {z | ∃ p ∈ triangle a b c, ∃ r : ℝ, z = p + r • v} := by
  ext z
  constructor
  · rintro ⟨q,⟨p,hp,rfl⟩,r,hz⟩
    refine ⟨p,hp,(r-inner ℝ (unit v) p) / ‖v‖,?_⟩
    calc
      z = projection (unit v) p + r • unit v := hz
      _ = p + (r-inner ℝ (unit v) p) • unit v := by
        unfold projection
        module
      _ = p + ((r-inner ℝ (unit v) p) / ‖v‖) • v := by
        simp only [unit, smul_smul, div_eq_mul_inv]
  · rintro ⟨p,hp,r,hz⟩
    exact projectedCylinder_mem_direction v hv a b c h hp r hz

theorem lowerCylinder_carrier_intercept {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (ε A B : ℝ) :
    (lowerCylinder hab hT ε A B).carrier =
      {z | ∃ p ∈ lowerIntercept a b T, ∃ r : ℝ, z = p + r • tiltV ε A B} := by
  rw [lowerCylinder, projectedCylinder_carrier_direction _ (tiltV_ne_zero ε A B),
    lowerIntercept_eq_convexHull hab hT]
  rfl

theorem upperCylinder_carrier_intercept {a b T : ℝ} (hab : a < b) (hT : 0 < T)
    (ε A B : ℝ) :
    (upperCylinder hab hT ε A B).carrier =
      {z | ∃ p ∈ upperIntercept a b T, ∃ r : ℝ, z = p + r • tiltW ε A B} := by
  rw [upperCylinder, projectedCylinder_carrier_direction _ (tiltW_ne_zero ε A B),
    upperIntercept_eq_convexHull hab hT]
  rfl

theorem lowerAngularBase_eq_projection_intercept (ε : ℝ) (he : 0 < ε)
    (j : Fin (n ε)) :
    lowerAngularBase ε j = projection (lowerAngularAxis ε j) ''
      lowerIntercept (mesh (n ε) j) (mesh (n ε) (j + 1))
        (cutoff ε (mesh (n ε) j) (mesh (n ε) (j + 1))) := by
  rw [lowerIntercept_eq_convexHull (mesh_strict (N := n ε) (ceil_count_pos he) j)
    (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j + 1)))]
  rfl

theorem upperAngularBase_eq_projection_intercept (ε : ℝ) (he : 0 < ε)
    (j : Fin (n ε)) :
    upperAngularBase ε j = projection (upperAngularAxis ε j) ''
      upperIntercept (mesh (n ε) j) (mesh (n ε) (j + 1))
        (cutoff ε (mesh (n ε) j) (mesh (n ε) (j + 1))) := by
  rw [upperIntercept_eq_convexHull (mesh_strict (N := n ε) (ceil_count_pos he) j)
    (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j + 1)))]
  rfl

theorem TriCylinder.ext_axis_base {c d : TriCylinder}
    (ha : c.axis = d.axis) (hb : c.base = d.base) : c = d := by
  cases c
  cases d
  cases ha
  cases hb
  rfl

theorem finiteFamily_explicit_laws (ε : ℝ) (he : 0 < ε) :
    ExplicitAngularFamily ε (finiteFamily ε he) := by
  intro j
  simp only [lowerAngularIndex, upperAngularIndex, finiteFamily, Function.comp_apply,
    Fin.cast_cast, Fin.cast_eq_self, Fin.append_left, Fin.append_right]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ExplicitAngularFamily.unique {ε : ℝ}
    {c d : Fin (2 * n ε) → TriCylinder}
    (hc : ExplicitAngularFamily ε c) (hd : ExplicitAngularFamily ε d) : c = d := by
  have h : ∀ k : Fin (n ε + n ε),
      c (Fin.cast (two_mul (n ε)).symm k) =
        d (Fin.cast (two_mul (n ε)).symm k) := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · exact TriCylinder.ext_axis_base ((hc j).1.trans (hd j).1.symm)
        ((hc j).2.1.trans (hd j).2.1.symm)
    · exact TriCylinder.ext_axis_base ((hc j).2.2.1.trans (hd j).2.2.1.symm)
        ((hc j).2.2.2.trans (hd j).2.2.2.symm)
  funext i
  simpa only [Fin.cast_cast, Fin.cast_eq_self] using h (Fin.cast (two_mul (n ε)) i)

theorem ExplicitAngularFamily.eq_finiteFamily {ε : ℝ} (he : 0 < ε)
    {c : Fin (2 * n ε) → TriCylinder} (hc : ExplicitAngularFamily ε c) :
    c = finiteFamily ε he := hc.unique (finiteFamily_explicit_laws ε he)

theorem ExplicitAngularFamily.exact_area_sum {ε : ℝ} (he : 0 < ε)
    {c : Fin (2 * n ε) → TriCylinder} (hc : ExplicitAngularFamily ε c) :
    totalArea c / H =
      ∑ j : Fin (n ε), normalizedTerm ε (mesh (n ε) j) (mesh (n ε) (j + 1)) := by
  rw [hc.eq_finiteFamily he]
  exact finiteFamily_total ε he

theorem ExplicitAngularFamily.covers {ε : ℝ} (he : 0 < ε)
    (hsmall : ε ≤ 1 / 2000) {c : Fin (2 * n ε) → TriCylinder}
    (hc : ExplicitAngularFamily ε c) : Covers c := by
  rw [hc.eq_finiteFamily he]
  apply finiteFamily_covers he
  norm_num [η] at *
  exact hsmall

end TriangularCovering

end

end OAI
