import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.TriangularCovering.Main

namespace OAI

noncomputable section
open Set
open TriangularCovering

namespace CylinderCovering.AngularGeneral

private lemma radial_parameters {a b T r s : ℝ}
    (hab : a < b) (hT : 0 < T) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r+s ≤ 1) :
    ∃ q ∈ Icc a b, ∃ S ∈ Icc (0:ℝ) T,
      S = r*T+s*T ∧ q*S = r*(a*T)+s*(b*T) := by
  by_cases hz : r+s = 0
  · have hrz : r=0 := by linarith
    have hsz : s=0 := by linarith
    subst r; subst s
    exact ⟨a,⟨le_rfl,hab.le⟩,0,⟨le_rfl,hT.le⟩,by ring,by ring⟩
  · have hpos : 0 < r+s := lt_of_le_of_ne (add_nonneg hr hs) (Ne.symm hz)
    refine ⟨(r*a+s*b)/(r+s),?_,(r+s)*T,?_,by ring,?_⟩
    · constructor
      · apply (le_div_iff₀ hpos).2
        nlinarith only [mul_nonneg hs (sub_nonneg.mpr hab.le)]
      · apply (div_le_iff₀ hpos).2
        nlinarith only [mul_nonneg hr (sub_nonneg.mpr hab.le)]
    · exact ⟨mul_nonneg hpos.le hT.le,by nlinarith only [hrs,hT]⟩
    · field_simp

lemma lowerIntercept_eq_triangle {D : Data} {j : ℕ} {T : ℝ}
    (hab : D.node j < D.node (j+1)) (hT : 0 < T)
    (hcap : ∀ q ∈ interval D j, D.radius j q = T) :
    lowerIntercept D j = triangle (lowerVertices (D.node j) (D.node (j+1)) T 0)
      (lowerVertices (D.node j) (D.node (j+1)) T 1)
      (lowerVertices (D.node j) (D.node (j+1)) T 2) := by
  ext z
  constructor
  · rintro ⟨q,hq,S,hS,rfl⟩
    rw [hcap q hq] at hS
    exact lower_triangle_mem hab hT hS.1 hS.2
      (mul_le_mul_of_nonneg_right hq.1 hS.1)
      (mul_le_mul_of_nonneg_right hq.2 hS.1)
  · intro hz
    rcases (mem_triangle_iff _ _ _ _).1 hz with ⟨r,s,hr,hs,hrs,hz⟩
    obtain ⟨q,hq,S,hS,hseq,hy⟩ := radial_parameters hab hT hr hs hrs
    refine ⟨q,hq,S,?_,?_⟩
    · rw [hcap q hq]
      exact hS
    · rw [hz,hy,hseq]
      ext i
      fin_cases i <;> dsimp [lowerVertices,point] <;> ring

lemma upperIntercept_eq_triangle {D : Data} {j : ℕ} {T : ℝ}
    (hab : D.node j < D.node (j+1)) (hT : 0 < T)
    (hcap : ∀ q ∈ interval D j, D.radius j q = T) :
    upperIntercept D j = triangle (upperVertices (D.node j) (D.node (j+1)) T 0)
      (upperVertices (D.node j) (D.node (j+1)) T 1)
      (upperVertices (D.node j) (D.node (j+1)) T 2) := by
  ext z
  constructor
  · rintro ⟨q,hq,S,hS,rfl⟩
    rw [hcap q hq] at hS
    exact upper_triangle_mem hab hT hS.1 hS.2
      (mul_le_mul_of_nonneg_right hq.1 hS.1)
      (mul_le_mul_of_nonneg_right hq.2 hS.1)
  · intro hz
    rcases (mem_triangle_iff _ _ _ _).1 hz with ⟨r,s,hr,hs,hrs,hz⟩
    obtain ⟨q,hq,S,hS,hseq,hy⟩ := radial_parameters hab hT hr hs hrs
    refine ⟨q,hq,S,?_,?_⟩
    · rw [hcap q hq]
      exact hS
    · rw [hz,hy,hseq]
      ext i
      fin_cases i <;> dsimp [upperVertices,point] <;> ring

lemma lowerBase_eq_constantCylinder {D : Data} {j : ℕ} {T : ℝ}
    (hab : D.node j < D.node (j+1)) (hT : 0 < T)
    (hcap : ∀ q ∈ interval D j, D.radius j q = T) (τ : ℝ) :
    lowerBase τ D j =
      (TriangularCovering.lowerCylinder hab hT τ (D.alpha j) (D.beta j)).base := by
  unfold lowerBase
  rw [lowerIntercept_eq_triangle hab hT hcap]
  have hd : lowerDirection τ D j = tiltV τ (D.alpha j) (D.beta j) := by
    ext i
    fin_cases i <;> dsimp [lowerDirection,point,tiltV]
    ring
  change projection (TriangularCovering.unit (lowerDirection τ D j)) '' _ = _
  rw [hd]
  rfl

lemma upperBase_eq_constantCylinder {D : Data} {j : ℕ} {T : ℝ}
    (hab : D.node j < D.node (j+1)) (hT : 0 < T)
    (hcap : ∀ q ∈ interval D j, D.radius j q = T) (τ : ℝ) :
    upperBase τ D j =
      (TriangularCovering.upperCylinder hab hT τ (D.alpha j) (D.beta j)).base := by
  unfold upperBase
  rw [upperIntercept_eq_triangle hab hT hcap]
  have hd : upperDirection τ D j = tiltW τ (D.alpha j) (D.beta j) := by
    ext i
    fin_cases i <;> dsimp [upperDirection,point,tiltW]
    ring
  change projection (TriangularCovering.unit (upperDirection τ D j)) '' _ = _
  rw [hd]
  rfl

theorem constant_cap_triangular {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) {j : ℕ} (hj : j < D.count)
    (hc : ∃ T : ℝ, ∀ q ∈ interval D j, D.radius j q = T) :
    IsNondegenerateTriangle (lowerBase τ D j) ∧
    IsNondegenerateTriangle (upperBase τ D j) := by
  obtain ⟨T,hcap⟩ := hc
  have hab := hD.2.2.2.1 j hj
  have hleft : D.node j ∈ interval D j := ⟨le_rfl,hab.le⟩
  have hT : 0 < T := by
    rw [← hcap (D.node j) hleft]
    exact hD.2.2.2.2.2.2.2.1 j hj (D.node j) hleft
  rw [lowerBase_eq_constantCylinder hab hT hcap,
    upperBase_eq_constantCylinder hab hT hcap]
  exact ⟨(TriangularCovering.lowerCylinder hab hT τ (D.alpha j) (D.beta j)).triangular,
    (TriangularCovering.upperCylinder hab hT τ (D.alpha j) (D.beta j)).triangular⟩

end CylinderCovering.AngularGeneral

end

end OAI
