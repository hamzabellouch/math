import OAI.Geometry.TriangularCovering.CoordinateCover
import OAI.Geometry.TriangularCovering.Projection

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma H_pos : 0 < H := by norm_num [H]
lemma H_ne_zero : H ≠ 0 := ne_of_gt H_pos
lemma H_sq : H^2 = 2 := by norm_num [H]

def tiltV (ε A B : ℝ) : Space := !₂[1, ε*A, H*ε*B]
def tiltW (ε A B : ℝ) : Space := !₂[-ε*A, 1, H*ε*B]

def lowerVertices (a b T : ℝ) : Fin 3 → Space :=
  ![point 0 0 0, point 0 (a*T) T, point 0 (b*T) T]
def upperVertices (a b T : ℝ) : Fin 3 → Space :=
  ![point 0 0 1, point (a*T) 0 (1-T), point (b*T) 0 (1-T)]

lemma tiltV_ne_zero (ε A B : ℝ) : tiltV ε A B ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 0) h
  norm_num [tiltV] at this

lemma tiltW_ne_zero (ε A B : ℝ) : tiltW ε A B ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 1) h
  norm_num [tiltW] at this

lemma tiltV_norm (ε A B : ℝ) : ‖tiltV ε A B‖ = Real.sqrt (1+ε^2*(A^2+2*B^2)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_coord]
  dsimp [tiltV]
  congr 1
  nlinarith only [H_sq]

lemma tiltW_norm (ε A B : ℝ) : ‖tiltW ε A B‖ = Real.sqrt (1+ε^2*(A^2+2*B^2)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_coord]
  dsimp [tiltW]
  congr 1
  nlinarith only [H_sq]

lemma lower_triple (a b T ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (lowerVertices a b T 1-lowerVertices a b T 0)
        (lowerVertices a b T 2-lowerVertices a b T 0)) =
      H*(a-b)*T^2 / ‖tiltV ε A B‖ := by
  simp only [unit, inner_smul_left, conj_trivial, inner_coord, cross3_coord]
  dsimp [lowerVertices, point, tiltV]
  ring

lemma upper_triple (a b T ε A B : ℝ) :
    inner ℝ (unit (tiltW ε A B))
      (cross3 (upperVertices a b T 1-upperVertices a b T 0)
        (upperVertices a b T 2-upperVertices a b T 0)) =
      H*(a-b)*T^2 / ‖tiltW ε A B‖ := by
  simp only [unit, inner_smul_left, conj_trivial, inner_coord, cross3_coord]
  dsimp [upperVertices, point, tiltW]
  ring

lemma lower_triple_ne_zero {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (lowerVertices a b T 1-lowerVertices a b T 0)
        (lowerVertices a b T 2-lowerVertices a b T 0)) ≠ 0 := by
  rw [lower_triple]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero H_ne_zero (sub_ne_zero.mpr (ne_of_lt hab)))
    (pow_ne_zero _ (ne_of_gt hT))) (norm_ne_zero_iff.mpr (tiltV_ne_zero ε A B))

lemma upper_triple_ne_zero {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    inner ℝ (unit (tiltW ε A B))
      (cross3 (upperVertices a b T 1-upperVertices a b T 0)
        (upperVertices a b T 2-upperVertices a b T 0)) ≠ 0 := by
  rw [upper_triple]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero H_ne_zero (sub_ne_zero.mpr (ne_of_lt hab)))
    (pow_ne_zero _ (ne_of_gt hT))) (norm_ne_zero_iff.mpr (tiltW_ne_zero ε A B))

def lowerCylinder {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) : TriCylinder :=
  projectedCylinder (unit (tiltV ε A B)) (unit_norm (tiltV_ne_zero ε A B))
    (lowerVertices a b T 0) (lowerVertices a b T 1) (lowerVertices a b T 2)
    (lower_triple_ne_zero hab hT ε A B)

def upperCylinder {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) : TriCylinder :=
  projectedCylinder (unit (tiltW ε A B)) (unit_norm (tiltW_ne_zero ε A B))
    (upperVertices a b T 0) (upperVertices a b T 1) (upperVertices a b T 2)
    (upper_triple_ne_zero hab hT ε A B)

lemma lowerCylinder_area {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    area (lowerCylinder hab hT ε A B).base =
      H*(b-a)*T^2 / (2*Real.sqrt (1+ε^2*(A^2+2*B^2))) := by
  rw [lowerCylinder, projectedCylinder_area, lower_triple, tiltV_norm]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos H_pos,
    abs_of_neg (sub_neg.mpr hab), abs_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma upperCylinder_area {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    area (upperCylinder hab hT ε A B).base =
      H*(b-a)*T^2 / (2*Real.sqrt (1+ε^2*(A^2+2*B^2))) := by
  rw [upperCylinder, projectedCylinder_area, upper_triple, tiltW_norm]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos H_pos,
    abs_of_neg (sub_neg.mpr hab), abs_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma sector_weights {a b T y t : ℝ} (hab : a < b) (hT : 0 < T)
    (_ht0 : 0 ≤ t) (htT : t ≤ T) (hay : a*t ≤ y) (hyb : y ≤ b*t) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s ≤ 1 ∧ r*T+s*T=t ∧ r*(a*T)+s*(b*T)=y := by
  let r := (b*t-y)/((b-a)*T)
  let s := (y-a*t)/((b-a)*T)
  have hden : 0 < (b-a)*T := mul_pos (sub_pos.mpr hab) hT
  have hrs : r*T+s*T = t := by
    dsimp [r,s]
    field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hT]
    ring
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hyb) hden.le
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr hay) hden.le
  refine ⟨r,s,hr,hs,?_,hrs,?_⟩
  · nlinarith only [hrs, htT, hT]
  · dsimp [r,s]
    field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hT]
    ring

lemma lower_triangle_mem {a b T y t : ℝ} (hab : a < b) (hT : 0 < T)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hay : a*t ≤ y) (hyb : y ≤ b*t) :
    point 0 y t ∈ triangle (lowerVertices a b T 0)
      (lowerVertices a b T 1) (lowerVertices a b T 2) := by
  obtain ⟨r,s,hr,hs,hrs,het,hey⟩ := sector_weights hab hT ht0 htT hay hyb
  rw [mem_triangle_iff]
  refine ⟨r,s,hr,hs,hrs,?_⟩
  ext i
  fin_cases i <;> dsimp [lowerVertices, point]
  · ring
  · nlinarith only [hey]
  · linear_combination -H * het

lemma upper_triangle_mem {a b T x s : ℝ} (hab : a < b) (hT : 0 < T)
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (hax : a*s ≤ x) (hxb : x ≤ b*s) :
    point x 0 (1-s) ∈ triangle (upperVertices a b T 0)
      (upperVertices a b T 1) (upperVertices a b T 2) := by
  obtain ⟨r,q,hr,hq,hrq,hes,hex⟩ := sector_weights hab hT hs0 hsT hax hxb
  rw [mem_triangle_iff]
  refine ⟨r,q,hr,hq,hrq,?_⟩
  ext i
  fin_cases i <;> dsimp [upperVertices, point]
  · nlinarith only [hex]
  · ring
  · linear_combination H * hes

lemma lowerCylinder_hit {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B x y t : ℝ)
    (hr0 : 0 ≤ t-ε*x*B) (hrT : t-ε*x*B ≤ T)
    (hl : a*(t-ε*x*B) ≤ y-ε*x*A) (hu : y-ε*x*A ≤ b*(t-ε*x*B)) :
    point x y t ∈ (lowerCylinder hab hT ε A B).carrier := by
  apply projectedCylinder_mem_direction (tiltV ε A B) (tiltV_ne_zero ε A B)
    _ _ _ _ (lower_triangle_mem hab hT hr0 hrT hl hu) x
  ext i
  fin_cases i <;> dsimp [point, tiltV] <;> ring

lemma upperCylinder_hit {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B x y t : ℝ)
    (hs0 : 0 ≤ 1-t+ε*y*B) (hsT : 1-t+ε*y*B ≤ T)
    (hl : a*(1-t+ε*y*B) ≤ x+ε*y*A) (hu : x+ε*y*A ≤ b*(1-t+ε*y*B)) :
    point x y t ∈ (upperCylinder hab hT ε A B).carrier := by
  apply projectedCylinder_mem_direction (tiltW ε A B) (tiltW_ne_zero ε A B)
    _ _ _ _ (upper_triangle_mem hab hT hs0 hsT hl hu) y
  ext i
  fin_cases i <;> dsimp [point, tiltW] <;> ring

end TriangularCovering

namespace TriangularCovering

lemma cutoff_pos_all (ε a b : ℝ) : 0 < cutoff ε a b := by
  have hd : 0 ≤ d a := by unfold d; positivity
  have hm : 0 ≤ cutoffCoeff a b := by
    unfold cutoffCoeff η
    have := le_max_left (d a) (d b)
    linarith
  dsimp [cutoff]
  positivity

lemma mesh_strict {N : ℕ} (hN : 0 < N) (j : ℕ) : mesh N j < mesh N (j+1) := by
  have := mesh_succ N j
  have := step_pos hN
  linarith

def lowerFamily (ε : ℝ) (he : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  lowerCylinder (mesh_strict (ceil_count_pos he) j) (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j+1))) ε
    (alpha (mesh (n ε) j) (mesh (n ε) (j+1)))
    (beta (mesh (n ε) j) (mesh (n ε) (j+1)))

def upperFamily (ε : ℝ) (he : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  upperCylinder (mesh_strict (ceil_count_pos he) j) (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j+1))) ε
    (alpha (mesh (n ε) j) (mesh (n ε) (j+1)))
    (beta (mesh (n ε) j) (mesh (n ε) (j+1)))

def finiteFamily (ε : ℝ) (he : 0 < ε) : Fin (2*n ε) → TriCylinder :=
  (Fin.append (lowerFamily ε he) (upperFamily ε he)) ∘ Fin.cast (two_mul (n ε))

lemma finiteFamily_covers {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ η/2) :
    Covers (finiteFamily ε he) := by
  rintro z ⟨x,y,t,_ht0,_ht1,hx,hy,rfl⟩
  rcases finite_coordinate_cover_ceil he hsmall hx hy with ⟨j,hj,hl⟩ | ⟨j,hj,hu⟩
  · refine ⟨Fin.cast (two_mul (n ε)).symm (Fin.castAdd (n ε) (⟨j,hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_left]
    exact lowerCylinder_hit _ _ _ _ _ _ _ _ hl.1.1 hl.2 hl.1.2.1 hl.1.2.2
  · refine ⟨Fin.cast (two_mul (n ε)).symm (Fin.natAdd (n ε) (⟨j,hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_right]
    exact upperCylinder_hit _ _ _ _ _ _ _ _ hu.1.1 hu.2 hu.1.2.1 hu.1.2.2

lemma finiteFamily_total (ε : ℝ) (he : 0 < ε) :
    totalArea (finiteFamily ε he) / H =
      ∑ j : Fin (n ε), normalizedTerm ε (mesh (n ε) j) (mesh (n ε) (j+1)) := by
  have hs : totalArea (finiteFamily ε he) =
      (∑ j : Fin (n ε), area (lowerFamily ε he j).base) +
      (∑ j : Fin (n ε), area (upperFamily ε he j).base) := by
    change (∑ i : Fin (2*n ε),
      (fun k : Fin (n ε+n ε) => area (Fin.append (lowerFamily ε he) (upperFamily ε he) k).base)
        ((finCongr (two_mul (n ε))) i)) = _
    rw [Equiv.sum_comp (finCongr (two_mul (n ε)))
      (fun k => area (Fin.append (lowerFamily ε he) (upperFamily ε he) k).base)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hs, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [lowerFamily, upperFamily, lowerCylinder_area, upperCylinder_area]
  dsimp [normalizedTerm, speedSq, n]
  field_simp [H_ne_zero]
  ring

end TriangularCovering

end

end OAI
