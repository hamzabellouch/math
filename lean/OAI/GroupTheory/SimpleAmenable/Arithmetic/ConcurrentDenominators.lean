import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentDenominators

noncomputable def lineNormal (a : ℕ) (j : Fin 4) : CutRing × CutRing :=
  ![(1,0),(0,1),(-(cutTau^a),1),(1,-(cutTau^a))] j

noncomputable def lineDet (a : ℕ) (i j : Fin 4) : CutRing :=
  (lineNormal a i).1*(lineNormal a j).2-(lineNormal a j).1*(lineNormal a i).2

theorem cutForm_normal (a : ℕ) (j : Fin 4) (z : ℝ × ℝ) :
    cutForm a j z = ordinary (lineNormal a j).1*z.1+ordinary (lineNormal a j).2*z.2 := by
  fin_cases j <;> simp [cutForm,lineNormal] <;> ring

theorem lineDet_ne_zero {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i ≠ j) :
    lineDet a i j ≠ 0 := by
  have hp : 1 < ordinary (cutTau^a) := by
    simpa using one_lt_pow₀ Real.one_lt_goldenRatio (show a≠0 by omega)
  have hn : cutTau^a ≠ 0 := by
    intro he; have hh := congrArg ordinary he; simp only [map_zero] at hh; linarith
  have hm : 1-cutTau^a*cutTau^a ≠ 0 := by
    intro he; have hh := congrArg ordinary he
    simp only [map_sub,map_one,map_mul,map_zero] at hh
    nlinarith
  have hm' : cutTau^a*cutTau^a-1 ≠ 0 := by
    intro he; apply hm; linear_combination -he
  fin_cases i <;> fin_cases j <;>
    simp_all [lineDet,lineNormal]

theorem intersection_pair_denominator (a : ℕ) (i j : Fin 4)
    (c d : CutRing) (z : ℝ × ℝ)
    (hi : cutForm a i z = ordinary c) (hj : cutForm a j z = ordinary d) :
    ∃ u v : CutRing,
      ordinary u=((QuadraticAlgebra.norm (lineDet a i j) : ℤ) : ℝ)*z.1 ∧
      ordinary v=((QuadraticAlgebra.norm (lineDet a i j) : ℤ) : ℝ)*z.2 := by
  let δ := lineDet a i j
  let x := c*(lineNormal a j).2-d*(lineNormal a i).2
  let y := (lineNormal a i).1*d-(lineNormal a j).1*c
  have hx : ordinary x=ordinary δ*z.1 := by
    rw [cutForm_normal] at hi hj
    simp only [x,δ,lineDet,map_sub,map_mul]
    linear_combination -(ordinary (lineNormal a j).2)*hi+(ordinary (lineNormal a i).2)*hj
  have hy : ordinary y=ordinary δ*z.2 := by
    rw [cutForm_normal] at hi hj
    simp only [y,δ,lineDet,map_sub,map_mul]
    linear_combination -(ordinary (lineNormal a i).1)*hj+(ordinary (lineNormal a j).1)*hi
  refine ⟨x*star δ,y*star δ,?_,?_⟩ <;>
    simp only [map_mul,hx,hy,← conjugate_eq_ordinary_star]
  · rw [← cut_norm_identity δ]; ring
  · rw [← cut_norm_identity δ]; ring

noncomputable def commonVertexDenominator (a : ℕ) : ℕ :=
  (∏ i : Fin 4, ∏ j : Fin 4,
    if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j)).natAbs

theorem commonVertexDenominator_pos {a : ℕ} (ha : 0<a) : 0<commonVertexDenominator a := by
  apply Int.natAbs_pos.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split_ifs with h
  · norm_num
  · exact cut_norm_nonzero (lineDet_ne_zero ha i j h)

theorem pair_norm_dvd_vertexDenominator (a : ℕ) (i j : Fin 4) (hij : i≠j) :
    QuadraticAlgebra.norm (lineDet a i j) ∣ (commonVertexDenominator a : ℤ) := by
  apply Int.dvd_natAbs.mpr
  have hi := Finset.dvd_prod_of_mem
    (fun i : Fin 4 => ∏ j : Fin 4, if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j))
    (Finset.mem_univ i)
  have hj := Finset.dvd_prod_of_mem
    (fun j : Fin 4 => if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j))
    (Finset.mem_univ j)
  have hh : QuadraticAlgebra.norm (lineDet a i j) ∣
      ∏ j : Fin 4, if i=j then (1 : ℤ) else QuadraticAlgebra.norm (lineDet a i j) := by
    simpa only [ite_eq_right hij] using hj
  exact hh.trans hi

theorem all_intersections_common_denominator {a : ℕ} (_ha : 0<a)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing) (z : ℝ × ℝ)
    (hi : cutForm a i z = ordinary c) (hj : cutForm a j z = ordinary d) :
    ∃ u v : CutRing,
      ordinary u=(commonVertexDenominator a : ℝ)*z.1 ∧
      ordinary v=(commonVertexDenominator a : ℝ)*z.2 := by
  obtain ⟨u,v,hu,hv⟩ := intersection_pair_denominator a i j c d z hi hj
  obtain ⟨k,hk⟩ := pair_norm_dvd_vertexDenominator a i j hij
  have hkr : (commonVertexDenominator a : ℝ)=
      ((QuadraticAlgebra.norm (lineDet a i j) : ℤ) : ℝ)*(k : ℝ) := by exact_mod_cast hk
  refine ⟨(k : CutRing)*u,(k : CutRing)*v,?_,?_⟩ <;>
    simp only [map_mul,map_intCast,hu,hv,hkr] <;> ring

end ConcurrentDenominators

section VertexResidues

noncomputable def cutResidue (D : ℕ) (z : CutRing) : CutRing :=
  ⟨z.re % (D : ℤ),z.im % (D : ℤ)⟩
noncomputable def cutQuotient (D : ℕ) (z : CutRing) : CutRing :=
  ⟨z.re / (D : ℤ),z.im / (D : ℤ)⟩

theorem cut_residue_decomposition (D : ℕ) (z : CutRing) :
    z = cutResidue D z + (D : CutRing)*cutQuotient D z := by
  ext <;> simp [cutResidue,cutQuotient,Int.emod_add_mul_ediv]

noncomputable def finiteCutResidue (D : ℕ) (t : Fin D × Fin D) : CutRing :=
  ⟨t.1.val,t.2.val⟩

theorem cutResidue_exists_finite {D : ℕ} (hD : 0<D) (z : CutRing) :
    ∃ t : Fin D × Fin D, cutResidue D z=finiteCutResidue D t := by
  have hDi : (0 : ℤ)<D := by exact_mod_cast hD
  let p : Fin D := ⟨(z.re % (D : ℤ)).toNat,by
    have h := Int.emod_lt_of_pos z.re hDi
    have hn := Int.emod_nonneg z.re (ne_of_gt hDi)
    omega⟩
  let q : Fin D := ⟨(z.im % (D : ℤ)).toNat,by
    have h := Int.emod_lt_of_pos z.im hDi
    have hn := Int.emod_nonneg z.im (ne_of_gt hDi)
    omega⟩
  refine ⟨⟨p,q⟩,?_⟩
  ext <;> simp [cutResidue,finiteCutResidue,p,q,Int.emod_nonneg _ (ne_of_gt hDi)]

noncomputable def vertexRepresentative (D : ℕ)
    (t : (Fin D × Fin D) × (Fin D × Fin D)) : ℝ × ℝ :=
  (ordinary (finiteCutResidue D t.1)/(D : ℝ),ordinary (finiteCutResidue D t.2)/(D : ℝ))

theorem denominated_vertex_normal_form {D : ℕ} (hD : 0<D)
    (z : ℝ × ℝ) (u v : CutRing)
    (hu : ordinary u=(D : ℝ)*z.1) (hv : ordinary v=(D : ℝ)*z.2) :
    ∃ t : (Fin D × Fin D) × (Fin D × Fin D), ∃ x y : CutRing,
      z=vertexRepresentative D t+(ordinary x,ordinary y) := by
  obtain ⟨p,hp⟩ := cutResidue_exists_finite hD u
  obtain ⟨q,hq⟩ := cutResidue_exists_finite hD v
  have hd : (D : ℝ)≠0 := by exact_mod_cast ne_of_gt hD
  have hx := congrArg ordinary (cut_residue_decomposition D u)
  have hy := congrArg ordinary (cut_residue_decomposition D v)
  simp only [map_add,map_mul,map_natCast,hp,hq,hu,hv] at hx hy
  refine ⟨(p,q),cutQuotient D u,cutQuotient D v,?_⟩
  apply Prod.ext
  · change z.1=ordinary (finiteCutResidue D p)/(D : ℝ)+ordinary (cutQuotient D u)
    apply (mul_left_cancel₀ hd)
    rw [mul_add,mul_div_cancel₀ _ hd]
    exact hx
  · change z.2=ordinary (finiteCutResidue D q)/(D : ℝ)+ordinary (cutQuotient D v)
    apply (mul_left_cancel₀ hd)
    rw [mul_add,mul_div_cancel₀ _ hd]
    exact hy

theorem all_intersections_finite_templates {a : ℕ} (ha : 0<a)
    (i j : Fin 4) (hij : i≠j) (c d : CutRing) (z : ℝ × ℝ)
    (hi : cutForm a i z=ordinary c) (hj : cutForm a j z=ordinary d) :
    ∃ t : (Fin (commonVertexDenominator a) × Fin (commonVertexDenominator a)) ×
        (Fin (commonVertexDenominator a) × Fin (commonVertexDenominator a)),
      ∃ x y : CutRing,
        z=vertexRepresentative (commonVertexDenominator a) t+(ordinary x,ordinary y) := by
  obtain ⟨u,v,hu,hv⟩ := all_intersections_common_denominator ha i j hij c d z hi hj
  exact denominated_vertex_normal_form (commonVertexDenominator_pos ha) z u v hu hv

end VertexResidues

end SimpleAmenable
end
end

end OAI
