import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TangentChartTemplates
import OAI.GroupTheory.SimpleAmenable.Arithmetic.ConcurrentDenominators

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentAnchors

theorem allowable_line_anchor (a : ℕ) (j : Fin 4) (c : CutRing)
    (z : ℝ × ℝ) (hz : cutForm a j z=ordinary c) {ε : ℝ} (hε : 0<ε) :
    ∃ u : CutRing × CutRing, integralCutForm a j u=c ∧
      dist (ordinary u.1,ordinary u.2) z<ε := by
  by_cases hj : j=2 ∨ j=3
  · exact slope_line_anchor a j hj c z hz hε
  fin_cases j
  · obtain ⟨y,hy,hy'⟩ := exists_cut_between (x := z.2-ε) (y := z.2+ε) (by linarith)
    refine ⟨(c,y),by simp [integralCutForm],?_⟩
    have hx : z.1=ordinary c := hz
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,← hx,sub_self,abs_zero,max_eq_right (abs_nonneg _)]
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · obtain ⟨x,hx,hx'⟩ := exists_cut_between (x := z.1-ε) (y := z.1+ε) (by linarith)
    refine ⟨(x,c),by simp [integralCutForm],?_⟩
    have hy : z.2=ordinary c := hz
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,← hy,sub_self,abs_zero,max_eq_left (abs_nonneg _)]
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · exact False.elim (hj (Or.inl rfl))
  · exact False.elim (hj (Or.inr rfl))

abbrev VertexType (D : ℕ) := (Fin D × Fin D) × (Fin D × Fin D)

def AllowableVertexLine (a : ℕ) (z : ℝ × ℝ) (j : Fin 4) : Prop :=
  ∃ c : CutRing, cutForm a j z=ordinary c

theorem finite_vertex_anchors (a D : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ U : VertexType D → Fin 4 → CutRing × CutRing,
      ∀ t j, AllowableVertexLine a (vertexRepresentative D t) j →
        cutForm a j (vertexRepresentative D t)=ordinary (integralCutForm a j (U t j)) ∧
        dist (ordinary (U t j).1,ordinary (U t j).2) (vertexRepresentative D t)<ε := by
  classical
  have h (t : VertexType D) (j : Fin 4) : ∃ u : CutRing × CutRing,
      AllowableVertexLine a (vertexRepresentative D t) j →
        cutForm a j (vertexRepresentative D t)=ordinary (integralCutForm a j u) ∧
        dist (ordinary u.1,ordinary u.2) (vertexRepresentative D t)<ε := by
    by_cases h : AllowableVertexLine a (vertexRepresentative D t) j
    · obtain ⟨c,hc⟩ := h
      obtain ⟨u,hu,hd⟩ := allowable_line_anchor a j c _ hc hε
      exact ⟨u,fun _ => ⟨by rw [hu]; exact hc,hd⟩⟩
    · exact ⟨0,fun hh => (h hh).elim⟩
  choose U hU using h
  exact ⟨U,hU⟩

theorem representative_line_allowable (a D : ℕ) (t : VertexType D)
    (u : CutRing × CutRing) (j : Fin 4) (c : CutRing) (z : ℝ × ℝ)
    (hz : z=vertexRepresentative D t+(ordinary u.1,ordinary u.2))
    (hc : cutForm a j z=ordinary c) : AllowableVertexLine a (vertexRepresentative D t) j := by
  refine ⟨c-integralCutForm a j u,?_⟩
  rw [hz,cutForm_add,cutForm_ordinary] at hc
  rw [map_sub]
  linarith

theorem translated_vertex_anchors (a D : ℕ) {ε : ℝ}
    (U : VertexType D → Fin 4 → CutRing × CutRing)
    (hU : ∀ t j, AllowableVertexLine a (vertexRepresentative D t) j →
      cutForm a j (vertexRepresentative D t)=ordinary (integralCutForm a j (U t j)) ∧
      dist (ordinary (U t j).1,ordinary (U t j).2) (vertexRepresentative D t)<ε)
    (t : VertexType D) (u : CutRing × CutRing) (j : Fin 4) (c : CutRing) (z : ℝ × ℝ)
    (hz : z=vertexRepresentative D t+(ordinary u.1,ordinary u.2))
    (hc : cutForm a j z=ordinary c) :
    integralCutForm a j (u+U t j)=c ∧
      dist (ordinary (u+U t j).1,ordinary (u+U t j).2) z<ε := by
  obtain ⟨he,hd⟩ := hU t j (representative_line_allowable a D t u j c z hz hc)
  constructor
  · apply ordinary_injective
    rw [← cutForm_ordinary]
    have hpair : (ordinary (u+U t j).1,ordinary (u+U t j).2)=
        (ordinary (U t j).1,ordinary (U t j).2)+(ordinary u.1,ordinary u.2) := by
      ext <;> simp [add_comm]
    rw [hpair,cutForm_add,cutForm_ordinary,← he,← cutForm_add,← hz,hc]
  · have hpair : (ordinary (u+U t j).1,ordinary (u+U t j).2)=
        (ordinary (U t j).1,ordinary (U t j).2)+(ordinary u.1,ordinary u.2) := by
      ext <;> simp [add_comm]
    rwa [hpair,hz,dist_add_right]

theorem concurrent_chart_tables_eventually {a m D : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {ι : Type*} [Finite ι]
    (hr : 0 < ordinary r ∧ ordinary r < 1/2) (hm' : 15 ≤ m+1)
    (U : VertexType D → Fin 4 → CutRing × CutRing)
    (P : VertexType D → ι → Fin 5 × (CutRing × CutRing)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ t u I b hb, B.PrimitiveFamilyLaw I b hb
        (translatedTemplate (Sum.elim
          (fun j : Fin 4 => (⟨j.val+1,by omega⟩,U t j)) (P t)) u) := by
  exact fixedChartTables_eventually hr hm'
    (fun t => Sum.elim (fun j : Fin 4 => (⟨j.val+1,by omega⟩,U t j)) (P t))

end ConcurrentAnchors

section LineIntersectionBounds

theorem real_two_lines_intersect (A B C E c d : ℝ) (h : A*E-C*B ≠ 0) :
    ∃ z : ℝ × ℝ, A*z.1+B*z.2=c ∧ C*z.1+E*z.2=d := by
  refine ⟨((c*E-d*B)/(A*E-C*B),(A*d-C*c)/(A*E-C*B)),?_,?_⟩ <;>
    dsimp only <;> rw [← mul_div_assoc, ← mul_div_assoc, ← add_div] <;>
      apply (div_eq_iff h).mpr <;> ring

theorem real_two_lines_distance_bound (A B C E c d : ℝ) (h : A*E-C*B ≠ 0)
    (z p : ℝ × ℝ) (hz : A*z.1+B*z.2=c) (hz' : C*z.1+E*z.2=d)
    (δ : ℝ) (hδ : 0≤δ)
    (hp : |c-(A*p.1+B*p.2)| ≤ δ) (hp' : |d-(C*p.1+E*p.2)| ≤ δ) :
    dist z p ≤ ((|A| + |B| + |C| + |E|)/|A*E-C*B|)*δ := by
  have hd : 0 < |A*E-C*B| := abs_pos.mpr h
  have hx : (A*E-C*B)*(z.1-p.1)=E*(c-(A*p.1+B*p.2))-B*(d-(C*p.1+E*p.2)) := by
    linear_combination E*hz-B*hz'
  have hy : (A*E-C*B)*(z.2-p.2)=A*(d-(C*p.1+E*p.2))-C*(c-(A*p.1+B*p.2)) := by
    linear_combination A*hz'-C*hz
  have hx' : |A*E-C*B| * |z.1-p.1| ≤ (|E| + |B|)*δ := by
    rw [← abs_mul,hx]
    calc
      _ ≤ |E*(c-(A*p.1+B*p.2))| + |B*(d-(C*p.1+E*p.2))| := abs_sub _ _
      _ ≤ |E| * δ+|B| * δ := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hp' (abs_nonneg _))
      _ = _ := by ring
  have hy' : |A*E-C*B| * |z.2-p.2| ≤ (|A| + |C|)*δ := by
    rw [← abs_mul,hy]
    calc
      _ ≤ |A*(d-(C*p.1+E*p.2))| + |C*(c-(A*p.1+B*p.2))| := abs_sub _ _
      _ ≤ |A| * δ+|C| * δ := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hp' (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
      _ = _ := by ring
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff]
  rw [div_mul_eq_mul_div]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [abs_nonneg A,abs_nonneg C]
  · apply (le_div_iff₀ hd).mpr
    nlinarith [abs_nonneg B,abs_nonneg E]

theorem real_lineDet_ne_zero {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i≠j) :
    ordinary (lineNormal a i).1*ordinary (lineNormal a j).2-
      ordinary (lineNormal a j).1*ordinary (lineNormal a i).2 ≠ 0 := by
  have hh := ordinary_injective.ne (lineDet_ne_zero ha i j hij)
  simpa only [lineDet,map_sub,map_mul,map_zero] using hh

theorem allowable_lines_intersect {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i≠j)
    (c d : CutRing) : ∃ z : ℝ × ℝ, cutForm a i z=ordinary c ∧ cutForm a j z=ordinary d := by
  obtain ⟨z,hz,hz'⟩ := real_two_lines_intersect _ _ _ _ (ordinary c) (ordinary d)
    (real_lineDet_ne_zero ha i j hij)
  exact ⟨z,by rwa [cutForm_normal],by rwa [cutForm_normal]⟩

end LineIntersectionBounds

end SimpleAmenable
end
end

end OAI
