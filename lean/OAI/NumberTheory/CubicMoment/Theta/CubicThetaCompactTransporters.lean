import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactRowBounds

namespace OAI

/-! Only finitely many Eisenstein matrices can carry one compact
positive-height chart into another. This proves the local finiteness
needed for the quotient construction. -/
noncomputable section
open Set
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFullInversion_bottomRow (g : SL(2,Eisenstein)) :
    (cubicThetaFullInversion*g) 1 0=g 0 0 ∧ (cubicThetaFullInversion*g) 1 1=g 0 1 := by
  change ((!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)*(g:Matrix (Fin 2) (Fin 2) Eisenstein)) 1 0=g 0 0 ∧
    ((!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) Eisenstein)*(g:Matrix (Fin 2) (Fin 2) Eisenstein)) 1 1=g 0 1
  simp [Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaCompact_transporter_finite {K L : Set (ℂ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKpos : ∀ p∈K, 0<p.2) (hLpos : ∀ p∈L, 0<p.2) :
    Set.Finite {g : SL(2,Eisenstein) | ∃ p∈K, cubicThetaMobius (cubicThetaFullComplex g) p∈L} := by
  let L' := cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) '' L
  have hL' : IsCompact L' := hL.image_of_continuousOn
    (cubicThetaMobius_continuousOn _ hLpos)
  have hL'pos : ∀ p∈L', 0<p.2 := by
    rintro p ⟨q,hq,rfl⟩
    exact cubicThetaMobius_height_pos _ (hLpos q hq)
  obtain ⟨B1,hB1⟩ := cubicThetaCompact_bottomRow_bound hK hL hKpos hLpos
  obtain ⟨B2,hB2⟩ := cubicThetaCompact_bottomRow_bound hK hL' hKpos hL'pos
  let B := max B1 B2
  have hi : Function.Injective (fun g : SL(2,Eisenstein) => ((g 0 0,g 0 1),(g 1 0,g 1 1))) := by
    intro g h he
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact congrArg (fun t => t.1.1) he
    · exact congrArg (fun t => t.1.2) he
    · exact congrArg (fun t => t.2.1) he
    · exact congrArg (fun t => t.2.2) he
  have hfin : Set.Finite {g : SL(2,Eisenstein) |
      (norm (g 0 0) ≤ B ∧ norm (g 0 1) ≤ B) ∧ (norm (g 1 0) ≤ B ∧ norm (g 1 1) ≤ B)} :=
    (((finite_norm_le B).prod (finite_norm_le B)).prod
      ((finite_norm_le B).prod (finite_norm_le B))).preimage hi.injOn
  apply hfin.subset
  rintro g ⟨p,hp,hq⟩
  have hb1 := hB1 g p hp hq
  have hq' : cubicThetaMobius (cubicThetaFullComplex (cubicThetaFullInversion*g)) p∈L' := by
    refine ⟨cubicThetaMobius (cubicThetaFullComplex g) p,hq,?_⟩
    rw [map_mul,← cubicThetaMobius_comp _ _ (hKpos p hp)]
  have hb2 := hB2 (cubicThetaFullInversion*g) p hp hq'
  rw [(cubicThetaFullInversion_bottomRow g).1,(cubicThetaFullInversion_bottomRow g).2] at hb2
  have h1 : B1 ≤ B := le_max_left _ _
  have h2 : B2 ≤ B := le_max_right _ _
  exact ⟨⟨by linarith [norm_nonneg (g 0 1)],by linarith [norm_nonneg (g 0 0)]⟩,
    ⟨by linarith [norm_nonneg (g 1 1)],by linarith [norm_nonneg (g 1 0)]⟩⟩

end CubicFirstMoment

end

end OAI
