import OAI.Analysis.KadisonKastler.FullCopyHilbertSum

namespace OAI

/-! # Proper finite cuts of a full countable projection decomposition -/

namespace KadisonKastler
open Generator.Tracial Filter
open scoped Topology BigOperators
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] {M : VonNeumannAlgebra H}

namespace CountableProjectionCopies
variable (C : CountableProjectionCopies M (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))

theorem projection_ne_zero (i : ℕ) : (C.projection i).val≠0 := by
  intro hz
  have hh : (C.projection i).val*C.witness i=C.witness i := by
    rw [← C.final,mul_assoc,C.initial,mul_one]
  rw [hz,zero_mul] at hh
  have hi := C.initial i
  rw [← hh,star_zero,mul_zero] at hi
  exact zero_ne_one hi

def finiteCut (F : Finset ℕ) : AlgebraProjection M :=
  AlgebraProjection.finsetSum C.projection F (fun _ _ _ _ hij => C.orthogonal hij)

theorem finiteCut_ne_one (F : Finset ℕ) : (C.finiteCut F).val≠1 := by
  classical
  let i := F.sup id+1
  have hi : i∉F := by
    intro hi
    have hb := Finset.le_sup (f := id) hi
    change F.sup id+1 ≤ F.sup id at hb
    omega
  have ho : (C.projection i).val*(C.finiteCut F).val=0 := by
    change (C.projection i).val*(∑ j ∈ F, (C.projection j).val)=0
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact C.orthogonal (fun he => hi (he.symm ▸ hj))
  intro he
  rw [he,mul_one] at ho
  exact C.projection_ne_zero i ho

omit [Nontrivial H] in
theorem exists_finiteCut_approx (ξ : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℕ, ‖ξ-(C.finiteCut F).val.val ξ‖<ε := by
  have hs := C.total ξ
  have hn := (Metric.tendsto_nhds.mp hs) ε hε
  obtain ⟨F,hF⟩ := hn.exists
  refine ⟨F,?_⟩
  have he : (C.finiteCut F).val.val ξ=∑ i ∈ F,(C.projection i).val.val ξ := by
    change (M.toStarSubalgebra.subtype (∑ i ∈ F,(C.projection i).val)) ξ=_
    rw [map_sum]
    simp only [sum_apply]
    rfl
  rw [he,norm_sub_rev]
  simpa only [dist_eq_norm] using hF

end CountableProjectionCopies
end
end KadisonKastler

end OAI
