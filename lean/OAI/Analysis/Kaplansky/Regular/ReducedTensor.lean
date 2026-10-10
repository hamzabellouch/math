import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.SlotEstimates
import OAI.Analysis.Kaplansky.Regular.NearGram

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def tensorCoeff (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (a : A) : tensorAlgebra (G:=G) ρ :=
  ⟨diagonal (ρ a),StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩))⟩
def tensorGroup (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (g : G) : tensorAlgebra (G:=G) ρ :=
  ⟨left g,StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨g,rfl⟩))⟩

lemma tensor_two_isometries_of_small_tuple (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (a : ι → A)
    (hc : ∑ i, star (a i)*a i = 1)
    (hr : ∑ i, a i*star (a i) ≤ (1/10000:ℝ) • (1:A)) :
    ∃ s t : tensorAlgebra (G:=F2) ρ, star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  classical
  let e : Fin 2 × ι → ℕ := fun p => (Fintype.equivFin (Fin 2 × ι) p).val
  have he : Function.Injective e := Fin.val_injective.comp (Fintype.equivFin _).injective
  let x (r : Fin 2) : tensorAlgebra (G:=F2) ρ :=
    ∑ i, tensorCoeff ρ (a i) * tensorGroup ρ (freeGen (e (r,i)))
  apply two_isometries_of_near_gram x
  have hc' : ∑ i, star (ρ (a i))*ρ (a i) = 1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg ρ hc
  have hr' : ∑ i, ρ (a i)*star (ρ (a i)) ≤ (1/10000:ℝ) • (1 : H →L[ℂ] H) := by
    have h := map_rel ρ hr
    have hs : ρ ((1/10000:ℝ) • (1:A)) = (1/10000:ℝ) • (1 : H →L[ℂ] H) :=
      (ρ.toAlgHom.map_smul_of_tower (1/10000:ℝ) (1:A)).trans (by rw [map_one])
    rw [hs] at h
    simpa only [map_sum,map_mul,map_star] using h
  intro r s
  have h := free_rows_near_gram e he (fun i => ρ (a i)) hc' hr' r s
  change ‖(tensorAlgebra (G:=F2) ρ).subtype (star (x r)*x s - (if r=s then 1 else 0))‖ ≤ _
  by_cases hrs : r=s
  all_goals
    simp only [hrs,↓reduceIte,map_sub,map_mul,map_star,map_one,map_zero,x,map_sum] at h ⊢
    exact h

lemma tensor_two_isometries_of_row_contraction (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    {ι : Type*} [Fintype ι] (a : ι → A) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∑ i, star (a i)*a i = 1) (hr : ∑ i, a i*star (a i) ≤ c • (1:A)) :
    ∃ s t : tensorAlgebra (G:=F2) ρ, star s*s=1 ∧ star t*t=1 ∧ star s*t=0 := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1/10000) hc1
  obtain ⟨J,hJ,b,hb1,hb2⟩ := exists_small_row_tuple a c hc0 hc hr k
  let := hJ
  apply tensor_two_isometries_of_small_tuple ρ b hb1
  exact hb2.trans (smul_le_smul_of_nonneg_right hk.le (zero_le_one' A))


end KaplanskyConsequences.Regular

end

end OAI
