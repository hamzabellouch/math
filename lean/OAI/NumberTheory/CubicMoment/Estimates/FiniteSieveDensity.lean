import OAI.NumberTheory.CubicMoment.Estimates.SievedModelAssembly

namespace OAI

/-! Identify the finite square-divisor density with the already proved
convergent Möbius residue series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma collectedSieve_weighted_sum_real (C : Finset Eisenstein) (F : Eisenstein → ℝ) :
    (∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
      collectedSquarefreeSieveCoefficient C d*F d) =
    ∑ c ∈ C, ∑ d ∈ C, (idealMoebius c:ℝ)*(idealMoebius d:ℝ)*F (primarySquarefreeJoin c d) := by
  have h := collectedSieve_weighted_sum C (fun d => (F d:ℂ))
  exact_mod_cast h

lemma collectedSieve_eq_zero_off_image (C : Finset Eisenstein) {d : Eisenstein}
    (hd : d ∉ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2)) :
    collectedSquarefreeSieveCoefficient C d = 0 := by
  by_contra hn
  obtain ⟨a,ha,b,hb,he⟩ := collectedSieveCoefficient_nonzero C d hn
  exact hd (Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,he⟩)

lemma finiteSieveDensity_eq_sum (C : Finset Eisenstein) :
    finiteSieveDensity C = ∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
      collectedSquarefreeSieveCoefficient C d/(norm d)^2 := by
  simpa only [finiteSieveDensity,div_eq_mul_inv] using
    (collectedSieve_weighted_sum_real C (fun d => ((norm d)^2)⁻¹)).symm

lemma finiteSieveDensity_eq_residue (D : ℝ) :
    finiteSieveDensity (squarefreeDivisorTruncation D) =
      ∑' d : Eisenstein, squarefreeSieveResidueTerm D d := by
  let C := squarefreeDivisorTruncation D
  let S := (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2)
  have hs : (∑' d : Eisenstein, squarefreeSieveResidueTerm D d) =
      ∑ d ∈ S, squarefreeSieveResidueTerm D d := by
    apply tsum_eq_sum
    intro d hd
    unfold squarefreeSieveResidueTerm
    rw [collectedSieve_eq_zero_off_image C hd]
    split_ifs <;> simp
  rw [hs,finiteSieveDensity_eq_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hd
  have ha := squarefreeTruncation_spec D a (Finset.mem_product.mp hab).1
  have hb := squarefreeTruncation_spec D b (Finset.mem_product.mp hab).2
  simp only [squarefreeSieveResidueTerm,ite_eq_left (primarySquarefreeJoin_primary ha.1 hb.1)]

 theorem finiteSieveDensity_error : ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 1 ≤ D →
    |finiteSieveDensity (squarefreeDivisorTruncation D)-
      (∑' d : Eisenstein, moebiusResidueTerm d)| ≤ K*D^(-(1/2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := sieveResidue_difference_le
  refine ⟨K,hK,?_⟩
  intro D hD
  rw [finiteSieveDensity_eq_residue]
  exact hbound D (zero_lt_one.trans_le hD)

end CubicFirstMoment

end

end OAI
