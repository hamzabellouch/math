import OAI.NumberTheory.CubicMoment.Estimates.NoncubeOrdinaryBounds
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeFrequencyBounds

namespace OAI

/-! All three sieve orientations on the same concrete noncube frequency block. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def coprimePairs (S T : Finset Eisenstein) : Finset (Eisenstein × Eisenstein) :=
  (S.product T).filter (fun p => IsCoprime p.1 p.2)

lemma coprimeResidualSupport_subset (R J S T : Finset Eisenstein) :
    coprimeResidualSupport R J (coprimePairs S T) ⊆ residualCubeSupport R S T J := by
  intro n hn
  obtain ⟨⟨⟨r,j⟩,⟨s,t⟩⟩,hz,rfl⟩ := Finset.mem_image.mp hn
  have hz' := Finset.mem_product.mp hz
  have hrj := Finset.mem_product.mp hz'.1
  have hst := Finset.mem_product.mp (Finset.mem_filter.mp hz'.2).1
  apply Finset.mem_biUnion.mpr
  refine ⟨r,hrj.1,Finset.mem_image.mpr ⟨s*t^2*j^3,?_,?_⟩⟩
  · exact Finset.mem_image.mpr ⟨(s,t,j),Finset.mem_product.mpr
      ⟨hst.1,Finset.mem_product.mpr ⟨hst.2,hrj.2⟩⟩,rfl⟩
  · ring

/-- The two cubic estimates and the ordinary estimate apply to the same
positive mass; no exceptional-moment hypothesis is used. -/
theorem noncube_three_sieve_bounds (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (B R S T J H : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        min ((R.card:ℝ)*J.card*C₁ *
          min ((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))))
          ((R.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N)) *
            ∑ b ∈ B, ‖β b‖^2 := by
  obtain ⟨C₁,hC₁,hcubic⟩ := residualFrequency_sieve_bound ε hε
  obtain ⟨C₂,hC₂,hordinary⟩ := coprimeResidual_ordinary_sieve hHuxley hε
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro B R S T J H N U V hN hU hV hB hS hT hH β
  have hc := (frequency_subset_mass_le H (residualCubeSupport R S T J) B
    (hH.trans (coprimeResidualSupport_subset R J S T)) β).trans
    (hcubic B R S T J N U V hN hU hV hB hS hT β)
  have hP : ∀ p ∈ coprimePairs S T,
      PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ U*V := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hst := Finset.mem_product.mp hp'.1
    refine ⟨⟨(hS p.1 hst.1).1,(hT p.2 hst.2).1,(hS p.1 hst.1).2.1,
      (hT p.2 hst.2).2.1,hp'.2⟩,?_⟩
    rw [pairConductor,norm_mul_eq]
    exact mul_le_mul (hS p.1 hst.1).2.2 (hT p.2 hst.2).2.2 (norm_nonneg _) (by linarith)
  have ho := (frequency_subset_mass_le H _ B hH β).trans
    (hordinary B R J (coprimePairs S T) (U*V) N
      (one_le_mul_of_one_le_of_one_le hU hV) hN hP
      (fun b hb => ⟨(hB b hb).1,(hB b hb).2.2⟩) β)
  rw [min_mul_of_nonneg _ _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  exact le_min hc ho

end CubicFirstMoment

end

end OAI
