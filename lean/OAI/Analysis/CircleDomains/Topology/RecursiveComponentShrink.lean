import OAI.Analysis.CircleDomains.Topology.NextComponentShrink

namespace OAI

/-! The actual recursively chosen shrinking homeomorphisms, with
summable geometric forward and quotient-inverse displacement bounds. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

def componentShrinkRadius (n : ℕ) : ℝ := (1/2)^n

lemma componentShrinkRadius_pos (n : ℕ) : 0<componentShrinkRadius n := by
  unfold componentShrinkRadius
  positivity

lemma exists_recursive_component_shrink
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {F : Set ℂ} (hF : IsCompact F) (hFc : IsConnected Fᶜ)
    (p : ℂ → Y) (q : ℂ → Z) (hp : Continuous p) (hq : Continuous q)
    (hconstant : ∀ x ∈ F, ∀ y ∈ connectedComponentIn F x, q y=q x) :
    ∃ H : ℕ → (ℂ ≃ₜ ℂ),
      (∀ n, ComponentImageSmall F p (H n) (componentShrinkRadius n)) ∧
      (∀ n x, dist (p (H (n+1) x)) (p (H n x))<2*componentShrinkRadius n) ∧
      ∀ n x, dist (q ((H (n+1)).symm x)) (q ((H n).symm x))<componentShrinkRadius n := by
  let Stage (n : ℕ) := {H : ℂ ≃ₜ ℂ // ComponentImageSmall F p H (componentShrinkRadius n)}
  have hstep (n : ℕ) (H : Stage n) : ∃ K : Stage (n+1),
      (∀ x, dist (p (K.val x)) (p (H.val x))<2*componentShrinkRadius n) ∧
      ∀ x, dist (q (K.val.symm x)) (q (H.val.symm x))<componentShrinkRadius n := by
    have hsmall : ComponentImageSmall F p H.val ((2*componentShrinkRadius n)/2) := by
      have he : (2*componentShrinkRadius n)/2=componentShrinkRadius n := by ring
      rw [he]
      exact H.property
    obtain ⟨K,hK,hpK,hqK⟩ := exists_next_component_shrinker hsard hsch hF hFc p q hp hq
      hconstant H.val (mul_pos (by norm_num) (componentShrinkRadius_pos n))
      (componentShrinkRadius_pos n) (componentShrinkRadius_pos (n+1)) hsmall
    exact ⟨⟨K,hK⟩,hpK,hqK⟩
  choose next hnext using hstep
  obtain ⟨H0,h0⟩ := exists_initial_component_shrinker hsard hsch hF hFc p hp
    (componentShrinkRadius_pos 0)
  let stage : (n : ℕ) → Stage n := Nat.rec ⟨H0,h0⟩ (fun n H => next n H)
  refine ⟨fun n => (stage n).val,fun n => (stage n).property,?_,?_⟩
  · intro n x
    exact (hnext n (stage n)).1 x
  · intro n x
    exact (hnext n (stage n)).2 x

end CircleDomainRigidity

end

end OAI
