import OAI.Probability.ClassicalON.BondMeanOrder

namespace OAI

universe uK

noncomputable section
open Set
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph
variable {K : Type uK} [Fintype K]

def annulusIndicator (G : LatticeGraph) (N : ℤ) (z : Site) (η : G.edges → Bool) : ℝ :=
  crossingIndicator (fun e : (G.annulusGraph N z).edges => e.val.1) (fun e => e.val.2)
    (G.annulusInner N z) (G.annulusOuter N z) (fun e => η (G.restrictEdge _ e))

omit [Fintype K] in
theorem annulusIndicator_nonneg (G : LatticeGraph) (N : ℤ) (z : Site) (η : G.edges → Bool) :
    0≤G.annulusIndicator N z η := crossingIndicator_nonneg _ _ _ _ _

omit [Fintype K] in
theorem annulusIndicator_monotone (G : LatticeGraph) (N : ℤ) (z : Site) :
    Monotone (G.annulusIndicator N z) := by
  intro η ξ h
  apply crossingIndicator_monotone
  intro e
  exact h (G.restrictEdge _ e)

omit [Fintype K] in
theorem annulusEdgesEquiv_symm_val (G : LatticeGraph) (N : ℤ) (z : K → Site)
    (hz : SeparatedCenters N z) (i : K) (e : (G.annulusGraph N (z i)).edges) :
    ((G.annulusEdgesEquiv N z hz i).symm e).val=G.restrictEdge _ e := by
  obtain ⟨e,rfl⟩ := (G.annulusEdgesEquiv N z hz i).surjective e
  simp only [Equiv.symm_apply_apply,annulusEdgesEquiv_restrictEdge]

theorem separated_annuli_factor (G : LatticeGraph) (b : G.edges → ℝ) (N : ℤ) (hN : 0≤N)
    (z : K → Site) (hz : SeparatedCenters N z)
    (f : (i : K) → ((G.annulusGraph N (z i)).edges → Bool) → ℝ) :
    poleBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (G.allAnnulusPins N z)
      (fun _ => true) (fun η => ∏ i,f i (fun e => η (G.restrictEdge _ e)))=
    ∏ i,poleBondMean (fun e : (G.annulusGraph N (z i)).edges => e.val.1) (fun e => e.val.2)
      (G.annulusCoupling b N (z i)) (G.annulusPins N (z i)) (fun _ => true) (f i) := by
  let F : (k : Option K) → ({e : G.edges // G.annulusEdgeLabel N z e=k} → Bool) → ℝ :=
    fun k => match k with
    | none => fun _ => 1
    | some i => fun η => f i (arrowEquiv (G.annulusEdgesEquiv N z hz i) η)
  have he (η : G.edges → Bool) : (∏ k,F k (fun e => η e.val))=
      ∏ i,f i (fun e => η (G.restrictEdge _ e)) := by
    rw [Fintype.prod_option]
    simp only [F,one_mul,arrowEquiv,Equiv.coe_fn_mk,annulusEdgesEquiv_symm_val]
  have hp := poleBondMean_blocks (fun e : G.edges => e.val.1) (fun e => e.val.2) b
    (G.allAnnulusPins N z) (G.annulusVertexLabel N z) (G.annulusEdgeLabel N z)
    (fun e => G.annulus_left_label N hN z hz e) (fun e => G.annulus_right_label N hN z hz e) F
  simpa only [he,Fintype.prod_option,F,blockBondMean_one,one_mul,← G.annulus_blockMean b N hN z hz] using hp

theorem separated_annuli_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (K : Type) [Fintype K] (z : K → Site),SeparatedCenters (2^k:ℕ) z →
      freeBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b
        (fun η => ∏ i,G.annulusIndicator (2^k:ℕ) (z i) η)≤ε^Fintype.card K := by
  obtain ⟨k,hk,hs⟩ := local_annulus_small β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G b hb K _ z hz
  have hn : (0:ℤ)≤(2^k:ℕ) := by positivity
  apply le_trans (freeBondMean_le_poleBondMean _ _ _ (fun e => (hb e).1) (G.allAnnulusPins (2^k:ℕ) z)
    _ (fun η => Finset.prod_nonneg (fun i _ => G.annulusIndicator_nonneg _ _ η)) ?_)
  · rw [show (fun η => ∏ i,G.annulusIndicator (2^k:ℕ) (z i) η)=
      (fun η => ∏ i,crossingIndicator (fun e : (G.annulusGraph (2^k:ℕ) (z i)).edges => e.val.1)
        (fun e => e.val.2) (G.annulusInner (2^k:ℕ) (z i)) (G.annulusOuter (2^k:ℕ) (z i))
          (fun e => η (G.restrictEdge _ e))) from rfl]
    rw [G.separated_annuli_factor b _ hn z hz]
    calc
      _≤∏ _i : K,ε := by
        apply Finset.prod_le_prod₀
        · intro i _
          rw [G.annulus_blockMean b _ hn z hz i]
          exact blockBondMean_nonneg _ _ _ (fun e => (hb e).1) _ _ _ _
            (fun η => crossingIndicator_nonneg _ _ _ _ _)
        · intro i _
          exact hs G b hb (z i)
      _=ε^Fintype.card K := by simp
  · intro η ξ h
    apply Finset.prod_le_prod₀
    · intro i _; exact G.annulusIndicator_nonneg _ _ η
    · intro i _; exact G.annulusIndicator_monotone _ _ h

end ClassicalON.LatticeGraph

end

end OAI
