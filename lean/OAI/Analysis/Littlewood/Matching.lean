import OAI.Analysis.Littlewood.Nibble

namespace OAI

universe uV uE

namespace AsymptoticallyMinimalLittlewood.Nibble
noncomputable section
open scoped BigOperators
open Finset
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype E] in
lemma pruned_degree_near (U B : Finset V) (S : Finset E) (A : E → Finset V)
    {D C e : ℝ} (hC : 0≤C) (hsub : ∀ i∈S, A i⊆U)
    (hdeg : ∀ v∈U\B, |((incident S A v).card : ℝ)-D|≤e*D/2)
    (hcode : ∀ v∈U, ∀ w∈U, v≠w → ((incident S A v∩incident S A w).card : ℝ)≤C)
    (hB : B⊆U) (hsmall : (B.card : ℝ)*C≤e*D/2) :
    ∀ v∈U\B, |((incident (restrictEdges S A (U\B)) A v).card : ℝ)-D|≤e*D := by
  intro v hv
  obtain ⟨hvU,hvB⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hlo,hhi⟩ := abs_le.mp (hdeg v hv)
  have hloss := degree_loss_deleting U B S A hC hsub v
    (fun w hw hne ↦ hcode v hvU w (hB hw) hne) hvB
  have hu : ((incident (restrictEdges S A (U\B)) A v).card : ℝ)≤(incident S A v).card := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro y hy
    rw [incident_restrict] at hy
    exact (Finset.mem_filter.mp hy).1
  have heD : 0≤e*D := by
    have hh := (abs_nonneg (((incident S A v).card : ℝ)-D)).trans (hdeg v hv)
    linarith
  apply abs_le.mpr
  constructor <;> linarith

lemma matching_after_pruning (r : ℕ) (hr : 1≤r) {K₀ η : ℝ}
    (hK₀ : 0≤K₀) (hη : 0<η) :
    ∃ e T : ℝ, 0<e ∧ 0<T ∧
    ∀ {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E],
    ∀ (U B : Finset V) (S : Finset E) (A : E → Finset V) (D C : ℝ),
      B⊆U → T≤D → T≤((U\B).card : ℝ) → 0≤C → C≤e*D →
      U.card*C≤K₀*D → B.card*C≤e*D/2 →
      (∀ i∈S, A i⊆U) → (∀ i∈S, (A i).card=r) →
      (∀ v∈U\B, |((incident S A v).card : ℝ)-D|≤e*D/2) →
      (∀ v∈U, ∀ w∈U, v≠w → ((incident S A v∩incident S A w).card : ℝ)≤C) →
      ∃ M⊆S, (M : Set E).Pairwise (fun i j ↦ Disjoint (A i) (A j)) ∧
        (1-η)*((U\B).card : ℝ)≤r*(M.card : ℝ) := by
  obtain ⟨e,T,he,hT,h⟩ := almost_perfect_matching r hr hK₀ hη
  refine ⟨e,T,he,hT,?_⟩
  intro V E instV instF instE U B S A D C hB hD hn hC hCe hcode hsmall hsub hunif hdeg hpair
  have hcard : ((U\B).card : ℝ)≤U.card := Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
  obtain ⟨M,hM,hdis,hsize⟩ := h (U\B) (restrictEdges S A (U\B)) A D C hD hn hC hCe
    ((mul_le_mul_of_nonneg_right hcard hC).trans hcode)
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    (fun i hi ↦ hunif i (Finset.mem_filter.mp hi).1)
    (pruned_degree_near U B S A hC hsub hdeg hpair hB hsmall) (by
      intro v hv w hw hvw
      apply (Nat.cast_le.mpr (Finset.card_le_card (show
        incident (restrictEdges S A (U\B)) A v∩incident (restrictEdges S A (U\B)) A w ⊆
          incident S A v∩incident S A w from ?_))).trans
        (hpair v (Finset.mem_sdiff.mp hv).1 w (Finset.mem_sdiff.mp hw).1 hvw)
      intro i hi
      simp only [Finset.mem_inter,incident_restrict,Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1,hi.2.1⟩)
  exact ⟨M,fun i hi ↦ (Finset.mem_filter.mp (hM hi)).1,hdis,hsize⟩

end
end AsymptoticallyMinimalLittlewood.Nibble

end OAI
