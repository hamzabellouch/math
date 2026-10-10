import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSubsetCount

namespace OAI

/-! # Ordered tuple parametrization of prime subsets -/
namespace JointDickman
open Finset

noncomputable def orderedPrimeTuples (P : Finset ℕ) (h : ℕ) : Finset (Fin h → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin h => P)).filter StrictMono

theorem orderedPrimeTuples_mem {P : Finset ℕ} {h : ℕ} {v : Fin h → ℕ} :
    v ∈ orderedPrimeTuples P h ↔ (∀ i, v i ∈ P) ∧ StrictMono v := by
  classical
  simp only [orderedPrimeTuples, mem_filter, Fintype.mem_piFinset]

theorem sum_powersetCard_eq_ordered_tuples (P : Finset ℕ) (h : ℕ)
    (f : Finset ℕ → ℝ) :
    (∑ D ∈ P.powersetCard h, f D) =
      ∑ v ∈ orderedPrimeTuples P h, f (univ.image v) := by
  classical
  symm
  apply sum_bij (fun v _ => univ.image v)
  · intro v hv
    obtain ⟨hvP,hvmono⟩ := orderedPrimeTuples_mem.mp hv
    apply mem_powersetCard.mpr
    constructor
    · intro p hp
      obtain ⟨i,_,rfl⟩ := mem_image.mp hp
      exact hvP i
    · rw [card_image_of_injective _ hvmono.injective, card_univ, Fintype.card_fin]
  · intro v hv w hw he
    have hvmono := (orderedPrimeTuples_mem.mp hv).2
    have hwmono := (orderedPrimeTuples_mem.mp hw).2
    have hcard : (univ.image v).card = h := by
      rw [card_image_of_injective _ hvmono.injective, card_univ, Fintype.card_fin]
    have hvord := orderEmbOfFin_unique hcard (fun i => mem_image.mpr ⟨i,mem_univ _,rfl⟩) hvmono
    have hword := orderEmbOfFin_unique hcard
      (fun i => by rw [he]; exact mem_image.mpr ⟨i,mem_univ _,rfl⟩) hwmono
    exact hvord.trans hword.symm
  · intro D hD
    obtain ⟨hDP,hcard⟩ := mem_powersetCard.mp hD
    refine ⟨D.orderEmbOfFin hcard, ?_, ?_⟩
    · exact orderedPrimeTuples_mem.mpr
        ⟨fun i => hDP (D.orderEmbOfFin_mem hcard i), (D.orderEmbOfFin hcard).strictMono⟩
    · exact D.image_orderEmbOfFin_univ hcard
  · intros; rfl

theorem ordered_tuple_prod {h : ℕ} {v : Fin h → ℕ} (hv : StrictMono v)
    (f : ℕ → ℝ) : (∏ p ∈ univ.image v, f p) = ∏ i, f (v i) :=
  prod_image hv.injective.injOn

end JointDickman

end OAI
