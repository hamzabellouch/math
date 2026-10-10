import OAI.MeasureTheory.Falconer.Estimates.RescaledCellPackets
import OAI.MeasureTheory.Falconer.Incidence.FrozenPacketProduct

namespace OAI

/-! Pencil-normalized scale combination for actual rescaled cell pencils. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem rescaled_cell_scale_product {δ Δ s t K KP y a m M n H MC mc : ℝ}
    (hδ : 0 < δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ1 : δ/Δ ≤ 1/2)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hy : |y| ≤ 1)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ Δ/4 ∧ |p 1-a| ≤ Δ/4)
    (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound (δ/Δ) t KP
      (P.image (localPacketPoint Δ y a)))
    (hT : ∀ p ∈ P, (T p).Nonempty ∧ m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound δ s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l)
    (D : ℕ) (hD : ∀ p ∈ P, (T p).card ≤ D)
    (hm : 0 < m) (hmc : 0 < mc) (hn : 0 < n) (hH : 0 ≤ H) (hMC : 0 ≤ MC)
    (A B V : Finset (Space 2)) (G : Space 2 → Finset (Space 2))
    (hBA : B ⊆ A) (hB : (B.card:ℝ) ≤ MC)
    (hcover : ∀ p ∈ P, ∀ l ∈ T p, ∃ b ∈ B, l ∈ G b)
    (hband : ∀ b ∈ A, n ≤ ((G b).card:ℝ) ∧ ((G b).card:ℝ) ≤ 2*n)
    (htotal : (∑ b ∈ A, ((G b).card:ℝ)) ≤ H*(V.card:ℝ)) :
    let J := Nat.log 2 D+1
    ∃ k : ℕ, ∃ Q ⊆ P.image (localPacketPoint Δ y a), Q.Nonempty ∧
      (P.card:ℝ) ≤ (J:ℝ)*(Q.card:ℝ) ∧
      (∀ p ∈ Q, |p 0| ≤ 1/4 ∧ |p 1| ≤ 1/4) ∧
      FiniteSeparatedAt (δ/Δ) Q ∧ NormalizedFiniteBallBound (δ/Δ) t (KP*(J:ℝ)) Q ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ p ∈ Q, (U p).Nonempty ∧ InBoundedLineChart (U p) ∧
          FiniteSeparatedAt (δ/Δ) (U p) ∧
          NormalizedFiniteBallBound (δ/Δ) s (2*((K*3^s)*7^s)*(J:ℝ)) (U p) ∧
          (∀ l ∈ U p, TubeIncident (δ/Δ) p l) ∧
          m/(2*(J:ℝ)*(2:ℝ)^k) ≤ ((U p).card:ℝ) ∧
          ((U p).card:ℝ) ≤ M/(2:ℝ)^k) ∧
        ((A.card:ℝ)/mc)*(((Q.biUnion U).card:ℝ)/(m/(2*(J:ℝ)*(2:ℝ)^k))) ≤
          (52*(J:ℝ)*H*(MC/mc))*((V.card:ℝ)/m) ∧
        ((∀ a : ℝ, |a| ≤ 1/2 → |lineGridRound (δ/Δ) a| ≤ 1/2) →
          ∀ p ∈ Q, ∀ l ∈ U p, |l 0| ≤ 1/2) := by
  obtain ⟨k,Q,hQP,hQ,hmass,hsmall,hsep,hball,U,hU,hlocal,hslopes⟩ :=
    rescaled_cell_packet_refinement hδ hΔ hΔ1 hρ1 hs hK hKP hy P T hP hcell hPsep hPball hT D hD
  refine ⟨k,Q,hQP,hQ,hmass,hsmall,hsep,hball,U,hU,?_,hslopes⟩
  let J := Nat.log 2 D+1
  have hJ : 0 < (J:ℝ) := by dsimp [J]; positivity
  have hF : P.biUnion T ⊆ B.biUnion G := by
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨b,hb,hl⟩ := hcover p hp l hl
    exact Finset.mem_biUnion.mpr ⟨b,hb,hl⟩
  have hprod := frozen_packet_card_product hn hH hMC A B (P.biUnion T) V G hBA hB hF hband htotal
  have hraw : (A.card:ℝ)*((2:ℝ)^k*((Q.biUnion U).card:ℝ)) ≤ 26*H*MC*(V.card:ℝ) := calc
    _ ≤ (A.card:ℝ)*(13*((P.biUnion T).card:ℝ)) := mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)
    _ = 13*((A.card:ℝ)*((P.biUnion T).card:ℝ)) := by ring
    _ ≤ 13*(2*H*MC*(V.card:ℝ)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by ring
  have hfactor : 0 ≤ 2*(J:ℝ)/(mc*m) := by positivity
  calc
    _ = ((A.card:ℝ)*((2:ℝ)^k*((Q.biUnion U).card:ℝ)))*(2*(J:ℝ)/(mc*m)) := by field_simp; ring
    _ ≤ (26*H*MC*(V.card:ℝ))*(2*(J:ℝ)/(mc*m)) := mul_le_mul_of_nonneg_right hraw hfactor
    _ = _ := by ring

end Falconer

end OAI
