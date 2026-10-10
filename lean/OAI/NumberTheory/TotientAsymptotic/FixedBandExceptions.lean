import OAI.NumberTheory.TotientAsymptotic.FixedSimplexBandCount
import OAI.NumberTheory.TotientAsymptotic.FixedModelTransfer
import OAI.NumberTheory.TotientAsymptotic.FordStructureCount
import OAI.NumberTheory.TotientAsymptotic.TupleCoefficient

namespace OAI

/-! Fixed terminal truncation first, then a growing retained-coordinate
cutoff: this order makes the actual model-band exception count negligible. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem fixed_model_band_exception_bound : ∃ D : ℝ,0 < D ∧
    ∀ H : ℕ,∃ C c : ℝ,0 < C ∧ 0 < c ∧
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (modelBandsCondition x P) ≤
        (D*Real.exp (-(H:ℝ)^2/4)+C*Real.exp (-c*(P:ℝ)))*tupleNormalization x := by
  classical
  obtain ⟨A,hA,hsmall⟩ := small_head_real_gaussian
  obtain ⟨D,hD,hstruct⟩ := ford_structure_value_count
  refine ⟨A+D,add_pos hA hD,?_⟩
  intro H
  obtain ⟨C,c,hC,hc,hgood⟩ := fixed_simplex_bad_band_count H
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [hgood,eventually_ge_atTop (1:ℕ)] with P hP hP1
  filter_upwards [hP,hsmall,hstruct,fixed_model_band_failure_transfer,
    m_tendsto.eventually (eventually_gt_atTop H),eventually_gt_atTop (1:ℝ)]
    with x hx hs ht htransfer hm hx1
  let Q := preimageExceptionValues x (modelBandsCondition x P)
  have hw (v : {v // v∈Q}) : ∃ n : ℕ,0 < n ∧ n.totient=v.val ∧
      ¬modelBandsCondition x P n := (Finset.mem_filter.mp v.property).2
  choose f hf using hw
  let n : ℕ→ℕ := fun v => if hv : v∈Q then f ⟨v,hv⟩ else 1
  have hn (v) (hv : v∈Q) : 0 < n v ∧ (n v).totient=v ∧
      ¬modelBandsCondition x P (n v) := by
    simpa only [n,dite_eq_left hv] using hf ⟨v,hv⟩
  have hvx (v) (hv : v∈Q) : (v:ℝ) ≤ x :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2).trans
      (Nat.floor_le (by linarith only [hx1]))
  let S := Q.filter (fun v => (fordPrime (n v) 0:ℝ) < x^(1/4:ℝ))
  let T := Q.filter (fun v => ¬fordSimplexCondition x H (n v))
  let R := Q\(S∪T)
  have hS := hs H hm.le S (by
    intro v hv
    obtain ⟨hv,hsmall⟩ := Finset.mem_filter.mp hv
    exact ⟨⟨n v,(hn v hv).1,(hn v hv).2.1⟩,hvx v hv,
      n v,(hn v hv).1,(hn v hv).2.1,hsmall⟩)
  have hT := ht H hm T n (by
    intro v hv
    obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
    exact ⟨(hn v hv).1,(hn v hv).2.1,hvx v hv,hbad⟩)
  have hR := hx R n (by
    intro v hv
    obtain ⟨hv,hout⟩ := Finset.mem_sdiff.mp hv
    have hns : ¬(fordPrime (n v) 0:ℝ) < x^(1/4:ℝ) := by
      intro hh
      exact hout (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv,hh⟩))
    have hst : fordSimplexCondition x H (n v) := by
      by_contra hh
      exact hout (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv,hh⟩))
    exact ⟨(hn v hv).1,(hn v hv).2.1,le_of_not_gt hns,hvx v hv,hst⟩) (by
      intro v hv
      have hvQ := (Finset.mem_sdiff.mp hv).1
      have hb := (hn v hvQ).2.2
      change ¬∀ i∈Finset.Icc 1 (m x-P),_ at hb
      push Not at hb
      obtain ⟨i,hi,hbi⟩ := hb
      refine ⟨i,hi,?_⟩
      have hi' := Finset.mem_Icc.mp hi
      have him : i < m x := by omega
      apply htransfer i him
      by_cases hlo : (9/10:ℝ)*bandScale x i ≤ primeDoubleLog (n v) i
      · exact Or.inr (hbi hlo)
      · exact Or.inl (lt_of_not_ge hlo))
  have hcover : Q⊆S∪T∪R := by
    intro v hv
    by_cases hh : v∈S∪T
    · exact Finset.mem_union_left _ hh
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,hh⟩)
  have hcard : (Q.card:ℝ) ≤ (S.card:ℝ)+T.card+R.card := by
    exact_mod_cast (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  change (Q.card:ℝ) ≤ _
  exact hcard.trans ((add_le_add (add_le_add hS hT) hR).trans_eq (by unfold tupleNormalization; ring))

end TotientAsymptotic

end

end OAI
