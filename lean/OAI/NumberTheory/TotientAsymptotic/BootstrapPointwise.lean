import OAI.NumberTheory.TotientAsymptotic.BootstrapGoodCount
import OAI.NumberTheory.TotientAsymptotic.CoarseTotientBounds

namespace OAI

/-! The finite-envelope bootstrap inequality at a single dyadic endpoint. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem bootstrap_pointwise : ∃ C : ℝ,0 < C ∧ ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧ ∀ᶠ J : ℕ in atTop,∀ K : ℕ,1 ≤ K →
    Real.exp ((Real.log ((2:ℝ)^J))^(81/100:ℝ)) ≤ (2:ℝ)^K →
    V ((2:ℝ)^J) ≤ ((2:ℝ)^J)^(3/4:ℝ)+
      ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J))+
      C*((2:ℝ)^J/Real.log ((2:ℝ)^J))*(1+B ((2:ℝ)^J))*
        dyadicTotientEnvelope K*(1+Real.log K) := by
  classical
  obtain ⟨C,hC,hgood⟩ := bootstrap_good_count
  obtain ⟨ε,hε,hbad⟩ := bootstrap_good_value_discard
  refine ⟨C,hC,ε,hε,?_⟩
  have hlim : Tendsto (fun J : ℕ => (2:ℝ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hlim.eventually hgood,hbad] with J hgood hbad
  intro K hK hsize
  let x := (2:ℝ)^J
  let T := totientValues x
  let A : Finset ℕ := T.filter (fun (v : ℕ) => (v:ℝ) ≤ x^(3/4:ℝ))
  let D : Finset ℕ := (T\A).filter (fun (v : ℕ) => ¬BootstrapGood x v)
  let Q : Finset ℕ := T\(A∪D)
  have hT (v : ℕ) (hv : v ∈ T) : IsTotient v ∧ (v:ℝ) ≤ x := by
    obtain ⟨hv,ht⟩ := Finset.mem_filter.mp hv
    exact ⟨ht,(Nat.cast_le.mpr (Finset.mem_Icc.mp hv).2).trans (Nat.floor_le (by positivity))⟩
  have hA : (A.card:ℝ) ≤ x^(3/4:ℝ) := by
    have hsub : A ⊆ totientValues (x^(3/4:ℝ)) := by
      intro v hv
      obtain ⟨hv,hs⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨isTotient_pos (hT v hv).1,Nat.le_floor hs⟩,(hT v hv).1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (V_le_self (by positivity))
  have hD := hbad D (by
    intro v hv
    obtain ⟨hv,hh⟩ := Finset.mem_filter.mp hv
    have h := hT v (Finset.mem_sdiff.mp hv).1
    refine ⟨h.1,?_,hh⟩
    have hh : (v:ℝ) ≤ (2:ℝ)^J := h.2
    exact_mod_cast hh)
  have hQ := hgood K hK hsize Q (by
    intro v hv
    obtain ⟨hv,hnot⟩ := Finset.mem_sdiff.mp hv
    have hnotA : v ∉ A := fun ha => hnot (Finset.mem_union_left _ ha)
    have hnotD : v ∉ D := fun hd => hnot (Finset.mem_union_right _ hd)
    have hlarge : x^(3/4:ℝ) < (v:ℝ) := by
      by_contra hh
      exact hnotA (Finset.mem_filter.mpr ⟨hv,le_of_not_gt hh⟩)
    have hg : BootstrapGood x v := by
      by_contra hh
      exact hnotD (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hv,hnotA⟩,hh⟩)
    exact ⟨(hT v hv).1,hg,hlarge,(hT v hv).2⟩)
  have hc : (T.card:ℝ) ≤ (A.card:ℝ)+(D.card:ℝ)+(Q.card:ℝ) := by
    have hsub : T ⊆ A∪D∪Q := by
      intro v hv
      by_cases ha : v ∈ A∪D
      · exact Finset.mem_union_left _ ha
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,ha⟩)
    have hu : (A∪D∪Q).card ≤ (A∪D).card+Q.card := Finset.card_union_le _ _
    have had : (A∪D).card ≤ A.card+D.card := Finset.card_union_le _ _
    have hh : T.card ≤ A.card+D.card+Q.card := by have := Finset.card_le_card hsub; omega
    exact_mod_cast hh
  exact hc.trans (add_le_add (add_le_add hA hD) hQ)

end TotientAsymptotic

end

end OAI
