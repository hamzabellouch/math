import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTop

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Construction Filter

def higherSourceEpsilon : ℝ := 1/10000

theorem higherSource_rich_shell_selection (α β c : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) :
    ∃ ρ γ c₀ : ℝ,0 < ρ ∧ 0 < γ ∧ 0 < c₀ ∧
      ∃ M h : ℕ,2 ≤ M ∧ ∃ Kmin : ℝ,0 < Kmin ∧
      ∀ K0 : ℕ,Kmin ≤ (K0:ℝ) → ∀ᶠ L : ℝ in atTop,
      ∀ E : Finset ℕ,
        (∀p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
        c*L ≤ harmonicPrimeMass E →
        ∃ j : Fin (h+1),let k := K0*M^j.val;
        ∃ w A B D s U u : ℝ,
          0 < k ∧ γ*L ≤ w ∧ w ≤ (β-α+1)*L ∧
          0 ≤ A ∧ A+2*w ≤ B ∧ B+2*w ≤ D ∧ D+w ≤ β*L ∧
          ρ*L ≤ harmonicIntervalMass E B (B+w) ∧
          A ≤ s ∧ s+1 ≤ A+w ∧ c₀ ≤ harmonicIntervalMass E s (s+1) ∧
          D ≤ U ∧ U+5*(k:ℝ) ≤ D+w ∧
          U ≤ u ∧ u+1 ≤ U+higherSourceEpsilon*(k:ℝ) ∧
          α*L-1 ≤ u ∧ u ≤ β*L ∧ c₀ ≤ harmonicIntervalMass E u (u+1) ∧
          B+w ≤ u-γ*L ∧ s+1 ≤ u-3*(γ*L) ∧
          ∀ v : ℝ,U ≤ v → v+higherSourceEpsilon*(k:ℝ) ≤ U+5*(k:ℝ) →
            ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+higherSourceEpsilon*(k:ℝ) ∧
              c₀ ≤ harmonicIntervalMass E (U+(i:ℝ)) (U+(i:ℝ)+1) := by
  obtain ⟨ρ,γ,c₀,c₁,hρ,hγ,hc₀,_hc₁,M,h,hM,Kmin,hKmin,hselect⟩ :=
    rich_shell_selection α β c higherSourceEpsilon hα hαβ hc
      (by norm_num [higherSourceEpsilon])
  refine ⟨ρ,γ,c₀,hρ,hγ,hc₀,M,h,hM,Kmin,hKmin,?_⟩
  intro K0 hK
  filter_upwards [hselect K0 hK] with L hL
  intro E hE hmass
  obtain ⟨w,A,B,D,s,U,j,hj,hwlo,hwhi,hA,hAB,hBD,hDend,hmB,hsA,hsend,hsmass,
    hDU,hUend,hrich⟩ := hL E hE hmass
  let k := K0*M^j
  have hk : 0 < k := by
    have hKpos : 0 < K0 := by exact_mod_cast (hKmin.trans_le hK)
    exact Nat.mul_pos hKpos (pow_pos (by omega : 0 < M) _)
  have hr : ∀ v : ℝ,U ≤ v → v+higherSourceEpsilon*(k:ℝ) ≤ U+5*(k:ℝ) →
      ∃ i : ℕ,v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+higherSourceEpsilon*(k:ℝ) ∧
        c₀ ≤ harmonicIntervalMass E (U+(i:ℝ)) (U+(i:ℝ)+1) :=
    fun v hv he => (hrich v hv he).2
  obtain ⟨i,hui,huend,huband,hutop,humass⟩ :=
    exists_higherSource_top_shell (by norm_num [higherSourceEpsilon])
      (by norm_num [higherSourceEpsilon]) hc₀ (fun p hp => (hE p hp).2.1)
      (hUend.trans hDend) hr
  have hgap := higherSource_lower_shell_gaps hwlo hAB hBD hsend hDU hui
  exact ⟨⟨j,by omega⟩,w,A,B,D,s,U,U+(i:ℝ),hk,hwlo,hwhi,hA,hAB,hBD,hDend,
    hmB,hsA,hsend,hsmass,hDU,hUend,hui,huend,huband,hutop,humass,hgap.1,hgap.2,hr⟩

end Ostmann.Characters

end

end OAI
