import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionDensity
import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionStarting
import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionThree

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Construction Filter

theorem rich_shell_selection (α β c ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hc : 0 < c) (hε : 0 < ε) :
    ∃ ρ γ c₀ c₁ : ℝ, 0 < ρ ∧ 0 < γ ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∃ M h : ℕ, 2 ≤ M ∧ ∃ Kmin : ℝ, 0 < Kmin ∧
      ∀ K0 : ℕ, Kmin ≤ (K0:ℝ) → ∀ᶠ L : ℝ in atTop,
      ∀ E : Finset ℕ,
        (∀ p ∈ E, p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
        c*L ≤ harmonicPrimeMass E →
        ∃ w A B D s U : ℝ, ∃ j : ℕ, j ≤ h ∧ γ*L ≤ w ∧ w ≤ (β-α+1)*L ∧
          0 ≤ A ∧ A+2*w ≤ B ∧ B+2*w ≤ D ∧ D+w ≤ β*L ∧
          ρ*L ≤ harmonicIntervalMass E B (B+w) ∧
          A ≤ s ∧ s+1 ≤ A+w ∧ c₀ ≤ harmonicIntervalMass E s (s+1) ∧
          D ≤ U ∧ U+5*((K0*M^j:ℕ):ℝ) ≤ D+w ∧
          ∀ v : ℝ, U ≤ v → v+ε*((K0*M^j:ℕ):ℝ) ≤ U+5*((K0*M^j:ℕ):ℝ) →
            c₁*ε*((K0*M^j:ℕ):ℝ) ≤ harmonicIntervalMass E v (v+ε*((K0*M^j:ℕ):ℝ)) ∧
            ∃ i : ℕ, v ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ v+ε*((K0*M^j:ℕ):ℝ) ∧
              c₀ ≤ harmonicIntervalMass E (U+(i:ℝ)) (U+(i:ℝ)+1) := by
  obtain ⟨ρ,γ,hρ,hγ,hthree⟩ := three_rich_harmonic_intervals α β c hα hαβ hc
  let b := β-α+1
  have hb : 0 < b := by dsimp [b]; linarith
  let d := ρ/(4*b)
  have hd : 0 < d := div_pos hρ (by positivity)
  have hdb : d*b = ρ/4 := by dsimp [d]; field_simp
  obtain ⟨M,h,hM,c₁,Kbase,hc₁,hKbase,hden⟩ := harmonic_density_increment d ε hd hε
  obtain ⟨C,hC,hblocks⟩ := exists_paired_harmonic_blocks
  obtain ⟨Cs,hCs,hshell⟩ := exists_rich_grid_unit_shell
  let c₀ := min d (c₁/2)
  have hc₀ : 0 < c₀ := lt_min hd (by positivity)
  let Kmin := max Kbase (max (2*(Cs+1)/(c₁*ε)) (2/ε))
  have hKmin : 0 < Kmin := hKbase.trans_le (le_max_left _ _)
  refine ⟨ρ,γ,c₀,c₁,hρ,hγ,hc₀,hc₁,M,h,hM,Kmin,hKmin,?_⟩
  intro K0 hK
  have hKbase0 : Kbase ≤ (K0:ℝ) := (le_max_left _ _).trans hK
  have hKshell : 2*(Cs+1)/(c₁*ε) ≤ (K0:ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hKunit : 2/ε ≤ (K0:ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hKpos : (0:ℝ)<K0 := hKbase.trans_le hKbase0
  have hMr : (1:ℝ) ≤ M := by exact_mod_cast (show 1≤M by omega)
  let W := 5*(K0:ℝ)*(M:ℝ)^h
  have hW : 0 < W := by dsimp [W]; positivity
  filter_upwards [hthree,eventually_ge_atTop (1:ℝ),eventually_ge_atTop (4*(W+C+1)/ρ),
    eventually_ge_atTop (4*(C+2)/ρ)] with L hthreeL hL hlarge hsmall
  have hlarge' : 4*(W+C+1) ≤ ρ*L := by have hh := (div_le_iff₀ hρ).mp hlarge; nlinarith only [hh]
  have hsmall' : 4*(C+2) ≤ ρ*L := by have hh := (div_le_iff₀ hρ).mp hsmall; nlinarith only [hh]
  intro E hE hm
  have hprime : ∀ p ∈ E, p.Prime := fun p hp => (hE p hp).1
  obtain ⟨w,A,B,D,hwlo,hwhi,hA,hAB,hBD,hDend,hmA,hmB,hmD⟩ := hthreeL E hE hm
  have hw : 0 < w := lt_of_lt_of_le (mul_pos hγ (by linarith)) hwlo
  have hD : 0 ≤ D := by linarith only [hA,hAB,hBD,hw]
  obtain ⟨s,R,hsA,hsend,hsmass0,hR,hRend,hmR⟩ :=
    hblocks E hprime w A D b ρ L d W hw hA hD hd hW hdb hwhi hlarge' hsmall' hmA hmD
  obtain ⟨j,hj,U,hRU,hUend,huniform⟩ := hden K0 hKbase0 E hprime R (hD.trans hR) hmR
  have hsmass : c₀ ≤ harmonicIntervalMass E s (s+1) := (min_le_left _ _).trans hsmass0
  refine ⟨w,A,B,D,s,U,j,hj,hwlo,hwhi,hA,hAB,hBD,hDend,hmB,hsA,hsend,hsmass,
    hR.trans hRU,hUend.trans hRend,?_⟩
  intro v hv hvend
  have hmshort := huniform v hv hvend
  refine ⟨hmshort,?_⟩
  let k : ℝ := ((K0*M^j:ℕ):ℝ)
  have hkk : (K0:ℝ) ≤ k := by
    dsimp only [k]
    rw [Nat.cast_mul,Nat.cast_pow]
    exact le_mul_of_one_le_right hKpos.le (one_le_pow₀ hMr)
  have hlen : 2 ≤ ε*k := by
    have hh := (div_le_iff₀ hε).mp hKunit
    have ht := mul_le_mul_of_nonneg_left hkk hε.le
    nlinarith only [hh,ht]
  have hcost : 2*(Cs+1) ≤ c₁*ε*k := by
    have hh := (div_le_iff₀ (mul_pos hc₁ hε)).mp hKshell
    have ht := mul_le_mul_of_nonneg_left hkk (mul_pos hc₁ hε).le
    nlinarith only [hh,ht]
  have hshort : c₀*((v+ε*k)-v)+Cs < harmonicIntervalMass E v (v+ε*k) := by
    have hcle : c₀ ≤ c₁/2 := min_le_right _ _
    have hh := mul_le_mul_of_nonneg_right hcle (show 0 ≤ ε*k by linarith)
    change c₁*ε*k ≤ harmonicIntervalMass E v (v+ε*k) at hmshort
    nlinarith only [hmshort,hh,hcost,hCs]
  exact hshell E hprime U v (v+ε*k) c₀ (hD.trans (hR.trans hRU)) hv (by linarith) hc₀.le hshort

end Ostmann.Characters

end

end OAI
