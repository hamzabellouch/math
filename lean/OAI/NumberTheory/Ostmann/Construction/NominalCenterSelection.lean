import OAI.NumberTheory.Ostmann.Construction.NominalCenterSelectionBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped Topology BigOperators

theorem exists_nominalCenterArray (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ G₀ c tb td : ℝ, 0≤G₀ →
      (G₀-2≤c ∧ c≤G₀+favorableBlockWidth L+2) →
      |tb|≤favorableBlockWidth L/16 → |td|≤favorableBlockWidth L/16 →
      Nonempty (NominalCenterArray d k L (nominalJ Bs BD Bz k L G₀ c td) tb
        (fun j => nominalCompensation Bs BD Bz k L G₀ c td j)) := by
  classical
  have hpair := exists_balanced_pair_centers d (1/16) (2*(2:ℝ)^k) (1/1000)
    (by norm_num) (by norm_num)
  have htriple := exists_balanced_triple_centers d (1/16) (2*(2:ℝ)^k) (1/1000)
    (by norm_num) (by norm_num)
  have hh := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop 16
  filter_upwards [nominalTotals_eventually Bs BD Bz hk,hpair,htriple,hh]
    with L hnom hp ht hh
  change 16≤favorableBlockWidth L at hh
  intro G₀ c tb td hG hc htb htd
  obtain ⟨hJ,hTop,hComp⟩ := hnom G₀ c tb td hG hc htb htd
  have hP : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  let J := nominalJ Bs BD Bz k L G₀ c td
  let w : Fin k → ℝ := fun j => nominalCompensation Bs BD Bz k L G₀ c td j
  have hT := floor_half_total_bounds (h := favorableBlockWidth L) hh hTop.1 hTop.2
  have hhn : 0≤favorableBlockWidth L := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hP) hhn
  obtain ⟨u,v,z,hSum,hu,hv,hz,hbu,hbv,hbz⟩ := ht ⌊(J-2*tb)/2⌋
    (by simpa only [one_div,mul_comm (16:ℝ)⁻¹,←div_eq_mul_inv,J] using hT.1)
    (by dsimp [J]; nlinarith only [hT.2,hprod])
  have hPairs (j : Fin k) : ∃a b : ℤ, a+b=⌊w j/2⌋ ∧
      |(a:ℝ)-(⌊w j/2⌋:ℝ)/2|≤(1/1000:ℝ)*favorableBlockWidth L ∧
      |(b:ℝ)-(⌊w j/2⌋:ℝ)/2|≤(1/1000:ℝ)*favorableBlockWidth L ∧
      BalancedCellAfterTwo d a ∧ BalancedCellAfterTwo d b := by
    have hj := floor_half_total_bounds (h := favorableBlockWidth L) hh (hComp j j.isLt).1 (hComp j j.isLt).2
    apply hp ⌊w j/2⌋
    · simpa only [one_div,mul_comm (16:ℝ)⁻¹,←div_eq_mul_inv,w] using hj.1
    · dsimp [w]
      nlinarith [hj.2]
  choose a b hs ha hb hba hbb using hPairs
  have hrad : (1/1000:ℝ)*favorableBlockWidth L=favorableBlockWidth L/1000 := by ring
  rw [hrad] at hu hv hz
  simp_rw [hrad] at ha hb
  refine ⟨{
    top := ![u,v,z]
    comp := fun j => ![a j,b j]
    top_sum := ?_
    comp_sum := ?_
    top_near := ?_
    comp_near := ?_
    top_balanced := ?_
    comp_balanced := ?_}⟩
  · simpa [Fin.sum_univ_succ,add_assoc] using hSum
  · intro j
    simpa [Fin.sum_univ_succ] using hs j
  · intro i
    fin_cases i
    · exact hu
    · exact hv
    · exact hz
  · intro j i
    fin_cases i
    · exact ha j
    · exact hb j
  · intro i
    fin_cases i
    · exact hbu
    · exact hbv
    · exact hbz
  · intro j i
    fin_cases i
    · exact hba j
    · exact hbb j

end Ostmann.Construction

end

end OAI
