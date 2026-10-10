import OAI.NumberTheory.Ostmann.Characters.MixedFlatnessSpectatorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters
open Construction QuadraticCenter Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem eventually_primeBand_inverse_le {α β r : ℝ} (hα : 0<α) (hr : 0<r) :
    ∀ᶠ L : ℝ in atTop,∀p∈logLogPrimeBand (α*L) (β*L),p≠2 ∧ (p:ℝ)⁻¹≤r := by
  have ht := (Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop hα)).eventually_ge_atTop
    (1/r+3)
  filter_upwards [ht] with L hL
  change 1/r+3≤Real.exp (α*L) at hL
  intro p hp
  obtain ⟨hprime,hlo,hhi⟩ := (logLogPrimeBand_mem_iff _ _ _).mp hp
  have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
  have hlog : 0<Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hl := Real.exp_le_exp.mpr hlo.le
  rw [Real.exp_log hlog] at hl
  have hm : 1/r+3≤(p:ℝ) := by linarith [Real.log_le_sub_one_of_pos hp0]
  refine ⟨?_,?_⟩
  · intro he
    subst p
    norm_num at hm
    have hh : 0<r⁻¹ := inv_pos.mpr hr
    linarith
  · have hpmin : 1/r≤(p:ℝ) := by linarith
    have hh := one_div_le_one_div_of_le (by positivity : 0<1/r) hpmin
    simpa only [one_div,inv_inv] using hh

def HigherHarmonicBandInput (d : Decomposition) (α β : ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → ∀ᶠ L : ℝ in atTop,∀ P : Finset ℕ,(∀p∈P,p.Prime) →
    (∀p∈P,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L) →
    (∑p∈P,higherPrimeBias d p/p)≤ε*L

theorem eventually_mixedBad_harmonic_band_le (d : Decomposition) {α β : ℝ}
    (hα : 0<α) (hαβ : α<β) (hhigher : HigherHarmonicBandInput d α β)
    (δ η : ℝ) (hδ : 0<δ) (hη : 0<η) :
    ∀ᶠ L : ℝ in atTop,
      harmonicPrimeMass (mixedBadPrimes d
        (balancedPrimePart d (logLogPrimeBand (α*L) (β*L))) δ)≤η*L := by
  let ε := η*δ^2/192
  let r := ε/(2*(β-α))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hr : 0<r := by dsimp [r]; exact div_pos hε (by linarith)
  filter_upwards [eventually_quadratic_harmonic_band_le d hα hαβ ε hε,
    hhigher ε hε,eventually_primeBand_inverse_le (β:=β) hα hr,
    logLogPrimeBand_mass_eventually hα.le hαβ,eventually_ge_atTop (0:ℝ)]
    with L hquad hhigh hrad hmass hL
  let P := balancedPrimePart d (logLogPrimeBand (α*L) (β*L))
  have hsub : P⊆logLogPrimeBand (α*L) (β*L) := Finset.filter_subset _ _
  have hp : ∀p∈P,p.Prime := fun p hp=>logLogPrimeBand_prime (hsub hp)
  have hband : ∀p∈P,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L := by
    intro p hp
    have hh := (logLogPrimeBand_mem_iff _ _ _).mp (hsub hp)
    exact ⟨hh.2.1.le,hh.2.2⟩
  have hq := hquad P hp hband
  have ha := hhigh P hp hband
  have hB := mixedBadPrimes_mass_bound d P hp (fun p hp=>(hrad p (hsub hp)).1)
    (fun p hp=>(Finset.mem_filter.mp hp).2) hδ hr.le (fun p hp=>(hrad p (hsub hp)).2)
  have hm : harmonicPrimeMass P≤2*(β-α)*L := by
    have hh := (hmass ∅ (by simp)).2.2
    simp only [Finset.sdiff_empty] at hh
    exact (Supply.harmonicPrimeMass_mono hsub).trans hh
  have hprod := mul_le_mul_of_nonneg_left hm hr.le
  have hre : r*(2*(β-α)*L)=ε*L := by
    dsimp [r]
    field_simp [ne_of_gt (sub_pos.mpr hαβ)]
  rw [hre] at hprod
  have hs : δ^2*harmonicPrimeMass (mixedBadPrimes d P δ)≤144*ε*L := by linarith
  have hsq : 0<δ^2 := sq_pos_of_pos hδ
  change harmonicPrimeMass (mixedBadPrimes d P δ)≤η*L
  dsimp [ε] at hs
  nlinarith [mul_nonneg hη.le hL]

end Ostmann.Characters

end

end OAI
