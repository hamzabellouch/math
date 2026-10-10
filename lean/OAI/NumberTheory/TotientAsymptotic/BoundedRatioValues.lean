import OAI.NumberTheory.TotientAsymptotic.PublishedFiber
import OAI.NumberTheory.TotientAsymptotic.TupleTotients

namespace OAI

noncomputable section
open scoped Topology Classical
open Filter
namespace TotientAsymptotic

def boundedRatioValues (x a b : ℝ) : Finset ℕ :=
  (totientValues x).filter (fun v => a ≤ (ell v : ℝ)/v ∧ (ell v : ℝ)/v ≤ b)

/-- The bounded-multiplier version of the published full-fiber construction
retains the seed's strict margin above k. -/
theorem bounded_ratio_positive_proportion {d k : ℕ} (hd : IsTotient d)
    (hseed : k*d < ell d) (hppt : PPTBoundedFiberPropagation d) :
    ∃ a b η : ℝ, (k : ℝ)<a ∧ 0<η ∧ 0<b ∧ ∀ᶠ x : ℝ in atTop,
      η*V x ≤ ((boundedRatioValues x a b).card : ℝ) := by
  obtain ⟨η,K,hη,hK,hprop⟩ := hppt
  let a : ℝ := (ell d : ℝ)/d
  have hd0 : (0 : ℝ)<d := by exact_mod_cast isTotient_pos hd
  have hka : (k : ℝ)<a := (lt_div_iff₀ hd0).mpr (by exact_mod_cast hseed)
  have ha : 0<a := (Nat.cast_nonneg k).trans_lt hka
  refine ⟨a,K*a,η,hka,hη,mul_pos hK ha,?_⟩
  filter_upwards [hprop] with x hx
  obtain ⟨hx,S,hcard,hS⟩ := hx
  apply hcard.trans
  have hinj : Set.InjOn (fun b : ℕ => d*b.totient) (↑S) := by
    intro b hb c hc heq
    exact mul_totient_injective_of_full_fibers hd (hS b hb).1 (hS c hc).1
      (hS b hb).2.2.1 (hS c hc).2.2.1 heq
  have hsub : S.image (fun b => d*b.totient) ⊆ boundedRatioValues x a (K*a) := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hb,hbx,hfull,hKbound⟩ := hS b hb
    have hvt := isTotient_of_fullFiber hd hfull
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨isTotient_pos hvt,Nat.le_floor hbx⟩,hvt⟩,?_,?_⟩
    · exact ratio_le_of_full_fiber hd hb rfl hfull
    · rw [fullFiber_ratio_eq hd hb hfull]
      exact (mul_le_mul_of_nonneg_left hKbound ha.le).trans_eq (mul_comm _ _)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hc
  exact_mod_cast hc

end TotientAsymptotic

end

end OAI
