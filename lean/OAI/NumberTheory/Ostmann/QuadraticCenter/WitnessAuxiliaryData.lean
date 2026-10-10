import OAI.NumberTheory.Ostmann.QuadraticCenter.CanonicalAuxiliarySum
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterKBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem witness_auxiliary_product_data {F : Finset ℕ} {Z z K : ℕ}
    (hF : ∀p∈F,p.Prime) (hcard : F.card=K) (hK : 0<K)
    (hZ : 1≤Z) (hsize : ((∏p∈F,p:ℕ):ℝ)≤(Z:ℝ)^(1/50:ℝ))
    (hlarge : ∀p∈F,z≤p) :
    Squarefree (∏p∈F,p) ∧ 2≤(∏p∈F,p) ∧
      (∏p∈F,p).primeFactors.card=K ∧ (∏p∈F,p)≤Z ∧
      (∀p∈(∏p∈F,p).primeFactors,z≤p) := by
  have hsf := canonicalAuxiliary_full_squarefree hF
  have hpf : (∏p∈F,p).primeFactors=F := Nat.primeFactors_prod hF
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p,hp⟩ := hne
  have hpdiv : p∣∏p∈F,p := Finset.dvd_prod_of_mem (fun p => p) hp
  have htwo : 2≤∏p∈F,p := (hF p hp).two_le.trans (Nat.le_of_dvd hsf.ne_zero.bot_lt hpdiv)
  have hZr : (1:ℝ)≤Z := by exact_mod_cast hZ
  have hpow : (Z:ℝ)^(1/50:ℝ)≤Z := by
    calc
      _ ≤ (Z:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZr (by norm_num)
      _ = _ := Real.rpow_one _
  refine ⟨hsf,htwo,?_,?_,?_⟩
  · rw [hpf,hcard]
  · exact_mod_cast hsize.trans hpow
  · simpa only [hpf] using hlarge

theorem eventually_auxiliaryK_pos :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent → 0<auxiliaryK Z z := by
  filter_upwards [eventually_auxiliaryK_bounds,eventually_ge_atTop (1:ℝ)] with T hK hT
  intro Z z hZl hZu hz hzl hzu
  have hp : 0<T^(3/4:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  exact_mod_cast hp.trans_le (hK Z z hZl hZu hz hzl hzu).1

end Ostmann.QuadraticCenter

end

end OAI
