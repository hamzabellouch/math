import OAI.NumberTheory.TotientAsymptotic.BootstrapRegularity
import OAI.NumberTheory.TotientAsymptotic.BootstrapViolation

namespace OAI

/-! The surviving values satisfy the bootstrap inequality for every preimage. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def BootstrapGood (x : ℝ) (v : ℕ) : Prop :=
  CountingRegular (loglogCutoff (bootstrapBottom (B x))) x v ∧
    ∀ n : ℕ,0 < n → n.totient=v →
      a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x

theorem bootstrap_good_value_discard : ∃ ε : ℕ → ℝ,Tendsto ε atTop (nhds 0) ∧
    ∀ᶠ J : ℕ in atTop,∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ v ≤ 2^J ∧ ¬BootstrapGood ((2:ℝ)^J) v) →
    (Q.card:ℝ) ≤ ε J*(dyadicTotientEnvelope J*(2:ℝ)^J/Real.log ((2:ℝ)^J)) := by
  classical
  obtain ⟨δ,hδ,hreg⟩ := bootstrap_regularity_exception
  obtain ⟨C,hC,hviol⟩ := bootstrap_regular_violation
  let ε := fun J : ℕ => δ J+C*Real.exp (-B ((2:ℝ)^J)/200)
  have he : Tendsto (fun b : ℝ => Real.exp (-b/200)) atTop (nhds 0) := by
    have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (1/200) (by norm_num)
    convert hh using 1
    funext b
    simp only [Real.rpow_zero,one_mul]
    congr 1
    ring
  have hε : Tendsto ε atTop (nhds 0) := by
    have hh := hδ.add ((he.comp dyadic_B_tendsto).const_mul C)
    simpa only [Function.comp_apply,mul_zero,add_zero] using hh
  refine ⟨ε,hε,?_⟩
  have hxlim : Tendsto (fun J : ℕ => (2:ℕ)^J) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hreg,hxlim.eventually hviol,eventually_ge_atTop (1:ℕ)] with J hreg hviol hJ
  let x := (2:ℝ)^J
  let S := loglogCutoff (bootstrapBottom (B x))
  have hx1 : 1 < x := by
    have hh : (2:ℕ) ≤ 2^J := by
      have ht : (2:ℕ)^1 ≤ 2^J := Nat.pow_le_pow_right (by norm_num) hJ
      simpa using ht
    change (1:ℝ) < (2:ℝ)^J
    exact_mod_cast (show 1 < (2:ℕ)^J by omega)
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hE : 1 ≤ dyadicTotientEnvelope J := dyadicTotientEnvelope_one_le J
  have hscale : 0 ≤ x/Real.log x := by positivity
  have hscaleE : x/Real.log x ≤ dyadicTotientEnvelope J*x/Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hE hscale
    simpa only [one_mul,mul_div_assoc] using hh
  intro Q hQ
  let A := Q.filter (fun v => ¬CountingRegular S x v)
  let T := Q\A
  have hA := hreg A (by
    intro v hv
    obtain ⟨hv,hbad⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.1,hbad⟩)
  have hT := hviol T (by
    intro v hv
    obtain ⟨hv,hvA⟩ := Finset.mem_sdiff.mp hv
    have hr : CountingRegular S x v := by
      by_contra hh
      exact hvA (Finset.mem_filter.mpr ⟨hv,hh⟩)
    have hf : ¬∀ n : ℕ,0 < n → n.totient=v →
        a 1*fordPrimeCoordinate n 1+a 2*fordPrimeCoordinate n 2 ≤ (101/100:ℝ)*B x := by
      intro hh
      exact (hQ v hv).2.2 ⟨hr,hh⟩
    push Not at hf
    obtain ⟨n,hn,hφ,hbad⟩ := hf
    refine ⟨(hQ v hv).2.1,?_,n,hn,hφ,?_⟩
    · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hr
    · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hbad)
  have hT' : (T.card:ℝ) ≤ C*Real.exp (-B x/200)*(dyadicTotientEnvelope J*x/Real.log x) := by
    have ht : (T.card:ℝ) ≤ C*x*(Real.log x)^(-201/200:ℝ) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hT
    have hid : C*x*(Real.log x)^(-201/200:ℝ)=C*Real.exp (-B x/200)*(x/Real.log x) := by
      have hinv : (Real.log x)⁻¹=Real.exp (-B x) := by rw [Real.exp_neg,B,Real.exp_log hlog]
      have hp : (Real.log x)^(-201/200:ℝ)=Real.exp (-B x/200)*Real.exp (-B x) := by
        rw [Real.rpow_def_of_pos hlog,← Real.exp_add]
        congr 1
        unfold B
        ring
      rw [hp]
      simp only [div_eq_mul_inv,hinv]
      ring
    exact ht.trans (hid ▸ mul_le_mul_of_nonneg_left hscaleE (by positivity))
  have hcard : (Q.card:ℝ)=(A.card:ℝ)+(T.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show A ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=A.card+T.card by dsimp [T]; omega)
  rw [hcard]
  calc
    _ ≤ δ J*(dyadicTotientEnvelope J*x/Real.log x)+
        C*Real.exp (-B x/200)*(dyadicTotientEnvelope J*x/Real.log x) := add_le_add hA hT'
    _ = _ := by dsimp [ε,x]; ring

end TotientAsymptotic

end

end OAI
