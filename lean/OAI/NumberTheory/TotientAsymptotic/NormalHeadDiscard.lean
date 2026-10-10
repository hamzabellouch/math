import OAI.NumberTheory.TotientAsymptotic.NormalHeadCount
import OAI.NumberTheory.TotientAsymptotic.MassUpper
import OAI.NumberTheory.TotientAsymptotic.PrefixSize
import OAI.NumberTheory.TotientAsymptotic.GoodTuples

namespace OAI

/-! Normality failures of the largest prime have vanishing relative mass. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalHeadTuples (x : ℝ) (H : ℕ) (t : ℝ) : Finset (TotientTuple (R x H)) :=
  (tupleFinset x H t).filter (fun τ => ¬IsNormalPrime (normalityScale x 0) τ.head)

def normalHeadError (x : ℝ) : ℝ :=
  (1+B x)^5*Real.exp (-((B x)^(1/3 : ℝ))/6)

lemma normalHeadError_tendsto : Tendsto normalHeadError atTop (nhds 0) := by
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/3)).comp B_tendsto
  have hd := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 15 (1/6) (by norm_num)).comp ht).const_mul 32
  apply squeeze_zero' (g := fun x : ℝ => 32*((B x)^(1/3 : ℝ))^15*
    Real.exp (-(1/6 : ℝ)*(B x)^(1/3 : ℝ)))
  · filter_upwards [B_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
    exact mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  · filter_upwards [B_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
    have he : ((B x)^(1/3 : ℝ))^3=B x := by
      rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ B x)]
      norm_num
    have hp : (1+B x)^5 ≤ (2*B x)^5 := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hpow : (2*B x)^5=32*((B x)^(1/3 : ℝ))^15 := by
      calc
        _ = 32*(B x)^5 := by ring
        _ = 32*(((B x)^(1/3 : ℝ))^3)^5 := by rw [he]
        _ = _ := by ring
    unfold normalHeadError
    rw [show -((B x)^(1/3 : ℝ))/6= -(1/6 : ℝ)*(B x)^(1/3 : ℝ) by ring]
    exact mul_le_mul_of_nonneg_right (hp.trans_eq hpow) (Real.exp_pos _).le
  · have h15 (u : ℝ) : u^(15 : ℝ)=u^(15 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast u 15
    simp only [Function.comp_def,h15] at hd
    simpa only [mul_assoc,mul_zero] using hd

lemma nonNormalHeadTuples_fibers {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (nonNormalHeadTuples x H t).card = ∑ ζ ∈ prefixDataFinset x H,
      ((nonNormalHeadTuples x H t).filter (fun τ => τ.tail=ζ)).card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter (nonNormalHeadTuples x H t)
    (prefixDataFinset x H) TotientTuple.tail]
  congr 1
  symm
  apply Finset.filter_eq_self.mpr
  intro τ hτ
  exact mem_prefixDataFinset.mpr ((mem_tupleFinset hPH).mp (Finset.mem_filter.mp hτ).1).2.2.1

lemma non_normal_head_tuple_count (hford : FordLemma26Input) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ H : ℕ, P H ≤ H →
      ∀ t : ℝ, t ≤ x →
      ((nonNormalHeadTuples x H t).card : ℝ) ≤
        C*normalHeadError x*(x/Real.log x)*M x H (fun _ => 1) := by
  obtain ⟨C,hC,hcount⟩ := non_normal_head_count hford
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,B_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hB
  intro H hPH t ht
  have hS : 2 < normalityScale x 0 := by
    have hroot := Real.one_le_rpow hB (by norm_num : (0 : ℝ)≤1/3)
    have he : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ)≠0)]
    have hzero : fordBandScale x 0=B x := by simp [fordBandScale]
    rw [normalityScale,hzero]
    exact he.trans_le (Real.exp_le_exp.mpr (Real.one_le_exp (by linarith)))
  have hEs : (Real.log (normalityScale x 0))^(-1/6 : ℝ)=Real.exp (-((B x)^(1/3 : ℝ))/6) := by
    have hzero : fordBandScale x 0=B x := by simp [fordBandScale]
    rw [normalityScale,hzero,Real.log_exp,← Real.exp_mul]
    congr 1
    ring

  rw [nonNormalHeadTuples_fibers hPH,Nat.cast_sum,mass_eq_sum_prefixData]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ζ hζ
  let T := (nonNormalHeadTuples x H t).filter (fun τ => τ.tail=ζ)
  let Q := T.image TotientTuple.head
  have hz := mem_prefixDataFinset.mp hζ
  have hD := basic_prefix_denominator_pos hPH hz
  have hinj : Set.InjOn TotientTuple.head (↑T : Set (TotientTuple (R x H))) := by
    intro τ hτ σ hσ he
    have htτ := (Finset.mem_filter.mp hτ).2
    have htσ := (Finset.mem_filter.mp hσ).2
    cases τ
    cases σ
    simp_all
  have hc : T.card=Q.card := (Finset.card_image_of_injOn hinj).symm
  change (T.card : ℝ) ≤ _
  rw [hc]
  have hb := hx (normalityScale x 0) hS (ζ.d*∏ i, (ζ.primes i-1)) hD Q (by
    intro p hp
    obtain ⟨τ,hτ,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hτ,he⟩ := Finset.mem_filter.mp hτ
    obtain ⟨hτ,hnormal⟩ := Finset.mem_filter.mp hτ
    have hb := (mem_tupleFinset hPH).mp hτ
    refine ⟨hb.1,hb.2.1,?_,hnormal⟩
    have hv := hb.2.2.2
    have htτ : τ=⟨τ.head,ζ⟩ := by cases τ; simp_all
    rw [htτ,tupleValue_eq_head] at hv
    exact hv.trans ht)
  apply hb.trans_eq
  rw [hEs]
  unfold normalHeadError
  push_cast
  field_simp


theorem normal_head_tuple_discard (hbox : FordUnitPrimeBoxInput)
    (hren : FordRenewalInput) (hmertens : MertensProductInput) (hford : FordLemma26Input) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
        ((nonNormalHeadTuples x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  obtain ⟨C,hC,hcount⟩ := non_normal_head_tuple_count hford
  obtain ⟨D,hD,hmass⟩ := mass_upper hbox hren hmertens
  refine ⟨fun H => (H : ℝ)⁻¹,?_,?_⟩
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  filter_upwards [hmass,eventually_ge_atTop 2] with H hH hH2
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have he0 : Tendsto (fun x => (C*(D*Real.exp ((4*(lam/rho))*cofactorScale H)))*normalHeadError x)
      atTop (nhds 0) := by
    simpa only [mul_zero] using normalHeadError_tendsto.const_mul
      (C*(D*Real.exp ((4*(lam/rho))*cofactorScale H)))
  have he := he0.eventually (eventually_lt_nhds (inv_pos.mpr hHpos))
  filter_upwards [hH,hcount,he,eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hm hc he hx hB
  intro t ht
  have hE : 0 ≤ normalHeadError x := by
    unfold normalHeadError
    positivity
  have hX : 0 ≤ x/Real.log x := div_nonneg (by linarith) (Real.log_pos hx).le
  have hG := (G_pos hB (m x)).le
  calc
    _ ≤ C*normalHeadError x*(x/Real.log x)*M x H (fun _ => 1) := hc H (P_lt_self hH2).le t ht
    _ ≤ C*normalHeadError x*(x/Real.log x)*
        (D*Real.exp ((4*(lam/rho))*cofactorScale H)*G x (m x)) :=
      mul_le_mul_of_nonneg_left (hm _ (fun _ => le_rfl)) (mul_nonneg (mul_nonneg hC.le hE) hX)
    _ = (C*(D*Real.exp ((4*(lam/rho))*cofactorScale H))*normalHeadError x)*
        (x/Real.log x*G x (m x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he.le (mul_nonneg hX hG)

end TotientAsymptotic

end

end OAI
