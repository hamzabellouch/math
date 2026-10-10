import OAI.NumberTheory.TotientAsymptotic.RestoreCommonPrefix
import OAI.NumberTheory.TotientAsymptotic.CollisionHeadCount

namespace OAI

/-! Summation over all first-difference indices in the actual collision set. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

lemma G_eventually_one_le (hren : FordRenewalInput) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ G x (m x) := by
  obtain ⟨D,hD,hproj⟩ := uniform_projected_volume_bound hren
  have he := (summable_projectedEnvelope hD).tendsto_atTop_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hproj,m_tendsto.eventually he,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))] with x hx he hB
  have hg := (div_le_iff₀ (G_pos hB (m x))).mp (hx (m x) le_rfl)
  have hg0 : G x 0=1 := by simp [G]
  rw [Nat.sub_self,hg0] at hg
  exact hg.trans (mul_le_of_le_one_left (G_pos hB _).le he.le)

lemma collision_exponential_kernel {x : ℝ} {i : ℕ} (hi : i < m x)
    (hband : (99/100 : ℝ)*lam*(m x-i : ℕ)/rho^(m x-i) ≤ fordBandScale x i) :
    ((m x-i : ℕ) : ℝ)^4*Real.exp (-fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4)) ≤
      collisionKernel (lam/32) (m x-i) := by
  have hh : (0 : ℝ) < (m x-i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  have hpow := pow_pos rho_pos (m x-i)
  have hsave : lam/(32*(((m x-i : ℕ) : ℝ)^3*rho^(m x-i))) ≤
      fordBandScale x i/(16*((m x-i : ℕ) : ℝ)^4) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : lam/(32*(((m x-i : ℕ) : ℝ)^3*rho^(m x-i)))*
        (16*((m x-i : ℕ) : ℝ)^4)=lam*((m x-i : ℕ) : ℝ)/(2*rho^(m x-i)) := by
      field_simp
      ring
    rw [he]
    apply le_trans _ hband
    calc
      lam*((m x-i : ℕ) : ℝ)/(2*rho^(m x-i)) =
          (1/2 : ℝ)*(lam*((m x-i : ℕ) : ℝ)/rho^(m x-i)) := by ring
      _ ≤ (99/100 : ℝ)*(lam*((m x-i : ℕ) : ℝ)/rho^(m x-i)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg (mul_nonneg lam_pos.le hh.le) hpow.le)
      _ = _ := by ring
  unfold collisionKernel
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  convert neg_le_neg hsave using 1 <;> ring

lemma good_collision_card_le_first_sum {x t : ℝ} {H : ℕ} (hPH : P H ≤ H) :
    (goodCollisionPairs x H t).card ≤
      ∑ i ∈ Finset.Icc 0 (R x H), (firstCollisionPairs x H t i).card := by
  have hsub : goodCollisionPairs x H t ⊆
      (Finset.Icc 0 (R x H)).biUnion (firstCollisionPairs x H t) := by
    intro q hq
    obtain ⟨hpairs,hne,hv⟩ := Finset.mem_filter.mp hq
    obtain ⟨hl,hr⟩ := Finset.mem_product.mp hpairs
    have hl' := (mem_goodTupleFinset hPH).mp hl
    have hr' := (mem_goodTupleFinset hPH).mp hr
    obtain ⟨i,hi,hfirst,hcommon⟩ := chosen_collision_first hPH hl'.1 hr'.1 hv hne
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_Icc.mpr ⟨Nat.zero_le _,hi⟩,
      Finset.mem_filter.mpr ⟨hq,hfirst,hcommon⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma firstCollisionPairs_zero (x : ℝ) (H : ℕ) (t : ℝ) :
    firstCollisionPairs x H t 0=headCollisionPairs x H t := by
  ext q
  simp only [firstCollisionPairs,headCollisionPairs,Finset.mem_filter,FirstDifferenceAt,
    wholeWitnessPrime,ite_true,not_lt_zero,IsEmpty.forall_iff,forall_const,and_true]

lemma first_index_kernel_sum {m H : ℕ} (hHm : H ≤ m) {c : ℝ} (hc : 0 < c) :
    (∑ i ∈ Finset.Icc 0 (m-H), collisionKernel c (m-i)) ≤ collisionTail c H := by
  let T := (Finset.Icc 0 (m-H)).image (fun i => m-i-H)
  have hinj : Set.InjOn (fun i => m-i-H) (↑(Finset.Icc 0 (m-H)) : Set ℕ) := by
    intro i hi j hj he
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    change m-i-H=m-j-H at he
    omega
  have he : (∑ i ∈ Finset.Icc 0 (m-H), collisionKernel c (m-i)) =
      ∑ n ∈ T, collisionKernel c (H+n) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    congr 1
    omega
  rw [he]
  apply ((summable_collisionKernel hc).comp_injective (fun n k he => by omega)).sum_le_tsum
  intro n _
  exact collisionKernel_nonneg c (H+n)

lemma head_exponential_le_block {b h : ℝ} (hb : 0 ≤ b) (hh : 1 ≤ h) :
    Real.exp (-b/(8*h^4)) ≤ h^4*Real.exp (-b/(16*h^4)) := by
  have hpow : 1 ≤ h^4 := one_le_pow₀ hh
  have hdiv : b/(16*h^4) ≤ b/(8*h^4) :=
    div_le_div_of_nonneg_left hb (by positivity) (by nlinarith [sq_nonneg (h^2)])
  have he : Real.exp (-b/(8*h^4)) ≤ Real.exp (-b/(16*h^4)) := by
    simpa only [neg_div] using Real.exp_le_exp.mpr (neg_le_neg hdiv)
  exact he.trans (le_mul_of_one_le_left (Real.exp_pos _).le hpow)

/-- The full ordered collision count, including every common prefix and
both residual tuple factorizations, has a phase-independent vanishing error. -/
theorem good_collision_count (hford : FordLemma51Input) (hmertens : MertensProductInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t ≤ x,
      ((goodCollisionPairs x H t).card : ℝ) ≤ ε H*(x/Real.log x*G x (m x)) := by
  let C : ℝ := 160/Real.log 2
  let ε := fun H => C*collisionTail (lam/32) H
  have hC : 1 ≤ C := by
    dsimp [C]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mpr
    linarith [Real.log_two_lt_d9]
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa only [ε,mul_zero] using (collisionTail_tendsto (lam/32)).const_mul C
  refine ⟨ε,hε,?_⟩
  filter_upwards [actual_positive_collision_count hford hmertens hbox hren,
    head_collision_count hford hmertens,eventually_tail_cut_separated,eventually_ge_atTop 1]
    with H hpos hhead hsep hH
  filter_upwards [hpos,hhead,G_eventually_one_le hren,ford_band_lower,
    m_tendsto.eventually (eventually_ge_atTop H),eventually_gt_atTop (1 : ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hp hh hG hf hm hx hB
  intro t ht
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hA : 0 ≤ C*(x/Real.log x)*G x (m x) := by positivity
  have hindex : ∀ i ∈ Finset.Icc 0 (R x H),
      ((firstCollisionPairs x H t i).card : ℝ) ≤
        C*(x/Real.log x)*G x (m x)*collisionKernel (lam/32) (m x-i) := by
    intro i hi
    have hiR := (Finset.mem_Icc.mp hi).2
    have him : i < m x := by unfold R at hiR; omega
    have hk := collision_exponential_kernel him (hf i him)
    by_cases hi0 : i=0
    · subst i
      rw [firstCollisionPairs_zero]
      have hm1 : (1 : ℝ) ≤ m x := by exact_mod_cast hH.trans hm
      have he := head_exponential_le_block hB.le hm1
      have hzero : fordBandScale x 0=B x := by simp [fordBandScale]
      rw [hzero,Nat.sub_zero] at hk
      have hcoef : x/Real.log x ≤ C*(x/Real.log x)*G x (m x) := by
        have hxdiv : 0 ≤ x/Real.log x := by positivity
        have hm := mul_le_mul_of_nonneg_right hC hxdiv
        have hg := mul_le_mul_of_nonneg_left hG (mul_nonneg (by linarith : 0 ≤ C) hxdiv)
        nlinarith
      calc
        _ ≤ x/Real.log x*Real.exp (-B x/(8*(m x : ℝ)^4)) := hh t ht
        _ ≤ (x/Real.log x)*((m x : ℝ)^4*Real.exp (-B x/(16*(m x : ℝ)^4))) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ ≤ (C*(x/Real.log x)*G x (m x))*
            ((m x : ℝ)^4*Real.exp (-B x/(16*(m x : ℝ)^4))) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ ≤ (C*(x/Real.log x)*G x (m x))*collisionKernel (lam/32) (m x) :=
          mul_le_mul_of_nonneg_left hk hA
        _ = _ := by simp only [Nat.sub_zero]
    · have hip : 1 ≤ i := by omega
      apply (hp i hip hiR t ht).trans
      simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left hk hA
  calc
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H), ((firstCollisionPairs x H t i).card : ℝ) := by
      exact_mod_cast good_collision_card_le_first_sum (x := x) (t := t) (by omega : P H ≤ H)
    _ ≤ ∑ i ∈ Finset.Icc 0 (R x H),
        C*(x/Real.log x)*G x (m x)*collisionKernel (lam/32) (m x-i) :=
      Finset.sum_le_sum hindex
    _ = (C*(x/Real.log x)*G x (m x))*
        ∑ i ∈ Finset.Icc 0 (R x H), collisionKernel (lam/32) (m x-i) := by rw [Finset.mul_sum]
    _ ≤ (C*(x/Real.log x)*G x (m x))*collisionTail (lam/32) H :=
      mul_le_mul_of_nonneg_left (first_index_kernel_sum hm (div_pos lam_pos (by norm_num))) hA
    _ = ε H*(x/Real.log x*G x (m x)) := by dsimp [ε]; ring

end TotientAsymptotic

end

end OAI
