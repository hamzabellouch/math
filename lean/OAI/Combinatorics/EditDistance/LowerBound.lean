import OAI.Combinatorics.EditDistance.DepthInversion
import OAI.Combinatorics.EditDistance.FiniteLower
import OAI.Combinatorics.EditDistance.DistortionMonotonicity

namespace OAI

/-!
# Binary witnesses for every sufficiently large length bound
-/

namespace EditLower

universe u

open EditDistortion EditParameters Filter

theorem eventually_length_witness : ∀ᶠ d : ℕ in atTop,
    ∃ n : ℕ, n ≤ d ∧ ∃ S : Set (List Bool), S.Finite ∧ S.Nonempty ∧ S.Nontrivial ∧
      (∀ w ∈ S, w.length = n) ∧
      exponentScale (1/1200) d ≤ leastDistortion (fun x y : S => (edit x.val y.val : ℝ)) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventually_depth_witness
  let J := max (max K (24^4)) 2
  have hlim : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hchoose := hlim.eventually (EditDepth.eventually_choose_depth J)
  filter_upwards [hchoose,eventually_ge_atTop 1] with d hd hd1
  let k := EditDepth.depth (Real.log (d : ℝ))
  have hk : J ≤ k := hd.1
  have hkK : K ≤ k := (le_max_left K (24^4)).trans ((le_max_left _ _).trans hk)
  have hk24 : 24^4 ≤ k := (le_max_right K (24^4)).trans ((le_max_left _ _).trans hk)
  have hk2 : 2 ≤ k := (le_max_right _ _).trans hk
  have hk0 : 0 < k := by omega
  obtain ⟨S,hfin,hne,hnt,hlen,hD⟩ := hK k hkK
  have hn : encodedLength k ≤ d := by
    have hlog : Real.log (encodedLength k : ℝ) ≤ Real.log (d : ℝ) :=
      (log_length_bound hk2).trans hd.2.1
    have hnp : (0 : ℝ) < encodedLength k := by exact_mod_cast encodedLength_pos hk0
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd1
    exact_mod_cast (Real.log_le_log_iff hnp hdp).mp hlog
  refine ⟨encodedLength k,hn,S,hfin,hne,hnt,hlen,?_⟩
  apply le_trans ?_ ((ratio_exponential hk24).trans hD)
  apply Real.exp_le_exp.mpr
  simpa only [div_eq_mul_inv,mul_comm,one_mul,k] using hd.2.2

theorem lower_main : ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ (Alpha : Type u) [Fintype Alpha], 2 ≤ Fintype.card Alpha →
      exponentScale c d ≤ E Alpha d) ∧ BinaryWitness c d := by
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp eventually_length_witness
  refine ⟨1/1200,by norm_num,d₀,?_⟩
  intro d hd
  obtain ⟨n,hn,S,hfin,hne,hnt,hlen,hD⟩ := hd₀ d hd
  constructor
  · intro Alpha inst hAlpha
    exact hD.trans (binary_subset_lower Alpha hAlpha hn S hfin hnt hlen)
  · exact ⟨n,hn,S,hfin,hne,hlen,hD⟩

end EditLower

end OAI
