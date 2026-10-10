import OAI.MeasureTheory.Falconer.Shells.HighShellLeibnizSymbols

namespace OAI

namespace PlanarFalconer

theorem pair_assignment_endpoint_budget (S : Finset PolicyDescriptor) (k : PairMaskIndex → ℕ)
    (K : ℕ) (hk : ∑ a ∈ pairMaskIndices S, k a ≤ K) (l : Fin 2) :
    ∑ b ∈ S, k (b,l) ≤ K := by
  apply le_trans _ hk
  change (∑ b ∈ S, k (b,l)) ≤ ∑ a ∈ S.product (Finset.univ : Finset (Fin 2)), k a
  rw [Finset.product_eq_sprod,Finset.sum_product S (Finset.univ : Finset (Fin 2)) k]
  apply Finset.sum_le_sum
  intro b hb
  exact Finset.single_le_sum (f := fun y : Fin 2 => k (b,y)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem minimal_assignment_scale (A : ℕ → ℝ) {N q a t j : ℕ} {sig v : ℝ}
    (hsig : 0 ≤ sig) (hq : 0 < q) (hqscale : sig*N ≤ (q:ℝ))
    (hw : a+100*q < t) (hv : (t:ℝ)-sig*N ≤ v)
    {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))) :
    assignmentScale (policyDescriptorList A N q a t) N sig b.2 ≤
      (2:ℝ)^((j:ℝ)*(v-a)) := by
  apply high_shell_extracted_scale _ Prod.fst b.2 hsig N a t j
  · intro c hc
    exact policyDescriptor_real_length A hq (Finset.mem_product.mp hc).1
  · have hg := high_shell_gap hqscale hw hv
    have hn : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig (Nat.cast_nonneg _)
    linarith
  · exact hv
  · exact inverseLeibnizTerms_budget j _ hb

theorem minimal_assignment_scale_absorbed (A : ℕ → ℝ) {N q a t j : ℕ} {sig v : ℝ}
    (hsig : 0 ≤ sig) (hq : 0 < q) (hqscale : sig*N ≤ (q:ℝ))
    (hw : a+100*q < t) (hv : (t:ℝ)-sig*N ≤ v)
    {b : ℂ × (PairMaskIndex → ℕ)}
    (hb : b ∈ inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))) :
    0 ≤ (2:ℝ)^(-(j:ℝ)*(v-a))*assignmentScale (policyDescriptorList A N q a t) N sig b.2 ∧
    (2:ℝ)^(-(j:ℝ)*(v-a))*assignmentScale (policyDescriptorList A N q a t) N sig b.2 ≤ 1 := by
  have hpos : 0 ≤ assignmentScale (policyDescriptorList A N q a t) N sig b.2 :=
    Finset.prod_nonneg (fun c _ => pow_nonneg (inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le) _)
  refine ⟨mul_nonneg (by positivity) hpos,?_⟩
  apply (mul_le_mul_of_nonneg_left (minimal_assignment_scale A hsig hq hqscale hw hv hb)
    (by positivity : 0 ≤ (2:ℝ)^(-(j:ℝ)*(v-a)))).trans_eq
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  convert Real.rpow_zero 2 using 2
  ring

theorem minimal_inverseLeibniz_cost (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) (j : ℕ) :
    ((inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))).map
      (fun b => ‖b.1‖)).sum ≤
    (inverseStationaryExpr j).cost * (2*((N:ℝ)+1)^3)^(2*j) := by
  apply (inverseLeibnizTerms_cost j _).trans
  apply mul_le_mul_of_nonneg_left _ (inverseStationaryExpr j).cost_nonneg
  apply pow_le_pow_left₀ (by positivity)
  apply max_le
  · have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    nlinarith [one_le_pow₀ (by linarith : (1:ℝ) ≤ (N:ℝ)+1) (n := 3)]
  · have hc : ((policyDescriptorList A N q a t).card:ℝ) ≤ ((N:ℝ)+1)^3 := by
      exact_mod_cast policyDescriptorList_card A hq
    change ((Finset.product (policyDescriptorList A N q a t) (Finset.univ : Finset (Fin 2))).card:ℝ) ≤ _
    rw [Finset.product_eq_sprod,Finset.card_product (policyDescriptorList A N q a t) (Finset.univ : Finset (Fin 2))]
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    linarith

end PlanarFalconer

end OAI
