import OAI.InformationTheory.QuantumCircuit.RetainedMean

namespace OAI

/-! Regularity of the retained trajectories. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

lemma Count.high_flip_action_le {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) {r q : ℝ} (hgap : q + F.card ≤ r) (ψ : State N) :
    ‖act (M.high r) ψ‖ ≤ ‖act ((M.flip F).high q) ψ‖ := by
  have hh := congrArg star (M.high_flip_absorb F hF hgap)
  simp only [star_mul, (M.high_projection r).isSelfAdjoint.star_eq,
    ((M.flip F).high_projection q).isSelfAdjoint.star_eq] at hh
  calc
    _ = ‖act (M.high r) (act ((M.flip F).high q) ψ)‖ := by rw [← act_mul, hh]
    _ ≤ _ := act_norm_le_of_contraction _ (IsStarProjection.norm_le _ (M.high_projection r)) _

lemma eventually_heavy_probability {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, Real.exp (-((N : ℝ)^b)) ≤
      1 / (2 * (N + 1 : ℝ)^(⌈(N : ℝ)^a⌉₊ + 1)) := by
  filter_upwards [eventually_pattern_cost ha hab hb] with N hN
  have hh : Real.exp (-1 : ℝ) ≤ 1/2 := by
    rw [Real.exp_neg]
    have he := Real.add_one_le_exp (1 : ℝ)
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) he2
  simp only [Real.rpow_zero] at hN
  apply (le_div_iff₀ (by positivity : 0 < 2 * (N + 1 : ℝ)^(⌈(N : ℝ)^a⌉₊ + 1))).mpr
  nlinarith [hN.trans hh]

lemma list_real_sum_le {ι : Type*} (l : List ι) (f : ι → ℝ) (C : ℝ)
    (h : ∀ i ∈ l, f i ≤ C) : (l.map f).sum ≤ (l.length : ℝ) * C := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact (add_le_add (h i (List.mem_cons_self ..))
      (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))).trans_eq (add_comm _ _)

theorem retained_layer_regular
    (hspec : PublishedProductSpectralResolution) (d : ℕ)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (P : ∀ ν, ProductInput (m ν))
    {b h p : ℝ} (hb : 0 ≤ b) (hbh : b < h) (_hh : h < 1) (hp : 0 < p) (hph : p < h) :
    ∀ᶠ ν in atTop, ∀ U : Operator (m ν), IsCircuit d U →
      ∀ R : ReflectionLayer (m ν),
      (∀ A ∈ R.gates, (m ν : ℝ)^(-6 : ℝ) ≤ ‖act A.zero (act U (P ν).state)‖^2) →
      ∀ S : List (Count (m ν)), S.Sublist R.gates → (S.length : ℝ) ≤ (m ν : ℝ)^b →
      ‖act ((jointTest S).high ((m ν : ℝ)^h)) (act U (P ν).state)‖ ≤
        Real.exp (-((m ν : ℝ)^p)) := by
  let ε := (h - b) / 4
  let a := b + ε
  let c := b + 2 * ε
  let β := b + 3 * ε
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hac : a < c := by dsimp [a, c]; linarith
  have hcβ : c < β := by dsimp [c, β]; linarith
  have hβh : β < h := by dsimp [β, ε]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  obtain ⟨p', hmp, hph'⟩ := exists_between (max_lt hph hβh)
  obtain ⟨h', hp'h', hh'h⟩ := exists_between hph'
  have hpp' : p < p' := (le_max_left _ _).trans_lt hmp
  have hβp' : β < p' := (le_max_right _ _).trans_lt hmp
  have hcp' : c < p' := hcβ.trans hβp'
  filter_upwards [retained_test_mean hspec d m hm P hε,
    uniform_product_overlap_tail d m hm P (hp.trans hpp') hp'h',
    hm.eventually (eventually_power_le hac 2),
    hm.eventually (eventually_heavy_probability hc hcβ hβ),
    hm.eventually (eventually_two_powers_le hh'h (hcp'.trans (hp'h'.trans hh'h))),
    hm.eventually (eventually_exp_power_gap hpp' hβp' (hp.trans hpp') 1 1 1 1
      (by norm_num) (by norm_num)),
    hm.eventually (eventually_ge_atTop 1)]
    with ν hmean hov hmark hmass hshift hdec hN
  intro U hU R hret S hS hsize
  let ψ := act U (P ν).state
  let M := jointTest S
  have hψ : ‖ψ‖ = 1 := (act_unitary_norm hU.mem_unitary _).trans (P ν).norm_state
  have hM : meanCount M ψ ≤ (m ν : ℝ)^a := by
    rw [meanCount_joint hspec S (R.disjoint.sublist hS)]
    calc
      _ ≤ (S.length : ℝ) * (m ν : ℝ)^ε :=
        list_real_sum_le S (fun A => meanCount A ψ) _
          (fun A hA => hmean U hU A (hret A (hS.subset hA)))
      _ ≤ (m ν : ℝ)^b * (m ν : ℝ)^ε :=
        mul_le_mul_of_nonneg_right hsize (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := (Real.rpow_add (by exact_mod_cast (show 0 < m ν by omega)) _ _).symm
  have hmark' : meanCount M ψ ≤ (m ν : ℝ)^c / 2 := by linarith
  obtain ⟨F, hFM, hFc, hFmass⟩ := heavy_low_outcome hspec hN M ψ hψ
    (r := (m ν : ℝ)^c) (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < m ν by omega)) _) hmark'
  have hF : Real.exp (-((m ν : ℝ)^β)) ≤ outcomeMass M ψ F := hmass.trans hFmass
  have htail := hov U hU (M.flip F)
  have ht : ‖act (M.high ((m ν : ℝ)^h)) ψ‖ ≤
      ‖act ((M.flip F).high ((m ν : ℝ)^h')) ψ‖ :=
    M.high_flip_action_le F hFM (by linarith) ψ
  have hprod : Real.exp (-((m ν : ℝ)^β)) * ‖act (M.high ((m ν : ℝ)^h)) ψ‖ ≤
      Real.exp (-((m ν : ℝ)^p')) := by
    have hprob : outcomeMass M ψ F = ‖act (M.flip F).zero ψ‖^2 := by
      rw [M.flip_zero]; rfl
    rw [hprob] at hF
    exact (mul_le_mul hF ht (norm_nonneg _) (sq_nonneg _)).trans htail
  have hdiv : ‖act (M.high ((m ν : ℝ)^h)) ψ‖ ≤
      Real.exp (-((m ν : ℝ)^p')) / Real.exp (-((m ν : ℝ)^β)) :=
    (le_div_iff₀ (Real.exp_pos (-((m ν : ℝ)^β)))).mpr
      (by simpa only [mul_comm] using hprod)
  have hexp : Real.exp (-((m ν : ℝ)^p')) / Real.exp (-((m ν : ℝ)^β)) =
      Real.exp ((m ν : ℝ)^β - (m ν : ℝ)^p') := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [hexp] at hdiv
  exact hdiv.trans (by simpa only [one_mul] using hdec)

end QAC

end

end OAI
