import OAI.Probability.SwitchChain.PairEqualityOrientation

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem equalitySpace_eq_bot_of_inactive (i j k l : Fin n)
    (h : ∀ G : GraphState n d, ¬ active i j k l G) :
    equalitySpace (d := d) i j k l = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    ext G
    change f G = 0
    obtain ⟨c, hc⟩ := hf G
    have he := hc G (SameFiber.refl _ _)
    simpa only [ite_eq_right (h G), mul_zero] using he
  · exact bot_le

theorem projection_eq_zero_of_not_disjoint (i j k l : Fin n)
    (h : ¬ Disjoint ({i,j} : Finset (Fin n)) {k,l}) :
    projection (d := d) i j k l = 0 := by
  have hinactive : ∀ G : GraphState n d, ¬ active i j k l G := by
    intro G ha
    obtain ⟨v,hv,hv'⟩ := Finset.not_disjoint_iff.mp h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    have hk := ((mem_singletonSet G.val i j k).mp ha.1).1
    have hl := ((mem_singletonSet G.val i j l).mp ha.2).1
    rcases hv with rfl | rfl <;> rcases hv' with hv' | hv'
    · exact hk.1 hv'.symm
    · exact hl.1 hv'.symm
    · exact hk.2 hv'.symm
    · exact hl.2 hv'.symm
  have he := congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_eq_bot_of_inactive i j k l hinactive)
  exact he.trans Submodule.starProjection_bot

private theorem exists_pair_endpoints (a : Finset (Fin n)) (ha : a.card = 2) :
    ∃ p : Fin n × Fin n, p.1 ≠ p.2 ∧ a = {p.1,p.2} := by
  obtain ⟨i,j,hij,hpair⟩ := Finset.card_eq_two.mp ha
  exact ⟨(i,j),hij,hpair⟩

private def endpoints (a : Finset (Fin n)) (ha : a.card = 2) : Fin n × Fin n :=
  Classical.choose (exists_pair_endpoints a ha)

private theorem endpoints_spec (a : Finset (Fin n)) (ha : a.card = 2) :
    (endpoints a ha).1 ≠ (endpoints a ha).2 ∧
      a = {(endpoints a ha).1,(endpoints a ha).2} :=
  Classical.choose_spec (exists_pair_endpoints a ha)

def pairProjection (a b : Finset (Fin n)) : StateSpace n d →L[ℝ] StateSpace n d :=
  if ha : a.card = 2 then
    if hb : b.card = 2 then
      projection (endpoints a ha).1 (endpoints a ha).2
        (endpoints b hb).1 (endpoints b hb).2
    else 0
  else 0

theorem pairProjection_eq (a b : Finset (Fin n))
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (ha : a = {i,j}) (hb : b = {k,l}) :
    pairProjection (d := d) a b = projection i j k l := by
  have hca : a.card = 2 := by rw [ha]; simp [hij]
  have hcb : b.card = 2 := by rw [hb]; simp [hkl]
  rw [pairProjection, dite_eq_left hca, dite_eq_left hcb]
  have hpa := endpoints_spec a hca
  have hpb := endpoints_spec b hcb
  calc
    _ = projection i j (endpoints b hcb).1 (endpoints b hcb).2 :=
      projection_eq_of_left_pair_eq _ _ _ _ _ _ hpa.1 (hpa.2.symm.trans ha)
    _ = _ := projection_eq_of_right_pair_eq _ _ _ _ _ _ (hpb.2.symm.trans hb)

@[simp] theorem pairProjection_pair (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    pairProjection (d := d) {i,j} {k,l} = projection i j k l :=
  pairProjection_eq _ _ i j k l hij hkl rfl rfl

@[simp] theorem pairProjection_eq_zero_left (a b : Finset (Fin n))
    (ha : a.card ≠ 2) : pairProjection (d := d) a b = 0 := by
  simp only [pairProjection, dite_eq_right ha]

@[simp] theorem pairProjection_eq_zero_right (a b : Finset (Fin n))
    (hb : b.card ≠ 2) : pairProjection (d := d) a b = 0 := by
  unfold pairProjection
  split_ifs <;> rfl

theorem pairProjection_eq_zero_of_not_disjoint (a b : Finset (Fin n))
    (hab : ¬ Disjoint a b) : pairProjection (d := d) a b = 0 := by
  by_cases ha : a.card = 2
  · by_cases hb : b.card = 2
    · obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
      obtain ⟨k,l,hkl,rfl⟩ := Finset.card_eq_two.mp hb
      rw [pairProjection_pair i j k l hij hkl]
      exact projection_eq_zero_of_not_disjoint i j k l hab
    · exact pairProjection_eq_zero_right a b hb
  · exact pairProjection_eq_zero_left a b ha

theorem sum_pairProjection_norm_sq (a : Finset (Fin n))
    (s : Finset (Finset (Fin n))) (f : StateSpace n d) :
    (∑ b ∈ s, if Disjoint a b then ‖pairProjection a b f‖ ^ 2 else 0) =
      ∑ b ∈ s, ‖pairProjection a b f‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : Disjoint a b
  · rw [ite_eq_left hab]
  · rw [ite_eq_right hab, pairProjection_eq_zero_of_not_disjoint a b hab]
    simp

theorem pairProjection_idempotent (a b : Finset (Fin n)) (f : StateSpace n d) :
    pairProjection a b (pairProjection a b f) = pairProjection a b f := by
  unfold pairProjection
  split_ifs
  · exact Submodule.starProjection_eq_self_iff.mpr
      ((equalitySpace _ _ _ _).starProjection_apply_mem f)
  all_goals simp

theorem pairProjection_isSymmetric (a b : Finset (Fin n)) :
    (pairProjection (d := d) a b).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪pairProjection a b f, g⟫ = ⟪f, pairProjection a b g⟫
  by_cases ha : a.card = 2
  · by_cases hb : b.card = 2
    · simp only [pairProjection, dite_eq_left ha, dite_eq_left hb]
      exact (equalitySpace (d := d) (endpoints a ha).1 (endpoints a ha).2
        (endpoints b hb).1 (endpoints b hb).2).inner_starProjection_left_eq_right f g
    · rw [pairProjection_eq_zero_right a b hb]
      simp
  · rw [pairProjection_eq_zero_left a b ha]
    simp

theorem inner_pairProjection (a b : Finset (Fin n)) (f : StateSpace n d) :
    ⟪f, pairProjection a b f⟫ = ‖pairProjection a b f‖ ^ 2 := by
  have h := pairProjection_isSymmetric a b f (pairProjection a b f)
  change ⟪pairProjection a b f, pairProjection a b f⟫ =
    ⟪f, pairProjection a b (pairProjection a b f)⟫ at h
  rw [pairProjection_idempotent, real_inner_self_eq_norm_sq] at h
  exact h.symm

theorem sum_pairProjection_energy (a : Finset (Fin n))
    (s : Finset (Finset (Fin n))) (f : StateSpace n d) :
    (∑ b ∈ s, ‖pairProjection a b f‖ ^ 2) =
      ⟪f, ∑ b ∈ s, pairProjection a b f⟫ := by
  simp only [inner_sum, inner_pairProjection]

end Problem315.PairEquality

end

end OAI
