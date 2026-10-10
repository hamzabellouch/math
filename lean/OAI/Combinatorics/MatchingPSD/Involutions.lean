import OAI.Combinatorics.MatchingPSD.Model

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

section CommutingInvolutions

variable {ι : Type u_1} {V : Type u_2} [AddCommGroup V] [Module ℝ V]

lemma eigen_add_commuting (A B : Module.End ℝ V) (hAB : Commute A B)
    (v : V) (c : ℝ) (hv : A v = c • v) :
    A (v + B v) = c • (v + B v) := by
  have hc : A (B v) = B (A v) := congrArg (fun f : Module.End ℝ V => f v) hAB.eq
  rw [map_add, hv, hc, hv, map_smul, smul_add]

lemma eigen_sub_commuting (A B : Module.End ℝ V) (hAB : Commute A B)
    (v : V) (c : ℝ) (hv : A v = c • v) :
    A (v - B v) = c • (v - B v) := by
  have hc : A (B v) = B (A v) := congrArg (fun f : Module.End ℝ V => f v) hAB.eq
  rw [map_sub, hv, hc, hv, map_smul, smul_sub]

lemma simultaneous_sign_eigenvector_on (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) (s : Finset ι) :
    ∃ (χ : ι → ℝ) (v : V), v ∈ W ∧ v ≠ 0 ∧
      ∀ i ∈ s, (χ i = 1 ∨ χ i = -1) ∧ A i v = χ i • v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨v, hv, hv0⟩ := hne
    exact ⟨fun _ => 1, v, hv, hv0, by simp⟩
  | @insert i s his ih =>
    obtain ⟨χ, v, hv, hv0, heig⟩ := ih
    by_cases hp : v + A i v = 0
    · have hm : v - A i v ≠ 0 := by
        intro hm
        have htwo : (2 : ℝ) • v = 0 := by
          rw [two_smul]
          linear_combination (norm := abel) hp + hm
        exact hv0 ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
      refine ⟨Function.update χ i (-1), v - A i v,
        W.sub_mem hv (hstable i v hv), hm, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [Function.update_self, neg_smul, one_smul]
        refine ⟨by simp, ?_⟩
        rw [map_sub, hinv]
        abel
      · have hji : j ≠ i := by intro h; subst j; exact his hj
        rw [Function.update_of_ne hji]
        exact ⟨(heig j hj).1, eigen_sub_commuting (A j) (A i) (hcomm j i)
          v (χ j) (heig j hj).2⟩
    · refine ⟨Function.update χ i 1, v + A i v,
        W.add_mem hv (hstable i v hv), hp, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [Function.update_self, one_smul]
        refine ⟨by simp, ?_⟩
        rw [map_add, hinv, add_comm]
      · have hji : j ≠ i := by intro h; subst j; exact his hj
        rw [Function.update_of_ne hji]
        exact ⟨(heig j hj).1, eigen_add_commuting (A j) (A i) (hcomm j i)
          v (χ j) (heig j hj).2⟩

lemma simultaneous_sign_eigenvector [Fintype ι] (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (hne : ∃ v ∈ W, v ≠ 0) :
    ∃ (χ : ι → ℝ) (v : V), v ∈ W ∧ v ≠ 0 ∧
      ∀ i, (χ i = 1 ∨ χ i = -1) ∧ A i v = χ i • v := by
  simpa using simultaneous_sign_eigenvector_on A hcomm hinv W hstable hne Finset.univ

lemma simultaneous_sign_eigenvector_preserving [Fintype ι]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (s : Finset ι) (χ : ι → ℝ)
    (v : V) (hv : v ∈ W) (hv0 : v ≠ 0) (he : ∀ i ∈ s, A i v = χ i • v) :
    ∃ (ψ : ι → ℝ) (w : V), w ∈ W ∧ w ≠ 0 ∧
      (∀ i, (ψ i = 1 ∨ ψ i = -1) ∧ A i w = ψ i • w) ∧
      ∀ i ∈ s, ψ i = χ i := by
  let U : Submodule ℝ V :=
    { carrier := {w | w ∈ W ∧ ∀ i ∈ s, A i w = χ i • w}
      zero_mem' := by simp
      add_mem' := by
        rintro a b ⟨ha, hea⟩ ⟨hb, heb⟩
        exact ⟨W.add_mem ha hb, fun i hi => by rw [map_add, hea i hi, heb i hi, smul_add]⟩
      smul_mem' := by
        rintro c a ⟨ha, hea⟩
        exact ⟨W.smul_mem c ha, fun i hi => by rw [map_smul, hea i hi, smul_comm]⟩ }
  have hU (j : ι) (w : V) (hw : w ∈ U) : A j w ∈ U := by
    refine ⟨hstable j w hw.1, ?_⟩
    intro i hi
    have hc := congrArg (fun f : Module.End ℝ V => f w) (hcomm i j).eq
    change A i (A j w) = A j (A i w) at hc
    rw [hc, hw.2 i hi, map_smul]
  obtain ⟨ψ, w, hw, hw0, hew⟩ := simultaneous_sign_eigenvector A hcomm hinv U hU
    ⟨v, ⟨hv, he⟩, hv0⟩
  refine ⟨ψ, w, hw.1, hw0, hew, ?_⟩
  intro i hi
  exact smul_left_injective ℝ hw0 ((hew i).2.symm.trans (hw.2 i hi))

lemma independent_eigenprofiles {κ : Type u_3} (A : ι → Module.End ℝ V)
    (hcomm : ∀ i j, Commute (A i) (A j)) (χ : κ → ι → ℝ)
    (hinj : Function.Injective χ) (v : κ → V) (hv : ∀ k, v k ≠ 0)
    (heig : ∀ k i, A i (v k) = χ k i • v k) : LinearIndependent ℝ v := by
  have hi := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo A
    (fun i j c => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) c)
  apply (hi.comp hinj).linearIndependent _ _ hv
  intro k
  change v k ∈ ⨅ i, (A i).maxGenEigenspace (χ k i)
  rw [Submodule.mem_iInf]
  intro i
  exact Module.End.eigenspace_le_maxGenEigenspace
    (Module.End.mem_eigenspace_iff.mpr (heig k i))

lemma binomial_le_finrank_of_eigenvector [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ V]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (P : Equiv.Perm ι → V ≃ₗ[ℝ] V)
    (hconj : ∀ p i v, A (p i) (P p v) = P p (A i v))
    (s : Finset ι) (v : V) (hv : v ≠ 0)
    (heig : ∀ i, A i v = (if i ∈ s then (-1 : ℝ) else 1) • v) :
    (Fintype.card ι).choose s.card ≤ Module.finrank ℝ V := by
  classical
  let T := ↥((Finset.univ : Finset ι).powersetCard s.card)
  have hp (t : T) : ∃ p : Equiv.Perm ι, s.map p.toEmbedding = t.1 :=
    Equiv.Perm.exists_map_finset_eq s t.1
      (Finset.mem_powersetCard.mp t.2).2.symm
  choose p hp using hp
  let χ (t : T) (i : ι) : ℝ := if i ∈ t.1 then -1 else 1
  have hχ : Function.Injective χ := by
    intro t u h
    apply Subtype.ext
    ext i
    have hh := congrFun h i
    dsimp [χ] at hh
    by_cases ht : i ∈ t.1 <;> by_cases hu : i ∈ u.1 <;> simp_all <;> norm_num at hh
  have hprof (t : T) (i : ι) : A i (P (p t) v) = χ t i • P (p t) v := by
    have hi : (p t).symm i ∈ s ↔ i ∈ t.1 := by
      rw [← hp t]
      simp
    by_cases hii : i ∈ t.1 <;>
      simpa [heig, χ, hi, hii] using hconj (p t) ((p t).symm i) v
  have hli := independent_eigenprofiles A hcomm χ hχ
    (fun t => P (p t) v) (fun t => by simpa using hv) hprof
  have hc := hli.fintype_card_le_finrank
  simpa only [T, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ] using hc

lemma binomial_le_finrank_of_eigenvector_mem [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ V]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (P : Equiv.Perm ι → V ≃ₗ[ℝ] V)
    (hconj : ∀ p i v, A (p i) (P p v) = P p (A i v))
    (W : Submodule ℝ V) (hW : ∀ p v, v ∈ W → P p v ∈ W)
    (s : Finset ι) (v : V) (hvW : v ∈ W) (hv : v ≠ 0)
    (heig : ∀ i, A i v = (if i ∈ s then (-1 : ℝ) else 1) • v) :
    (Fintype.card ι).choose s.card ≤ Module.finrank ℝ W := by
  classical
  let T := ↥((Finset.univ : Finset ι).powersetCard s.card)
  have hp (t : T) : ∃ p : Equiv.Perm ι, s.map p.toEmbedding = t.1 :=
    Equiv.Perm.exists_map_finset_eq s t.1
      (Finset.mem_powersetCard.mp t.2).2.symm
  choose p hp using hp
  let χ (t : T) (i : ι) : ℝ := if i ∈ t.1 then -1 else 1
  have hχ : Function.Injective χ := by
    intro t u h
    apply Subtype.ext
    ext i
    have hh := congrFun h i
    dsimp [χ] at hh
    by_cases ht : i ∈ t.1 <;> by_cases hu : i ∈ u.1 <;> simp_all <;> norm_num at hh
  have hprof (t : T) (i : ι) : A i (P (p t) v) = χ t i • P (p t) v := by
    have hi : (p t).symm i ∈ s ↔ i ∈ t.1 := by
      rw [← hp t]
      simp
    by_cases hii : i ∈ t.1 <;>
      simpa [heig, χ, hi, hii] using hconj (p t) ((p t).symm i) v
  have hli := independent_eigenprofiles A hcomm χ hχ
    (fun t => P (p t) v) (fun t => by simpa using hv) hprof
  let vw (t : T) : W := ⟨P (p t) v, hW (p t) v hvW⟩
  have hliw : LinearIndependent ℝ vw := LinearIndependent.of_comp W.subtype hli
  have hc := hliw.fintype_card_le_finrank
  simpa only [T, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ] using hc

end CommutingInvolutions
end MatchingSmoothing

end OAI
