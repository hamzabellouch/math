import OAI.Probability.SATComputability.IncidentRates
import OAI.Probability.SATComputability.GridBlockLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable def activeMask {n : ℕ} (a : ActiveClause n) : Finset (DeletionCandidate (n+1)) :=
  clauseMask (classClause (activeClass a))

noncomputable def baseMask {n : ℕ} (a : Triple (SignedLiteral n)) : Finset (DeletionCandidate n) :=
  clauseMask ((tripleVectorEquiv _).symm a)

theorem active_base_counts {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask (fun a => classBaseMask (activeClass a)) c =
      countsMask baseMask (fun a => c (.inl a)) := by
  ext x
  simp [countsMask, classBaseMask, activeClass, baseMask, Sum.forall, Prod.forall]

theorem active_mask_counts {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask activeMask c = restoredMask
      (countsMask baseMask (fun a => c (.inl a)))
      (countsMask (fun a => classIncidentMask false (activeClass a)) c)
      (countsMask (fun a => classIncidentMask true (activeClass a)) c) := by
  rw [← active_base_counts, ← countsMask_restored]
  congr 1
  funext a
  exact classClause_restored (activeClass a)

theorem active_free_lifetime {n M r : ℕ} (c : ActiveClause n × Fin M → ℕ) :
    maskLifetime M (freeDeletionBudgetMask (n+1) r 0) (maskGrid activeMask c) =
      maskLifetime M (deletionBudgetMask n r) (maskGrid baseMask (fun p => c (.inl p.1,p.2))) := by
  have he : maskGrid activeMask c = fun j => restoredMask
      (countsMask baseMask (fun a => c (.inl a,j)))
      (countsMask (fun a => classIncidentMask false (activeClass a)) (fun a => c (a,j)))
      (countsMask (fun a => classIncidentMask true (activeClass a)) (fun a => c (a,j))) := by
    funext j
    exact active_mask_counts _
  rw [he, free_restored_lifetime]
  rfl

theorem active_stronger_counts {n : ℕ} (c : ActiveClause n → ℕ) :
    countsMask strongerClassMask c = restoredMask
      (countsMask baseMask (fun a => c (.inl a)))
      (countsMask incidentMask (fun a => c (.inr (true,a))))
      (countsMask incidentMask (fun a => c (.inr (false,a)))) :=
  countsMask_stronger c

theorem active_gap_domination {n M r : ℕ} (c : ActiveClause n × Fin M → ℕ) :
    (maskLifetime M (freeDeletionBudgetMask (n+1) r 0) (maskGrid activeMask c) -
      maskLifetime M (deletionBudgetMask (n+1) r) (maskGrid activeMask c))^(6/5 : ℝ) ≤
    (maskLifetime M (deletionBudgetMask n r) (maskGrid baseMask (fun p => c (.inl p.1,p.2))) -
      maskLifetime M (deletionBudgetMask (n+1) r) (fun j => restoredMask
        (countsMask baseMask (fun a => c (.inl a,j)))
        (countsMask incidentMask (fun a => c (.inr (true,a),j)))
        (countsMask incidentMask (fun a => c (.inr (false,a),j)))))^(6/5 : ℝ) := by
  have hnon : 0 ≤ maskLifetime M (freeDeletionBudgetMask (n+1) r 0) (maskGrid activeMask c) -
      maskLifetime M (deletionBudgetMask (n+1) r) (maskGrid activeMask c) :=
    sub_nonneg.mpr (maskLifetime_mono (deletionBudgetMask_subset_free (n+1) r 0) _)
  rw [active_free_lifetime] at hnon ⊢
  apply Real.rpow_le_rpow hnon _ (by norm_num : (0 : ℝ) ≤ 6/5)
  apply sub_le_sub_left
  apply maskLifetime_map_le id _ _ _ _ (fun _ h => h)
  intro j x hx
  have he := active_stronger_counts (fun a => c (a,j))
  rw [← he] at hx
  exact countsMask_mono (fun a => strongerClassMask_subset a) _ hx

theorem poissonCountLaw_three {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (r : ℝ≥0) (f : (A → ℕ) → (B → ℕ) → (C → ℕ) → ℝ)
    (D : ℝ) (hD : ∀ a b c, |f a b c| ≤ D) :
    (∫ s : A ⊕ (B ⊕ C) → ℕ,
      f (fun a => s (.inl a)) (fun b => s (.inr (.inl b))) (fun c => s (.inr (.inr c)))
      ∂poissonCountLaw (A ⊕ (B ⊕ C)) r) =
      ∫ a, ∫ b, ∫ c, f a b c ∂poissonCountLaw C r
        ∂poissonCountLaw B r ∂poissonCountLaw A r := by
  rw [poissonCountLaw_sum r _ D (fun s => hD _ _ _)]
  apply integral_congr_ae
  filter_upwards [] with a
  exact poissonCountLaw_sum r _ D (fun _ => hD _ _ _)

theorem active_streams_expect {n M : ℕ} (r : ℝ≥0)
    (ψ : (Fin M → Finset (DeletionCandidate n)) →
      (Fin M → Finset (DeletionCandidate n)) → (Fin M → Finset (DeletionCandidate n)) → ℝ) :
    (∫ c : ActiveClause n × Fin M → ℕ,
      ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
        (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
        (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2)))
      ∂poissonCountLaw (ActiveClause n × Fin M) r) =
      (gridMaskLaw M r baseMask).expect (fun b =>
        (gridMaskLaw M r incidentMask).expect (fun f =>
          (gridMaskLaw M r incidentMask).expect (fun t => ψ b f t))) := by
  let X := Fin M → Finset (DeletionCandidate n)
  let D := ∑ p : X × X × X, |ψ p.1 p.2.1 p.2.2|
  have hD (b f t : X) : |ψ b f t| ≤ D :=
    Finset.single_le_sum (fun p _ => abs_nonneg (ψ p.1 p.2.1 p.2.2))
      (Finset.mem_univ (b,f,t))
  have he := poissonCountLaw_equiv (splitActiveGrid n M) r
    (fun s => ψ (maskGrid baseMask (fun p => s (.inl p)))
      (maskGrid incidentMask (fun p => s (.inr (.inr p))))
      (maskGrid incidentMask (fun p => s (.inr (.inl p)))))
  change (∫ c : ActiveClause n × Fin M → ℕ,
      ψ (maskGrid baseMask (fun p => c (.inl p.1,p.2)))
        (maskGrid incidentMask (fun p => c (.inr (true,p.1),p.2)))
        (maskGrid incidentMask (fun p => c (.inr (false,p.1),p.2)))
      ∂poissonCountLaw (ActiveClause n × Fin M) r) = _ at he
  rw [he, poissonCountLaw_three r
    (fun (b : Triple (SignedLiteral n) × Fin M → ℕ)
      (f t : IncidentClass n × Fin M → ℕ) =>
        ψ (maskGrid baseMask b) (maskGrid incidentMask t) (maskGrid incidentMask f))
    D (fun a b c => hD _ _ _)]
  have hi (b : Triple (SignedLiteral n) × Fin M → ℕ)
      (f : IncidentClass n × Fin M → ℕ) :
      (∫ t, ψ (maskGrid baseMask b) (maskGrid incidentMask t) (maskGrid incidentMask f)
        ∂poissonCountLaw (IncidentClass n × Fin M) r) =
        (gridMaskLaw M r incidentMask).expect
          (fun t => ψ (maskGrid baseMask b) t (maskGrid incidentMask f)) :=
    (gridMaskLaw_expect r incidentMask
      (fun t => ψ (maskGrid baseMask b) t (maskGrid incidentMask f))).symm
  simp_rw [hi]
  have hm (b : Triple (SignedLiteral n) × Fin M → ℕ) :
      (∫ f, (gridMaskLaw M r incidentMask).expect
        (fun t => ψ (maskGrid baseMask b) t (maskGrid incidentMask f))
        ∂poissonCountLaw (IncidentClass n × Fin M) r) =
      (gridMaskLaw M r incidentMask).expect (fun f =>
        (gridMaskLaw M r incidentMask).expect (fun t => ψ (maskGrid baseMask b) t f)) :=
    (gridMaskLaw_expect r incidentMask (fun f =>
      (gridMaskLaw M r incidentMask).expect (fun t => ψ (maskGrid baseMask b) t f))).symm
  simp_rw [hm]
  rw [← gridMaskLaw_expect r baseMask (fun b =>
    (gridMaskLaw M r incidentMask).expect (fun f =>
      (gridMaskLaw M r incidentMask).expect (fun t => ψ b t f)))]
  apply FiniteLaw.expect_congr
  intro b
  exact finite_expect_comm _ _ _

theorem active_original_expect {n M : ℕ} (r : ℝ≥0)
    (ψ : (Fin M → Finset (DeletionCandidate (n+1))) → ℝ) :
    (∫ c : TripleClasses (SignedLiteral n) × Fin M → ℕ,
      ψ (maskGrid (fun a => clauseMask (classClause a)) c)
      ∂poissonCountLaw (TripleClasses (SignedLiteral n) × Fin M) r) =
    ∫ c : ActiveClause n × Fin M → ℕ, ψ (maskGrid activeMask c)
      ∂poissonCountLaw (ActiveClause n × Fin M) r := by
  let e : ActiveClause n × Fin M → TripleClasses (SignedLiteral n) × Fin M :=
    fun p => (activeClass p.1,p.2)
  have he : Function.Injective e := by
    intro p q h
    change (activeClass p.1,p.2) = (activeClass q.1,q.2) at h
    exact Prod.ext (activeClass_injective n (Prod.mk.inj h).1) (Prod.mk.inj h).2
  rw [← poissonCountLaw_embedding_integral e he r]
  apply integral_congr_ae
  filter_upwards [] with c
  congr 1
  funext j
  exact (countsMask_active (fun a => c (a,j))).symm

theorem base_grid_law {n : ℕ} [NeZero n] (M : ℕ) (r : ℝ≥0) :
    gridMaskLaw M r (baseMask (n := n)) = FiniteLaw.pi (fun _ : Fin M =>
      candidateBlock (r*Fintype.card (Triple (SignedLiteral n))) 3 Finset.univ) := by
  rw [← gridMaskLaw_equiv (tripleVectorEquiv (SignedLiteral n)) r baseMask]
  have hm : baseMask ∘ tripleVectorEquiv (SignedLiteral n) = clauseMask := by
    funext a
    simp only [baseMask, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hm, gridMaskLaw_clauses]
  rw [Fintype.card_congr (tripleVectorEquiv (SignedLiteral n))]

end FixedClauseThreshold.Computability

end OAI
