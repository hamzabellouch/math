import OAI.NumberTheory.PowerFree.HilbertGrowth

namespace OAI

open scoped BigOperators

namespace QuarticPowerFree

section

attribute [local instance] Classical.propDecidable

theorem pderiv_totalDegree_lt {σ K : Type*} [CommSemiring K]
    (i : σ) (p : MvPolynomial σ K) (h : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs : ∀ m ∈ (MvPolynomial.pderiv i p).support,
      m.sum (fun _ e => e) < p.totalDegree := by
    intro m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hc
    have hp : m + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr (fun he => hc (by rw [he, zero_mul]))
    have hh := MvPolynomial.le_totalDegree hp
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (by rfl)] at hh
    exact hh
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr h
  have hpos : 0 < p.totalDegree := (Nat.zero_le _).trans_lt (hs m hm)
  exact (Finset.sup_lt_iff hpos).mpr hs

theorem pderiv_vars_subset {σ K : Type*} [CommSemiring K]
    (i : σ) (p : MvPolynomial σ K) :
    (MvPolynomial.pderiv i p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨m, hm, hjm⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hj
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  refine (MvPolynomial.mem_vars_iff_mem_support j).mpr
    ⟨m + Finsupp.single i 1,
      MvPolynomial.mem_support_iff.mpr (fun he => hc (by rw [he, zero_mul])), ?_⟩
  rw [Finsupp.mem_support_iff, Finsupp.add_apply]
  have hh := Finsupp.mem_support_iff.mp hjm
  omega

theorem pderiv_ne_zero_of_mem_vars {σ K : Type*} [CommRing K]
    [IsDomain K] [CharZero K] (i : σ) (p : MvPolynomial σ K)
    (hi : i ∈ p.vars) : MvPolynomial.pderiv i p ≠ 0 := by
  classical
  obtain ⟨m, hm, him⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
  have hcoeff : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  intro h
  have hh := congrArg (fun polynomial => polynomial.coeff (m - Finsupp.single i 1)) h
  rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hmi,
    AddMonoidAlgebra.coeff_zero] at hh
  have hnat : ∀ n : ℕ, (n : K) + 1 ≠ 0 := by
    intro n
    exact_mod_cast Nat.succ_ne_zero n
  exact (mul_ne_zero hcoeff (hnat _)) hh

theorem eq_zero_of_aeval_eq_zero_of_vars_subset {σ K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val))
    (p : MvPolynomial σ K) (hp : (p.vars : Set σ) ⊆ J)
    (hz : MvPolynomial.aeval z p = 0) : p = 0 := by
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (fun j : J => j.val) Subtype.val_injective (by simpa using hp)
  subst p
  rw [MvPolynomial.aeval_rename] at hz
  have hh : q = 0 := (algebraicIndependent_iff_injective_aeval.mp hJ)
    (hz.trans (map_zero _).symm)
  simp [hh]

theorem exists_relation_with_nonzero_pderiv {σ K F : Type*}
    [Field K] [CharZero K] [CommRing F] [Algebra K F]
    (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val))
    (i : σ) (p : MvPolynomial σ K) (hp : p ≠ 0)
    (hvars : (p.vars : Set σ) ⊆ insert i J) (hz : MvPolynomial.aeval z p = 0) :
    ∃ q : MvPolynomial σ K, q ≠ 0 ∧ (q.vars : Set σ) ⊆ insert i J ∧
      q.totalDegree ≤ p.totalDegree ∧ MvPolynomial.aeval z q = 0 ∧
      MvPolynomial.aeval z (MvPolynomial.pderiv i q) ≠ 0 := by
  classical
  let S : Set (MvPolynomial σ K) :=
    {q | q ≠ 0 ∧ (q.vars : Set σ) ⊆ insert i J ∧ MvPolynomial.aeval z q = 0}
  have hpS : p ∈ S := ⟨hp, hvars, hz⟩
  let q := Function.argminOn MvPolynomial.totalDegree S ⟨p, hpS⟩
  have hq : q ∈ S := Function.argminOn_mem _ _ _
  have hiq : i ∈ q.vars := by
    by_contra hn
    apply hq.1
    apply eq_zero_of_aeval_eq_zero_of_vars_subset z J hJ q _ hq.2.2
    intro j hj
    rcases hq.2.1 hj with he | he
    · exact False.elim (hn (he ▸ hj))
    · exact he
  have hder : MvPolynomial.pderiv i q ≠ 0 := pderiv_ne_zero_of_mem_vars i q hiq
  have hdeg := pderiv_totalDegree_lt i q hder
  refine ⟨q, hq.1, hq.2.1, ?_, hq.2.2, ?_⟩
  · exact Function.argminOn_le _ _ hpS
  · intro he
    have hdS : MvPolynomial.pderiv i q ∈ S :=
      ⟨hder, fun j hj => hq.2.1 (pderiv_vars_subset i q hj), he⟩
    exact Function.not_lt_argminOn MvPolynomial.totalDegree S hdS hdeg

theorem exists_diagonal_jacobian_relations {σ K F : Type*}
    [Fintype σ] [DecidableEq σ] [Field K] [CharZero K] [CommRing F] [IsDomain F] [Algebra K F]
    (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val)) (D : ℕ)
    (hrel : ∀ i : ↥(Jᶜ), ∃ p : MvPolynomial σ K, p ≠ 0 ∧
      (p.vars : Set σ) ⊆ insert i.val J ∧ p.totalDegree ≤ D ∧
      MvPolynomial.aeval z p = 0) :
    ∃ G : ↥(Jᶜ) → MvPolynomial σ K,
      (∀ i, (G i).totalDegree ≤ D) ∧
      (∀ i, MvPolynomial.aeval z (G i) = 0) ∧
      Matrix.det (fun i j : ↥(Jᶜ) => MvPolynomial.aeval z
        (MvPolynomial.pderiv j.val (G i))) ≠ 0 := by
  classical
  have hh : ∀ i : ↥(Jᶜ), ∃ q : MvPolynomial σ K,
      (q.vars : Set σ) ⊆ insert i.val J ∧ q.totalDegree ≤ D ∧
      MvPolynomial.aeval z q = 0 ∧
      MvPolynomial.aeval z (MvPolynomial.pderiv i.val q) ≠ 0 := by
    intro i
    obtain ⟨p, hp, hv, hd, he⟩ := hrel i
    obtain ⟨q, _, hvq, hdq, heq, hder⟩ :=
      exists_relation_with_nonzero_pderiv z J hJ i.val p hp hv he
    exact ⟨q, hvq, hdq.trans hd, heq, hder⟩
  choose G hvars hdeg heval hder using hh
  refine ⟨G, hdeg, heval, ?_⟩
  have hmat : (fun i j : ↥(Jᶜ) => MvPolynomial.aeval z
      (MvPolynomial.pderiv j.val (G i))) =
      Matrix.diagonal (fun i : ↥(Jᶜ) => MvPolynomial.aeval z
        (MvPolynomial.pderiv i.val (G i))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars, map_zero]
      intro hj
      rcases hvars i hj with hj | hj
      · exact hij (Subtype.ext hj.symm)
      · exact j.property hj
  rw [hmat, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hder i)

theorem exists_nonsingular_rows_of_span_eq_top {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field F] (A : Matrix α β F)
    (hA : Submodule.span F (Set.range A) = ⊤) :
    ∃ a : β → α, Function.Injective a ∧ Matrix.det (fun i j => A (a i) j) ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F A
  let := Fintype.ofInjective a ha
  let b : Module.Basis κ F (β → F) := Module.Basis.mk hli (by rw [hspan, hA])
  have hcard : Fintype.card β = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := F), Module.finrank_eq_card_basis b]
  let e : β ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_row
  exact hli.comp e e.injective

noncomputable def genericJacobianRow {σ β K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (v : β → σ) :
    MvPolynomial σ K →ₗ[K] (β → F) :=
  LinearMap.pi (fun j => (MvPolynomial.aeval z).toLinearMap.comp
    (MvPolynomial.pderiv (v j)).toLinearMap)

theorem jacobianRow_mem_span {σ α β K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (v : β → σ)
    (G : α → MvPolynomial σ K) (p : MvPolynomial σ K)
    (hp : p ∈ Submodule.span K (Set.range G)) :
    genericJacobianRow z v p ∈ Submodule.span F
      (Set.range (fun i => genericJacobianRow z v (G i))) := by
  let W := Submodule.span F (Set.range (fun i => genericJacobianRow z v (G i)))
  have hs : Submodule.span K (Set.range G) ≤
      (W.restrictScalars K).comap (genericJacobianRow z v) := by
    apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  exact hs hp

theorem exists_nonsingular_jacobian_of_span {σ α β K F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field K] [Field F] [Algebra K F]
    (z : σ → F) (v : β → σ) (G : α → MvPolynomial σ K)
    (P : β → MvPolynomial σ K)
    (hP : ∀ i, P i ∈ Submodule.span K (Set.range G))
    (hdet : Matrix.det (fun i j => MvPolynomial.aeval z
      (MvPolynomial.pderiv (v j) (P i))) ≠ 0) :
    ∃ a : β → α, Function.Injective a ∧
      Matrix.det (fun i j => MvPolynomial.aeval z
        (MvPolynomial.pderiv (v j) (G (a i)))) ≠ 0 := by
  classical
  let A : Matrix β β F := fun i => genericJacobianRow z v (P i)
  have hli : LinearIndependent F A := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have htop : Submodule.span F (Set.range A) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (Module.finrank_fintype_fun_eq_card (R := F)).symm
  apply exists_nonsingular_rows_of_span_eq_top (fun i => genericJacobianRow z v (G i))
  apply top_unique
  rw [← htop]
  apply Submodule.span_le.mpr
  rintro q ⟨i, rfl⟩
  exact jacobianRow_mem_span z v G (P i) (hP i)

end
open MvPolynomial
attribute [local instance] Classical.propDecidable

theorem bounded_generic_jacobian {n h D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : (h.factorial : ℚ) * P.coeff h ≤ D)
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a)))) :
    ∃ J : Set (Fin n), Nat.card J = h ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) K,
        (∀ i, (G i).totalDegree ≤ D) ∧ (∀ i, G i ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (G i)) ∉ I := by
  classical
  let z : Fin n → MvPolynomial (Fin n) K ⧸ I := fun a => Ideal.Quotient.mk I (X a)
  have hjj : Function.Injective j := by
    intro a b hab
    exact hj.injective (congrArg (fun x => Ideal.Quotient.mk I (X x)) hab)
  obtain ⟨J, hJr⟩ : ∃ J : Set (Fin n), Set.range j = J := ⟨_, rfl⟩
  have hmem (a : Fin n) : a ∈ Set.range j ↔ a ∈ J := Set.ext_iff.mp hJr a
  let e : Fin h ≃ J := (Equiv.ofInjective j hjj).trans (Set.equivOfEq hJr)
  have heval (a : Fin h) : (e a).val = j a := rfl
  have hej (a : J) : j (e.symm a) = a.val := (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply a))
  have hJ : AlgebraicIndependent K (fun a : J => z a.val) := by
    have hh := hj.comp e.symm e.symm.injective
    simpa only [Function.comp_def, hej, z] using hh
  have hae : aeval z = Ideal.Quotient.mkₐ K I := by ext a; simp only [aeval_X]; rfl
  have hr : ∀ i : ↥(Jᶜ), ∃ p : MvPolynomial (Fin n) K, p ≠ 0 ∧
      (p.vars : Set (Fin n)) ⊆ insert i.val J ∧ p.totalDegree ≤ D ∧ aeval z p = 0 := by
    intro i
    let v : Fin (h+1) → Fin n := Fin.cases i.val j
    have hvj : AlgebraicIndependent K
        (fun a : Fin h => Ideal.Quotient.mk I (X (v a.succ))) := hj
    obtain ⟨q,hq,_,hd,hker⟩ := bounded_projection_relation I P hP hT v hvj
    have hvi : Function.Injective v := by
      intro a b hab
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => rfl
        | succ b => exact False.elim (i.property ((hmem i.val).mp (Set.mem_range.mpr ⟨b,hab.symm⟩)))
      | succ a =>
        cases b using Fin.cases with
        | zero => exact False.elim (i.property ((hmem i.val).mp (Set.mem_range.mpr ⟨a,hab⟩)))
        | succ b => exact congrArg Fin.succ (hjj hab)
    refine ⟨rename v q, (rename_injective v hvi).ne hq.ne_zero, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b,_,rfl⟩ := mem_vars_rename v q ha
      cases b using Fin.cases with
      | zero => exact Set.mem_insert _ _
      | succ b => exact Set.mem_insert_of_mem _ ((hmem (j b)).mp (Set.mem_range_self b))
    · apply (totalDegree_rename_le v q).trans
      exact_mod_cast hd.trans hD
    · rw [hae]
      exact (hker q).mpr (dvd_refl q)
  obtain ⟨G,hdeg,hvan,hdet⟩ := exists_diagonal_jacobian_relations z J hJ D hr
  refine ⟨J, ?_, G,hdeg,?_,?_⟩
  · exact (Nat.card_congr e.symm).trans (Nat.card_fin h)
  · intro i
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [hae, Ideal.Quotient.mkₐ_eq_mk] using hvan i)
  · have hdet' : Matrix.det (fun i l : ↥(Jᶜ) => Ideal.Quotient.mk I (pderiv l.val (G i))) ≠ 0 := by
      simpa only [hae, Ideal.Quotient.mkₐ_eq_mk] using hdet
    intro hm
    apply hdet'
    let M : Matrix ↥(Jᶜ) ↥(Jᶜ) (MvPolynomial (Fin n) K) := fun i l => pderiv l.val (G i)
    have hm0 : Ideal.Quotient.mk I M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have he : ((Ideal.Quotient.mk I).mapMatrix M).det = 0 :=
      ((Ideal.Quotient.mk I).map_det M).symm.trans hm0
    exact he

end QuarticPowerFree

end OAI
