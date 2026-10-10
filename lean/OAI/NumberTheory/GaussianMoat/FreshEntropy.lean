import OAI.NumberTheory.GaussianMoat.DenseBins

namespace OAI

universe uKappa uBeta uIota uOmega uXi uAlpha

namespace GaussianMoat
open scoped BigOperators Classical

theorem expect_restrict {κ : Type uKappa} {β : Type uBeta} [Fintype κ] [Fintype β] [Nonempty β]
    (s : Finset κ) (F : (s → β) → ℝ) :
    (𝔼 σ : κ → β, F (fun p => σ p)) = 𝔼 τ : s → β, F τ := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun x => x ∈ s) (fun _ => β)
  calc
    _ = 𝔼 pair : (s → β) × ({x : κ // x ∉ s} → β), F pair.1 := by
      exact Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [← Finset.univ_product_univ,Finset.expect_product]
      simp only [Fintype.expect_const]

theorem expect_precomp_injective {ι : Type uIota} {κ : Type uKappa} {β : Type uBeta} [Fintype ι] [Fintype κ]
    [Fintype β] [Nonempty β] (e : ι → κ) (he : Function.Injective e)
    (F : (ι → β) → ℝ) :
    (𝔼 σ : κ → β, F (σ ∘ e)) = 𝔼 τ : ι → β, F τ := by
  classical
  let s := Finset.univ.image e
  let ee : ι ≃ s := Equiv.ofBijective (fun i => ⟨e i, Finset.mem_image.mpr
    ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨fun i j h => he (congrArg Subtype.val h),by
      rintro ⟨y,hy⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hy
      exact ⟨i,Subtype.ext hi⟩⟩
  calc
    _ = 𝔼 τ : s → β, F (fun i => τ (ee i)) := expect_restrict s _
    _ = _ := by
      exact Fintype.expect_equiv (Equiv.arrowCongr ee.symm (Equiv.refl β)) _ _ (fun _ => rfl)

lemma signMeasure_real_eq_expect {ι : Type uIota} [Fintype ι] (S : Set (ι → Bool)) :
    (signMeasure ι).real S = 𝔼 σ : ι → Bool, if σ ∈ S then (1 : ℝ) else 0 := by
  rw [signMeasure_real_set]
  simp [Finset.expect,NNRat.smul_def,div_eq_inv_mul]

lemma expect_sign_restriction {ι : Type uIota} {κ : Type uKappa} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (S : Set (ι → Bool)) :
    (𝔼 σ : κ → Bool, if σ ∘ e ∈ S then (1 : ℝ) else 0) =
      (signMeasure ι).real S := by
  exact (expect_precomp_injective e he (fun τ => if τ ∈ S then (1 : ℝ) else 0)).trans
    (signMeasure_real_eq_expect S).symm

lemma uniform_entropy_event_bound {Ω : Type uOmega} {Ξ : Type uXi} {α : Type uAlpha} [Fintype Ω] [Nonempty Ω]
    [Fintype Ξ] [Nonempty Ξ] (X : Ξ → Ω → α) (bad : Ξ → Prop)
    (hg : ∀ σ, ¬bad σ → Function.Injective (X σ)) :
    (1-(𝔼 σ, if bad σ then (1 : ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      𝔼 σ, (FinLaw.uniform Ω).Hf (X σ) := by
  have hp (σ : Ξ) : (1-(if bad σ then (1 : ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      (FinLaw.uniform Ω).Hf (X σ) := by
    by_cases hb : bad σ
    · simpa [hb] using (FinLaw.uniform Ω).Hf_nonneg (X σ)
    · simp only [hb,ite_false,sub_zero,one_mul]
      rw [FinLaw.uniform_Hf_injective _ (hg σ hb)]
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hp σ)
  simpa only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] using h

abbrev SplitSieve.restrict (s : SplitSieve) (Q : Finset ℕ) (hQ : Q ⊆ s.primes) : SplitSieve where
  primes := Q
  factor := s.factor
  prime_mem := fun p hp => s.prime_mem p (hQ hp)
  mod_four := fun p hp => s.mod_four p (hQ hp)
  factor_irreducible := fun p hp => s.factor_irreducible p (hQ hp)
  factor_norm := fun p hp => s.factor_norm p (hQ hp)

noncomputable def SplitSieve.enumeration (s : SplitSieve) : Fin s.primes.card ≃ s.primes :=
  s.primes.equivFin.symm

noncomputable def prefixIndices (k r : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.val < r)

lemma mem_prefixIndices {k r : ℕ} (i : Fin k) : i ∈ prefixIndices k r ↔ i.val < r := by
  simp [prefixIndices]

lemma prefixIndices_card {k r : ℕ} (hr : r ≤ k) : (prefixIndices k r).card = r := by
  have he : prefixIndices k r = (Finset.univ : Finset (Fin r)).image
      (fun i => (⟨i.val,by omega⟩ : Fin k)) := by
    ext i
    simp only [mem_prefixIndices,Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun hi => ⟨⟨i.val,hi⟩,rfl⟩,fun ⟨j,hj⟩ => by cases hj; exact j.isLt⟩
  have hinj : Function.Injective (fun i : Fin r => (⟨i.val,by omega⟩ : Fin k)) :=
    fun i j h => Fin.ext (congrArg (fun j : Fin k => j.val) h)
  rw [he,Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin r

noncomputable def SplitSieve.prefixSet (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : Finset ℕ :=
  (prefixIndices s.primes.card r).image (fun i => (s.enumeration (π i)).val)

lemma SplitSieve.prefixSet_subset (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : s.prefixSet π r ⊆ s.primes := by
  intro p hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
  exact (s.enumeration (π i)).property

lemma SplitSieve.prefixSet_card (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) {r : ℕ} (hr : r ≤ s.primes.card) :
    (s.prefixSet π r).card = r := by
  have hinj : Function.Injective (fun i => (s.enumeration (π i)).val) :=
    Subtype.val_injective.comp (s.enumeration.injective.comp π.injective)
  rw [SplitSieve.prefixSet,Finset.card_image_of_injective _ hinj]
  exact prefixIndices_card hr

noncomputable abbrev SplitSieve.prefixSieve (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : SplitSieve :=
  s.restrict (s.prefixSet π r) (s.prefixSet_subset π r)

noncomputable def SplitSieve.residueVector (s : SplitSieve)
    (σ : Fin s.primes.card → Bool) (z : GaussianInt) (i : Fin s.primes.card) : ℕ :=
  residueCode (signedFactor (s.factor (s.enumeration i)) (σ i)) z

noncomputable def SplitSieve.prefixIndex (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) (p : (s.prefixSet π r)) : Fin s.primes.card :=
  s.enumeration.symm ⟨p.val,s.prefixSet_subset π r p.property⟩

lemma SplitSieve.prefixIndex_injective (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) : Function.Injective (s.prefixIndex π r) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun y : s.primes => (y : ℕ)) (s.enumeration.symm.injective hpq)

lemma SplitSieve.prefix_injective_of_no_bad (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ)
    (σ : Fin s.primes.card → Bool) (Δ : Finset GaussianInt) (Q : Set GaussianInt)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ Q)
    (hb : ¬(s.prefixSieve π r).badSign Q (σ ∘ s.prefixIndex π r)) :
    Function.Injective (fun x : Δ => FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r x) := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  apply hb
  refine ⟨x-y,hΔ x x.property y y.property,sub_ne_zero.mpr hne,?_⟩
  apply (s.prefixSieve π r).prod_factors_dvd _ (fun _ h => h)
  intro p hp
  obtain ⟨i,hi,hp'⟩ := Finset.mem_image.mp hp
  have hres := congrFun hxy i
  have hiv := (mem_prefixIndices i).mp hi
  simp only [FinLaw.prefixVar,hiv,ite_eq_left,Option.some.injEq] at hres
  have hidx : s.prefixIndex π r ⟨p,hp⟩ = π i := by
    apply s.enumeration.injective
    apply Subtype.ext
    simpa only [SplitSieve.prefixIndex,Equiv.apply_symm_apply] using hp'.symm
  rw [SplitSieve.extendSigns_mem _ _ p hp]
  change signedFactor (s.factor p) (σ (s.prefixIndex π r ⟨p,hp⟩)) ∣ _
  rw [hidx]
  simpa only [SplitSieve.residueVector,hp'] using
      (residueCode_eq _ _ _).mp hres

theorem SplitSieve.prefix_entropy_rectangle (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) {r : ℕ} (hr : r ≤ s.primes.card)
    (Δ : Finset GaussianInt) (hΔne : Δ.Nonempty)
    {T R W d : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (harea : R*W ≤ ((s.prefixSieve π r).period : ℝ)^(1-d))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ orientedRectangle e R W) :
    let := hΔne.to_subtype
    (1-Real.exp (-(d^3*r/5120)))*Real.log Δ.card ≤
      𝔼 σ : Fin s.primes.card → Bool,
        (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r) := by
  let := hΔne.to_subtype
  let t := s.prefixSieve π r
  let Q := orientedRectangle e R W
  have hc : t.primes.card=r := s.prefixSet_card π hr
  have hprob : (𝔼 σ : Fin s.primes.card → Bool,
      if t.badSign Q (σ ∘ s.prefixIndex π r) then (1 : ℝ) else 0) ≤
      Real.exp (-(d^3*r/5120)) := by
    calc
      _ = (signMeasure t.primes).real {τ | t.badSign Q τ} := by
        convert expect_sign_restriction (s.prefixIndex π r) (s.prefixIndex_injective π r)
          {τ | t.badSign Q τ} using 1
        congr 1
        ext σ; simp
      _ ≤ _ := by
        have ht := t.signed_rectangle he hT (fun p hp => hpT p (s.prefixSet_subset π r hp))
          hW hWR hd hd1 harea (by rwa [hc])
        simpa only [hc] using ht
  have hg := uniform_entropy_event_bound
    (fun σ => FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r)
    (fun σ => t.badSign Q (σ ∘ s.prefixIndex π r))
    (fun σ hb => s.prefix_injective_of_no_bad π r σ Δ Q hΔ hb)
  simp only [Fintype.card_coe] at hg
  have hl : 0 ≤ Real.log (Δ.card : ℝ) := Real.log_nonneg (by exact_mod_cast hΔne.card_pos)
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hprob 1) hl).trans hg

noncomputable def SplitSieve.meanLog (s : SplitSieve) : ℝ :=
  𝔼 i : Fin s.primes.card, Real.log (s.enumeration i : ℕ)

lemma SplitSieve.prefix_log_period (s : SplitSieve)
    (π : Equiv.Perm (Fin s.primes.card)) (r : ℕ) :
    Real.log ((s.prefixSieve π r).period : ℝ) =
      ∑ i ∈ prefixIndices s.primes.card r, Real.log (s.enumeration (π i) : ℕ) := by
  rw [SplitSieve.log_period]
  rw [Finset.sum_coe_sort (s.prefixSieve π r).primes (fun p : ℕ => Real.log (p : ℝ))]
  change (∑ p ∈ s.prefixSet π r, Real.log (p : ℝ)) = _
  unfold SplitSieve.prefixSet
  exact Finset.sum_image (Subtype.val_injective.comp
    (s.enumeration.injective.comp π.injective)).injOn

lemma SplitSieve.prefix_product_tail (s : SplitSieve) (hk : 0 < s.primes.card)
    {r : ℕ} (hr : r ≤ s.primes.card) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T) :
    (𝔼 π : Equiv.Perm (Fin s.primes.card),
      if Real.log ((s.prefixSieve π r).period : ℝ) < r*s.meanLog-δ then (1 : ℝ) else 0) ≤
      r*(Real.log 2)^2/δ^2 := by
  let : Nonempty (Fin s.primes.card) := ⟨⟨0,hk⟩⟩
  have hb (i : Fin s.primes.card) : Real.log T ≤ Real.log (s.enumeration i : ℕ) ∧
      Real.log (s.enumeration i : ℕ) ≤ Real.log T+Real.log 2 := by
    have hh := hpT (s.enumeration i) (s.enumeration i).property
    constructor
    · exact Real.log_le_log hT hh.1
    · have h := Real.log_le_log (hT.trans_le hh.1) hh.2
      rwa [Real.log_mul (by norm_num : (2 : ℝ)≠0) hT.ne',add_comm] at h
  have h := perm_sample_interval_tail (fun i => Real.log (s.enumeration i : ℕ))
    (prefixIndices s.primes.card r) hδ hb
  convert h using 1 <;>
    simp only [prefixIndices_card hr,SplitSieve.meanLog,← s.prefix_log_period]
  congr 1

theorem SplitSieve.signed_prefix_entropy (s : SplitSieve)
    {r : ℕ} (hr : r ≤ s.primes.card) (Δ : Finset GaussianInt) (hΔne : Δ.Nonempty)
    {T R W d δ : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log (R*W) ≤ (1-d)*(r*s.meanLog-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ orientedRectangle e R W) :
    let := hΔne.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card ≤
      (FinLaw.uniform Δ).signedEntropy (fun σ x => s.residueVector σ x) r := by
  let := hΔne.to_subtype
  have hk : 0 < s.primes.card := by
    by_contra hn
    have hz : r=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hlarge
    norm_num at hlarge
  have hRW : 0 < R*W := mul_pos (by linarith) (by linarith)
  have hlog : 0 ≤ Real.log (Δ.card : ℝ) := Real.log_nonneg (by exact_mod_cast hΔne.card_pos)
  let ε := Real.exp (-(d^3*r/5120))
  let bad (π : Equiv.Perm (Fin s.primes.card)) :=
    Real.log ((s.prefixSieve π r).period : ℝ) < r*s.meanLog-δ
  have hp (π : Equiv.Perm (Fin s.primes.card)) :
      (1-(if bad π then (1 : ℝ) else 0)-ε)*Real.log Δ.card ≤
      𝔼 σ : Fin s.primes.card → Bool,
        (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r) := by
    by_cases hb : bad π
    · have hn : 0 ≤ (𝔼 σ : Fin s.primes.card → Bool,
          (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => s.residueVector σ x) π r)) :=
        Finset.expect_nonneg (fun _ _ => (FinLaw.uniform Δ).Hf_nonneg _)
      simp only [hb,ite_eq_left,sub_self,zero_sub]
      exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hlog).trans hn
    · simp only [hb,ite_false,sub_zero]
      apply s.prefix_entropy_rectangle π hr Δ hΔne he hT hpT hW hWR hd hd1 ?_ hlarge hΔ
      have hP : 0 < ((s.prefixSieve π r).period : ℝ) := by
        exact_mod_cast (s.prefixSieve π r).period_pos
      apply (Real.log_le_log_iff hRW (Real.rpow_pos_of_pos hP _)).mp
      rw [Real.log_rpow hP]
      exact hgap.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hb) (by linarith))
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hp π)
  simp only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] at hav
  have hb := s.prefix_product_tail hk hr (by linarith : (0 : ℝ)<T) hδ hpT
  have hlow := mul_le_mul_of_nonneg_right (sub_le_sub_right (sub_le_sub_left hb 1) ε) hlog
  apply hlow.trans
  convert hav using 1
  unfold FinLaw.signedEntropy FinLaw.orderedEntropy
  exact Finset.expect_comm _ _ _

lemma SplitSieve.residueVector_entropy_le {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (P : FinLaw Ω) (Z : Ω → GaussianInt)
    (σ : Fin s.primes.card → Bool) (i : Fin s.primes.card) :
    P.Hf (fun ω => s.residueVector σ (Z ω) i) ≤ Real.log (s.enumeration i : ℕ) := by
  let π := signedFactor (s.factor (s.enumeration i)) (σ i)
  have hπ : π ≠ 0 := (signedFactor_irreducible
    (s.factor_irreducible _ (s.enumeration i).property) _).ne_zero
  obtain ⟨hfin,hcard⟩ := residueCode_range_card hπ
  have h := P.Hf_le_log_card_set (fun ω => residueCode π (Z ω)) hfin.toFinset
    (fun ω => hfin.mem_toFinset.mpr ⟨Z ω,rfl⟩)
  rw [← Set.ncard_eq_toFinset_card (Set.range (residueCode π)) hfin,hcard] at h
  have hn : π.norm.natAbs=(s.enumeration i : ℕ) := by
    dsimp [π]
    rw [signedFactor_norm,s.factor_norm _ (s.enumeration i).property,Int.natAbs_natCast]
  rw [hn] at h
  exact h

lemma SplitSieve.residue_prefix_entropy_le {Ω : Type uOmega} [Fintype Ω]
    (s : SplitSieve) (P : FinLaw Ω) (Z : Ω → GaussianInt)
    (σ : Fin s.primes.card → Bool) {b : ℕ} (hb : b ≤ s.primes.card)
    {U : ℝ} (hU : ∀ p ∈ s.primes, Real.log (p : ℝ) ≤ U) :
    P.orderedEntropy (fun ω => s.residueVector σ (Z ω)) b ≤ b*U := by
  have h (π : Equiv.Perm (Fin s.primes.card)) := P.Hf_prefix_le_sum
    (fun ω => s.residueVector σ (Z ω)) (fun _ => U)
    (fun i => (s.residueVector_entropy_le P Z σ i).trans
      (hU _ (s.enumeration i).property)) π hb
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun π _ => h π)
  simpa only [FinLaw.orderedEntropy,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Fintype.expect_const] using hh

theorem SplitSieve.actual_fresh_entropy (s : SplitSieve)
    {b r : ℕ} (hbr : b < r) (hr : r ≤ s.primes.card)
    (Δ : Finset GaussianInt) (hΔne : Δ.Nonempty)
    (X Y : Δ → GaussianInt) (hXY : ∀ ω, X ω-Y ω=ω)
    {T R W d δ : ℝ} {e : ℂ} (he : ‖e‖=1) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ s.primes, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log (R*W) ≤ (1-d)*(r*s.meanLog-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ orientedRectangle e R W) :
    let := hΔne.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card-
        2*b*Real.log (2*T) ≤
      (r-b : ℕ)*(𝔼 σ : Fin s.primes.card → Bool,
        𝔼 π : Equiv.Perm (Fin s.primes.card),
          (FinLaw.uniform Δ).cHf (fun ω => s.residueVector σ ω (π ⟨b,by omega⟩))
            (fun ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X x)) π b ω,
              FinLaw.prefixVar (fun x => s.residueVector σ (Y x)) π b ω))) := by
  let := hΔne.to_subtype
  let P := FinLaw.uniform Δ
  have hU (p : ℕ) (hp : p ∈ s.primes) : Real.log (p : ℝ) ≤ Real.log (2*T) :=
    Real.log_le_log (by have := (hpT p hp).1; linarith) (hpT p hp).2
  have hp (σ : Fin s.primes.card → Bool) := P.fresh_entropy_from_prefix
    (fun ω => s.residueVector σ (X ω)) (fun ω => s.residueVector σ (Y ω))
    (fun ω => s.residueVector σ ω) hbr hr (by
      intro i ω ν hx hy
      change residueCode _ (ω : GaussianInt) = residueCode _ (ν : GaussianInt)
      rw [← hXY ω,← hXY ν]
      exact residueCode_sub hx hy)
  have hX σ := s.residue_prefix_entropy_le P X σ (by omega : b ≤ s.primes.card) hU
  have hY σ := s.residue_prefix_entropy_le P Y σ (by omega : b ≤ s.primes.card) hU
  have hl (σ : Fin s.primes.card → Bool) :
      P.orderedEntropy (fun ω => s.residueVector σ ω) r-2*b*Real.log (2*T) ≤
      (r-b : ℕ)*(𝔼 π : Equiv.Perm (Fin s.primes.card),
        P.cHf (fun ω => s.residueVector σ ω (π ⟨b,by omega⟩))
          (fun ω => (FinLaw.prefixVar (fun x => s.residueVector σ (X x)) π b ω,
            FinLaw.prefixVar (fun x => s.residueVector σ (Y x)) π b ω))) := by
    linarith [hp σ,hX σ,hY σ]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hl σ)
  simp only [Finset.expect_sub_distrib,Fintype.expect_const,← Finset.mul_expect] at hh
  have hg := s.signed_prefix_entropy hr Δ hΔne he hT hpT hW hWR hd hd1 hδ hgap hlarge hΔ
  exact (sub_le_sub_right hg _).trans hh

end GaussianMoat

end OAI
