import OAI.NumberTheory.TotientAsymptotic.PPTTrivialFibers
import Mathlib.Logic.Equiv.Fin.Rotate

namespace OAI

/-!
The injective choice of nontrivial preimages used in Ford, Section 5,
p. 25, between (5.20) and (5.21).  Candidate sets are partitioned by their
totient value.  A singleton fiber uses its given nontrivial preimage; on a
larger fiber, a cyclic permutation followed by multiplication by a fixed
seed preimage supplies distinct nontrivial preimages.  The full fiber
multiplicity is retained throughout this construction.
-/

noncomputable section

namespace TotientAsymptotic

private lemma ppt_finRotate_ne_self {n : ℕ} (hn : 1 < n) (i : Fin n) :
    finRotate n i ≠ i := by
  cases n with
  | zero => omega
  | succ n =>
    intro he
    have hv := congrArg Fin.val he
    rw [coe_finRotate] at hv
    split_ifs at hv with hi
    · have hilast : (i : ℕ) = n := by rw [hi]; rfl
      omega
    · omega

private def pptFiniteRotation (α : Type*) [Fintype α] : Equiv.Perm α :=
  (Fintype.equivFin α).trans ((finRotate (Fintype.card α)).trans (Fintype.equivFin α).symm)

private lemma pptFiniteRotation_ne_self (α : Type*) [Fintype α]
    (hcard : 1 < Fintype.card α) (a : α) : pptFiniteRotation α a ≠ a := by
  intro he
  have he' := congrArg (Fintype.equivFin α) he
  have he'' : finRotate (Fintype.card α) (Fintype.equivFin α a) =
      Fintype.equivFin α a := by
    simpa only [pptFiniteRotation, Equiv.trans_apply, Equiv.apply_symm_apply] using he'
  exact ppt_finRotate_ne_self hcard _ he''

/-- Two rough candidates of the same totient cannot properly divide one
another.  The only alternative in the general totient lemma is doubling,
which roughness excludes. -/
lemma ppt_rough_eq_of_dvd_same_totient {d b c : ℕ} (hd : 0 < d)
    (hc : ∀ p : ℕ, p.Prime → p ∣ c → d+1 < p)
    (hφ : b.totient = c.totient) (hdiv : b ∣ c) : b = c := by
  apply (Nat.eq_or_eq_of_totient_eq_totient hdiv hφ).resolve_right
  intro hdouble
  have htwo : 2 ∣ c := by rw [← hdouble]; exact dvd_mul_right 2 b
  have hh := hc 2 Nat.prime_two htwo
  omega

lemma ppt_rough_eq_of_dvd_seed_multiple {d q b c : ℕ} (hd : 0 < d)
    (hq : q.totient = d)
    (hb : ∀ p : ℕ, p.Prime → p ∣ b → d+1 < p)
    (hc : ∀ p : ℕ, p.Prime → p ∣ c → d+1 < p)
    (hφ : b.totient = c.totient) (hdiv : b ∣ c*q) : b = c := by
  apply ppt_rough_eq_of_dvd_same_totient hd hc hφ
  exact (seed_preimage_coprime hd hq hb).dvd_mul_right.mp hdiv

private lemma ppt_bad_witness_on_fiber {d q v : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient = d) (T : Finset ℕ)
    (hT : ∀ n ∈ T, 0 < n ∧ n.totient = v ∧
      ∀ p : ℕ, p.Prime → p ∣ n → d+1 < p)
    (hbad : ∀ n ∈ T, ∃ u : ℕ, 0 < u ∧ u.totient = d*n.totient ∧ ¬n ∣ u) :
    ∃ F : ℕ → ℕ, Set.InjOn F (T : Set ℕ) ∧
      ∀ n ∈ T, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n ∧
        (1 < T.card → ∃ c ∈ T, F n = c*q) := by
  classical
  by_cases hcard : 1 < T.card
  · let σ := pptFiniteRotation ↥T
    let F : ℕ → ℕ := fun n => if hn : n ∈ T then (σ ⟨n, hn⟩).val*q else 0
    have hσ (n : ↥T) : (σ n).val ≠ n.val := by
      intro he
      apply pptFiniteRotation_ne_self ↥T (by simpa using hcard) n
      exact Subtype.ext he
    have hF (n : ℕ) (hn : n ∈ T) : F n = (σ ⟨n, hn⟩).val*q := by
      simp only [F, dite_eq_left hn]
    refine ⟨F, ?_, ?_⟩
    · intro n hn m hm he
      change n ∈ T at hn
      change m ∈ T at hm
      have he' : (σ ⟨n, hn⟩).val*q = (σ ⟨m, hm⟩).val*q := by
        simpa only [hF n hn, hF m hm] using he
      have he'' := Nat.eq_of_mul_eq_mul_right hqpos he'
      have hs : σ ⟨n, hn⟩ = σ ⟨m, hm⟩ := Subtype.ext he''
      exact congrArg Subtype.val (σ.injective hs)
    · intro n hn
      let c := σ ⟨n, hn⟩
      have hc := hT c.val c.property
      have hn' := hT n hn
      have hcn : c.val.totient = n.totient := hc.2.1.trans hn'.2.1.symm
      have hnF : F n = c.val*q := hF n hn
      rw [hnF]
      refine ⟨Nat.mul_pos hc.1 hqpos, ?_, ?_, ?_⟩
      · rw [seed_multiple_totient hd hq hc.2.2, hcn]
      · intro hdiv
        have he := ppt_rough_eq_of_dvd_seed_multiple hd hq hn'.2.2 hc.2.2 hcn.symm hdiv
        exact hσ ⟨n, hn⟩ he.symm
      · intro _
        exact ⟨c.val, c.property, rfl⟩
  · let F : ℕ → ℕ := fun n => if hn : n ∈ T then Classical.choose (hbad n hn) else 0
    have hsmall : T.card ≤ 1 := Nat.le_of_not_gt hcard
    refine ⟨F, ?_, ?_⟩
    · intro n hn m hm _
      exact Finset.card_le_one.mp hsmall n hn m hm
    · intro n hn
      have hb := Classical.choose_spec (hbad n hn)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [F, dite_eq_left hn] using hb.1
      · simpa only [F, dite_eq_left hn] using hb.2.1
      · simpa only [F, dite_eq_left hn] using hb.2.2
      · intro hc
        omega

/-- The injective association retains its seed-multiple construction on
every nonsingleton totient fiber. This is needed for normality exclusion. -/
theorem ppt_injective_bad_preimages_seed_branch {d q : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient = d) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → d+1 < p)
    (hbad : ∀ n ∈ S, ∃ u : ℕ, 0 < u ∧ u.totient = d*n.totient ∧ ¬n ∣ u) :
    ∃ F : ℕ → ℕ, Set.InjOn F (S : Set ℕ) ∧
      (∀ n ∈ S, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n) ∧
      ∀ n ∈ S, (∃ m ∈ S, m ≠ n ∧ m.totient = n.totient) →
        ∃ c ∈ S, F n = c*q := by
  classical
  let T : ℕ → Finset ℕ := fun v => S.filter (fun n => n.totient = v)
  have hex (v : ℕ) : ∃ F : ℕ → ℕ, Set.InjOn F (T v : Set ℕ) ∧
      ∀ n ∈ T v, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n ∧
        (1 < (T v).card → ∃ c ∈ T v, F n = c*q) := by
    apply ppt_bad_witness_on_fiber hd hqpos hq (T v)
    · intro n hn
      have hh := Finset.mem_filter.mp hn
      exact ⟨(hS n hh.1).1, hh.2, (hS n hh.1).2⟩
    · intro n hn
      exact hbad n (Finset.mem_filter.mp hn).1
  choose F hFinj hFprop using hex
  let G : ℕ → ℕ := fun n => F n.totient n
  have hmem (n : ℕ) (hn : n ∈ S) : n ∈ T n.totient := Finset.mem_filter.mpr ⟨hn, rfl⟩
  have hG (n : ℕ) (hn : n ∈ S) :
      0 < G n ∧ (G n).totient = d*n.totient ∧ ¬n ∣ G n := by
    have hh := hFprop n.totient n (hmem n hn)
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  refine ⟨G, ?_, hG, ?_⟩
  · intro n hn m hm he
    have hscaled : d*n.totient = d*m.totient :=
      (hG n hn).2.1.symm.trans ((congrArg Nat.totient he).trans (hG m hm).2.1)
    have hv : n.totient = m.totient := Nat.eq_of_mul_eq_mul_left hd hscaled
    apply hFinj n.totient (hmem n hn) (Finset.mem_filter.mpr ⟨hm, hv.symm⟩)
    change F n.totient n = F m.totient m at he
    simpa only [← hv] using he
  · intro n hn hmulti
    obtain ⟨m, hm, hmn, hφ⟩ := hmulti
    have hmT : m ∈ T n.totient := Finset.mem_filter.mpr ⟨hm, hφ⟩
    have hc : 1 < (T n.totient).card := by
      by_contra hsmall
      have hcard : (T n.totient).card ≤ 1 := Nat.le_of_not_gt hsmall
      exact hmn (Finset.card_le_one.mp hcard m hmT n (hmem n hn))
    obtain ⟨c, hcT, hcF⟩ := (hFprop n.totient n (hmem n hn)).2.2.2 hc
    exact ⟨c, (Finset.mem_filter.mp hcT).1, hcF⟩

/-- The bad-preimage association is injective even when many candidates
share one totient.  No injectivity of the totient function is assumed. -/
theorem ppt_injective_bad_preimages {d q : ℕ} (hd : 0 < d)
    (hqpos : 0 < q) (hq : q.totient = d) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → d+1 < p)
    (hbad : ∀ n ∈ S, ∃ u : ℕ, 0 < u ∧ u.totient = d*n.totient ∧ ¬n ∣ u) :
    ∃ F : ℕ → ℕ, Set.InjOn F (S : Set ℕ) ∧
      ∀ n ∈ S, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n := by
  obtain ⟨F, hF, hprop, _⟩ :=
    ppt_injective_bad_preimages_seed_branch hd hqpos hq S hS hbad
  exact ⟨F, hF, hprop⟩

/-- In particular, all failed candidates can be counted by distinct
nontrivial target preimages.  The only arithmetic hypothesis on the seed
is that it is a positive totient. -/
theorem ppt_injective_failed_candidates {d : ℕ} (hd : IsTotient d) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → d+1 < p)
    (hbad : ∀ n ∈ S, ¬FullFiber d n) :
    ∃ F : ℕ → ℕ, Set.InjOn F (S : Set ℕ) ∧
      ∀ n ∈ S, 0 < F n ∧ (F n).totient = d*n.totient ∧ ¬n ∣ F n := by
  obtain ⟨q, hqpos, hq⟩ := hd
  have hdpos : 0 < d := hq ▸ Nat.totient_pos.mpr hqpos
  apply ppt_injective_bad_preimages hdpos hqpos hq S hS
  intro n hn
  have hnot : ¬ ∀ u : ℕ, 0 < u → u.totient = d*n.totient → n ∣ u := by
    intro hall
    exact hbad n hn ((fullFiber_iff_all_preimages_dvd hdpos (hS n hn).1
      (hS n hn).2).mpr hall)
  push Not at hnot
  exact hnot

end TotientAsymptotic

end

end OAI
