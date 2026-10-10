import OAI.Combinatorics.PolynomialVacuum.Algebra.KillSite
import OAI.Combinatorics.PolynomialVacuum.Algebra.SpectatorDegree

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem killSite_exchange_carried {ι : Type*} (j : ι) (x y : MvPolynomial ι ℂ)
    (hx : killSite j x=0) (a b : Pair) (h : charge a.2 < charge b.1) :
    killSite j (polyExchangeNumerator x y a b)=0 := by
  rw [polyExchange_split]
  simp only [map_add,map_mul,map_pow,killSite_C,hx,zero_pow (by decide : 2≠0),zero_mul,zero_add,
    exchange_zero_carried a b h,map_zero,mul_zero]

theorem killSite_exchange_spectator {ι : Type*} (j : ι) (x y : MvPolynomial ι ℂ)
    (hy : killSite j y=0) (a b : Pair) (h : charge a.1 < charge b.2) :
    killSite j (polyExchangeNumerator x y a b)=0 := by
  rw [polyExchange_split]
  simp only [map_add,map_mul,map_pow,killSite_C,hy,zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero,
    exchange_zero_spectator a b h,map_zero]

theorem tensorExchange_carried_zero {N : ℕ} {ι : Type*}
    (a b mark : Fin N) (hab : a≠b) (hma : mark≠a) (hmb : mark≠b)
    (x y : MvPolynomial ι ℂ) (j : ι) (W : PolynomialTensor N ι)
    (hx : killSite j x=0)
    (hf : ∀ s, s mark=Spin.minus → charge (s a)<1 → killSite j (W s)=0)
    (s : Fin N → Spin) (hm : s mark=Spin.minus) (hb : charge (s b)<1) :
    killSite j (tensorExchange a b x y W s)=0 := by
  simp only [tensorExchange,map_sum,map_mul]
  apply Finset.sum_eq_zero
  intro ab _
  change killSite j (polyExchangeNumerator x y (s a,s b) ab) *
    killSite j (W (replacePair s a b ab))=0
  by_cases ht : charge ab.1<1
  · rw [hf _ (by simpa only [replacePair_other s hma hmb] using hm)
      (by simpa only [replacePair_left s hab] using ht),mul_zero]
  · have hl : charge (s b)<charge ab.1 := by omega
    rw [killSite_exchange_carried j x y hx _ ab hl,zero_mul]

theorem transportCup_marked_zero {n : ℕ} (i : Fin (n+1))
    (ks : List (Fin (n+1))) (c e : Fin (n+2)) (hp : CarriedPath c ks e)
    (hks : ∀ k ∈ ks, i<k) (W : PolynomialTensor (n+2) (Fin (n+1)))
    (hf : ∀ s, s (pairLeft i)=Spin.minus → charge (s c)<1 → killSite i (W s)=0) :
    ∀ s, s (pairLeft i)=Spin.minus → charge (s e)<1 →
      killSite i (transportCup i ks W s)=0 := by
  induction ks generalizing W c with
  | nil =>
    simp only [CarriedPath] at hp
    subst e
    simpa [transportCup] using hf
  | cons k ks ih =>
    obtain ⟨rfl,hp⟩:=hp
    have hik : i<k := hks k (by simp)
    have hab : pairLeft k≠pairRight k := by intro h; have:=congrArg Fin.val h; simp [pairLeft,pairRight] at this
    have hma : pairLeft i≠pairLeft k := fun h => ne_of_lt hik (Fin.castSucc_injective _ h)
    have hmb : pairLeft i≠pairRight k := by
      intro h; have:=congrArg Fin.val h
      simp only [pairLeft,pairRight,Fin.val_castSucc,Fin.val_succ] at this
      have hh : i.val<k.val := hik
      omega
    exact ih (pairRight k) hp (fun l hl => hks l (by simp [hl]))
      (tensorExchange (pairLeft k) (pairRight k) (C T*X i) (X k) W)
      (fun s hm hs => tensorExchange_carried_zero _ _ _ hab hma hmb _ _ i W (by simp) hf s hm hs)

theorem dividedCupPrescription_marked_zero {n : ℕ} (ψ : State n) (i : Fin (n+1))
    (s : Fin (n+2) → Spin) (hm : s (pairLeft i)=Spin.minus)
    (hl : s (Fin.last (n+1))≠Spin.plus) : killSite i (dividedCupPrescription ψ i s)=0 := by
  have hz (v : Fin (n+2) → Spin) (hv : v (pairLeft i)=Spin.minus)
      (hc : charge (v (pairRight i))<1) : killSite i (initialCup ψ i v)=0 := by
    have hcup : cup (v (pairLeft i),v (pairRight i))=0 := by
      rw [hv]; cases hh : v (pairRight i) <;> simp_all [cup,charge]
    simp [initialCup,hcup]
  have ht := transportCup_marked_zero i (rightSpectators i) _ _ (rightSpectators_path i)
    (by intro k hk; simpa [rightSpectators] using (List.mem_filter.mp hk).2) (initialCup ψ i) hz
  have hc : charge (s (Fin.last (n+1)))<1 := by cases h : s (Fin.last (n+1)) <;> simp_all [charge]
  simp only [dividedCupPrescription,map_mul,ht s hm hc,mul_zero]

theorem tensorExchange_spectator_zero {N : ℕ} {ι : Type*}
    (a b : Fin N) (x y : MvPolynomial ι ℂ) (j : ι) (W : PolynomialTensor N ι)
    (hy : killSite j y=0)
    (hf : ∀ s, s b=Spin.minus → killSite j (W s)=0)
    (s : Fin N → Spin) (hs : s a=Spin.minus) : killSite j (tensorExchange a b x y W s)=0 := by
  simp only [tensorExchange,map_sum,map_mul]
  apply Finset.sum_eq_zero
  intro ab _
  change killSite j (polyExchangeNumerator x y (s a,s b) ab) *
    killSite j (W (replacePair s a b ab))=0
  by_cases ht : ab.2=Spin.minus
  · rw [hf _ (by simpa only [replacePair_right] using ht),mul_zero]
  · have hl : charge (s a)<charge ab.2 := by rw [hs]; cases hh : ab.2 <;> simp_all [charge]
    rw [killSite_exchange_spectator j x y hy _ ab hl,zero_mul]

theorem tensorExchange_unaffected_zero {N : ℕ} {ι : Type*}
    (a b mark : Fin N) (hma : mark≠a) (hmb : mark≠b)
    (x y : MvPolynomial ι ℂ) (j : ι) (W : PolynomialTensor N ι)
    (hf : ∀ s, s mark=Spin.minus → killSite j (W s)=0)
    (s : Fin N → Spin) (hs : s mark=Spin.minus) : killSite j (tensorExchange a b x y W s)=0 := by
  simp only [tensorExchange,map_sum,map_mul]
  apply Finset.sum_eq_zero
  intro ab _
  change killSite j (polyExchangeNumerator x y (s a,s b) ab) *
    killSite j (W (replacePair s a b ab))=0
  rw [hf _ (by simpa only [replacePair_other s hma hmb] using hs),mul_zero]

theorem transportCup_spectator_zero {n : ℕ} (i j : Fin (n+1))
    (ks : List (Fin (n+1))) (c e : Fin (n+2)) (hp : CarriedPath c ks e)
    (W : PolynomialTensor (n+2) (Fin (n+1)))
    (hf : ∀ s, s (spectatorSlot j c)=Spin.minus → killSite j (W s)=0) :
    ∀ s, s (spectatorSlot j e)=Spin.minus → killSite j (transportCup i ks W s)=0 := by
  induction ks generalizing W c with
  | nil =>
    simp only [CarriedPath] at hp
    subst e
    simpa [transportCup] using hf
  | cons k ks ih =>
    obtain ⟨rfl,hp⟩:=hp
    apply ih (pairRight k) hp
    intro s hs
    by_cases hjk : j=k
    · subst k
      simp only [spectatorSlot_self_right] at hs
      simp only [spectatorSlot_self_left] at hf
      exact tensorExchange_spectator_zero _ _ _ _ j W (by simp) hf s hs
    · obtain ⟨he,ha,hb⟩:=spectatorSlot_other hjk
      exact tensorExchange_unaffected_zero _ _ _ ha hb _ _ j W hf s (he ▸ hs)

end PolynomialVacuumAlgebra

end OAI
