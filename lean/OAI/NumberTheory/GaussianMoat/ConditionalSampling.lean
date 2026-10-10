import OAI.NumberTheory.GaussianMoat.PrimeMass

namespace OAI

universe uOmega uAlpha uBeta uGamma uIota uDelta

namespace GaussianMoat
open Filter Topology Finset

namespace FinLaw
open scoped BigOperators
variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] {k : ℕ}

theorem cHf_eq_of_fibers {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (C : Ω → γ)
    (h : ∀ ω ν, C ω = C ν → (X ω = X ν ↔ Y ω = Y ν)) :
    p.cHf X C = p.cHf Y C := by
  unfold cHf
  congr 1
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq]
  constructor <;> intro hh
  · exact ⟨(h ω ν hh.2).mp hh.1,hh.2⟩
  · exact ⟨(h ω ν hh.2).mpr hh.1,hh.2⟩

theorem cHf_le_of_determined {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (C : Ω → γ)
    (h : ∀ ω ν, Y ω = Y ν → C ω = C ν → X ω = X ν) :
    p.cHf X C ≤ p.cHf Y C := by
  apply sub_le_sub_right
  apply p.Hf_le_of_determined
  intro ω ν hh
  rcases Prod.mk.inj hh with ⟨hy,hc⟩
  exact Prod.ext (h ω ν hy hc) hc

theorem cHf_finset_subadd {ι : Type uIota} {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → ι → α) (C : Ω → β) (S : Finset ι) :
    p.cHf (fun ω (i : S) => X ω i) C ≤ ∑ i ∈ S, p.cHf (fun ω => X ω i) C := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : p.cHf (fun ω (i : (∅:Finset ι)) => X ω i) C = p.cHf (fun _ => ()) C := by
      apply p.cHf_eq_of_fibers
      intro ω ν _
      simp only [iff_true]
      funext i
      exact False.elim (Finset.notMem_empty i.val i.property)
    have hc : p.cHf (fun _ => ()) C = 0 := by
      unfold cHf
      have hh := p.Hf_eq_of_fibers (fun ω => ((),C ω)) C (fun _ _ => by simp)
      rw [hh,sub_self]
    simp [he,hc]
  | @insert i S hi ih =>
    have he : p.cHf (fun ω (j : (insert i S : Finset ι)) => X ω j) C =
        p.cHf (fun ω => (X ω i,fun j : S => X ω j)) C := by
      apply p.cHf_eq_of_fibers
      intro ω ν _
      constructor
      · intro h
        apply Prod.ext
        · exact congrFun h ⟨i,Finset.mem_insert_self _ _⟩
        · funext j; exact congrFun h ⟨j,Finset.mem_insert_of_mem j.property⟩
      · intro h
        funext j
        rcases Finset.mem_insert.mp j.property with hj | hj
        · simpa [hj] using congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) ⟨j,hj⟩
    rw [he,Finset.sum_insert hi]
    have hh := p.cHf_pair_subadd (fun ω => X ω i) (fun ω (j : S) => X ω j) C
    linarith

theorem cHf_fintype_subadd {ι : Type uIota} {β : Type uBeta} [Fintype ι] (p : FinLaw Ω)
    (X : Ω → ι → α) (C : Ω → β) :
    p.cHf X C ≤ ∑ i, p.cHf (fun ω => X ω i) C := by
  have h := p.cHf_finset_subadd X C Finset.univ
  have he : p.cHf (fun ω (i : (Finset.univ : Finset ι)) => X ω i) C = p.cHf X C := by
    apply p.cHf_eq_of_fibers
    intro ω ν _
    exact ⟨fun hh => funext (fun i => congrFun hh ⟨i,Finset.mem_univ i⟩),
      fun hh => funext (fun i => congrFun hh i)⟩
  rwa [he] at h

omit [Fintype Ω] in

theorem prefixVar_swap (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (s : ℕ)
    (i j : Fin k) (hi : s ≤ i.val) (hj : s ≤ j.val) :
    prefixVar X (π*Equiv.swap i j) s = prefixVar X π s := by
  classical
  funext ω a
  by_cases ha : a.val<s
  · have hai : a≠i := by intro he; subst a; omega
    have haj : a≠j := by intro he; subst a; omega
    simp [prefixVar,ha,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hai haj]
  · simp [prefixVar,ha]

theorem ordered_remaining_exchange_cond {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → Fin k → α) (C : Equiv.Perm (Fin k) → Ω → β)
    (i j : Fin k) (hC : ∀ π, C (π*Equiv.swap i j) = C π) :
    (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π i)) (C π)) =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π j)) (C π) := by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  change p.cHf (fun ω => X ω (π i)) (C π) =
    p.cHf (fun ω => X ω ((π*Equiv.swap i j) j)) (C (π*Equiv.swap i j))
  rw [hC]
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]

theorem prefix_conditional_block {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (C : Ω → β)
    {b q : ℕ} (hbq : b ≤ q) (hq : q ≤ k)
    (hC : ∀ ω ν, C ω = C ν → prefixVar X π b ω = prefixVar X π b ν) :
    p.cHf (prefixVar X π q) C ≤
      ∑ j : Fin (q-b), p.cHf (fun ω => X ω (π ⟨b+j.val,by omega⟩)) C := by
  let R := fun ω (j : Fin (q-b)) => X ω (π ⟨b+j.val,by omega⟩)
  apply (p.cHf_le_of_determined (prefixVar X π q) R C ?_).trans
    (p.cHf_fintype_subadd R C)
  intro ω ν hR hcond
  funext i
  by_cases hi : i.val < b
  · have h := congrFun (hC ω ν hcond) i
    simpa [prefixVar,hi,show i.val<q by omega] using h
  by_cases hiq : i.val < q
  · have h := congrFun hR ⟨i.val-b,by omega⟩
    have hidx : (⟨b+(i.val-b), by omega⟩ : Fin k) = i := by
      apply Fin.ext
      change b+(i.val-b)=i.val
      omega
    simpa only [R,hidx,prefixVar,hiq,ite_eq_left] using congrArg some h
  · simp [prefixVar,hiq]

theorem ordered_prefix_conditional_bound {β : Type uBeta} (p : FinLaw Ω)
    (X : Ω → Fin k → α) (C : Equiv.Perm (Fin k) → Ω → β)
    {b q : ℕ} (hbq : b < q) (hq : q ≤ k)
    (hC : ∀ π ω ν, C π ω = C π ν → prefixVar X π b ω = prefixVar X π b ν)
    (hswap : ∀ π (j : Fin k), b ≤ j.val →
      C (π*Equiv.swap ⟨b,by omega⟩ j) = C π) :
    (𝔼 π : Equiv.Perm (Fin k), p.cHf (prefixVar X π q) (C π)) ≤
      (q-b : ℕ) * (𝔼 π : Equiv.Perm (Fin k),
        p.cHf (fun ω => X ω (π ⟨b,by omega⟩)) (C π)) := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
    p.prefix_conditional_block X π (C π) hbq.le hq (hC π))
  rw [Finset.expect_sum_comm] at h
  have he (j : Fin (q-b)) :
      (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨b+j.val,by omega⟩)) (C π)) =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨b,by omega⟩)) (C π) := by
    exact (p.ordered_remaining_exchange_cond X C ⟨b,by omega⟩ ⟨b+j.val,by omega⟩
      (fun π => hswap π _ (by change b ≤ b+j.val; omega))).symm
  simpa only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

theorem ordered_enrichment_accounting {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} (p : FinLaw Ω)
    (X Y Z : Ω → Fin k → α) (d : Ω → Fin k → β) (H : Ω → γ) (E : Ω → δ)
    {b q : ℕ} (hb : 0 < b) (hbq : b < q) (hq : q ≤ k)
    (hd : ∀ i ω ν, X ω i = X ν i → Y ω i = Y ν i → d ω i = d ν i)
    (hY : ∀ i ω ν, X ω i = X ν i → d ω i = d ν i → Y ω i = Y ν i)
    (hH : ∀ i ω ν, H ω = H ν → d ω i = d ν i)
    (hZ : ∀ i ω ν, X ω i = X ν i → E ω = E ν → Z ω i = Z ν i) :
    (b : ℝ) * ((q-b : ℕ) *
      (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => d ω (π ⟨b,by omega⟩))
        (fun ω => (prefixVar X π b ω,prefixVar Y π b ω))) +
      p.orderedEntropy Z q-p.Hf H-p.Hf E) ≤
      (q : ℝ)*(p.orderedEntropy X b+p.orderedEntropy Y b) := by
  let C := fun (π : Equiv.Perm (Fin k)) ω =>
    ((prefixVar X π b ω,prefixVar Y π b ω),H ω)
  let A := 𝔼 π : Equiv.Perm (Fin k),
    p.cHf (fun ω => X ω (π ⟨b,by omega⟩)) (C π)
  let F := 𝔼 π : Equiv.Perm (Fin k),
    p.cHf (fun ω => d ω (π ⟨b,by omega⟩))
      (fun ω => (prefixVar X π b ω,prefixVar Y π b ω))
  have hblock := p.ordered_prefix_conditional_bound X C hbq hq
    (fun π ω ν hh => congrArg (fun c => c.1.1) hh) (by
      intro π j hj
      dsimp [C]
      rw [prefixVar_swap X π b _ j (by exact le_rfl) hj,
        prefixVar_swap Y π b _ j (by exact le_rfl) hj])
  have hlow (π : Equiv.Perm (Fin k)) :
      p.Hf (prefixVar Z π q)-p.Hf E-p.Hf (prefixVar X π b)-
        p.Hf (prefixVar Y π b)-p.Hf H ≤ p.cHf (prefixVar X π q) (C π) := by
    have hz : p.Hf (prefixVar Z π q) ≤ p.Hf (prefixVar X π q)+p.Hf E := by
      apply (p.Hf_le_of_determined (prefixVar Z π q)
        (fun ω => (prefixVar X π q ω,E ω)) ?_).trans (p.Hf_pair_subadd _ _)
      intro ω ν hh
      funext i
      by_cases hi : i.val<q
      · have hx : X ω (π i)=X ν (π i) := by
          simpa [prefixVar,hi] using congrFun (congrArg Prod.fst hh) i
        simpa only [prefixVar,hi,ite_eq_left] using congrArg some
          (hZ (π i) ω ν hx (congrArg Prod.snd hh))
      · simp [prefixVar,hi]
    have hc : p.Hf (C π) ≤ p.Hf (prefixVar X π b)+p.Hf (prefixVar Y π b)+p.Hf H := by
      have h1 := p.Hf_pair_subadd (fun ω => (prefixVar X π b ω,prefixVar Y π b ω)) H
      have h2 := p.Hf_pair_subadd (prefixVar X π b) (prefixVar Y π b)
      dsimp [C]
      linarith
    have hx := p.Hf_pair_ge_snd (C π) (prefixVar X π q)
    rw [p.Hf_pair_comm] at hx
    unfold cHf
    linarith
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hlow π)
  simp only [Finset.expect_sub_distrib,Fintype.expect_const] at hav
  have hal : p.orderedEntropy Z q-p.Hf E-p.orderedEntropy X b-
      p.orderedEntropy Y b-p.Hf H ≤ (q-b : ℕ)*A := hav.trans hblock
  have hchain := Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
    p.enrichment_chain (fun ω => X ω (π ⟨b,by omega⟩)) (fun ω => Y ω (π ⟨b,by omega⟩))
      (prefixVar X π b) (prefixVar Y π b) (fun ω => d ω (π ⟨b,by omega⟩)) H
      (hd _) (hY _) (hH _))
  simp only [Finset.expect_sub_distrib,Finset.expect_add_distrib] at hchain
  have hchain' : F ≤ (p.orderedEntropy X (b+1)-p.orderedEntropy X b)+
      (p.orderedEntropy Y (b+1)-p.orderedEntropy Y b)-A := by
    rwa [p.orderedEntropy_step X (by omega),p.orderedEntropy_step Y (by omega)]
  have hx := p.orderedEntropy_slope X hb (by omega)
  have hy := p.orderedEntropy_slope Y hb (by omega)
  have haux : A+F ≤ (p.orderedEntropy X b+p.orderedEntropy Y b)/b := by
    rw [add_div]
    linarith
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have hqR : (0 : ℝ)≤(q-b : ℕ) := by positivity
  have hm := mul_le_mul_of_nonneg_left haux hqR
  have hbmul := mul_le_mul_of_nonneg_left hm hbR.le
  have hn : ((q-b : ℕ) : ℝ) = q-b := by rw [Nat.cast_sub hbq.le]
  have hdiv : (b : ℝ)*((q-b : ℕ)*((p.orderedEntropy X b+p.orderedEntropy Y b)/b)) =
      (q-b : ℕ)*(p.orderedEntropy X b+p.orderedEntropy Y b) := by field_simp
  rw [hdiv] at hbmul
  have hlowmul := mul_le_mul_of_nonneg_left hal hbR.le
  change (b : ℝ)*((q-b : ℕ)*F+p.orderedEntropy Z q-p.Hf H-p.Hf E) ≤ _
  rw [hn] at hbmul hlowmul ⊢
  nlinarith

end FinLaw

open scoped BigOperators

lemma perm_expect_exchange {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i j : ι) :
    (𝔼 π : Equiv.Perm ι, f (π i)) = 𝔼 π : Equiv.Perm ι, f (π j) := by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  change f (π i) = f ((π*Equiv.swap i j) j)
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]

theorem perm_covariance_nonpos {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∑ i, f i = 0) {i j : ι} (hij : i ≠ j) :
    (𝔼 π : Equiv.Perm ι, f (π i)*f (π j)) ≤ 0 := by
  classical
  let S := Finset.univ.erase i
  have hS : S.Nonempty := ⟨j,Finset.mem_erase.mpr ⟨hij.symm,Finset.mem_univ _⟩⟩
  have hex (a : ι) (ha : a ∈ S) :
      (𝔼 π : Equiv.Perm ι, f (π i)*f (π a)) =
        𝔼 π : Equiv.Perm ι, f (π i)*f (π j) := by
    have hai : i ≠ a := (Finset.mem_erase.mp ha).1.symm
    apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap a j))
    intro π
    change f (π i)*f (π a) = f ((π*Equiv.swap a j) i)*f ((π*Equiv.swap a j) j)
    simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hai hij]
  have hsum (π : Equiv.Perm ι) : (∑ a ∈ S, f (π a)) = -f (π i) := by
    have h := Equiv.sum_comp π f
    rw [hf] at h
    have hi := Finset.sum_erase_add (s := Finset.univ) (f := fun a => f (π a))
      (Finset.mem_univ i)
    dsimp [S]
    linarith
  have hid : (S.card : ℝ)*(𝔼 π : Equiv.Perm ι, f (π i)*f (π j)) =
      -(𝔼 π : Equiv.Perm ι, f (π i)^2) := by
    calc
      _ = ∑ a ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π a)) := by
        rw [show (∑ a ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π a))) =
            ∑ _a ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π j)) from
              Finset.sum_congr rfl (fun a ha => hex a ha)]
        simp [nsmul_eq_mul]
      _ = 𝔼 π : Equiv.Perm ι, ∑ a ∈ S, f (π i)*f (π a) :=
        (Finset.expect_sum_comm _ _ _).symm
      _ = -(𝔼 π : Equiv.Perm ι, f (π i)^2) := by
        simp_rw [← Finset.mul_sum,hsum,mul_neg,← sq]
        rw [Finset.expect_neg_distrib]
  have hvar : 0 ≤ (𝔼 π : Equiv.Perm ι, f (π i)^2) :=
    Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  nlinarith

theorem perm_sample_second_moment {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∑ i, f i = 0) (S : Finset ι) {M : ℝ} (hM : ∀ i, (f i)^2 ≤ M) :
    (𝔼 π : Equiv.Perm ι, (∑ i ∈ S, f (π i))^2) ≤ S.card*M := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hsqr (π : Equiv.Perm ι) : (∑ j ∈ insert i S, f (π j))^2 =
        (f (π i))^2+(∑ j ∈ S, f (π j))^2+2*(∑ j ∈ S, f (π i)*f (π j)) := by
      rw [Finset.sum_insert hi,← Finset.mul_sum]
      ring
    simp_rw [hsqr,Finset.expect_add_distrib,← Finset.mul_expect,Finset.expect_sum_comm]
    have hb : (𝔼 π : Equiv.Perm ι, f (π i)^2) ≤ M :=
      (Finset.expect_le_expect (s := Finset.univ) (fun π _ => hM (π i))).trans_eq
        (Fintype.expect_const _)
    have hc : (∑ j ∈ S, (𝔼 π : Equiv.Perm ι, f (π i)*f (π j))) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      exact perm_covariance_nonpos f hf (fun he => hi (he.symm ▸ hj))
    rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]
    nlinarith

theorem expect_lower_tail_le {Ω : Type uOmega} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) {a δ V : ℝ} (hδ : 0 < δ)
    (hV : (𝔼 ω, (Z ω-a)^2) ≤ V) :
    (𝔼 ω, if Z ω < a-δ then (1 : ℝ) else 0) ≤ V/δ^2 := by
  classical
  have he : ∀ ω, δ^2*(if Z ω < a-δ then (1 : ℝ) else 0) ≤ (Z ω-a)^2 := by
    intro ω
    split_ifs with hh
    · nlinarith
    · simpa using sq_nonneg (Z ω-a)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun ω _ => he ω)
  rw [← Finset.mul_expect] at h
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by nlinarith)

theorem perm_sample_interval_tail {ι : Type uIota} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → ℝ) (S : Finset ι) {a M δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ i, a ≤ f i ∧ f i ≤ a+M) :
    (𝔼 π : Equiv.Perm ι,
      if (∑ i ∈ S, f (π i)) < S.card*(𝔼 i, f i)-δ then (1 : ℝ) else 0) ≤
      S.card*M^2/δ^2 := by
  let μ := 𝔼 i, f i
  have hlo : a ≤ μ := by
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hf i).1)
    simpa only [Fintype.expect_const] using h
  have hhi : μ ≤ a+M := by
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hf i).2)
    simpa only [Fintype.expect_const] using h
  have hsum : ∑ i, (f i-μ) = 0 := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [show (Fintype.card ι : ℝ)*μ = ∑ i, f i from Fintype.card_mul_expect f]
    ring
  have hsq (i : ι) : (f i-μ)^2 ≤ M^2 := by
    have h := hf i
    nlinarith
  have hvar := perm_sample_second_moment (fun i => f i-μ) hsum S hsq
  have hid (π : Equiv.Perm ι) : (∑ i ∈ S, (f (π i)-μ)) =
      (∑ i ∈ S, f (π i))-S.card*μ := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  simp_rw [hid] at hvar
  exact expect_lower_tail_le _ hδ hvar

namespace FinLaw
open scoped BigOperators
variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] {k : ℕ}

noncomputable def uniform (Ω : Type uOmega) [Fintype Ω] [Nonempty Ω] : FinLaw Ω where
  mass := fun _ => (Fintype.card Ω : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_one := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω).ne')

@[simp] theorem uniform_mass [Nonempty Ω] (ω : Ω) :
    uniform Ω ω = (Fintype.card Ω : ℝ)⁻¹ := rfl

theorem uniform_Hf_injective {β : Type uBeta} [Nonempty Ω] (X : Ω → β)
    (hX : Function.Injective X) : (uniform Ω).Hf X = Real.log (Fintype.card Ω) := by
  classical
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω).ne'
  unfold Hf
  simp only [hX.eq_iff,uniform_mass,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Real.log_inv]
  rw [← mul_assoc,mul_inv_cancel₀ hN]
  ring

theorem Hf_le_log_card_type {β : Type uBeta} [Fintype β] (p : FinLaw Ω) (X : Ω → β) :
    p.Hf X ≤ Real.log (Fintype.card β) := by
  rw [p.Hf_eq_H]
  exact (p.map X).entropy_le_log_card

theorem Hf_le_log_card_set {β : Type uBeta} (p : FinLaw Ω) (X : Ω → β)
    (S : Finset β) (hX : ∀ ω, X ω ∈ S) : p.Hf X ≤ Real.log S.card := by
  classical
  let Y := fun ω => (⟨X ω,hX ω⟩ : S)
  have he : p.Hf X = p.Hf Y := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [he]
  simpa using p.Hf_le_log_card_type Y

theorem map_mix {ι : Type uIota} {β : Type uBeta} [Fintype ι] [Fintype β]
    (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → β) :
    (p.mix q).map X = p.mix (fun i => (q i).map X) := by
  classical
  ext b
  simp only [map_mass,mix_mass,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

theorem Hf_mix_ge {ι : Type uIota} {β : Type uBeta} [Fintype ι]
    (p : FinLaw ι) (q : ι → FinLaw Ω) (X : Ω → β) :
    (∑ i, p i*(q i).Hf X) ≤ (p.mix q).Hf X := by
  classical
  let Y := fun ω => (⟨X ω,⟨ω,rfl⟩⟩ : Set.range X)
  let : Fintype (Set.range X) := Fintype.ofFinite _
  have he (r : FinLaw Ω) : r.Hf X = r.Hf Y := by
    apply r.Hf_eq_of_fibers
    intro ω ν
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp_rw [he,Hf_eq_H]
  change (∑ i, p i*((q i).map Y).entropy) ≤ ((p.mix q).map Y).entropy
  rw [map_mix]
  exact p.entropy_mix_ge _

theorem Hf_prefix_le (p : FinLaw Ω) (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k))
    (s : ℕ) : p.Hf (prefixVar X π s) ≤ p.Hf X := by
  exact p.Hf_le_of_determined _ _ (fun ω ν hh =>
    congrArg (fun y (i : Fin k) => if i.val < s then some (y (π i)) else none) hh)

theorem Hf_fintype_subadd {ι : Type uIota} {β : Type uBeta} [Fintype ι] (p : FinLaw Ω)
    (X : Ω → ι → β) : p.Hf X ≤ ∑ i, p.Hf (fun ω => X ω i) := by
  classical
  have he : p.Hf (fun ω (i : (Finset.univ : Finset ι)) => X ω i) = p.Hf X := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    constructor
    · intro hh
      funext i
      exact congrFun hh ⟨i,Finset.mem_univ _⟩
    · intro hh
      funext i
      exact congrFun hh i
  simpa only [he] using p.Hf_finset_subadd X Finset.univ

theorem Hf_prefix_le_sum (p : FinLaw Ω) (X : Ω → Fin k → α)
    (L : Fin k → ℝ) (hL : ∀ i, p.Hf (fun ω => X ω i) ≤ L i)
    (π : Equiv.Perm (Fin k)) {s : ℕ} (hs : s ≤ k) :
    p.Hf (prefixVar X π s) ≤ ∑ j : Fin s, L (π ⟨j.val,by omega⟩) := by
  let Y := fun ω (j : Fin s) => X ω (π ⟨j.val,by omega⟩)
  have he : p.Hf (prefixVar X π s) = p.Hf Y := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    constructor
    · intro hh
      funext j
      have h := congrFun hh ⟨j.val,by omega⟩
      simpa [prefixVar,j.isLt,Y] using h
    · intro hh
      funext j
      by_cases hj : j.val < s
      · have h := congrFun hh ⟨j.val,hj⟩
        simpa [prefixVar,hj,Y] using congrArg some h
      · simp [prefixVar,hj]
  rw [he]
  exact (p.Hf_fintype_subadd Y).trans (Finset.sum_le_sum (fun j _ => hL _))

theorem fresh_entropy_from_prefix {β : Type uBeta} (p : FinLaw Ω)
    (X Y : Ω → Fin k → α) (d : Ω → Fin k → β) {b s : ℕ}
    (hbs : b < s) (hs : s ≤ k)
    (hd : ∀ i ω ν, X ω i = X ν i → Y ω i = Y ν i → d ω i = d ν i) :
    p.orderedEntropy d s-p.orderedEntropy X b-p.orderedEntropy Y b ≤
      (s-b : ℕ)*(𝔼 π : Equiv.Perm (Fin k),
        p.cHf (fun ω => d ω (π ⟨b,by omega⟩))
          (fun ω => (prefixVar X π b ω,prefixVar Y π b ω))) := by
  let C := fun (π : Equiv.Perm (Fin k)) ω => (prefixVar X π b ω,prefixVar Y π b ω)
  have hdet : ∀ π ω ν, C π ω=C π ν → prefixVar d π b ω=prefixVar d π b ν := by
    intro π ω ν hh
    funext i
    by_cases hi : i.val < b
    · have hx := congrFun (congrArg Prod.fst hh) i
      have hy := congrFun (congrArg Prod.snd hh) i
      simp only [C,prefixVar,hi,ite_eq_left,Option.some.injEq] at hx hy
      simpa only [prefixVar,hi,ite_eq_left] using congrArg some (hd (π i) ω ν hx hy)
    · simp [prefixVar,hi]
  have hblock := p.ordered_prefix_conditional_bound d C hbs hs hdet (by
    intro π j hj
    dsimp [C]
    rw [prefixVar_swap X π b _ j (by exact le_rfl) hj,
      prefixVar_swap Y π b _ j (by exact le_rfl) hj])
  have hlow (π : Equiv.Perm (Fin k)) : p.Hf (prefixVar d π s)-
      p.Hf (prefixVar X π b)-p.Hf (prefixVar Y π b) ≤
        p.cHf (prefixVar d π s) (C π) := by
    have h1 := p.Hf_pair_subadd (prefixVar X π b) (prefixVar Y π b)
    have h2 := p.Hf_pair_ge_snd (C π) (prefixVar d π s)
    rw [p.Hf_pair_comm] at h2
    dsimp [C] at *
    unfold cHf
    linarith
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hlow π)
  simp only [Finset.expect_sub_distrib] at hav
  exact hav.trans hblock

end FinLaw

end GaussianMoat

end OAI
