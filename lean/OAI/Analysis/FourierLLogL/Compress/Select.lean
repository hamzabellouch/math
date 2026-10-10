import OAI.Analysis.FourierLLogL.Compress.Prefix
/-! # Selecting conditional iid comparator -/
open Set Function Filter
open scoped BigOperators
noncomputable section
namespace OAI

namespace FourierLLogL.Compress
open Real Law

private lemma choose_slow {a : ℕ → ℝ} (ha : Monotone a)
    (h0 : ∀ j, 0 ≤ a j) {E : ℝ} (hE : 0 ≤ E) (T N m : ℕ)
    (hN : 0 < N) (hm : m ≤ N) (hT : 3*N ≤ T)
    (hh : ∑ j ∈ Finset.range T, a j ≤ E) :
    ∃ j, j < N ∧ a j ≤ E/N ∧
      ∑ i ∈ Finset.range m, (a (j+i)-a j) ≤ m^2*E/(N:ℝ)^2 := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast hN
  let D := E/N
  have hs (l : ℕ) (hl : l ≤ 2*N) : a l ≤ D := by
    have Hlt : ∑ j ∈ Finset.range (l+N), a j ≤ E :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun i _ _ => h0 i)) hh
    rw [Finset.sum_range_add] at Hlt
    have H : ∑ _ ∈ Finset.range N, a l ≤ ∑ i ∈ Finset.range N, a (l+i) :=
      Finset.sum_le_sum fun i _ => ha (by omega : l ≤ l+i)
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at H
    apply (le_div_iff₀ hp).mpr
    have : 0 ≤ ∑ j ∈ Finset.range l, a j := Finset.sum_nonneg fun j _ => h0 j
    linarith
  have HD : 0 ≤ D := div_nonneg hE hp.le
  have hr (i : ℕ) (hi : i ≤ m) :
      ∑ j ∈ Finset.range N, (a (j+i)-a j) ≤ m*D := by
    have h1 := Finset.sum_range_add a N i
    have h2 := Finset.sum_range_add a i N
    have hcmp : ∑ j ∈ Finset.range i, a (N+j) ≤ ∑ j ∈ Finset.range i, D := by
      apply Finset.sum_le_sum
      intro j hj
      apply hs; rw [Finset.mem_range] at hj; omega
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hcmp
    have hl : 0 ≤ ∑ j ∈ Finset.range i, a j := Finset.sum_nonneg fun j _ => h0 j
    have hle : (i:ℝ)*D ≤ (m:ℝ)*D := by gcongr
    rw [show i+N=N+i by omega] at h2
    simp_rw [show ∀ j, j+i=i+j from fun j => add_comm _ _, Finset.sum_sub_distrib]
    linarith
  let f j := ∑ i ∈ Finset.range m, (a (j+i)-a j)
  have hAvg : ∑ j ∈ Finset.range N, f j ≤ ∑ i ∈ Finset.range N, ((m:ℝ)^2*E/(N:ℝ)^2) := by
    unfold f
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i ∈ Finset.range m, ((m:ℝ)*D) :=
        Finset.sum_le_sum fun i hi => hr i (Finset.mem_range.mp hi).le
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,D]; field_simp
  by_contra! hy
  apply (not_lt_of_ge hAvg)
  refine Finset.sum_lt_sum_of_nonempty ⟨0,Finset.mem_range.mpr hN⟩ (fun j hj => ?_)
  have hj := Finset.mem_range.mp hj

  exact hy _ hj (hs _ (by omega))

variable {α G Ω : Type} [Fintype α] [Fintype G] [Fintype Ω] [AddCommGroup G]

omit [AddCommGroup G] in
private lemma choose3 (P : Law Ω) (a b c : Ω → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hc : ∀ x, 0 ≤ c x)
    (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h1 : P.Ex a ≤ A) (h2 : P.Ex b ≤ B) (h3 : P.Ex c ≤ C) :
    ∃ x, 0 < P x ∧ a x ≤ 3*A ∧ b x ≤ 3*B ∧ c x ≤ 3*C := by
  obtain ⟨x,hx,hh⟩ := P.exists_le_Ex fun x => a x*A⁻¹+b x*B⁻¹+c x*C⁻¹
  have H : a x/A+b x/B+c x/C ≤ 3 := by
    simp_rw [Ex_add,Ex_mul, ← div_eq_mul_inv] at hh
    linarith [(div_le_one hA).mpr h1,(div_le_one hB).mpr h2,(div_le_one hC).mpr h3]
  have hI := div_nonneg (ha x) hA.le
  have hJ := div_nonneg (hb x) hB.le
  have hK := div_nonneg (hc x) hC.le
  exact ⟨x,hx,(div_le_iff₀ hA).mp (by linarith),(div_le_iff₀ hB).mp
    (by linarith),(div_le_iff₀ hC).mp (by linarith)⟩

lemma kl_covered {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Law Ω) (X : Ω → ι → α) (q : Law α) (h : ∀ i, P.send (fun a => X a i) = q) :
    covered P X q := by
  intro a ha i
  rw [← h i]
  exact P.send_pos (fun a => X a i) ha


def iid (p : Law α) (n : ℕ) := pack (fun _ : Fin n => p)

theorem select_context (tag : α → G) (c : G → ℝ) (hc : ∀ x, 0 ≤ c x)
    (T N m : ℕ) (hm0 : 0 < m) (hm : m ≤ N) (hT : 3*N ≤ T)
    (E : ℝ) (hE : 0 < E) [Nonempty α]
    (h : ∀ p : Law α, exp (-E) ≤ heatMoment (Fin T) p tag c) :
    ∃ (p : Law α) (Ψ : Law (WordSample N α G)), exch Ψ ∧
      (∀ i : Fin N, Ψ.send (fun a => a.1 i) = p) ∧
      log (Fintype.card α) - p.entropy ≤ 3*(E/N) ∧
      bill tag c p Ψ Prod.fst Prod.snd ≤ 3*E ∧
      tv (Ψ.send (prefixB Prod.fst m hm)) (iid p m) ≤ 2*m*√E/N := by
  obtain ⟨P,hp,hx,hu⟩ := noisy_symm tag c E h
  let X : WordSample T α G → Letters T α := Prod.fst
  let L := log (Fintype.card α)
  let a j := L-rateH P X j
  have h0 : 0 < N := by omega
  have h1 (j : ℕ) : 0 ≤ a j := sub_nonneg.mpr (rate_bdd P X j)
  let u := uniform α
  have hcov : covered P X u := kl_covered P X u hu
  have heq : ∑ j ∈ Finset.range T, a j ≤ E := by
    have H := kl_le_bill hcov tag c hc Prod.snd
    dsimp only [a,L]
    rw [sum_deficit]
    exact le_trans (le_trans
      (le_add_of_nonneg_right (P.Ex_nonneg fun x => hc (x.2))) H) hp
  obtain ⟨j,hj,hb,hj'⟩ := choose_slow (a:=a) (fun x y hh =>
    sub_le_sub_left (rate_antitone hx hh) _) h1 hE.le T N m h0 hm hT heq
  let W := prefixB X j (by omega)
  let V := readBlock X j N (by omega)
  let Y := readBlock X j m (by omega)
  let R (w) := P.after W w
  let H := readLetter X j (by omega)
  let ν (w) := (R w).send H
  let Pw := P.send W
  let b (w) := L-(ν w).entropy
  let k (w) := bill tag c u (R w) V Prod.snd
  let d (w) := kl ((R w).send Y) (pack (fun _ : Fin m => ν w))
  have Hb (w : Letters j α) : 0 ≤ b w :=
    sub_nonneg.mpr (entropy_le_log_card _)
  have Hk (w : Letters j α) : 0 ≤ k w := by
    apply bill_nonneg _ tag c hc
    intro a _ _
    rw [uniform_apply]
    positivity
  have hv (w) (i : Fin m) :
      (R w).send (fun x => Y x i) = ν w := conditional_block_marg hx (j:=j) (m:=m) (by omega) w i
  have hv' (w) (i : Fin N) :
      (R w).send (fun x => V x i) = ν w := conditional_block_marg hx (j:=j) (m:=N) (by omega) w i
  have Hd (w : Letters j α) : 0 ≤ d w := kl_nonneg
    (covered_pack (kl_covered _ _ _ (hv w)))
  have Hm' : (0:ℝ) < m := by exact_mod_cast hm0
  have HN : (0:ℝ) < N := by exact_mod_cast h0
  have H1 : Pw.Ex b ≤ E/N := by
    unfold b ν Pw
    rw [Ex_sub,Ex_const]
    exact le_trans (le_of_eq (by
      dsimp only [a]
      rw [rate_lt P X (show j<T by omega),Hcond_after]; rfl)) hb
  have H2 : Pw.Ex k ≤ E := le_trans
    (prefix_bill tag c u P X _ hcov j N (by omega)) hp
  have H3 : Pw.Ex d ≤ (m:ℝ)^2*E/N^2 := by
    unfold Pw d
    have HH := avg_block_kl hx (j:=j) (m:=m) (by omega) (by omega)
    apply le_trans (b:=∑ i ∈ Finset.range m, (rateH P X j - rateH P X (j+i))) HH.le
    apply le_trans (b:=∑ i ∈ Finset.range m, (a (j+i)-a j)) ?_ hj'
    apply Finset.sum_le_sum; intro i _; dsimp only [a]; linarith
  obtain ⟨w,hw,h1,h2,h3⟩ := choose3 Pw b k d Hb Hk Hd (E/N) E ((m:ℝ)^2*E/N^2)
    (by positivity) hE (by positivity) H1 H2 H3
  let Ψ := (R w).send (fun x => (V x,x.2))
  have hmx := conditional_block_exch hx (j:=j) (m:=N) (by omega) w
  refine ⟨ν w,Ψ,hmx,fun i => ?_,h1,?_,?_⟩
  · dsimp only [Ψ]
    rw [send_send]; exact hv' w i
  · dsimp only [Ψ]
    rw [bill_send]
    exact (bill_change (covered_subfamily (covered_after hcov W w hw) (offset j N (by omega)))
      tag c Prod.snd (ν w) (hv' w)).trans h2
  · have hh : Ψ.send (prefixB Prod.fst m hm) = (R w).send Y := by
      unfold Ψ; rw [send_send, show Y = _ from block_cut X j N m (by omega) hm]; rfl
    rw [hh]
    let v := tv ((R w).send Y) (iid (ν w) m)
    have ht : v^2 ≤ 3*((m:ℝ)^2*E/N^2) :=
      (tv_sq_le_kl (covered_pack (kl_covered _ _ _ (hv w)))).trans h3
    have h4 : 3*((m:ℝ)^2*E/N^2) ≤ (2*m*√E/N)^2 := by
      rw [div_pow,mul_pow,mul_pow, sq_sqrt hE.le]
      have H := pow_pos HN 2
      field_simp; nlinarith
    change v ≤ _
    nlinarith [ht.trans h4,sqrt_nonneg E,show 0 ≤ 2*m*√E/N by positivity]

end FourierLLogL.Compress

end OAI
