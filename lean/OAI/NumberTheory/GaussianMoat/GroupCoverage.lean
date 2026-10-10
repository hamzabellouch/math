import OAI.NumberTheory.GaussianMoat.KernelComposition

namespace OAI

universe uGroup uOmega uAlpha uIota uBeta uCapitalGamma

namespace GaussianMoat

section
open scoped BigOperators Classical
variable {G : Type uGroup} [Fintype G] [AddGroup G]

noncomputable def overlapCount (K E : Finset G) (x : G) : ℕ :=
  (E.filter (fun y => x+y ∈ K)).card

lemma overlapCount_sum (K E : Finset G) :
    (∑ x : G, overlapCount K E x) = K.card*E.card := by
  simp only [overlapCount,Finset.card_filter]
  rw [Finset.sum_comm]
  have hh (y : G) : (∑ x : G, if x+y ∈ K then (1:ℕ) else 0) = K.card := by
    calc
      _ = ∑ x : G, if x ∈ K then (1:ℕ) else 0 :=
        Equiv.sum_comp (Equiv.addRight y) (fun x => if x ∈ K then (1:ℕ) else 0)
      _ = K.card := by simp
  simp only [hh,Finset.sum_const,smul_eq_mul]
  ring

noncomputable def overlapExceptions (K E : Finset G) (δ : ℝ) : Finset G :=
  Finset.univ.filter (fun x => δ*K.card < overlapCount K E x)

lemma overlapExceptions_card (K E : Finset G) (hK : K.Nonempty) {δ : ℝ} (hδ : 0 < δ) :
    ((overlapExceptions K E δ).card:ℝ) ≤ E.card/δ := by
  have hKp : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hs : ((overlapExceptions K E δ).card:ℝ)*(δ*K.card) ≤
      ∑ x : G, (overlapCount K E x:ℝ) := by
    have h1 : ∑ x ∈ overlapExceptions K E δ, δ*K.card ≤
        ∑ x ∈ overlapExceptions K E δ, (overlapCount K E x:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.mem_filter.mp hx).2.le
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (overlapExceptions K E δ))
      (fun x _ _ => (Nat.cast_nonneg (overlapCount K E x): (0:ℝ)≤_))
    simpa only [Finset.sum_const,nsmul_eq_mul] using h1.trans h2
  have he : (∑ x : G, (overlapCount K E x:ℝ)) = (K.card:ℝ)*E.card := by
    exact_mod_cast overlapCount_sum K E
  rw [he] at hs
  apply (le_div_iff₀ hδ).mpr
  nlinarith only [hs,hKp]

lemma coverage_hit_lower (q : FinLaw G) (K E : Finset G) {τ δ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hq : ∀ y ∉ E, (τ+4*δ)/(Fintype.card G:ℝ) ≤ q y)
    {x : G} (hx : x ∉ overlapExceptions K E δ) :
    (τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ q.prob (fun y => x+y ∈ K) := by
  have hne := q.nonempty
  have hp : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hoc : (overlapCount K E x:ℝ) ≤ δ*K.card := by
    simpa only [overlapExceptions,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hx
  let S := Finset.univ.filter (fun y : G => x+y ∈ K ∧ y ∉ E)
  have hcount : (S.card:ℝ)+(overlapCount K E x:ℝ) = K.card := by
    have ht : S.card+overlapCount K E x=K.card := by
      have hbase : (Finset.univ.filter (fun y : G => x+y ∈ K)).card = K.card := by
        simp only [Finset.card_filter]
        calc
          _ = ∑ y : G, if y ∈ K then (1:ℕ) else 0 :=
            Equiv.sum_comp (Equiv.addLeft x) (fun y => if y ∈ K then (1:ℕ) else 0)
          _ = K.card := by simp
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun y : G => x+y ∈ K)) (p := fun y => y ∈ E)
      have hE : ((Finset.univ.filter (fun y : G => x+y ∈ K)).filter (fun y => y ∈ E)).card =
          overlapCount K E x := by
        unfold overlapCount
        congr 1
        ext y
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        tauto
      have hS : (Finset.univ.filter (fun y : G => x+y ∈ K)).filter (fun y => y ∉ E) = S := by
        ext y
        simp [S]
      rw [hE,hS,hbase] at hsplit
      omega
    exact_mod_cast ht
  have h1 : (S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)) ≤ ∑ y ∈ S, q y := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (s := S)
      (fun y hy => hq y (Finset.mem_filter.mp hy).2.2)
  have h2 : (∑ y ∈ S, q y) ≤ q.prob (fun y => x+y ∈ K) := by
    have he : q.prob (fun y => x+y ∈ K) =
        ∑ y ∈ Finset.univ.filter (fun y : G => x+y ∈ K), q y := by
      simp only [FinLaw.prob,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : x+y ∈ K <;> simp only [hy,ite_true,ite_false]
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ y,(Finset.mem_filter.mp hy).2.1⟩
    · intro y _ _
      exact q.nonneg y
  have h3 : (τ+2*δ)*K.card ≤ S.card*(τ+4*δ) := by
    have hc : (0:ℝ) ≤ K.card := Nat.cast_nonneg _
    have hd : τ+2*δ ≤ (1-δ)*(τ+4*δ) := by nlinarith only [hτ1,hδ1,hδ]
    have hm := mul_le_mul_of_nonneg_right hd hc
    have hs : (1-δ)*(K.card:ℝ) ≤ S.card := by linarith only [hcount,hoc]
    have ht := mul_le_mul_of_nonneg_right hs (by positivity : (0:ℝ) ≤ τ+4*δ)
    nlinarith only [hm,ht]
  calc
    _ ≤ (S.card:ℝ)*((τ+4*δ)/(Fintype.card G:ℝ)) := by
      simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right hp).mpr h3
    _ ≤ _ := h1.trans h2

noncomputable def coverageList (K : Finset G) (n : ℕ) (τ δ : ℝ) (h : Fin n → G) : Finset G :=
  Finset.univ.filter (fun x =>
    (∑ i : Fin n, if x+h i ∈ K then (1:ℝ) else 0) ≤
      n*(τ+δ)*K.card/(Fintype.card G:ℝ))

theorem coverageList_tail (q : FinLaw G) (K E : Finset G) (hK : K.Nonempty)
    {τ δ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hq : ∀ y ∉ E, (τ+4*δ)/(Fintype.card G:ℝ) ≤ q y) (n : ℕ) :
    (q.iid n).prob (fun h => ¬ coverageList K n τ δ h ⊆ overlapExceptions K E δ) ≤
      (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) := by
  have hne := q.nonempty
  have hp : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hKp : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  let μ := (τ+2*δ)*(K.card:ℝ)/(Fintype.card G:ℝ)
  let d := δ*(K.card:ℝ)/(Fintype.card G:ℝ)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hx (x : G) : (q.iid n).prob (fun h => x ∈ coverageList K n τ δ h ∧
      x ∉ overlapExceptions K E δ) ≤
      Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) := by
    by_cases he : x ∈ overlapExceptions K E δ
    · simp only [he,not_true_eq_false,and_false,FinLaw.prob,ite_false,Finset.sum_const_zero]
      exact (Real.exp_pos _).le
    · have hh := q.iid_lower_tail (fun y => x+y ∈ K) n hμ hd
        (coverage_hit_lower q K E hτ hτ1 hδ hδ1 hq he)
      have hth : (n:ℝ)*(μ-d) = (n:ℝ)*(τ+δ)*K.card/(Fintype.card G:ℝ) := by
        dsimp [μ,d]
        ring
      rw [hth] at hh
      have hm : (q.iid n).prob (fun h => x ∈ coverageList K n τ δ h ∧
          x ∉ overlapExceptions K E δ) ≤
          (q.iid n).prob (fun h =>
            (∑ i : Fin n, if x+h i ∈ K then (1:ℝ) else 0) ≤
              n*(τ+δ)*K.card/(Fintype.card G:ℝ)) := by
        apply FinLaw.prob_mono
        intro h hh
        exact (Finset.mem_filter.mp hh.1).2
      apply (hm.trans (by
        convert! hh using 1
        congr 1
        funext v
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : x+v i ∈ K <;> simp only [hi,ite_true,ite_false])).trans
      apply Real.exp_le_exp.mpr
      have heq : d^2/μ = δ^2*(K.card:ℝ)/((τ+2*δ)*(Fintype.card G:ℝ)) := by
        dsimp [d,μ]
        field_simp
      have ht : 0 < τ+2*δ := by positivity
      have ht1 : τ+2*δ ≤ 1 := by linarith only [hτ1,hδ1]
      have hratio : δ^2*(K.card:ℝ)/(Fintype.card G:ℝ) ≤ d^2/μ := by
        rw [heq]
        apply div_le_div_of_nonneg_left (by positivity) (mul_pos ht hp)
        exact mul_le_of_le_one_left hp.le ht1
      have hmul := mul_le_mul_of_nonneg_left hratio (show (0:ℝ) ≤ n/2 by positivity)
      calc
        _ = -((n:ℝ)/2*(d^2/μ)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
        _ ≤ -((n:ℝ)/2*(δ^2*(K.card:ℝ)/(Fintype.card G:ℝ))) := neg_le_neg hmul
        _ = _ := by ring
  have hu := (q.iid n).prob_exists_le_sum (fun x h => x ∈ coverageList K n τ δ h ∧
    x ∉ overlapExceptions K E δ)
  have hm : (q.iid n).prob (fun h => ¬ coverageList K n τ δ h ⊆ overlapExceptions K E δ) ≤
      (q.iid n).prob (fun h => ∃ x, x ∈ coverageList K n τ δ h ∧ x ∉ overlapExceptions K E δ) := by
    apply FinLaw.prob_mono
    intro h hh
    by_contra hn
    apply hh
    intro x hx
    by_contra he
    exact hn ⟨x,hx,he⟩
  apply (hm.trans hu).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun x _ => hx x)

end

namespace FinLaw

section
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] [Fintype α]

lemma prod_ite_forall {ι : Type uIota} [Fintype ι] (P : ι → Prop) (f : ι → ℝ) :
    (∏ i, if P i then f i else 0) = if ∀ i, P i then ∏ i, f i else 0 := by
  by_cases h : ∀ i, P i
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma iid_map (p : FinLaw Ω) (f : Ω → α) (n : ℕ) :
    (p.iid n).map (fun x i => f (x i)) = (p.map f).iid n := by
  ext y
  simp only [map_mass,iid_mass]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [prod_ite_forall]
  congr 1
  exact propext funext_iff

lemma iid_prob_forall (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) = (p.prob E)^n := by
  simp only [prob,iid_mass]
  calc
    _ = ∑ x : Fin n → Ω, ∏ i, if E (x i) then p (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have h := prod_ite_forall (fun i => E (x i)) (fun i => p (x i))
      by_cases hh : ∀ i, E (x i) <;> simpa only [hh,ite_true,ite_false] using h.symm
    _ = _ := by
      rw [← Fintype.prod_sum (fun (_ : Fin n) (ω : Ω) => if E ω then p ω else (0:ℝ))]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma iid_prob_implies (p : FinLaw Ω) (E F : Ω → Prop) (n : ℕ)
    (h : ∀ x, E x → ¬ F x) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) ≤ (1-p.prob F)^n := by
  rw [← p.prob_compl F,← p.iid_prob_forall]
  exact (p.iid n).prob_mono (fun x hx i => h _ (hx i))

lemma iid_survival_exp (p : FinLaw Ω) (E : Ω → Prop) (n : ℕ) {c : ℝ}
    (hp : c ≤ 1-p.prob E) :
    (p.iid n).prob (fun x => ∀ i, E (x i)) ≤ Real.exp (-(n:ℝ)*c) := by
  have hbase : p.prob E ≤ Real.exp (-c) := by
    have h := Real.add_one_le_exp (-c)
    linarith only [hp,h]
  rw [iid_prob_forall]
  calc
    _ ≤ (Real.exp (-c))^n := pow_le_pow_left₀ (p.prob_nonneg E) hbase n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma expect_map (p : FinLaw Ω) (f : Ω → α) (g : α → ℝ) :
    (∑ a, p.map f a*g a) = ∑ ω, p ω*g (f ω) := by
  simp only [map_mass,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [ite_mul,zero_mul]
  simp

lemma joint_expect_snd (p : FinLaw Ω) (q : Ω → FinLaw α) (f : Ω → α → ℝ) :
    (∑ v, p.joint q v*f v.1 v.2) = ∑ ω, p ω*(∑ a, q ω a*f ω a) := by
  simp only [Fintype.sum_prod_type,joint_mass,Finset.mul_sum,mul_assoc]

lemma prob_map_true (p : FinLaw Ω) (E : Ω → Prop) :
    p.map (fun ω => decide (E ω)) true = p.prob E := by
  simp only [map_mass,decide_eq_true_eq,prob]

lemma prob_le_of_expect (p : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {c t : ℝ} (ht : 0 < t)
    (hc : (∑ ω, p ω*f ω) ≤ c) :
    1-c/t ≤ p.prob (fun ω => f ω ≤ t) := by
  have h := (p.prob_le_expect_div f hf ht).trans ((div_le_div_iff_of_pos_right ht).mpr hc)
  have he := p.prob_compl (fun ω => f ω ≤ t)
  simp only [not_le] at he
  linarith only [h,he]

end

open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma H_sub_H_of_agree (p : FinLaw Ω) (X Y : Ω → α) (E : Ω → Bool)
    (hE : ∀ ω, p ω ≠ 0 → E ω = true → X ω=Y ω) :
    p.H X-p.H Y ≤ Real.binEntropy (p.map E true)+
      (1-p.map E true)*Real.log (Fintype.card α) := by
  have h := p.short_list X Y (fun y => {y}) E (b := 1) le_rfl (by
    intro ω hp he
    simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one,le_refl,and_true]
    exact hE ω hp he)
  rw [Real.log_one,mul_zero,add_zero] at h
  have hc := p.H_le_condH_add X Y
  linarith only [h,hc]

lemma condH_sub_condH_of_agree (p : FinLaw Ω) (X X' : Ω → α) (O O' : Ω → β)
    (E : Ω → Bool) (hE : ∀ ω, p ω ≠ 0 → E ω=true → X ω=X' ω ∧ O ω=O' ω) :
    p.condH X O-p.condH X' O' ≤ 2*Real.binEntropy (p.map E true)+
      (1-p.map E true)*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)) := by
  have h1 := p.H_sub_H_of_agree (fun ω => (X ω,O ω)) (fun ω => (X' ω,O' ω)) E
    (fun ω hp he => Prod.ext (hE ω hp he).1 (hE ω hp he).2)
  have h2 := p.H_sub_H_of_agree O' O E (fun ω hp he => (hE ω hp he).2.symm)
  have hn := p.nonempty
  have ha : Nonempty α := ⟨X (Classical.arbitrary Ω)⟩
  have hb : Nonempty β := ⟨O (Classical.arbitrary Ω)⟩
  have hca : (Fintype.card α:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcb : (Fintype.card β:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.card_prod,Nat.cast_mul,Real.log_mul hca hcb] at h1
  unfold condH
  linarith only [h1,h2]

lemma binEntropy_le_log_inverse {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.binEntropy a ≤ a*(1-Real.log a) := by
  have h : Real.negMulLog (1-a) ≤ a := by
    by_cases hz : 1-a=0
    · simp only [hz,Real.negMulLog_zero]
      exact ha.le
    · have hp : 0 < 1-a := lt_of_le_of_ne (by linarith) (Ne.symm hz)
      have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
      rw [Real.log_inv] at hh
      have hm := mul_le_mul_of_nonneg_left hh hp.le
      rw [mul_sub,mul_inv_cancel₀ hz,mul_one] at hm
      unfold Real.negMulLog
      nlinarith only [hm]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  dsimp only [Real.negMulLog] at h ⊢
  nlinarith only [h]

lemma binEntropy_sum_le {ι : Type uIota} [Fintype ι] (w : FinLaw ι) (a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    (∑ i, w i*Real.binEntropy (a i)) ≤ Real.binEntropy (∑ i, w i*a i) := by
  exact Real.strictConcave_binEntropy.concaveOn.le_map_sum (fun i _ => w.nonneg i) w.sum_one (fun i _ => ha i)

end FinLaw

open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype Γ] [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in
lemma prob_mem_finset (p : FinLaw G) (K : Finset G) :
    p.prob (fun x => x ∈ K) = ∑ x ∈ K, p x := by
  unfold prob
  calc
    _ = ∑ x ∈ K, if x ∈ K then p x else 0 := by
      symm
      convert! Finset.sum_subset (Finset.subset_univ K)
        (f := fun x => if x ∈ K then p x else (0:ℝ))
        (fun x _ hx => ite_eq_right hx) using 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x∈K <;> simp only [hx,ite_true,ite_false]
    _ = _ := Finset.sum_congr rfl (fun x hx => ite_eq_left hx)

lemma joint_prob_le_bad_add (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Bad : Ω → Prop) (E : Ω × Γ → Prop) {ε : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ ω, ¬ Bad ω → (q ω).prob (fun a => E (ω,a)) ≤ ε) :
    (p.joint q).prob E ≤ p.prob Bad+ε := by
  rw [prob_joint]
  have h (ω : Ω) : (q ω).prob (fun a => E (ω,a)) ≤ (if Bad ω then 1 else 0)+ε := by
    by_cases hb : Bad ω
    · simpa only [hb,ite_true] using (q ω).prob_le_one (fun a => E (ω,a)) |>.trans (by linarith only [hε])
    · simpa only [hb,ite_false,zero_add] using hg ω hb
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  convert! hh using 1
  simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,p.sum_one,one_mul,prob]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

omit [Fintype G] in

lemma iid_true_hit_expect (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : Ω → G) (h : Γ → G) (K : Finset G) (n : ℕ) :
    (∑ v, p.joint (fun ω => (q ω).iid n) v *
      (∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) =
      n*(p.joint q).prob (fun v => Y v.1+h v.2 ∈ K) := by
  rw [joint_expect_snd p (fun ω => (q ω).iid n)
    (fun ω v => ∑ i : Fin n, if Y ω+h (v i) ∈ K then (1:ℝ) else 0)]
  have he (i : Fin n) (ω : Ω) :
      (∑ v, (q ω).iid n v*(if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        (q ω).prob (fun a => Y ω+h a ∈ K) := by
    rw [← expect_map ((q ω).iid n) (fun v => v i) (fun a => if Y ω+h a ∈ K then (1:ℝ) else 0),
      iid_map_eval]
    unfold prob
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hh (ω : Ω) :
      (∑ v, (q ω).iid n v*(∑ i : Fin n, if Y ω+h (v i) ∈ K then (1:ℝ) else 0)) =
        n*(q ω).prob (fun a => Y ω+h a ∈ K) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [hh,mul_left_comm (p _) (n:ℝ)]
  rw [← Finset.mul_sum,prob_joint p q (fun v => Y v.1+h v.2∈K)]

lemma true_coverageList_probability (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : Ω → G) (h : Γ → G) (K : Finset G) (hK : K.Nonempty)
    {τ δ : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hp : (p.joint q).prob (fun v => Y v.1+h v.2 ∈ K) ≤
      τ*K.card/(Fintype.card G:ℝ)) :
    δ/(τ+δ) ≤ (p.joint (fun ω => (q ω).iid n)).prob
      (fun v => Y v.1 ∈ coverageList K n τ δ (fun i => h (v.2 i))) := by
  have hG : Nonempty G := ⟨Y (Classical.choice p.nonempty)⟩
  have hcard : (0:ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hkc : (0:ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr hK
  have hnc : (0:ℝ) < n := by exact_mod_cast hn
  have htd : 0 < τ+δ := by linarith
  have hb : (∑ v, p.joint (fun ω => (q ω).iid n) v *
      (∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)) ≤
        n*(τ*K.card/(Fintype.card G:ℝ)) := by
    rw [iid_true_hit_expect]
    exact mul_le_mul_of_nonneg_left hp hnc.le
  have hh := (p.joint (fun ω => (q ω).iid n)).prob_le_of_expect
    (fun v => ∑ i : Fin n, if Y v.1+h (v.2 i) ∈ K then (1:ℝ) else 0)
    (fun _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
    (t := n*(τ+δ)*K.card/(Fintype.card G:ℝ)) (by positivity) hb
  have he : 1-(n*(τ*K.card/(Fintype.card G:ℝ)))/(n*(τ+δ)*K.card/(Fintype.card G:ℝ)) =
      δ/(τ+δ) := by field_simp; ring
  rw [he] at hh
  simpa only [coverageList,Finset.mem_filter,Finset.mem_univ,true_and] using hh

lemma coverageList_size_probability (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (h : Γ → G) (K : Finset G) (hK : K.Nonempty) (E : Ω → Finset G)
    (Bad : Ω → Prop) {τ δ ε b : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hδ : 0 < δ) (hδ1 : δ ≤ 1/64)
    (hε : 0 ≤ ε) (n : ℕ)
    (hq : ∀ ω, ¬ Bad ω → ∀ y ∉ E ω,
      (τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE : ∀ ω, ¬ Bad ω → ((E ω).card:ℝ)/δ ≤ b)
    (herr : (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ))) ≤ ε) :
    (p.joint (fun ω => (q ω).iid n)).prob (fun v =>
      b < ((coverageList K n τ δ (fun i => h (v.2 i))).card:ℝ)) ≤ p.prob Bad+ε := by
  apply joint_prob_le_bad_add p _ Bad _ hε
  intro ω hg
  have ha := (coverageList_tail ((q ω).map h) K (E ω) hK hτ hτ1 hδ hδ1 (hq ω hg) n).trans herr
  rw [← iid_map,prob_map] at ha
  apply (prob_mono _ ?_).trans ha
  intro x hx hs
  have hc := Finset.card_le_card hs
  have hcR : ((coverageList K n τ δ (fun i => h (x i))).card:ℝ) ≤
      ((overlapExceptions K (E ω) δ).card:ℝ) := by exact_mod_cast hc
  have hb := (overlapExceptions_card K (E ω) hK hδ).trans (hE ω hg)
  linarith only [hx,hcR,hb]

end FinLaw
end GaussianMoat

end OAI
