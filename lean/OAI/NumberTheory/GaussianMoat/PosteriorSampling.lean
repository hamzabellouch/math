import OAI.NumberTheory.GaussianMoat.BackwardCoverage

namespace OAI

universe uOmega uAlpha uCapitalGamma uGroup uIota uBeta uGamma

namespace GaussianMoat

namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]

lemma prob_and_split (p : FinLaw Ω) (A B : Ω → Prop) :
    p.prob (fun ω => A ω ∧ B ω)+p.prob (fun ω => A ω ∧ ¬B ω)=p.prob A := by
  simp only [prob,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha,hb]

lemma prob_mix (p : FinLaw Ω) (q : Ω → FinLaw Γ) (E : Γ → Prop) :
    (p.mix q).prob E = ∑ ω, p ω*(q ω).prob E := by
  rw [← joint_map_snd,prob_map,prob_joint]

lemma posterior_unfavorable (p : FinLaw Ω) (C : Ω → α) (Bad : Ω → Prop) :
    (p.map C).prob (fun a => (1/2:ℝ)<(p.conditionOn C a).prob Bad) ≤ 2*p.prob Bad := by
  have h := (p.map C).prob_le_expect_div (fun a => (p.conditionOn C a).prob Bad)
    (fun a => (p.conditionOn C a).prob_nonneg _) (by norm_num : (0:ℝ)<1/2)
  rw [p.conditionOn_prob] at h
  linarith only [h]

lemma mixed_exception_card (p : FinLaw Ω) (Good : Ω → Prop) (E : Ω → Finset G)
    {e : ℝ} (he : 0≤e) (hE : ∀ ω, Good ω → ((E ω).card:ℝ)≤e)
    (hG : (1/2:ℝ)≤p.prob Good) :
    ((Finset.univ.filter (fun x : G =>
      p.prob (fun ω => Good ω ∧ x∉E ω)<1/4)).card:ℝ) ≤ 4*e := by
  let u := fun x => p.prob (fun ω => Good ω ∧ x∉E ω)
  let f := fun x => p.prob (fun ω => Good ω ∧ x∈E ω)
  let K := Finset.univ.filter (fun x : G => u x<1/4)
  have hsum : (∑ x : G, f x) ≤ e := by
    simp only [f,prob]
    rw [Finset.sum_comm]
    have hh (ω : Ω) : (∑ x : G, if Good ω ∧ x∈E ω then p ω else 0) ≤ p ω*e := by
      by_cases hg : Good ω
      · have hc : (∑ x : G, if Good ω ∧ x∈E ω then p ω else 0) = p ω*(E ω).card := by
          simp only [hg,true_and]
          calc
            _ = ∑ x : G, p ω*(if x∈E ω then (1:ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              split_ifs <;> simp
            _ = _ := by rw [← Finset.mul_sum]; simp
        rw [hc]
        exact mul_le_mul_of_nonneg_left (hE ω hg) (p.nonneg ω)
      · simp only [hg,false_and,ite_false,Finset.sum_const_zero]
        exact mul_nonneg (p.nonneg ω) he
    have ht := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hh ω)
    simp only [← Finset.sum_mul,p.sum_one,one_mul] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro ω _
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> rfl
  have hk (x : G) (hx : x∈K) : (1/4:ℝ)≤f x := by
    have h := p.prob_and_split Good (fun ω => x∈E ω)
    have hu : u x<1/4 := (Finset.mem_filter.mp hx).2
    change f x+u x=p.prob Good at h
    linarith only [hu,h,hG]
  have hl : (K.card:ℝ)/4 ≤ ∑ x∈K, f x := by
    have h := Finset.sum_le_sum (s := K) (fun x hx => hk x hx)
    simpa only [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv,one_mul] using h
  have hr : (∑ x∈K, f x) ≤ ∑ x:G, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
      (fun x _ _ => p.prob_nonneg _)
  change (K.card:ℝ)≤4*e
  linarith only [hl,hr,hsum]

omit [Fintype G] in
lemma mixed_floor (p : FinLaw Ω) (q : Ω → FinLaw Γ) (Good : Ω → Prop)
    (E : Ω → Finset G) (hit : Γ → G → Prop) {τ : ℝ} (hτ : 0≤τ)
    (hq : ∀ ω, Good ω → ∀ x∉E ω, τ≤(q ω).prob (fun v => hit v x))
    (x : G) (hx : (1/4:ℝ)≤p.prob (fun ω => Good ω ∧ x∉E ω)) :
    τ/4 ≤ (p.mix q).prob (fun v => hit v x) := by
  rw [prob_mix]
  have h (ω : Ω) : τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0) ≤ (q ω).prob (fun v => hit v x) := by
    by_cases hg : Good ω ∧ x∉E ω
    · rw [ite_eq_left hg,mul_one]
      exact hq ω hg.1 x hg.2
    · rw [ite_eq_right hg,mul_zero]
      exact (q ω).prob_nonneg _
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (p.nonneg ω))
  have he : (∑ ω, p ω*(τ*(if Good ω ∧ x∉E ω then (1:ℝ) else 0))) =
      τ*p.prob (fun ω => Good ω ∧ x∉E ω) := by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hx hτ
  linarith only [hh,hm]

lemma prob_exists_eq_sum_disjoint {ι : Type uIota} [Fintype ι]
    (p : FinLaw Ω) (E : ι → Ω → Prop)
    (h : ∀ ω i j, E i ω → E j ω → i=j) :
    p.prob (fun ω => ∃ i, E i ω) = ∑ i, p.prob (E i) := by
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : ∃ i, E i ω
  · obtain ⟨i,hi⟩ := he
    rw [ite_eq_left ⟨i,hi⟩,Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      exact ite_eq_right (fun hj => hji (h ω j i hj hi))
    · simp
  · simp only [ite_eq_right he]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => he ⟨i,hi⟩)

end FinLaw

section
namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {ι : Type uIota} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω] [Fintype ι] [Fintype α] [Fintype β]

lemma Hf_id (p : FinLaw Ω) : p.Hf id = p.entropy := by rw [Hf_eq_H,H,map_id]

lemma cHf_joint_fst (p : FinLaw ι) (q : ι → FinLaw Ω) (X : ι → Ω → γ) :
    (p.joint q).cHf (fun v => X v.1 v.2) Prod.fst = ∑ i, p i*(q i).Hf (X i) := by
  unfold cHf
  rw [Hf_pair_comm,Hf_joint_pair_vary]
  have h := (p.joint q).Hf_map Prod.fst id
  rw [joint_map_fst,Hf_id] at h
  change p.entropy = (p.joint q).Hf Prod.fst at h
  rw [← h]
  ring

lemma joint_iid_eval (p : FinLaw ι) (q : ι → FinLaw Ω) (n : ℕ) (i : Fin n) :
    (p.joint (fun a => (q a).iid n)).map (fun v => (v.1,v.2 i)) = p.joint q := by
  calc
    _ = p.joint (fun a => ((q a).iid n).map (fun x : Fin n → Ω => x i)) :=
      joint_map_second p (fun a => (q a).iid n) (fun x : Fin n → Ω => x i)
    _ = _ := by simp only [iid_map_eval]

theorem conditional_iid_information (p : FinLaw (α × β)) (q : α × β → FinLaw Ω) (n : ℕ) :
    (p.joint (fun a => (q a).iid n)).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) ≤
      (n:ℝ)*(p.joint q).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
  let P := p.joint (fun a => (q a).iid n)
  let Q := p.joint q
  have hsub := P.cHf_fintype_subadd Prod.snd (fun v => v.1.1)
  have hmarg (i : Fin n) : P.cHf (fun v => v.2 i) (fun v => v.1.1) =
      Q.cHf Prod.snd (fun v => v.1.1) := by
    have h := P.cHf_map (fun v => (v.1,v.2 i)) Prod.snd (fun v => v.1.1)
    rw [joint_iid_eval] at h
    exact h.symm
  simp only [hmarg,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsub
  have hcond : P.cHf Prod.snd (fun v => (v.1.1,v.1.2)) =
      (n:ℝ)*Q.cHf Prod.snd (fun v => (v.1.1,v.1.2)) := by
    change P.cHf Prod.snd Prod.fst = (n:ℝ)*Q.cHf Prod.snd Prod.fst
    rw [cHf_joint_fst p (fun a => (q a).iid n) (fun _ x => x),
      cHf_joint_fst p q (fun _ x => x)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    change p a*((q a).iid n).Hf id = (n:ℝ)*(p a*(q a).Hf id)
    rw [Hf_id,Hf_id,entropy_iid]
    ring
  change P.cIf _ _ _ ≤ (n:ℝ)*Q.cIf _ _ _
  rw [P.cIf_comm,Q.cIf_comm]
  unfold cIf
  rw [hcond]
  nlinarith only [hsub]

end FinLaw

open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Ω] [Fintype α] [Fintype Γ] [Fintype G]

noncomputable def passingList (hit : Γ → G → Prop) (n : ℕ) (v : Fin n → Γ) : Finset G :=
  Finset.univ.filter (fun x => ∀ i, ¬ hit (v i) x)

lemma expect_card_passingList (q : FinLaw Γ) (hit : Γ → G → Prop)
    (E : Finset G) {c : ℝ} (hhit : ∀ x ∉ E, c≤q.prob (fun v => hit v x)) (n : ℕ) :
    (∑ v, q.iid n v*((passingList hit n v).card:ℝ)) ≤
      (E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c) := by
  have hprob (x : G) (hx : x ∉ E) :
      (q.iid n).prob (fun v => x∈passingList hit n v) ≤ Real.exp (-(n:ℝ)*c) := by
    have hh := q.iid_survival_exp (fun v => ¬hit v x) n (c := c) (by
      rw [q.prob_compl]; linarith only [hhit x hx])
    simpa only [passingList,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have he : (∑ v, q.iid n v*((passingList hit n v).card:ℝ)) =
      ∑ x : G, (q.iid n).prob (fun v => x∈passingList hit n v) := by
    have hc (v : Fin n → Γ) : ((passingList hit n v).card:ℝ) =
        ∑ x : G, if x∈passingList hit n v then (1:ℝ) else 0 := by simp
    simp only [hc,Finset.mul_sum,prob]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro v _
    by_cases hx : x∈passingList hit n v <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero]
  rw [he]
  have hh (x : G) : (q.iid n).prob (fun v => x∈passingList hit n v) ≤
      (if x∈E then (1:ℝ) else 0)+Real.exp (-(n:ℝ)*c) := by
    by_cases hx : x∈E
    · simp only [hx,ite_true]
      exact ((q.iid n).prob_le_one _).trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    · simp only [hx,ite_false,zero_add]
      exact hprob x hx
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hh x)
  simpa only [Finset.sum_add_distrib,Finset.sum_boole,Finset.filter_mem_eq_inter,
    Finset.univ_inter,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs

lemma passingList_true (q : FinLaw Γ) (hit : Γ → G → Prop) (x : G)
    (h : ∀ v, q v≠0 → ¬hit v x) (n : ℕ) :
    ∀ v, q.iid n v≠0 → x∈passingList hit n v := by
  intro v hv
  simp only [passingList,Finset.mem_filter,Finset.mem_univ,true_and]
  intro i
  apply h
  intro hz
  apply hv
  change (∏ j : Fin n, q (v j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

lemma expect_log_le_log_expect (p : FinLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, p ω≠0 → 0<f ω) :
    (∑ ω, p ω*Real.log (f ω)) ≤ Real.log (∑ ω, p ω*f ω) := by
  let f' := fun ω => if p ω=0 then (1:ℝ) else f ω
  have hh := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (fun ω _ => p.nonneg ω) p.sum_one (fun ω _ => show 0<f' ω from by
      dsimp only [f']; split_ifs with hz; norm_num; exact hf ω hz)
  have he (ω : Ω) : p ω*f' ω=p ω*f ω := by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  have hl (ω : Ω) : p ω*Real.log (f' ω)=p ω*Real.log (f ω) := by
    dsimp only [f']; split_ifs with hz; simp [hz]; rfl
  simpa only [smul_eq_mul,he,hl] using hh

lemma expected_log_card_passingList (q : FinLaw Γ) (hit : Γ → G → Prop)
    (x : G) (htrue : ∀ v, q v≠0 → ¬hit v x)
    (E : Finset G) {c : ℝ} (hhit : ∀ y ∉ E, c≤q.prob (fun v => hit v y)) (n : ℕ) :
    (∑ v, q.iid n v*Real.log (passingList hit n v).card) ≤
      Real.log ((E.card:ℝ)+(Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*c)) := by
  have hp (v : Fin n → Γ) (hv : q.iid n v≠0) : (0:ℝ)<(passingList hit n v).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x,q.passingList_true hit x htrue n v hv⟩
  apply ((q.iid n).expect_log_le_log_expect (fun v => ((passingList hit n v).card:ℝ)) hp).trans
  apply Real.log_le_log ?_ (q.expect_card_passingList hit E hhit n)
  have hex : ∃ v, 0 < q.iid n v := by
    by_contra hh
    push Not at hh
    have hz : ∀ v, q.iid n v=0 := fun v => le_antisymm (hh v) ((q.iid n).nonneg v)
    have hs := (q.iid n).sum_one
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨v,hv⟩ := hex
  exact Finset.sum_pos' (fun v _ => mul_nonneg ((q.iid n).nonneg v) (Nat.cast_nonneg _))
    ⟨v,Finset.mem_univ v,mul_pos hv (hp v hv.ne')⟩

lemma conditional_passing_support (p : FinLaw Ω) (X : Ω → G) (C : Ω → α)
    (hit : α → G → Prop) (hs : ∀ ω, p ω≠0 → ¬hit (C ω) (X ω)) :
    p.cHf X C ≤ ∑ a, p.map C a*Real.log ((Finset.univ.filter (fun x => ¬hit a x)).card) := by
  have h := p.condH_le_support X C (fun a => Finset.univ.filter (fun x => ¬hit a x)) (by
    intro ω hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hs ω hw)
  simpa only [condH,← Hf_eq_H,cHf] using h

end FinLaw
end

namespace FinLaw
open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} [Fintype Ω]

lemma cHf_prefix_step (p : FinLaw Ω) {n k : ℕ} (X : Ω → Fin n → α)
    (C : Ω → β) (hk : k<n) :
    p.cHf (prefixVar X (Equiv.refl _) (k+1)) C =
      p.cHf (prefixVar X (Equiv.refl _) k) C+
        p.cHf (fun ω => X ω ⟨k,hk⟩) (fun ω => (prefixVar X (Equiv.refl _) k ω,C ω)) := by
  have he : p.cHf (prefixVar X (Equiv.refl _) (k+1)) C =
      p.cHf (fun ω => (prefixVar X (Equiv.refl _) k ω,X ω ⟨k,hk⟩)) C := by
    apply p.cHf_eq_of_fibers
    intro ω ν _
    constructor
    · intro h
      refine Prod.ext ?_ ?_
      · funext i
        by_cases hi : i.val<k
        · simpa only [prefixVar,hi,ite_eq_left,show i.val<k+1 by omega] using congrFun h i
        · simp [prefixVar,hi]
      · simpa [prefixVar] using congrFun h ⟨k,hk⟩
    · intro h
      funext i
      by_cases hi : i.val<k
      · simpa only [prefixVar,hi,ite_eq_left,show i.val<k+1 by omega] using
          congrFun (congrArg Prod.fst h) i
      · by_cases hie : i.val=k
        · have hi' : i=⟨k,hk⟩ := Fin.ext hie
          subst i
          simpa [prefixVar] using congrArg some (congrArg Prod.snd h)
        · simp [prefixVar,show ¬i.val<k+1 by omega]
  rw [he,p.cHf_chain]

lemma cHf_blocks_le (p : FinLaw Ω) {n : ℕ} (X : Ω → Fin n → α)
    (C : Ω → β) (S : Fin n → Ω → γ)
    (hS : ∀ i ω ν, prefixVar X (Equiv.refl _) i.val ω=prefixVar X (Equiv.refl _) i.val ν →
      C ω=C ν → S i ω=S i ν) :
    p.cHf X C ≤ ∑ i : Fin n, p.cHf (fun ω => X ω i) (S i) := by
  have h (k : ℕ) (hk : k≤n) : p.cHf (prefixVar X (Equiv.refl _) k) C ≤
      ∑ i : Fin k, p.cHf (fun ω => X ω ⟨i.val,by omega⟩) (S ⟨i.val,by omega⟩) := by
    induction k with
    | zero =>
      have he : p.cHf (prefixVar X (Equiv.refl _) 0) C = 0 := by
        unfold cHf
        have hh : p.Hf (fun ω => (prefixVar X (Equiv.refl _) 0 ω,C ω)) = p.Hf C := by
          apply p.Hf_eq_of_fibers
          intro ω ν
          simp only [prefixVar_zero,Prod.mk.injEq,true_and]
        rw [hh,sub_self]
      simp only [he,Finset.univ_eq_empty,Finset.sum_empty,le_refl]
    | succ k ih =>
      rw [p.cHf_prefix_step X C (by omega),Fin.sum_univ_castSucc]
      have hm := p.cHf_mono_of_refines (fun ω => X ω ⟨k,by omega⟩)
        (fun ω => (prefixVar X (Equiv.refl _) k ω,C ω)) (S ⟨k,by omega⟩)
        (fun ω ν hh => hS ⟨k,by omega⟩ ω ν (congrArg Prod.fst hh) (congrArg Prod.snd hh))
      exact add_le_add (ih (by omega)) hm
  have he : p.cHf (prefixVar X (Equiv.refl _) n) C=p.cHf X C := by
    apply p.cHf_eq_of_fibers
    intro ω ν _
    constructor
    · intro h
      funext i
      simpa [prefixVar,i.isLt] using congrFun h i
    · intro h
      funext i
      simp only [prefixVar,i.isLt,ite_eq_left,Equiv.refl_apply]
      exact congrArg some (congrFun h i)
  simpa only [he] using h n le_rfl

end FinLaw
end GaussianMoat

end OAI
