import OAI.NumberTheory.GaussianMoat.EntropyBand

namespace OAI

universe uOmega uIota uGroup uAlpha uOutput uCapitalGamma uBeta uGamma uDelta

namespace GaussianMoat

namespace FinLaw
open scoped BigOperators Classical

lemma cHf_dpi_subadd {Ω : Type uOmega} {ι : Type uIota} [Fintype Ω] [Fintype ι]
    (G : ι → Type uGroup) (p : FinLaw Ω) (X : (i : ι) → Ω → G i) {α : Type uAlpha} (C : Ω → α) :
    p.cHf (fun ω i => X i ω) C ≤ ∑ i, p.cHf (X i) C := by
  let Y := fun ω i => (⟨i,X i ω⟩ : Σ i, G i)
  have he : p.cHf (fun ω i => X i ω) C = p.cHf Y C := by
    apply p.cHf_congr_fibers _ _ _ _
    · intro ω ν
      constructor
      · intro h; funext i; exact congrArg (Sigma.mk i) (congrFun h i)
      · intro h; funext i; exact Sigma.mk.inj_iff.mp (congrFun h i) |>.2 |> eq_of_heq
    · intro ω ν; rfl
  rw [he]
  apply (p.cHf_fintype_subadd Y C).trans
  apply Finset.sum_le_sum
  intro i _
  apply le_of_eq
  apply p.cHf_congr_fibers _ _ _ _
  · intro ω ν
    exact ⟨fun h => eq_of_heq (Sigma.mk.inj_iff.mp h).2,fun h => congrArg (Sigma.mk i) h⟩
  · intro ω ν; rfl

lemma joint_passing_entropy {ι : Type uIota} {O : Type uOutput} {Γ : Type uCapitalGamma} [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ)
    (htrue : ∀ a, p a≠0 → ∀ v, q a v≠0 → ∀ i, ¬ hit i v (a.2 i)) :
    (p.joint (fun a => (q a).iid n)).cHf (fun v => v.1.2)
      (fun v => (v.1.1,v.2)) ≤
      ∑ a, p a*(∑ i, ∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card) := by
  let P := p.joint (fun a => (q a).iid n)
  let C := fun v : (O × (∀ i, G i)) × (Fin n → Γ) => (v.1.1,v.2)
  have hcoordinate (i : ι) :
      P.cHf (fun v => v.1.2 i) C ≤ ∑ v, P v*Real.log (passingList (hit i) n v.2).card := by
    have hh := P.conditional_passing_support (fun v => v.1.2 i) C
      (fun c x => ∃ j, hit i (c.2 j) x) (by
        intro v hv
        have hm : p v.1≠0 ∧ (q v.1).iid n v.2≠0 := mul_ne_zero_iff.mp hv
        have hx := (q v.1).passingList_true (hit i) (v.1.2 i)
          (fun a ha => htrue v.1 hm.1 a ha i) n v.2 hm.2
        simpa only [passingList,Finset.mem_filter,Finset.mem_univ,true_and,not_exists] using hx)
    have hh' : P.cHf (fun v => v.1.2 i) C ≤
        ∑ c, (P.map C) c * Real.log (passingList (hit i) n c.2).card := by
      convert hh using 1
      apply Finset.sum_congr rfl
      intro c _
      simp only [passingList,not_exists]
    rw [expect_map] at hh'
    exact hh'
  have hs := P.cHf_dpi_subadd G (fun i v => v.1.2 i) C
  apply hs.trans
  apply (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoordinate i)).trans
  apply le_of_eq
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,← mul_assoc]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp only [P,joint_mass]

theorem passing_information_lower {ι : Type uIota} {O : Type uOutput} {Γ : Type uCapitalGamma} [Fintype ι] [Fintype O] [Fintype Γ]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw (O × (∀ i, G i))) (q : O × (∀ i, G i) → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (n : ℕ)
    (htrue : ∀ a, p a≠0 → ∀ v, q a v≠0 → ∀ i, ¬ hit i v (a.2 i))
    (Bad : ι → O × (∀ i, G i) → Prop) {A e η : ℝ} (hA : 0≤A)
    (hH : (∑ i, Real.log (Fintype.card (G i)))-e ≤ p.cHf Prod.snd Prod.fst)
    (hBad : (∑ i, p.prob (Bad i)) ≤ η)
    (hlist : ∀ a, p a≠0 → ∀ i,
      (∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1)) :
    A*((Fintype.card ι:ℝ)-η)-e ≤
      (n:ℝ)*(p.joint q).cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
  let P := p.joint (fun a => (q a).iid n)
  have hcond := joint_passing_entropy G p q hit n htrue
  have hsum : (∑ a, p a*(∑ i, ∑ v, (q a).iid n v*Real.log (passingList (hit i) n v).card)) ≤
      (∑ i, Real.log (Fintype.card (G i)))-A*((Fintype.card ι:ℝ)-∑ i, p.prob (Bad i)) := by
    calc
      _ ≤ ∑ a, p a*(∑ i, (Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1))) := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : p a=0
        · simp only [ha,zero_mul,le_refl]
        · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlist a ha i)) (p.nonneg a)
      _ = _ := by
        simp only [Finset.sum_sub_distrib,mul_sub,
          ← Finset.sum_mul,p.sum_one,one_mul]
        congr 1
        rw [mul_comm]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        have hh (i : ι) : (∑ a, p a*(if Bad i a then (0:ℝ) else 1))=1-p.prob (Bad i) := by
          rw [← p.prob_compl]
          unfold prob
          apply Finset.sum_congr rfl
          intro a _
          by_cases hb : Bad i a <;> simp [hb]
        have hh' (i : ι) : (∑ a, p a*(A*(if Bad i a then (0:ℝ) else 1)))=
            A*(1-p.prob (Bad i)) := by
          rw [← hh i,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
        simp only [hh',mul_sub,mul_one,Finset.sum_sub_distrib,Finset.sum_const,
          Finset.card_univ,nsmul_eq_mul]
  have hinit : P.cHf (fun v => v.1.2) (fun v => v.1.1)=p.cHf Prod.snd Prod.fst := by
    have hh := P.cHf_map Prod.fst Prod.snd Prod.fst
    rw [joint_map_fst] at hh
    exact hh.symm
  have hlow : A*((Fintype.card ι:ℝ)-η)-e ≤
      P.cIf (fun v => v.1.2) Prod.snd (fun v => v.1.1) := by
    unfold cIf
    rw [hinit]
    have hm := mul_le_mul_of_nonneg_left hBad hA
    change P.cHf (fun v => v.1.2) (fun v => (v.1.1,v.2)) ≤ _ at hcond
    linarith only [hH,hcond,hsum,hm]
  exact hlow.trans (conditional_iid_information p q n)

open scoped BigOperators Classical
variable {Ω : Type uOmega} {α : Type uAlpha} {Γ : Type uCapitalGamma} [Fintype Ω] [Fintype α] [Fintype Γ]

lemma conditionOn_support (p : FinLaw Ω) (C : Ω → α) (a : α)
    (ha : p.map C a≠0) (ω : Ω) (hω : p.conditionOn C a ω≠0) :
    p ω≠0 ∧ C ω=a := by
  have hh := p.conditionOn_weight C a ω
  have hn := mul_ne_zero ha hω
  rw [hh] at hn
  split_ifs at hn with hc
  · exact ⟨hn,hc⟩
  · exact False.elim (hn rfl)

lemma joint_conditionOn_mix (p : FinLaw Ω) (C : Ω → α) (q : Ω → FinLaw Γ) :
    (p.map C).joint (fun a => (p.conditionOn C a).mix q)=
      (p.joint q).map (fun v => (C v.1,v.2)) := by
  ext ⟨a,v⟩
  rw [joint_mass,mix_mass,Finset.mul_sum]
  conv_rhs => rw [map_mass,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [← mul_assoc,conditionOn_weight]
  simp only [joint_mass,Prod.mk.injEq]
  by_cases hc : C ω=a
  · simp only [hc,true_and,ite_true,Finset.sum_ite_eq',Finset.mem_univ]
  · simp only [hc,false_and,ite_false,zero_mul,Finset.sum_const_zero]

lemma mix_support (p : FinLaw Ω) (q : Ω → FinLaw Γ) (v : Γ)
    (hv : p.mix q v≠0) : ∃ ω, p ω≠0 ∧ q ω v≠0 := by
  rw [mix_mass] at hv
  obtain ⟨ω,_,hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact ⟨ω,(mul_ne_zero_iff.mp hω)⟩

lemma expected_log_card_passingList_le {G : Type uGroup} [Fintype G]
    (q : FinLaw Γ) (hit : Γ → G → Prop) (x : G)
    (htrue : ∀ v, q v≠0 → ¬hit v x) (n : ℕ) :
    (∑ v, q.iid n v*Real.log (passingList hit n v).card) ≤ Real.log (Fintype.card G) := by
  have hh (v : Fin n → Γ) : q.iid n v*Real.log (passingList hit n v).card ≤
      q.iid n v*Real.log (Fintype.card G) := by
    by_cases hv : q.iid n v=0
    · simp only [hv,zero_mul,le_refl]
    · apply mul_le_mul_of_nonneg_left _ ((q.iid n).nonneg v)
      apply Real.log_le_log
      · exact_mod_cast Finset.card_pos.mpr ⟨x,q.passingList_true hit x htrue n v hv⟩
      · exact_mod_cast Finset.card_le_univ (passingList hit n v)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hh v)
  simpa only [← Finset.sum_mul,(q.iid n).sum_one,one_mul] using hs

lemma cIf_map {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} (p : FinLaw Ω) (F : Ω → α)
    (X : α → β) (Y : α → γ) (Z : α → δ) :
    (p.map F).cIf X Y Z=p.cIf (X ∘ F) (Y ∘ F) (Z ∘ F) := by
  unfold cIf
  rw [cHf_map,cHf_map]
  rfl

theorem posterior_passing_information_lower {ι : Type uIota} {O : Type uOutput} [Fintype ι] [Fintype O]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (p : FinLaw Ω) (old : Ω → O) (X : Ω → ∀ i, G i) (q : Ω → FinLaw Γ)
    (hit : (i : ι) → Γ → G i → Prop) (Good : ι → Ω → Prop)
    (E : (i : ι) → Ω → Finset (G i)) (e c : ι → ℝ) {A H η : ℝ} (n : ℕ)
    (hA : 0≤A) (he : ∀ i, 0≤e i) (hc : ∀ i, 0≤c i)
    (htrue : ∀ ω, p ω≠0 → ∀ v, q ω v≠0 → ∀ i, ¬hit i v (X ω i))
    (hE : ∀ i ω, Good i ω → ((E i ω).card:ℝ)≤e i)
    (hhit : ∀ i ω, Good i ω → ∀ x∉E i ω, c i≤(q ω).prob (fun v => hit i v x))
    (hH : (∑ i, Real.log (Fintype.card (G i)))-H ≤ p.cHf X old)
    (hBad : (∑ i, p.prob (fun ω => ¬Good i ω))≤η)
    (hnum : ∀ i, Real.log (4*e i+(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4))) ≤
      Real.log (Fintype.card (G i))-A) :
    A*((Fintype.card ι:ℝ)-2*η)-H ≤
      (n:ℝ)*(p.joint q).cIf (fun v => X v.1) Prod.snd (fun v => old v.1) := by
  let C := fun ω => (old ω,X ω)
  let μ := p.map C
  let Q := fun a => (p.conditionOn C a).mix q
  let Bad := fun i a => (1/2:ℝ)<(p.conditionOn C a).prob (fun ω => ¬Good i ω)
  have hsurv (a : O × (∀ i, G i)) (ha : μ a≠0) (v : Γ) (hv : Q a v≠0) (i : ι) :
      ¬hit i v (a.2 i) := by
    obtain ⟨ω,hω,hv⟩ := (p.conditionOn C a).mix_support q v hv
    have hw := p.conditionOn_support C a ha ω hω
    have hx : X ω=a.2 := congrArg Prod.snd hw.2
    rw [← hx]
    exact htrue ω hw.1 v hv i
  have hH' : (∑ i, Real.log (Fintype.card (G i)))-H ≤ μ.cHf Prod.snd Prod.fst := by
    rw [cHf_map]
    exact hH
  have hBad' : (∑ i, μ.prob (Bad i))≤2*η := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      p.posterior_unfavorable C (fun ω => ¬Good i ω))
    simp only [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hBad (by norm_num))
  have hlist (a : O × (∀ i, G i)) (ha : μ a≠0) (i : ι) :
      (∑ v, (Q a).iid n v*Real.log (passingList (hit i) n v).card) ≤
        Real.log (Fintype.card (G i))-A*(if Bad i a then 0 else 1) := by
    by_cases hb : Bad i a
    · rw [ite_eq_left hb,mul_zero,sub_zero]
      exact (Q a).expected_log_card_passingList_le (hit i) (a.2 i)
        (fun v hv => hsurv a ha v hv i) n
    · rw [ite_eq_right hb,mul_one]
      have hg : (1/2:ℝ)≤(p.conditionOn C a).prob (Good i) := by
        have hh := (p.conditionOn C a).prob_compl (Good i)
        dsimp only [Bad] at hb
        push Not at hb
        linarith only [hh,hb]
      let F := Finset.univ.filter (fun x : G i =>
        (p.conditionOn C a).prob (fun ω => Good i ω ∧ x∉E i ω)<1/4)
      have hf : (F.card:ℝ)≤4*e i :=
        (p.conditionOn C a).mixed_exception_card (Good i) (E i) (he i) (hE i) hg
      have hm (x : G i) (hx : x∉F) : c i/4≤(Q a).prob (fun v => hit i v x) := by
        apply (p.conditionOn C a).mixed_floor q (Good i) (E i) (hit i) (hc i) (hhit i) x
        have hh : ¬(p.conditionOn C a).prob (fun ω => Good i ω ∧ x∉E i ω)<1/4 := by
          simpa only [F,Finset.mem_filter,Finset.mem_univ,true_and] using hx
        exact le_of_not_gt hh
      have ht := (Q a).expected_log_card_passingList (hit i) (a.2 i)
        (fun v hv => hsurv a ha v hv i) F hm n
      have hpos : (0:ℝ)<(Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)) := by
        have hcard : 0<Fintype.card (G i) := Fintype.card_pos_iff.mpr ⟨a.2 i⟩
        exact mul_pos (by exact_mod_cast hcard) (Real.exp_pos _)
      have hl := Real.log_le_log (by positivity : (0:ℝ)<(F.card:ℝ)+
        (Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))
        (add_le_add hf (le_refl ((Fintype.card (G i):ℝ)*Real.exp (-(n:ℝ)*(c i/4)))))
      exact ht.trans (hl.trans (hnum i))
  have hh := passing_information_lower G μ Q hit n hsurv Bad hA hH' hBad' hlist
  have hdist : μ.joint Q=(p.joint q).map (fun v => (C v.1,v.2)) :=
    p.joint_conditionOn_mix C q
  rw [hdist,cIf_map] at hh
  exact hh

end FinLaw
end GaussianMoat

end OAI
