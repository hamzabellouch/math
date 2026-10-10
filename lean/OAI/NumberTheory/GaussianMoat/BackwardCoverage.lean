import OAI.NumberTheory.GaussianMoat.GroupCoverage

namespace OAI

universe uOmega uAlpha uBeta uIota uCapitalGamma uGroup

namespace GaussianMoat
open scoped BigOperators Classical
namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma short_list_probability_deficit (p : FinLaw Ω) (X : Ω → α) (C : Ω → β)
    (L : β → Finset α) {b : ℝ} (hb : 1 ≤ b) :
    let a := p.prob (fun ω => X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)
    a*(Real.log (Fintype.card α)-Real.log b)-Real.binEntropy a ≤
      Real.log (Fintype.card α)-p.cHf X C := by
  dsimp only
  have hh := p.short_list_deficit X C L
    (fun ω => decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b)) hb
    (fun ω _ he => of_decide_eq_true he)
  have ha : (p.map (fun ω => decide (X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b))) true =
      p.prob (fun ω => X ω ∈ L (C ω) ∧ ((L (C ω)).card:ℝ) ≤ b) := by
    simp only [map_mass,decide_eq_true_eq,prob]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> rfl
  rw [ha] at hh
  simpa only [condH,← Hf_eq_H,cHf] using hh

lemma average_deficit_lower {ι : Type uIota} [Fintype ι] (w : FinLaw ι)
    (a d : ι → ℝ) {a₀ v : ℝ} (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (ha₀ : 0 < a₀) (hav : a₀ ≤ ∑ i, w i*a i)
    (hv : 2*(1-Real.log a₀) ≤ v)
    (hdef : ∀ i, a i*v-Real.binEntropy (a i) ≤ d i) :
    a₀*v/2 ≤ ∑ i, w i*d i := by
  let A := ∑ i, w i*a i
  have hA : 0 < A := lt_of_lt_of_le ha₀ hav
  have hA1 : A ≤ 1 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (ha i).2 (w.nonneg i))
    simpa only [mul_one,w.sum_one] using hh
  have ha₀1 : a₀ ≤ 1 := hav.trans hA1
  have hl : Real.log a₀ ≤ Real.log A := Real.log_le_log ha₀ hav
  have hl0 : Real.log a₀ ≤ 0 := Real.log_nonpos ha₀.le ha₀1
  have hv0 : 0 ≤ v := by linarith only [hv,hl0]
  have hh := w.binEntropy_sum_le a ha
  have hp := binEntropy_le_log_inverse hA hA1
  have hdl := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hdef i) (w.nonneg i))
  rw [show (∑ i, w i*(a i*v-Real.binEntropy (a i))) =
      A*v-∑ i, w i*Real.binEntropy (a i) by
        simp only [mul_sub,Finset.sum_sub_distrib,← mul_assoc,← Finset.sum_mul,A]] at hdl
  have hlog := mul_le_mul_of_nonneg_left hl hA.le
  have hmult := mul_le_mul_of_nonneg_left hv hA.le
  have ham := mul_le_mul_of_nonneg_right hav hv0
  change (∑ i, w i*Real.binEntropy (a i)) ≤ Real.binEntropy A at hh
  nlinarith only [hdl,hh,hp,hlog,hmult,ham]

theorem shared_coverage_deficit {Γ : Type uCapitalGamma} {G : Type uGroup} [Fintype Γ] [Fintype G] [AddCommGroup G]
    (p : FinLaw Ω) (q : Ω → FinLaw Γ) (Y : Ω → G) (h : Γ → G)
    (K : Finset G) (hK : K.Nonempty) (E : Ω → Finset G) (Bad : Ω → Prop)
    {τ δ ε b : ℝ} {n : ℕ} (hn : 0<n)
    (hτ : 0≤τ) (hτ1 : τ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hε : 0≤ε) (hb : 1≤b)
    (hp : (p.joint q).prob (fun v => Y v.1+h v.2∈K) ≤ τ*K.card/(Fintype.card G:ℝ))
    (hq : ∀ ω, ¬ Bad ω → ∀ y ∉ E ω, (τ+4*δ)/(Fintype.card G:ℝ) ≤ (q ω).map h y)
    (hE : ∀ ω, ¬ Bad ω → ((E ω).card:ℝ)/δ≤b)
    (herr : (Fintype.card G:ℝ)*Real.exp (-(n:ℝ)*δ^2*K.card/(2*(Fintype.card G:ℝ)))≤ε) :
    let P := p.joint (fun ω => (q ω).iid n)
    let L := fun v : Fin n → Γ => coverageList K n τ δ (fun i => h (v i))
    let a := P.prob (fun v => Y v.1 ∈ L v.2 ∧ ((L v.2).card:ℝ)≤b)
    δ/(τ+δ)-p.prob Bad-ε ≤ a ∧
      a*(Real.log (Fintype.card G)-Real.log b)-Real.binEntropy a ≤
        Real.log (Fintype.card G)-P.cHf (fun v => Y v.1) Prod.snd := by
  dsimp only
  constructor
  · have htrue := p.true_coverageList_probability q Y h K hK hτ hδ hn hp
    have hsize := p.coverageList_size_probability q h K hK E Bad hτ hτ1 hδ hδ1 hε n hq hE herr
    have hi := (p.joint (fun ω => (q ω).iid n)).prob_inter_ge
      (fun v => Y v.1 ∈ coverageList K n τ δ (fun i => h (v.2 i)))
      (fun v => ((coverageList K n τ δ (fun i => h (v.2 i))).card:ℝ)≤b)
    simp only [not_le] at hi
    linarith only [htrue,hsize,hi]
  · exact short_list_probability_deficit (p.joint (fun ω => (q ω).iid n))
      (fun v => Y v.1) Prod.snd
      (fun v => coverageList K n τ δ (fun i => h (v i))) hb

end FinLaw

lemma perm_expect_apply {ι : Type uIota} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (i : ι) :
    (𝔼 π : Equiv.Perm ι, f (π i)) = 𝔼 j, f j := by
  let : Nonempty ι := ⟨i⟩
  calc
    _ = 𝔼 j : ι, 𝔼 π : Equiv.Perm ι, f (π j) := by
      rw [show (fun j : ι => 𝔼 π : Equiv.Perm ι, f (π j)) =
        (fun _ => 𝔼 π : Equiv.Perm ι, f (π i)) by
          funext j; exact perm_expect_exchange f j i]
      simp only [Fintype.expect_const]
    _ = 𝔼 π : Equiv.Perm ι, 𝔼 j : ι, f (π j) := Finset.expect_comm _ _ _
    _ = _ := by
      have he (π : Equiv.Perm ι) : (𝔼 j, f (π j)) = 𝔼 j, f j :=
        Fintype.expect_equiv π _ _ (fun _ => rfl)
      simp only [he,Fintype.expect_const]

namespace FinLaw
variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] {k : ℕ}

lemma Hf_sub_le_cHf (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf X-p.Hf Y ≤ p.cHf X Y := by
  have h := p.Hf_pair_ge_snd Y X
  rw [p.Hf_pair_comm Y X] at h
  exact sub_le_sub_right h _

lemma orderedEntropy_conditioning (p : FinLaw Ω) (X : Ω → Fin k → α)
    (C : Ω → β) {b : ℕ} (hb : b ≤ k) :
    p.orderedEntropy X b-p.Hf C ≤
      b*(𝔼 i : Fin k, p.cHf (fun ω => X ω i) C) := by
  have hh (π : Equiv.Perm (Fin k)) :
      p.Hf (prefixVar X π b)-p.Hf C ≤
        ∑ i : Fin b, p.cHf (fun ω => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C := by
    apply (p.Hf_sub_le_cHf _ C).trans
    apply (p.cHf_le_of_determined _
      (fun ω (i : Fin b) => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C ?_).trans
      (p.cHf_fintype_subadd _ C)
    intro ω ν hx _
    funext i
    by_cases hi : i.val<b
    · simpa only [prefixVar,hi,ite_eq_left] using congrArg some (congrFun hx ⟨i.val,hi⟩)
    · simp only [prefixVar,hi,ite_false]
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hh π)
  have he (i : Fin b) :
      (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨i.val,lt_of_lt_of_le i.isLt hb⟩)) C) =
        𝔼 j : Fin k, p.cHf (fun ω => X ω j) C :=
    perm_expect_apply (fun j => p.cHf (fun ω => X ω j) C) _
  simpa only [orderedEntropy,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.expect_sum_comm,he,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] using hav

lemma signedEntropy_conditioning (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α)
    (C : Ω → β) {b : ℕ} (hb : b ≤ k) :
    p.signedEntropy X b-p.Hf C ≤
      b*(𝔼 σ : Fin k → Bool, 𝔼 i : Fin k, p.cHf (fun ω => X σ ω i) C) := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    p.orderedEntropy_conditioning (X σ) C hb)
  simpa only [signedEntropy,Finset.expect_sub_distrib,Fintype.expect_const,
    Finset.mul_expect] using h

end FinLaw

theorem SplitSieve.coverage_conditioning {Ω : Type uOmega} {β : Type uBeta} [Fintype Ω]
    (s : SplitSieve) (p : FinLaw Ω) (Y : Ω → GaussianInt) (C : Ω → β)
    {b : ℕ} (hb : b ≤ s.primes.card) :
    s.pointEntropy p Y b-p.Hf C ≤
      b*(𝔼 σ : Fin s.primes.card → Bool, 𝔼 i : Fin s.primes.card,
        p.cHf (fun ω => s.residueVector σ (Y ω) i) C) :=
  p.signedEntropy_conditioning _ C hb

namespace FinLaw

section

theorem backward_coverage_step {Ω : Type uOmega} {Γ : Type uCapitalGamma} {ι : Type uIota} [Fintype Ω] [Fintype Γ] [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)] [∀ i, AddCommGroup (G i)]
    (w : FinLaw ι) (p : FinLaw Ω) (q : Ω → FinLaw Γ)
    (Y : (i : ι) → Ω → G i) (h : (i : ι) → Γ → G i)
    (Bad₀ : ι → Prop) (Bad₁ : ι → Ω → Prop)
    (K : (i : ι) → Finset (G i)) (E : (i : ι) → Ω → Finset (G i))
    (b : ι → ℝ) {τ δ ε η η' e v : ℝ} {n : ℕ}
    (hn : 0 < n) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/64) (hε : 0 ≤ ε) (hη : 0 < η)
    (hnext : ∑ i, w i*p.prob (Bad₁ i) ≤ η')
    (hsmall : η'+ε ≤ η*δ/2)
    (hscale : 2*(1-Real.log (η*δ/2)) ≤ v)
    (hgap : e < η*δ*v/4)
    (hdata : (∑ i, w i*(Real.log (Fintype.card (G i))-
      (p.joint (fun ω => (q ω).iid n)).cHf (fun x => Y i x.1) Prod.snd)) ≤ e)
    (hK : ∀ i, Bad₀ i → (K i).Nonempty)
    (hb : ∀ i, Bad₀ i → 1 ≤ b i)
    (hv : ∀ i, Bad₀ i → v ≤ Real.log (Fintype.card (G i))-Real.log (b i))
    (hp : ∀ i, Bad₀ i → (p.joint q).prob (fun x => Y i x.1+h i x.2 ∈ K i) ≤
      τ*(K i).card/(Fintype.card (G i):ℝ))
    (hq : ∀ i, Bad₀ i → ∀ ω, ¬Bad₁ i ω → ∀ y ∉ E i ω,
      (τ+4*δ)/(Fintype.card (G i):ℝ) ≤ (q ω).map (h i) y)
    (hE : ∀ i, Bad₀ i → ∀ ω, ¬Bad₁ i ω → ((E i ω).card:ℝ)/δ ≤ b i)
    (herr : ∀ i, Bad₀ i → (Fintype.card (G i):ℝ)*
      Real.exp (-(n:ℝ)*δ^2*(K i).card/(2*(Fintype.card (G i):ℝ))) ≤ ε) :
    w.prob Bad₀ ≤ η := by
  let P := p.joint (fun ω => (q ω).iid n)
  let L := fun i (x : Fin n → Γ) => coverageList (K i) n τ δ (fun j => h i (x j))
  let a := fun i => if Bad₀ i then P.prob
    (fun x => Y i x.1 ∈ L i x.2 ∧ ((L i x.2).card:ℝ) ≤ b i) else 0
  let d := fun i => Real.log (Fintype.card (G i))-P.cHf (fun x => Y i x.1) Prod.snd
  have hd (i : ι) : 0 ≤ d i := by
    exact sub_nonneg.mpr ((P.cHf_le_Hf _ _).trans (P.Hf_le_log_card_type _))
  have ha (i : ι) : a i ∈ Set.Icc (0:ℝ) 1 := by
    dsimp only [a]
    split_ifs
    · exact ⟨P.prob_nonneg _,P.prob_le_one _⟩
    · norm_num
  have hstep (i : ι) (hi : Bad₀ i) :
      δ-p.prob (Bad₁ i)-ε ≤ a i ∧ a i*v-Real.binEntropy (a i) ≤ d i := by
    have hh := shared_coverage_deficit p q (Y i) (h i) (K i) (hK i hi) (E i) (Bad₁ i)
      hn hτ hτ1 hδ hδ1 hε (hb i hi) (hp i hi) (hq i hi) (hE i hi) (herr i hi)
    dsimp only at hh
    have hh' : δ/(τ+δ)-p.prob (Bad₁ i)-ε ≤ a i ∧
        a i*(Real.log (Fintype.card (G i))-Real.log (b i))-Real.binEntropy (a i) ≤ d i := by
      simpa only [a,hi,ite_eq_left,P,L,d] using hh
    constructor
    · have htd : 0 < τ+δ := by linarith only [hτ,hδ]
      have htd1 : τ+δ ≤ 1 := by linarith only [hτ1,hδ1]
      have hfrac : δ ≤ δ/(τ+δ) := (le_div_iff₀ htd).mpr (by nlinarith only [htd1,hδ])
      linarith only [hh'.1,hfrac]
    · have hm := mul_le_mul_of_nonneg_left (hv i hi) (ha i).1
      linarith only [hh'.2,hm]
  have hl (i : ι) : δ*(if Bad₀ i then (1:ℝ) else 0)-p.prob (Bad₁ i)-ε ≤ a i := by
    by_cases hi : Bad₀ i
    · simpa only [hi,ite_true,mul_one] using (hstep i hi).1
    · simp only [hi,ite_false,mul_zero,a]
      linarith only [p.prob_nonneg (Bad₁ i),hε]
  have hdef (i : ι) : a i*v-Real.binEntropy (a i) ≤ d i := by
    by_cases hi : Bad₀ i
    · exact (hstep i hi).2
    · simpa only [a,hi,ite_false,Real.binEntropy_zero,zero_mul,sub_zero] using hd i
  by_contra hc
  have hθη : η < w.prob Bad₀ := lt_of_not_ge hc
  have hlavg := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hl i) (w.nonneg i))
  have heq : (∑ i, w i*(δ*(if Bad₀ i then (1:ℝ) else 0)-p.prob (Bad₁ i)-ε)) =
      δ*w.prob Bad₀-(∑ i, w i*p.prob (Bad₁ i))-ε := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,w.sum_one,one_mul,prob,
      Finset.mul_sum]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq] at hlavg
  have hav : η*δ/2 ≤ ∑ i, w i*a i := by
    have hm := mul_le_mul_of_nonneg_left hθη.le hδ.le
    linarith only [hlavg,hm,hnext,hsmall]
  have hbnd := average_deficit_lower w a d ha (by positivity : 0 < η*δ/2) hav hscale hdef
  change (∑ i, w i*d i) ≤ e at hdata
  nlinarith only [hbnd,hdata,hgap]

variable {Ω : Type uOmega} {G : Type uGroup} [Fintype Ω] [Fintype G]

theorem low_mass_average {ι : Type uIota} [Fintype ι]
    (G : ι → Type uGroup) [∀ i, Fintype (G i)]
    (w : FinLaw ι) (p : (i : ι) → FinLaw (G i))
    (K : (i : ι) → Finset (G i)) (Bad : ι → Prop) {b e : ℝ}
    (hb : 0 < b)
    (hK : ∀ i, ∀ x ∈ K i, p i x ≤ (3/8:ℝ)/(Fintype.card (G i):ℝ))
    (hbad : ∀ i, Bad i → b ≤ ((K i).card:ℝ)/(8*(Fintype.card (G i):ℝ)))
    (hdef : (∑ i, w i*(Real.log (Fintype.card (G i))-(p i).entropy)) ≤ e) :
    w.prob Bad ≤ e/b := by
  have h (i : ι) : b*(if Bad i then (1:ℝ) else 0) ≤
      Real.log (Fintype.card (G i))-(p i).entropy := by
    by_cases hi : Bad i
    · simp only [hi,ite_true,mul_one]
      exact (hbad i hi).trans ((p i).low_mass_deficit (K i) (by
        intro x hx
        convert hK i x hx using 1; ring))
    · simp only [hi,ite_false,mul_zero]
      exact sub_nonneg.mpr (p i).entropy_le_log_card
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (h i) (w.nonneg i))
  have he : (∑ i, w i*(b*(if Bad i then (1:ℝ) else 0)))=b*w.prob Bad := by
    rw [prob,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [he] at hs
  apply (le_div_iff₀ hb).mpr
  linarith only [hs,hdef]

end

variable {Ω : Type uOmega} {α : Type uAlpha} {β : Type uBeta} [Fintype Ω] [Fintype α] [Fintype β]

lemma uniform_map_perm [Nonempty Ω] (e : Equiv.Perm Ω) : (uniform Ω).map e = uniform Ω := by
  ext x
  rw [map_equiv_mass]
  rfl

lemma prob_uniform (E : Ω → Prop) [Nonempty Ω] :
    (uniform Ω).prob E = ((Finset.univ.filter E).card:ℝ)/(Fintype.card Ω:ℝ) := by
  simp only [prob,uniform_mass,div_eq_mul_inv]
  rw [← Finset.sum_boole]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma uniform_no_wrap (n a : ℕ) (ha : a ≤ n+1) :
    (uniform (Fin (n+1))).prob (fun i => i.val+a<n+1) = 1-(a:ℝ)/(n+1) := by
  rw [prob_uniform]
  have he : (Finset.univ.filter (fun i : Fin (n+1) => i.val+a<n+1)) =
      Finset.univ.filter (fun i : Fin (n+1) => i.val<n+1-a) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hcard : (Finset.univ.filter (fun i : Fin (n+1) => i.val+a<n+1)).card = n+1-a := by
    rw [he,Fin.card_filter_val_lt,Nat.min_eq_right (by omega)]
  calc
    _ = ((n+1-a:ℕ):ℝ)/(n+1) := by
      congr 1
      · convert! congrArg (fun k : ℕ => (k:ℝ)) hcard using 1
        congr 2
        ext i
        simp
      · simp
    _ = _ := by
      rw [Nat.cast_sub ha,Nat.cast_add,Nat.cast_one]
      field_simp

lemma joint_perm_second (p : FinLaw Ω) {Γ : Type uCapitalGamma} [Fintype Γ] [Nonempty Γ]
    (e : Equiv.Perm Γ) :
    (p.joint (fun _ => uniform Γ)).map (fun v => (v.1,e v.2)) = p.joint (fun _ => uniform Γ) := by
  have h := joint_map_fiber p (fun _ => uniform Γ) (fun _ v => e v)
  simpa only [uniform_map_perm] using h

lemma smoothing_prob (p : FinLaw Ω) (t : Ω → ℕ) (n a : ℕ) (ha : a≤n)
    (E : ℕ → Prop) :
    (p.joint (fun _ => uniform (Fin (n+1)))).prob (fun v => E (t v.1+v.2.val)) ≤
      (p.joint (fun _ => uniform (Fin (n+1)))).prob (fun v => E (t v.1+v.2.val+a))+
        (a:ℝ)/(n+1) := by
  let e : Equiv.Perm (Fin (n+1)) := Equiv.addRight ⟨a,by omega⟩
  let P := p.joint (fun _ => uniform (Fin (n+1)))
  have hprob : P.prob (fun v => E (t v.1+(e v.2).val)) =
      P.prob (fun v => E (t v.1+v.2.val)) := by
    have hh := congrArg (fun Q : FinLaw (Ω × Fin (n+1)) => Q.prob
      (fun v => E (t v.1+v.2.val))) (p.joint_perm_second e)
    simpa only [prob_map] using hh
  have hgood : P.prob (fun v => v.2.val+a<n+1) = 1-(a:ℝ)/(n+1) := by
    rw [prob_joint]
    simp only [uniform_no_wrap n a (by omega),← Finset.sum_mul,p.sum_one,one_mul]
  have hE : P.prob (fun v => E (t v.1+(e v.2).val) ∧ v.2.val+a<n+1) ≤
      P.prob (fun v => E (t v.1+v.2.val+a)) := by
    apply P.prob_mono
    intro v hv
    have he : (e v.2).val = v.2.val+a := by
      change (v.2+(⟨a,by omega⟩ : Fin (n+1))).val = _
      exact Fin.val_add_eq_of_add_lt hv.2
    simpa only [he,Nat.add_assoc] using hv.1
  have hh := P.prob_inter_ge (fun v => E (t v.1+(e v.2).val)) (fun v => v.2.val+a<n+1)
  have hc := P.prob_compl (fun v => v.2.val+a<n+1)
  rw [hgood] at hc
  rw [hprob] at hh
  linarith only [hE,hh,hc]

lemma smoothing_condH (p : FinLaw Ω) (t : Ω → ℕ) (n a : ℕ) (ha : a≤n)
    (X : ℕ → α) (C : ℕ → β) :
    (p.joint (fun _ => uniform (Fin (n+1)))).condH
      (fun v => X (t v.1+v.2.val+a)) (fun v => C (t v.1+v.2.val+a)) ≤
    (p.joint (fun _ => uniform (Fin (n+1)))).condH
      (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val)) +
      2*Real.binEntropy ((a:ℝ)/(n+1))+
        ((a:ℝ)/(n+1))*(Real.log (Fintype.card α)+2*Real.log (Fintype.card β)) := by
  let e : Equiv.Perm (Fin (n+1)) := Equiv.addRight ⟨a,by omega⟩
  let P := p.joint (fun _ => uniform (Fin (n+1)))
  let good := fun v : Ω × Fin (n+1) => decide (v.2.val+a<n+1)
  have hm : P.map good true=1-(a:ℝ)/(n+1) := by
    have hh : P.map good true=P.prob (fun v => v.2.val+a<n+1) := by
      simp only [map_mass,good,prob,decide_eq_true_eq]
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> rfl
    rw [hh,prob_joint]
    simp only [uniform_no_wrap n a (by omega),
      ← Finset.sum_mul,p.sum_one,one_mul]
  have he : P.condH (fun v => X (t v.1+(e v.2).val)) (fun v => C (t v.1+(e v.2).val)) =
      P.condH (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val)) := by
    have hh := congrArg (fun Q : FinLaw (Ω × Fin (n+1)) =>
      Q.condH (fun v => X (t v.1+v.2.val)) (fun v => C (t v.1+v.2.val))) (p.joint_perm_second e)
    simpa only [condH,H_map,Function.comp_def] using hh
  have h := P.condH_sub_condH_of_agree
    (fun v => X (t v.1+v.2.val+a)) (fun v => X (t v.1+(e v.2).val))
    (fun v => C (t v.1+v.2.val+a)) (fun v => C (t v.1+(e v.2).val)) good (by
      intro v _ hv
      have hlt : v.2.val+a<n+1 := of_decide_eq_true hv
      have hev : (e v.2).val=v.2.val+a := Fin.val_add_eq_of_add_lt hlt
      simp only [hev,Nat.add_assoc,and_self])
  rw [hm,he,Real.binEntropy_one_sub] at h
  linarith only [h]

end FinLaw
end GaussianMoat

end OAI
