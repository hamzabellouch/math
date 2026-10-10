import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalCharges

namespace OAI

section
open Finset
open scoped Classical BigOperators

namespace SharpLogRamsey.Selection
variable {α β : Type*} [Fintype α] [Fintype β]

theorem entropy_le_cross (p : Law α) (q : α → ℝ) (hq : ∀ a, 0<q a)
    (hqt : ∑ a, q a ≤ 1) : entropy p ≤ -∑ a, p.mass a*Real.log (q a) := by
  have h (a : α) : p.mass a-q a ≤
      p.mass a*Real.log (p.mass a)-p.mass a*Real.log (q a) := by
    have H := mul_log_div_ge (p.nonneg a) (hq a).le (by intro hh; exact ((hq a).ne' hh).elim)
    by_cases ha : p.mass a=0
    · simpa [ha] using H
    · rw [Real.log_div ha (hq a).ne', mul_sub] at H
      exact H
  have HH := sum_le_sum (fun a (_ : a∈univ) => h a)
  simp only [sum_sub_distrib, p.total] at HH
  unfold entropy
  linarith

lemma geometric_subprob (l : α → ℕ) (hl : Function.Injective l) {r : ℝ}
    (hr : 0<r) (hr1 : r<1) : ∑ a, (1-r)*r^(l a) ≤ 1 := by
  have hs : (∑ n ∈ univ.image l, r^n) ≤ ∑' n : ℕ, r^n := by
    exact (summable_geometric_of_lt_one hr.le hr1).sum_le_tsum _ (fun _ _ => pow_nonneg hr.le _)
  rw [sum_image (fun _ _ _ _ he => hl he), tsum_geometric_of_lt_one hr.le hr1] at hs
  rw [← mul_sum]
  have H := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hr1.le)
  simpa only [mul_inv_cancel₀ (sub_pos.mpr hr1).ne'] using H

theorem integer_entropy (p : Law α) (l : α → ℕ) (hl : Function.Injective l)
    (M : ℝ) (hM : 0<M) (hm : ∑ a, p.mass a*(l a:ℝ) ≤ M) :
    entropy p ≤ Real.log (M+1)+1 := by
  let r := M/(M+1)
  have hr : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hc : 1-r=1/(M+1) := by dsimp [r]; field_simp; ring
  have H := entropy_le_cross p (fun a => (1-r)*r^(l a))
    (fun a => mul_pos (sub_pos.mpr hr1) (pow_pos hr _))
    (geometric_subprob l hl hr hr1)
  have he : -∑ a, p.mass a*Real.log ((1-r)*r^(l a)) =
      Real.log (M+1) + (∑ a, p.mass a*(l a:ℝ))*Real.log (1+1/M) := by
    have her : Real.log r = -Real.log (1+1/M) := by
      have heq : r=(1+1/M)⁻¹ := by dsimp [r]; field_simp
      rw [heq,Real.log_inv]
    have hlogc : Real.log (1-r) = -Real.log (M+1) := by
      rw [hc, Real.log_div one_ne_zero (by positivity : M+1≠0), Real.log_one, zero_sub]
    simp_rw [Real.log_mul (sub_pos.mpr hr1).ne' (pow_pos hr _).ne',
      Real.log_pow, hlogc,her]
    simp only [mul_add, mul_neg, sum_add_distrib, sum_neg_distrib,
      ← mul_assoc, ← sum_mul,p.total,one_mul]
    ring
  rw [he] at H
  have hlog0 : 0≤Real.log (1+1/M) := Real.log_nonneg (by
    have h : (0:ℝ)≤1/M := by positivity
    linarith)
  have hlog := Real.log_le_sub_one_of_pos (show 0<1+1/M by positivity)
  have hh := mul_le_mul_of_nonneg_left hlog hM.le
  have hx : M*(1+1/M-1)=1 := by field_simp; ring
  rw [hx] at hh
  have hm' := mul_le_mul_of_nonneg_right hm hlog0
  linarith

noncomputable def massLevel (p : Law α) (a : α) : ℕ := ⌊-Real.log (p.mass a)⌋₊

lemma massLevel_mean (p : Law α) :
    (∑ a, p.mass a*(massLevel p a:ℝ)) ≤ entropy p := by
  unfold entropy
  rw [←sum_neg_distrib]
  apply sum_le_sum
  intro a _
  by_cases hp : p.mass a=0
  · simp [hp]
  have hlog : 0 ≤ -Real.log (p.mass a) :=
    neg_nonneg.mpr (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))
  have H := mul_le_mul_of_nonneg_left (Nat.floor_le hlog) (p.nonneg a)
  simpa only [massLevel, mul_neg] using H

abbrev Levels (p : Law α) := {n // n ∈ (univ.image (massLevel p) : Finset ℕ)}

noncomputable def levelIndex (p : Law α) (a : α) : Levels p :=
  ⟨massLevel p a, mem_image.mpr ⟨a, mem_univ _, rfl⟩⟩

lemma level_entropy (p : Law α) :
    entropy (p.map (levelIndex p)) ≤ Real.log (entropy p+2)+1 := by
  have hh := integer_entropy (p.map (levelIndex p)) Subtype.val Subtype.val_injective
    (entropy p+1) (by linarith [entropy_nonneg p])
  have hm : ∑ n : Levels p, (p.map (levelIndex p)).mass n*(n.val:ℝ) ≤ entropy p+1 := by
    rw [p.sum_map]
    exact (massLevel_mean p).trans (by linarith)
  simpa only [show entropy p+1+1=entropy p+2 by ring] using hh hm

lemma same_level_weight (p : Law α) {a b : α} (ha : 0<p.mass a) (hb : 0<p.mass b)
    (he : massLevel p a=massLevel p b) : p.mass a ≤ Real.exp 1*p.mass b := by
  have ha0 : 0 ≤ -Real.log (p.mass a) :=
    neg_nonneg.mpr (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))
  have h₁ := Nat.floor_le ha0
  have h₂ := Nat.lt_floor_add_one (-Real.log (p.mass b))
  change -(Real.log (p.mass b)) < (massLevel p b:ℝ)+1 at h₂
  have hle : Real.log (p.mass a) ≤ 1+Real.log (p.mass b) := by
    change (massLevel p a:ℝ) ≤ -Real.log (p.mass a) at h₁
    rw [he] at h₁
    linarith
  calc
    _ = Real.exp (Real.log (p.mass a)) := (Real.exp_log ha).symm
    _ ≤ Real.exp (1+Real.log (p.mass b)) := Real.exp_le_exp.mpr hle
    _ = _ := by rw [Real.exp_add,Real.exp_log hb]

noncomputable def Law.onEvent (p : Law α) (E : Finset α) (hE : 0<p.event E) : Law E where
  mass a := p.mass a / p.event E
  nonneg a := div_nonneg (p.nonneg a) hE.le
  total := by
    rw [←sum_div, sum_coe_sort]
    exact div_self hE.ne'

lemma Law.onEvent_mean (p : Law α) (E : Finset α) (hE : 0<p.event E) (f : α→ℝ) :
    ∑ a : E, (p.onEvent E hE).mass a*f a = (∑ a∈E, p.mass a*f a)/p.event E := by
  simp only [Law.onEvent,div_mul_eq_mul_div,←sum_div]
  congr 1
  exact sum_coe_sort E (fun a => p.mass a*f a)

theorem support_average (p : Law α) (l : α→β) (G : β→Finset α)
    (R : Finset β) (hR : (1:ℝ)/2 ≤ (p.map l).event R)
    (hG : ∀ b∈R, 0<(G b).card)
    (hfiber : ∀ b∈R, ∀ a∈G b, l a=b)
    (hcharge : ∀ b∈R, ∀ a∈G b,
      (p.map l).mass b ≤ Real.exp 1*2*(G b).card*p.mass a) (a : α) :
    ∑ b : R, ((p.map l).onEvent R (by linarith)).mass b *
      (if a∈G b then 1/((G b).card:ℝ) else 0) ≤ 4*Real.exp 1*p.mass a := by
  have hp := p.nonneg a
  have hR0 : 0<(p.map l).event R := by linarith
  have he := (p.map l).onEvent_mean R hR0
    (fun b => if a∈G b then 1/((G b).card:ℝ) else 0)
  rw [he]
  have hsum : (∑ b∈R, (p.map l).mass b*(if a∈G b then 1/((G b).card:ℝ) else 0)) ≤
      2*Real.exp 1*p.mass a := by
    by_cases ha : l a∈R
    · rw [sum_eq_single_of_mem (l a) ha]
      · by_cases hg : a∈G (l a)
        · simp only [ite_eq_left hg,one_div]
          have H := hcharge (l a) ha a hg
          have hc : (0:ℝ)<(G (l a)).card := by exact_mod_cast hG (l a) ha
          have H' : (p.map l).mass (l a)/((G (l a)).card:ℝ) ≤
              2*Real.exp 1*p.mass a := (div_le_iff₀ hc).mpr (by nlinarith [H])
          simpa only [div_eq_mul_inv] using H'
        · simp only [ite_eq_right hg,mul_zero]
          positivity
      · intro b hb hba
        have hab : a∉G b := by intro hh; exact hba (hfiber b hb a hh).symm
        simp [hab]
    · have hz : ∀ b∈R, a∉G b := by
        intro b hb hh
        exact ha ((hfiber b hb a hh) ▸ hb)
      have : (∑ b∈R, (p.map l).mass b*(if a∈G b then 1/((G b).card:ℝ) else 0))=0 := by
        apply sum_eq_zero
        intro b hb
        simp [hz b hb]
      rw [this]
      positivity
  apply (div_le_iff₀ hR0).mpr
  calc
    _ ≤ 2*Real.exp 1*p.mass a := hsum
    _ = (4*Real.exp 1*p.mass a)*(1/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)

theorem partition_entropy (p : Law α) (l : α→β) (S : Finset α)
    (hs : ∀ a, a∉S → p.mass a=0) :
    entropy p ≤ entropy (p.map l)+
      ∑ b, (p.map l).mass b*Real.log (S.filter (fun a => l a=b)).card := by
  let T (b : β) := S.filter (fun a => l a=b)
  have hm (b : β) : ∑ a∈T b, p.mass a=(p.map l).mass b := by
    apply sum_subset (by
      intro a ha
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩)
    intro a ha hna
    apply hs
    intro haS
    apply hna
    exact mem_filter.mpr ⟨haS,(mem_filter.mp ha).2⟩
  have hlog (b : β) :
      (p.map l).mass b*Real.log ((p.map l).mass b)-
      (p.map l).mass b*Real.log (T b).card ≤ ∑ a∈T b, p.mass a*Real.log (p.mass a) := by
    have H := log_sum (T b) p.mass (fun _ => 1) (fun a _ => p.nonneg a)
      (by intros; norm_num) (by intro i hi hf; norm_num at hf)
    simp only [div_one,sum_const,nsmul_eq_mul,mul_one,hm] at H
    by_cases hb : (p.map l).mass b=0
    · simpa [hb] using H
    have hc : (T b).card≠0 := by
      intro he
      have hz : T b=∅ := card_eq_zero.mp he
      exact hb (by simpa [hz] using (hm b).symm)
    rw [Real.log_div hb (by exact_mod_cast hc),mul_sub] at H
    exact H
  have H := sum_le_sum (fun b (_ : b∈univ) => hlog b)
  have he : (∑ b, ∑ a∈T b, p.mass a*Real.log (p.mass a))=
      ∑ a, p.mass a*Real.log (p.mass a) := by
    rw [show (∑ b, ∑ a∈T b, p.mass a*Real.log (p.mass a))=
      ∑ a∈S, p.mass a*Real.log (p.mass a) from sum_fiberwise S l _]
    exact sum_subset (subset_univ S) (fun a _ hna => by rw [hs a hna,zero_mul])
  rw [sum_sub_distrib,he] at H
  unfold entropy
  dsimp only [T] at H
  linarith

theorem partition_loss (p : Law α) (l : α→β) (S : Finset α)
    (hs : ∀ a, a∉S → p.mass a=0) (loss : β→ℝ) (J : ℝ)
    (hc : ∀ b, 0<(p.map l).mass b →
      Real.log (S.filter (fun a => l a=b)).card ≤ J-loss b/2) :
    ∑ b, (p.map l).mass b*loss b ≤ 2*(J-entropy p+entropy (p.map l)) := by
  have hh (b : β) : (p.map l).mass b*Real.log (S.filter (fun a => l a=b)).card ≤
      (p.map l).mass b*(J-loss b/2) := by
    by_cases hz : (p.map l).mass b=0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hc b (lt_of_le_of_ne ((p.map l).nonneg b) (Ne.symm hz)))
        ((p.map l).nonneg b)
  have H := (partition_entropy p l S hs).trans (add_le_add_right (sum_le_sum (fun b _ => hh b)) _)
  simp only [mul_sub,←mul_div_assoc,sum_sub_distrib,←sum_mul,←sum_div,(p.map l).total,one_mul] at H
  linarith

noncomputable def levelSet (p : Law α) (b : Levels p) : Finset α :=
  univ.filter (fun a => 0<p.mass a ∧ levelIndex p a=b)

lemma levelSet_mass (p : Law α) (b : Levels p) :
    ∑ a∈levelSet p b, p.mass a=(p.map (levelIndex p)).mass b := by
  simp only [Law.map,levelSet,sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases ha : 0<p.mass a
  · simp [ha]
  · have hz : p.mass a=0 := le_antisymm (le_of_not_gt ha) (p.nonneg a)
    simp [hz]

lemma levelSet_charge (p : Law α) (b : Levels p) {a : α} (ha : a∈levelSet p b) :
    (p.map (levelIndex p)).mass b ≤ Real.exp 1*(levelSet p b).card*p.mass a := by
  rw [←levelSet_mass p b]
  have ha' := (mem_filter.mp ha).2
  calc
    _ ≤ ∑ _x∈levelSet p b, Real.exp 1*p.mass a := by
      apply sum_le_sum
      intro x hx
      have hx' := (mem_filter.mp hx).2
      apply same_level_weight p hx'.1 ha'.1
      exact congrArg Subtype.val (hx'.2.trans ha'.2.symm)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

lemma bad_level_charge (p : Law α) (b : Levels p) (good : Finset α)
    (hhalf : 2*((levelSet p b)∩good).card < (levelSet p b).card) :
    (p.map (levelIndex p)).mass b ≤
      2*Real.exp 1*(∑ a∈levelSet p b\good, p.mass a) := by
  let S := levelSet p b
  let B := S\good
  have hS : 0<S.card := by dsimp [S]; omega
  have hc : S.card ≤ 2*B.card := by
    have he := card_sdiff_add_card_inter S good
    dsimp [S,B] at *
    omega
  have hrow (b' : α) (hb' : b'∈B) :
      (p.map (levelIndex p)).mass b ≤ Real.exp 1*S.card*p.mass b' :=
    levelSet_charge p b (mem_sdiff.mp hb').1
  have H := sum_le_sum (fun a (ha : a∈B) => hrow a ha)
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at H
  have hm := (p.map (levelIndex p)).nonneg b
  have Hc : (S.card:ℝ) ≤ 2*(B.card:ℝ) := by exact_mod_cast hc
  have Hm := mul_le_mul_of_nonneg_right Hc hm
  have H₂ : (S.card:ℝ)*(p.map (levelIndex p)).mass b ≤
      (S.card:ℝ)*(2*Real.exp 1*(∑ a∈B,p.mass a)) := by nlinarith
  exact (mul_le_mul_iff_right₀ (show (0:ℝ)<S.card by exact_mod_cast hS)).mp H₂

lemma good_level_charge (p : Law α) (b : Levels p) (good : Finset α)
    (hhalf : (levelSet p b).card ≤ 2*((levelSet p b)∩good).card)
    {a : α} (ha : a∈(levelSet p b)∩good) :
    (p.map (levelIndex p)).mass b ≤
      Real.exp 1*2*((levelSet p b)∩good).card*p.mass a := by
  have hc : ((levelSet p b).card:ℝ) ≤ 2*(((levelSet p b)∩good).card:ℝ) := by exact_mod_cast hhalf
  have hpa := p.nonneg a
  have H := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Real.exp_nonneg 1)) hpa
  exact (levelSet_charge p b (mem_inter.mp ha).1).trans (by nlinarith [H])

lemma Law.mass_ext {p q : Law α} (h : p.mass=q.mass) : p=q := by
  cases p
  cases q
  cases h
  rfl

lemma Law.map_comp {γ : Type*} [Fintype γ] (p : Law α) (f : α→β) (g : β→γ) :
    (p.map f).map g=p.map (g∘f) := by
  exact p.map_map f g

lemma Law.map_prod_marginals {γ δ : Type*} [Fintype γ] [Fintype δ]
    (p : Law (α×β)) (f : α→γ) (g : β→δ) :
    (p.map (fun z => (f z.1,g z.2))).fst=p.fst.map f ∧
    (p.map (fun z => (f z.1,g z.2))).snd=p.snd.map g := by
  constructor
  · rw [←Law.map_fst,Law.map_comp,←Law.map_fst,Law.map_comp]
    rfl
  · rw [←Law.map_snd,Law.map_comp,←Law.map_snd,Law.map_comp]
    rfl

lemma endpoint_levels_entropy (p : Law (α×β)) :
    entropy (p.map (fun z => (levelIndex p.fst z.1,levelIndex p.snd z.2))) ≤
      Real.log (entropy p.fst+2)+Real.log (entropy p.snd+2)+2 := by
  have H := entropy_subadditive (p.map (fun z => (levelIndex p.fst z.1,levelIndex p.snd z.2)))
  have hm := p.map_prod_marginals (levelIndex p.fst) (levelIndex p.snd)
  rw [hm.1,hm.2] at H
  linarith [level_entropy p.fst,level_entropy p.snd]

noncomputable def levelLoss (p : Law α) (A : ℝ) (b : Levels p) : ℝ :=
  Real.log (A/(levelSet p b).card)

lemma levelLoss_nonneg (p : Law α) {A : ℝ} (b : Levels p)
    (hcap : ((levelSet p b).card:ℝ) ≤ A) : 0≤levelLoss p A b := by
  unfold levelLoss
  by_cases hz : (levelSet p b).card=0
  · simp [hz]
  · have hc : (0:ℝ)<(levelSet p b).card := by exact_mod_cast (Nat.pos_of_ne_zero hz)
    exact Real.log_nonneg ((le_div_iff₀ hc).mpr (by simpa using hcap))

lemma levelLoss_size (p : Law α) {A K : ℝ} (hA : 0<A) (b : Levels p)
    (hc : 0<(levelSet p b).card) (hl : levelLoss p A b≤K) :
    A*Real.exp (-K) ≤ (levelSet p b).card := by
  have hc' : (0:ℝ)<(levelSet p b).card := by exact_mod_cast hc
  have H := Real.exp_le_exp.mpr hl
  rw [levelLoss,Real.exp_log (div_pos hA hc')] at H
  have H' := (div_le_iff₀ hc').mp H
  calc
    _ ≤ (Real.exp K*(levelSet p b).card)*Real.exp (-K) :=
      mul_le_mul_of_nonneg_right H' (Real.exp_nonneg _)
    _ = _ := by rw [mul_right_comm,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]

lemma level_bad_total (p : Law α) (good : Finset α) :
    (∑ b : Levels p, ∑ a∈levelSet p b\good, p.mass a)=p.event (univ\good) := by
  have he (b : Levels p) : levelSet p b\good =
      univ.filter (fun a => 0<p.mass a ∧ levelIndex p a=b ∧ a∉good) := by
    ext a
    simp [levelSet,and_assoc]
  have he' : univ\good=univ.filter (fun a : α => a∉good) := by ext; simp
  change (∑ b : Levels p, ∑ a∈levelSet p b\good,p.mass a)=∑ a∈univ\good,p.mass a
  simp_rw [he,he',sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases ha : 0<p.mass a
  · by_cases hg : a∈good <;> simp [ha,hg]
  · have hz := le_antisymm (le_of_not_gt ha) (p.nonneg a)
    simp [hz]

noncomputable def retainedLevels (p : Law α) (good : Finset α) (A K : ℝ) : Finset (Levels p) :=
  univ.filter (fun b => 0<(levelSet p b).card ∧ levelLoss p A b≤K ∧
    (levelSet p b).card ≤ 2*((levelSet p b)∩good).card)

lemma retained_mass (p : Law α) (good : Finset α) {A K : ℝ} (hK : 0<K)
    (hcap : ∀ b, ((levelSet p b).card:ℝ)≤A) :
    1-(∑ b, (p.map (levelIndex p)).mass b*levelLoss p A b)/K-
      2*Real.exp 1*p.event (univ\good) ≤
      (p.map (levelIndex p)).event (retainedLevels p good A K) := by
  let q := p.map (levelIndex p)
  let R := retainedLevels p good A K
  have hpoint (b : Levels p) : q.mass b ≤
      (if b∈R then q.mass b else 0)+q.mass b*levelLoss p A b/K+
      2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by
    have hm := q.nonneg b
    have hl := levelLoss_nonneg p b (hcap b)
    have hb0 : 0≤∑ a∈levelSet p b\good,p.mass a := sum_nonneg (fun a _ => p.nonneg a)
    by_cases hb : b∈R
    · rw [ite_eq_left hb]
      have hh : 0≤q.mass b*levelLoss p A b/K := by positivity
      have hh' : 0≤2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by positivity
      linarith
    rw [ite_eq_right hb,zero_add]
    by_cases hc : (levelSet p b).card=0
    · have h0 : q.mass b=0 := by
        rw [show q.mass b=(∑ a∈levelSet p b,p.mass a) from (levelSet_mass p b).symm]
        simp [card_eq_zero.mp hc]
      simp only [h0,zero_mul,zero_div,zero_add]
      positivity
    by_cases hlow : levelLoss p A b≤K
    · have hf : 2*((levelSet p b)∩good).card < (levelSet p b).card := by
        by_contra! hn
        apply hb
        exact mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero hc,hlow,hn⟩
      have H := bad_level_charge p b good hf
      have hh : 0≤q.mass b*levelLoss p A b/K := by positivity
      exact H.trans (by linarith)
    · have H : q.mass b ≤ q.mass b*levelLoss p A b/K := by
        apply (le_div_iff₀ hK).mpr
        exact mul_le_mul_of_nonneg_left (le_of_not_ge hlow) hm
      have hh : 0≤2*Real.exp 1*(∑ a∈levelSet p b\good,p.mass a) := by positivity
      linarith
  have H := sum_le_sum (fun b (_ : b∈univ) => hpoint b)
  simp only [sum_add_distrib,←sum_div,←mul_sum,q.total,←sum_filter] at H
  rw [level_bad_total p good] at H
  have heR : univ.filter (fun b => b∈R)=R := by ext; simp
  rw [heR] at H
  change 1≤q.event R+(∑ b,q.mass b*levelLoss p A b)/K+2*Real.exp 1*p.event (univ\good) at H
  change 1-_/_-_≤q.event R
  linarith

theorem auxiliary_supports (p : Law α) (good : Finset α) {A K : ℝ}
    (hA : 0<A) (hK : 0<K) (hcap : ∀ b, ((levelSet p b).card:ℝ)≤A)
    (hbudget : (∑ b, (p.map (levelIndex p)).mass b*levelLoss p A b)/K+
      2*Real.exp 1*p.event (univ\good) ≤ 1/2) :
    ∃ ρ : Law (retainedLevels p good A K),
      (∀ b : retainedLevels p good A K,
        A*Real.exp (-K)/2 ≤ (((levelSet p b)∩good).card:ℝ) ∧
        (((levelSet p b)∩good).card:ℝ)≤A) ∧
      ∀ a, (∑ b : retainedLevels p good A K, ρ.mass b*
        (if a∈(levelSet p b)∩good then 1/((((levelSet p b)∩good).card):ℝ) else 0))
        ≤ 4*Real.exp 1*p.mass a := by
  let R := retainedLevels p good A K
  have hR : (1:ℝ)/2 ≤ (p.map (levelIndex p)).event R := by
    have H := retained_mass p good hK hcap
    change 1-_/_-_≤(p.map (levelIndex p)).event R at H
    linarith
  let ρ := (p.map (levelIndex p)).onEvent R (by linarith)
  refine ⟨ρ, ?_, ?_⟩
  · intro b
    have hb := (mem_filter.mp b.property).2
    have hh : ((levelSet p b).card:ℝ) ≤ 2*(((levelSet p b)∩good).card:ℝ) := by
      exact_mod_cast hb.2.2
    have hl := levelLoss_size p hA b hb.1 hb.2.1
    have hc : (((levelSet p b)∩good).card:ℝ) ≤ (levelSet p b).card := by
      exact_mod_cast card_le_card inter_subset_left
    exact ⟨by linarith, hc.trans (hcap b)⟩
  · intro a
    apply support_average p (levelIndex p) (fun b => levelSet p b∩good) R hR
    · intro b hb
      have hh := (mem_filter.mp hb).2
      have hp := hh.1
      have hs := hh.2.2
      omega
    · intro b hb a ha
      exact (mem_filter.mp (mem_inter.mp ha).1).2.2
    · intro b hb a ha
      exact good_level_charge p b good ((mem_filter.mp hb).2.2.2) ha

end SharpLogRamsey.Selection

end

end OAI
