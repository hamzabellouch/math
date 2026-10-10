import OAI.Geometry.UnitDistances.Regularization

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section

structure Law (X : Type*) [Fintype X] where
  val : X  →  ℝ
  nonneg : ∀ x, 0  ≤  val x
  total : ∑ x, val x = 1

variable {X Y : Type*} [Fintype X] [Fintype Y]

def avg (μ : Law X) (f : X  →  ℝ) : ℝ := ∑ x,μ.val x*f x

def event (μ : Law X) (P : X  →  Prop) : ℝ := by
  classical
  exact avg μ (fun x => if P x then 1 else 0)

lemma avg_congr (μ : Law X) {f g : X → ℝ} (h : ∀ x, f x = g x) : avg μ f = avg μ g := by
  unfold avg
  exact sum_congr rfl (fun x _ => congrArg (μ.val x * ·) (h x))
lemma avg_ite (μ : Law X) (P : X → Prop) [DecidablePred P] :
    avg μ (fun x => if P x then 1 else 0) = event μ P := by
  unfold event
  apply avg_congr
  intro x
  split_ifs <;> rfl

lemma avg_const (μ : Law X) (c : ℝ) : avg μ (fun _ => c) = c := by
  simp [avg,← sum_mul,μ.total]
lemma avg_add (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x+g x)=avg μ f+avg μ g := by simp [avg,mul_add,sum_add_distrib]
lemma avg_sub (μ : Law X) (f g : X  →  ℝ) :
    avg μ (fun x => f x-g x)=avg μ f-avg μ g := by simp [avg,mul_sub,sum_sub_distrib]
lemma avg_smul (μ : Law X) (c : ℝ) (f : X  →  ℝ) :
    avg μ (fun x => c*f x)=c*avg μ f := by simp [avg,mul_left_comm, mul_sum]
lemma avg_mono (μ : Law X) {f g : X  →  ℝ} (h : ∀ x,f x ≤ g x) : avg μ f ≤ avg μ g :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x)
lemma avg_nonneg (μ : Law X) {f : X  →  ℝ} (h : ∀ x,0 ≤ f x) : 0 ≤ avg μ f :=
  sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (h x)
lemma avg_le_const (μ : Law X) {f : X  →  ℝ} {c : ℝ} (h : ∀ x,f x ≤ c) : avg μ f ≤ c :=
  (avg_mono μ h).trans_eq (avg_const μ c)
lemma const_le_avg (μ : Law X) {f : X  →  ℝ} {c : ℝ} (h : ∀ x,c ≤ f x) : c ≤ avg μ f :=
  (avg_const μ c).symm.trans_le (avg_mono μ h)
lemma event_nonneg (μ : Law X) (P : X  →  Prop) : 0 ≤ event μ P := by
  classical
  apply avg_nonneg; intro x; split <;> norm_num
lemma event_le_one (μ : Law X) (P : X  →  Prop) : event μ P ≤ 1 := by
  classical
  apply avg_le_const; intro x; split <;> norm_num
lemma event_compl (μ : Law X) (P : X  →  Prop) : event μ (fun x => ¬P x)=1-event μ P := by
  classical
  calc
    event μ (fun x => ¬P x) = avg μ (fun x => 1 - if P x then 1 else 0) := by
      apply avg_congr
      intro x
      split_ifs <;> simp_all
    _ = 1 - event μ P := by rw [avg_sub,avg_const,avg_ite]
lemma event_mono (μ : Law X) {P Q : X  →  Prop} (h : ∀ x,P x → Q x) : event μ P ≤ event μ Q := by
  classical
  apply avg_mono; intro x; split_ifs <;> simp_all
lemma event_union_le (μ : Law X) (P Q : X  →  Prop) :
    event μ (fun x => P x ∨ Q x) ≤ event μ P+event μ Q := by
  classical
  unfold event
  rw [← avg_add]
  apply avg_mono; intro x; split_ifs <;> simp_all

def pair (μ : Law X) (ν : Law Y) : Law (X×Y) where
  val x := μ.val x.1*ν.val x.2
  nonneg x := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by simp [Fintype.sum_prod_type,← mul_sum,ν.total,μ.total]

lemma pair_avg (μ : Law X) (ν : Law Y) (f : X×Y → ℝ) :
    avg (pair μ ν) f=avg μ (fun x => avg ν (fun y => f (x,y))) := by
  simp [avg,pair,Fintype.sum_prod_type,mul_sum,mul_assoc]
lemma pair_fst (μ : Law X) (ν : Law Y) (f : X → ℝ) :
    avg (pair μ ν) (fun x => f x.1)=avg μ f := by
  rw [pair_avg]; simp_rw [avg_const]
lemma pair_snd (μ : Law X) (ν : Law Y) (f : Y → ℝ) :
    avg (pair μ ν) (fun x => f x.2)=avg ν f := by
  rw [pair_avg]; dsimp only; rw [avg_const]
lemma pair_prod (μ : Law X) (ν : Law Y) (f : X → ℝ) (g : Y → ℝ) :
    avg (pair μ ν) (fun x => f x.1*g x.2)=avg μ f*avg ν g := by
  rw [pair_avg]; dsimp only; simp_rw [avg_smul];
  simp only [avg, ← mul_assoc, sum_mul]
lemma pair_union (μ : Law X) (P : X → Prop) :
    event (pair μ μ) (fun x => P x.1 ∨ P x.2)  ≤  2*event μ P := by
  classical
  have h := event_union_le (pair μ μ) (fun x => P x.1) (fun x => P x.2)
  have h₁ : event (pair μ μ) (fun x => P x.1) = event μ P := by
    rw [← avg_ite (pair μ μ) (fun x => P x.1), ← avg_ite μ P]
    exact pair_fst μ μ (fun x => if P x then 1 else 0)
  have h₂ : event (pair μ μ) (fun x => P x.2) = event μ P := by
    rw [← avg_ite (pair μ μ) (fun x => P x.2), ← avg_ite μ P]
    exact pair_snd μ μ (fun x => if P x then 1 else 0)
  rw [h₁,h₂] at h
  linarith
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.StrictCross
open Set
variable {A B : Type*}

def Adj (x y : A × B) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (x.1 ≠ y.1 ∧ x.2 = y.2)

lemma symm {x y : A × B} (h : Adj x y) : Adj y x := by
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨h₁.symm,Ne.symm h₂⟩
  · exact Or.inr ⟨Ne.symm h₁,h₂.symm⟩

lemma same_row {a : A} {b c : B} (hbc : b ≠ c) (x : A × B) :
    Adj x (a,b) ∧ Adj x (a,c) ↔ x.1=a ∧ x.2≠b ∧ x.2≠c := by
  simp only [Adj]
  constructor
  · rintro ⟨h,h'⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rcases h' with ⟨_,hc⟩ | ⟨hc,_⟩
      · exact ⟨ha,hb,hc⟩
      · exact (hc ha).elim
    · rcases h' with ⟨hc,_⟩ | ⟨_,hc⟩
      · exact (ha hc).elim
      · exact (hbc (hb.symm.trans hc)).elim
  · rintro ⟨ha,hb,hc⟩; exact ⟨Or.inl ⟨ha,hb⟩,Or.inl ⟨ha,hc⟩⟩

lemma swap_iff (x y : A × B) : Adj x.swap y.swap ↔ Adj x y := by
  simp only [Adj,Prod.fst_swap,Prod.snd_swap]
  tauto

lemma same_column {a c : A} {b : B} (hac : a ≠ c) (x : A × B) :
    Adj x (a,b) ∧ Adj x (c,b) ↔ x.2=b ∧ x.1≠a ∧ x.1≠c := by
  have h := same_row (a := b) hac x.swap
  rw [show (b,a) = (a,b).swap from rfl, show (b,c) = (c,b).swap from rfl,
    swap_iff,swap_iff] at h
  exact h

lemma corners {a c : A} {b d : B} (hac : a ≠ c) (hbd : b ≠ d) (x : A × B) :
    Adj x (a,b) ∧ Adj x (c,d) ↔ x=(a,d) ∨ x=(c,b) := by
  constructor
  · rintro ⟨h,h'⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rcases h' with ⟨hc,hd⟩ | ⟨hc,hd⟩
    · exact (hac (ha.symm.trans hc)).elim
    · exact Or.inl (Prod.ext ha hd)
    · exact Or.inr (Prod.ext hc hb)
    · exact (hbd (hb.symm.trans hd)).elim
  · rintro (rfl|rfl) <;> simp [Adj,hac,hbd,Ne.symm hac,Ne.symm hbd]

lemma third_off_row {a c : A} {b d e : B} (hbd : b ≠ d) (hac : a ≠ c)
    (x : A × B) (h₁ : Adj x (a,b)) (h₂ : Adj x (a,d)) (h₃ : Adj x (c,e)) :
    x=(a,e) := by
  have hx := (same_row hbd x).mp ⟨h₁,h₂⟩
  rcases h₃ with h | h
  · exact (hac (hx.1.symm.trans h.1)).elim
  · exact Prod.ext hx.1 h.2

lemma three_independent {a c e : A} {b d f : B}
    (hac : a ≠ c) (hae : a ≠ e) (hce : c ≠ e)
    (hbd : b ≠ d) (hbf : b ≠ f) (hdf : d ≠ f) (x : A × B) :
    ¬(Adj x (a,b) ∧ Adj x (c,d) ∧ Adj x (e,f)) := by
  rintro ⟨h₁,h₂,h₃⟩
  rcases (corners hac hbd x).mp ⟨h₁,h₂⟩ with h|h <;> rw [h] at h₃
  · simp [Adj,hae,hdf] at h₃
  · simp [Adj,hce,hbf] at h₃

theorem classification (Y : Finset (A × B)) :
    Y.card ≤ 1 ∨
    (∃ y∈Y, ∃ z∈Y, y≠z ∧ y.1=z.1 ∧
      ((∀ w∈Y,w.1=y.1) ∨ ∃ w∈Y,w.1≠y.1)) ∨
    (∃ y∈Y, ∃ z∈Y, y≠z ∧ y.2=z.2 ∧
      ((∀ w∈Y,w.2=y.2) ∨ ∃ w∈Y,w.2≠y.2)) ∨
    (∃ y∈Y, ∃ z∈Y, y.1≠z.1 ∧ y.2≠z.2 ∧
      ((∀ w∈Y,w=y ∨ w=z) ∨ ∃ w∈Y,
        y.1≠w.1 ∧ z.1≠w.1 ∧ y.2≠w.2 ∧ z.2≠w.2)) := by
  classical
  by_cases hs : Y.card ≤ 1
  · exact Or.inl hs
  have he : ∃ y∈Y,∃ z∈Y,y≠z := by
    by_contra! h
    exact hs (Finset.card_le_one.mpr h)
  rcases he with ⟨y,hy,z,hz,hyz⟩
  by_cases hr : ∃ y∈Y,∃ z∈Y,y≠z ∧ y.1=z.1
  · obtain ⟨y,hy,z,hz,hn,he⟩ := hr
    refine Or.inr (Or.inl ⟨y,hy,z,hz,hn,he,?_⟩)
    by_cases hw : ∀ w∈Y,w.1=y.1
    · exact Or.inl hw
    · exact Or.inr (by simpa only [not_forall,exists_prop] using hw)
  by_cases hc : ∃ y∈Y,∃ z∈Y,y≠z ∧ y.2=z.2
  · obtain ⟨y,hy,z,hz,hn,he⟩ := hc
    refine Or.inr (Or.inr (Or.inl ⟨y,hy,z,hz,hn,he,?_⟩))
    by_cases hw : ∀ w∈Y,w.2=y.2
    · exact Or.inl hw
    · exact Or.inr (by simpa only [not_forall,exists_prop] using hw)
  have h₁ : ∀ u∈Y,∀ v∈Y,u≠v → u.1≠v.1 := by
    intro u hu v hv hn he; exact hr ⟨u,hu,v,hv,hn,he⟩
  have h₂ : ∀ u∈Y,∀ v∈Y,u≠v → u.2≠v.2 := by
    intro u hu v hv hn he; exact hc ⟨u,hu,v,hv,hn,he⟩
  refine Or.inr (Or.inr (Or.inr ⟨y,hy,z,hz,h₁ y hy z hz hyz,h₂ y hy z hz hyz,?_⟩))
  by_cases hw : ∀ w∈Y,w=y ∨ w=z
  · exact Or.inl hw
  · obtain ⟨w,hw,hwy,hwz⟩ : ∃ w∈Y,w≠y ∧ w≠z := by
      simpa only [not_forall,not_or,exists_prop] using hw
    exact Or.inr ⟨w,hw,h₁ y hy w hw (Ne.symm hwy),h₁ z hz w hw (Ne.symm hwz),
      h₂ y hy w hw (Ne.symm hwy),h₂ z hz w hw (Ne.symm hwz)⟩

noncomputable def coefficient (r : ℝ) : ℝ :=
  if |r-1/2| ≤ (1/100:ℝ) then 1+1/20000 else 1-1/20000

lemma coefficient_lower (r : ℝ) : 1-1/20000 ≤ coefficient r := by
  unfold coefficient; split <;> norm_num

lemma score_polynomial (r : ℝ) :
    coefficient r * (r^2+(1-r)^2)-2*r*(1-r) ≥ (1/40000:ℝ) := by
  unfold coefficient
  split_ifs with h
  · nlinarith [sq_nonneg (2*r-1)]
  · have hn : (1/100:ℝ) < |r-1/2| := lt_of_not_ge h
    have hh : (1/100:ℝ)^2 < |r-1/2|^2 := (sq_lt_sq₀ (by norm_num) (abs_nonneg _)).mpr hn
    rw [sq_abs] at hh
    nlinarith [sq_nonneg (2*r-1)]
end PlanarUnitDistances.StrictCross

namespace PlanarUnitDistances.StarScore
open FiniteLaw StrictCross
noncomputable section
variable {X A B : Type*} [Fintype X]

def frequency (μ : Law X) (bit : X  →  Bool) : ℝ := event μ (fun x => bit x=true)
def variation (μ : Law X) (bit : X  →  Bool) : ℝ := 2*frequency μ bit*(1-frequency μ bit)

def slot (r : ℝ) (bit : X  →  Bool) (state : X  →  A×B) (x y : X) : ℝ := by
  classical
  exact if bit x ≠ bit y then -1 else
    if bit x then (if (state x).2=(state y).2 then coefficient r else 0)
    else (if (state x).1=(state y).1 then coefficient r else 0)

def score (μ : Law X) (bit : X  →  Bool) (state : X  →  A×B) : ℝ :=
  avg (pair μ μ) (fun xy => slot (frequency μ bit) bit state xy.1 xy.2)

lemma frequency_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ frequency μ bit := event_nonneg _ _
lemma frequency_le_one (μ : Law X) (bit : X  →  Bool) : frequency μ bit ≤ 1 := event_le_one _ _
lemma variation_nonneg (μ : Law X) (bit : X  →  Bool) : 0 ≤ variation μ bit := by
  unfold variation
  exact mul_nonneg (mul_nonneg (by norm_num) (frequency_nonneg _ _))
    (sub_nonneg.mpr (frequency_le_one _ _))
lemma variation_le_half (μ : Law X) (bit : X  →  Bool) : variation μ bit ≤ 1/2 := by
  unfold variation; nlinarith [sq_nonneg (frequency μ bit-1/2)]

lemma coefficient_upper (r : ℝ) : coefficient r ≤ 2 := by
  unfold coefficient; split <;> norm_num
lemma coefficient_nonneg (r : ℝ) : 0 ≤ coefficient r := by
  linarith [coefficient_lower r]
omit [Fintype X] in
lemma slot_lower (r : ℝ) (bit : X → Bool) (state : X → A×B) (x y : X) :
    -1 ≤ slot r bit state x y := by
  unfold slot
  split_ifs <;> linarith [coefficient_nonneg r]
omit [Fintype X] in
lemma slot_upper (r : ℝ) (bit : X → Bool) (state : X → A×B) (x y : X) :
    slot r bit state x y ≤ 2 := by
  unfold slot
  split_ifs <;> linarith [coefficient_upper r]

lemma mismatch (μ : Law X) (bit : X → Bool) :
    event (pair μ μ) (fun x => bit x.1≠bit x.2)=variation μ bit := by
  classical
  let f : X → ℝ := fun x => if bit x then 1 else 0
  have he (x : X×X) : (if bit x.1≠bit x.2 then (1:ℝ) else 0)=
      f x.1+f x.2-2*(f x.1*f x.2) := by
    dsimp [f]; cases h₁ : bit x.1 <;> cases h₂ : bit x.2 <;> norm_num
  rw [← avg_ite]
  have heq := avg_congr (pair μ μ) he
  rw [heq]
  rw [avg_sub,avg_add,avg_smul,pair_fst,pair_snd,pair_prod]
  have hf : avg μ f = frequency μ bit := by
    dsimp only [f,frequency]
    exact avg_ite _ _
  rw [hf]
  unfold variation; ring

lemma score_lower (μ : Law X) (bit : X → Bool) (state : X → A×B) :
    -variation μ bit ≤ score μ bit state := by
  classical
  have h (x : X×X) : -(if bit x.1≠bit x.2 then (1:ℝ) else 0)  ≤
      slot (frequency μ bit) bit state x.1 x.2 := by
    unfold slot; split_ifs <;> simp_all [coefficient_nonneg]
  have ha := avg_mono (pair μ μ) h
  have he : (fun x : X×X => -(if bit x.1 ≠ bit x.2 then (1:ℝ) else 0))=
      (fun x => (-1)*(if bit x.1≠bit x.2 then (1:ℝ) else 0)) := by funext; ring
  rw [he,avg_smul] at ha
  rw [avg_ite,mismatch,neg_one_mul] at ha
  exact ha

lemma score_ge_half_neg (μ : Law X) (bit : X → Bool) (state : X → A×B) :
    -(1/2:ℝ) ≤ score μ bit state := le_trans (by linarith [variation_le_half μ bit])
      (score_lower μ bit state)

theorem determined (μ : Law X) (bit : X → Bool) (state : X → A×B) (good : X → Prop)
    (h : ∀ x y,good x → good y → bit x=bit y → state x=state y) :
    (1/40000:ℝ)-6*event μ (fun x => ¬good x) ≤ score μ bit state := by
  classical
  let c := coefficient (frequency μ bit)
  have hpoint (x : X×X) :
      c-(c+1)*(if bit x.1≠bit x.2 then (1:ℝ) else 0)-
        3*(if ¬good x.1 ∨ ¬good x.2 then (1:ℝ) else 0)  ≤
      slot (frequency μ bit) bit state x.1 x.2 := by
    by_cases hg : good x.1 ∧ good x.2
    · have hg' : ¬(¬good x.1 ∨ ¬good x.2) := by tauto
      simp only [hg',ite_false,mul_zero,sub_zero]
      by_cases hb : bit x.1=bit x.2
      · have hs := h _ _ hg.1 hg.2 hb
        simp [slot,hb,hs,c]
      · simp [slot,hb]
    · have hbad : ¬good x.1 ∨ ¬good x.2 := by tauto
      simp only [hbad,ite_true,mul_one]
      have hc : c ≤ 2 := coefficient_upper _
      by_cases hb : bit x.1=bit x.2
      · simp only [hb,ne_eq,not_true_eq_false,ite_false,mul_zero,sub_zero]
        linarith [slot_lower (frequency μ bit) bit state x.1 x.2]
      · simp only [hb,ne_eq,not_false_eq_true,ite_true,mul_one]
        linarith [slot_lower (frequency μ bit) bit state x.1 x.2]
  have ha := avg_mono (pair μ μ) hpoint
  rw [avg_sub,avg_sub,avg_const,avg_smul,avg_smul] at ha
  rw [avg_ite,avg_ite] at ha
  rw [mismatch] at ha
  have hu := pair_union μ (fun x => ¬good x)
  have hn := score_polynomial (frequency μ bit)
  change c * _ - _  ≥  _ at hn
  unfold variation at ha
  unfold score
  nlinarith

theorem constant_good (μ : Law X) (bit : X → Bool) (state : X → A×B) (good : X → Prop)
    (h : ∀ x y,good x → good y → bit x=bit y ∧ state x=state y) :
    (1-1/20000:ℝ)-4*event μ (fun x => ¬good x) ≤ score μ bit state := by
  classical
  have hpoint (x : X×X) : (1-1/20000:ℝ)-
      2*(if ¬good x.1 ∨ ¬good x.2 then (1:ℝ) else 0)  ≤
      slot (frequency μ bit) bit state x.1 x.2 := by
    by_cases hg : good x.1 ∧ good x.2
    · have hg' : ¬(¬good x.1 ∨ ¬good x.2) := by tauto
      obtain ⟨hb,hs⟩ := h _ _ hg.1 hg.2
      simpa [slot,hg',hb,hs] using coefficient_lower (frequency μ bit)
    · have hbad : ¬good x.1 ∨ ¬good x.2 := by tauto
      simp only [hbad,ite_true,mul_one]
      linarith [slot_lower (frequency μ bit) bit state x.1 x.2]
  have ha := avg_mono (pair μ μ) hpoint
  rw [avg_sub,avg_const,avg_smul] at ha
  rw [avg_ite] at ha
  unfold score
  linarith [pair_union μ (fun x => ¬good x)]

theorem constant_bit (μ : Law X) (bit : X → Bool) (good : X → Prop)
    (h : ∀ x y,good x → good y → bit x=bit y) :
    variation μ bit ≤ 2*event μ (fun x => ¬good x) := by
  rw [← mismatch]
  apply le_trans (event_mono (pair μ μ) (fun x hx => ?_)) (pair_union μ (fun x => ¬good x))
  by_contra! he
  exact hx (h _ _ he.1 he.2)
end
end PlanarUnitDistances.StarScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
open scoped Classical
variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberMass (μ : Law X) (φ : X → Y) (y : Y) : ℝ := event μ (fun x => φ x=y)

omit [Fintype Y] in
lemma fiberMass_eq (μ : Law X) (φ : X → Y) (y : Y) :
    fiberMass μ φ y = ∑ x, if φ x=y then μ.val x else 0 := by
  classical
  unfold fiberMass event avg
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp_all
omit [Fintype Y] in
lemma fiberMass_nonneg (μ : Law X) (φ : X → Y) (y : Y) : 0 ≤ fiberMass μ φ y :=
  event_nonneg _ _
omit [Fintype Y] in
lemma atom_le_fiber (μ : Law X) (φ : X → Y) (x : X) : μ.val x ≤ fiberMass μ φ (φ x) := by
  classical
  rw [fiberMass_eq]
  have h := single_le_sum (s := univ) (f := fun y => if φ y=φ x then μ.val y else 0)
    (fun y _ => by split_ifs <;> simp [μ.nonneg]) (mem_univ x)
  simpa using h
lemma fiberMass_total (μ : Law X) (φ : X → Y) : ∑ y, fiberMass μ φ y = 1 := by
  classical
  simp_rw [fiberMass_eq]
  rw [sum_comm]
  simp [μ.total]

def push (μ : Law X) (φ : X → Y) : Law Y where
  val := fiberMass μ φ
  nonneg := fiberMass_nonneg μ φ
  total := fiberMass_total μ φ

lemma push_avg (μ : Law X) (φ : X → Y) (g : Y → ℝ) :
    avg (push μ φ) g = avg μ (fun x => g (φ x)) := by
  classical
  unfold avg push
  simp only [fiberMass_eq,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp

def cond (μ : Law X) (φ : X → Y) (y : Y) : Law X := by
  classical
  exact if h : 0 < fiberMass μ φ y then
    { val := fun x => if φ x=y then μ.val x/fiberMass μ φ y else 0
      nonneg := fun x => by
        have := μ.nonneg x
        split_ifs <;> positivity
      total := by
        have hf := fiberMass_eq μ φ y
        calc
          _ = (∑ x, if φ x=y then μ.val x else 0) / fiberMass μ φ y := by
            rw [sum_div]
            apply sum_congr rfl
            intro x _
            split_ifs <;> simp
          _ = 1 := by rw [← hf,div_self h.ne'] }
    else μ

omit [Fintype Y] in
lemma cond_weight (μ : Law X) (φ : X → Y) (y : Y) (x : X) :
    fiberMass μ φ y * (cond μ φ y).val x = if φ x=y then μ.val x else 0 := by
  classical
  by_cases hy : 0 < fiberMass μ φ y
  · simp only [cond,hy,↓reduceDIte]
    split_ifs
    · field_simp
    · ring
  · have hz := le_antisymm (le_of_not_gt hy) (fiberMass_nonneg μ φ y)
    simp only [hz,zero_mul]
    split_ifs with hxy
    · have h := atom_le_fiber μ φ x
      rw [hxy,hz] at h
      exact (le_antisymm h (μ.nonneg x)).symm
    · rfl

lemma cond_tower (μ : Law X) (φ : X → Y) (f : X → ℝ) :
    avg (push μ φ) (fun y => avg (cond μ φ y) f) = avg μ f := by
  classical
  unfold avg
  simp only [push,mul_sum,← mul_assoc,cond_weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  simp

omit [Fintype Y] in
lemma cond_support (μ : Law X) (φ : X → Y) (y : Y) (hy : 0 < fiberMass μ φ y)
    (x : X) (hx : φ x ≠ y) : (cond μ φ y).val x = 0 := by
  classical
  simp [cond,hy,hx]

omit [Fintype Y] in
lemma cond_event_fiber (μ : Law X) (φ : X → Y) (y : Y) (hy : 0 < fiberMass μ φ y)
    (P : X → Prop) :
    event (cond μ φ y) (fun x => ¬(P x ∧ φ x=y)) = event (cond μ φ y) (fun x => ¬P x) := by
  classical
  unfold event avg
  apply sum_congr rfl
  intro x _
  by_cases hx : φ x=y
  · simp [hx]
  · simp [cond_support μ φ y hy x hx]

lemma push_avg_mono_pos (μ : Law X) (φ : X → Y) {f g : Y → ℝ}
    (h : ∀ y, 0 < fiberMass μ φ y → f y ≤ g y) : avg (push μ φ) f ≤ avg (push μ φ) g := by
  apply sum_le_sum
  intro y _
  by_cases hy : 0 < fiberMass μ φ y
  · exact mul_le_mul_of_nonneg_left (h y hy) hy.le
  · have hz := le_antisymm (le_of_not_gt hy) (fiberMass_nonneg μ φ y)
    simp only [push,hz,zero_mul,le_refl]

lemma cond_event_tower (μ : Law X) (φ : X → Y) (P : X → Prop) :
    avg (push μ φ) (fun y => event (cond μ φ y) P) = event μ P := by
  classical
  unfold event
  exact cond_tower μ φ _
end
end PlanarUnitDistances.FiniteLaw

end OAI
