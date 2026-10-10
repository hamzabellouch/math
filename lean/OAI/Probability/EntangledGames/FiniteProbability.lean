import OAI.Probability.EntangledGames.CorrelatedSampling

namespace OAI

universe u_α u_β u_γ u_E u_F u_ι

noncomputable section
open scoped BigOperators
namespace ThresholdParallelRepetition.FiniteProbability

structure Law (α : Type u_α) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace Law
variable {α : Type u_α} {β : Type u_β} {γ : Type u_γ} {E : Type u_E} [Fintype α] [Fintype β] [Fintype γ]
  [AddCommMonoid E] [Module ℝ E]

def avg (p : Law α) (f : α → E) : E := ∑ x, p.weight x • f x

lemma avg_const (p : Law α) (e : E) : p.avg (fun _ => e) = e := by
  rw [avg, ← Finset.sum_smul, p.total, one_smul]
lemma avg_add (p : Law α) (f g : α → E) :
    p.avg (fun x => f x+g x) = p.avg f+p.avg g := by
  simp [avg, smul_add, Finset.sum_add_distrib]
lemma avg_sub {F : Type u_F} [AddCommGroup F] [Module ℝ F]
    (p : Law α) (f g : α → F) :
    p.avg (fun x => f x-g x) = p.avg f-p.avg g := by
  simp only [avg, smul_sub, Finset.sum_sub_distrib]
lemma avg_smul (p : Law α) (r : ℝ) (f : α → E) :
    p.avg (fun x => r • f x) = r • p.avg f := by
  simp only [avg, Finset.smul_sum, smul_comm (p.weight _) r]
lemma avg_sum {ι : Type u_ι} [Fintype ι] (p : Law α) (f : ι → α → E) :
    p.avg (fun x => ∑ i, f i x) = ∑ i, p.avg (f i) := by
  simp only [avg, Finset.smul_sum]; exact Finset.sum_comm
lemma avg_linear (p : Law α) (f : α → E) {F : Type u_F} [AddCommMonoid F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) : L (p.avg f) = p.avg (fun x => L (f x)) := by
  simp [avg]

lemma avg_nonneg (p : Law α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ p.avg f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (hf x)
lemma avg_mono (p : Law α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : p.avg f ≤ p.avg g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (p.nonneg x)
lemma avg_le_const (p : Law α) {f : α → ℝ} {r : ℝ} (h : ∀ x, f x ≤ r) : p.avg f ≤ r := by
  simpa only [avg_const] using p.avg_mono h
lemma weight_le_one (p : Law α) (x : α) : p.weight x ≤ 1 := by
  rw [← p.total]; exact Finset.single_le_sum (fun y _ => p.nonneg y) (Finset.mem_univ x)

def point [DecidableEq α] (x : α) : Law α where
  weight y := if y=x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  total := by simp

lemma point_avg [DecidableEq α] (x : α) (f : α → E) : (point x).avg f = f x := by
  simp [point, avg]

def bind (p : Law α) (q : α → Law β) : Law β where
  weight y := ∑ x, p.weight x*(q x).weight y
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) ((q x).nonneg y)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (q _).total, mul_one, p.total]

lemma bind_avg (p : Law α) (q : α → Law β) (f : β → E) :
    (p.bind q).avg f = p.avg (fun x => (q x).avg f) := by
  simp only [bind, avg, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

def map [DecidableEq β] (p : Law α) (f : α → β) : Law β := p.bind (fun x => point (f x))
lemma map_avg [DecidableEq β] (p : Law α) (f : α → β) (g : β → E) :
    (p.map f).avg g = p.avg (fun x => g (f x)) := by
  simp only [map, bind_avg, point_avg]

def prod (p : Law α) (q : Law β) : Law (α × β) where
  weight z := p.weight z.1*q.weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, p.total, q.total]

lemma prod_avg (p : Law α) (q : Law β) (f : α × β → E) :
    (p.prod q).avg f = p.avg (fun x => q.avg (fun y => f (x,y))) := by
  simp only [prod, avg, Fintype.sum_prod_type, mul_smul, Finset.smul_sum]

lemma avg_comm (p : Law α) (q : Law β) (f : α → β → E) :
    p.avg (fun x => q.avg (f x)) = q.avg (fun y => p.avg (fun x => f x y)) := by
  simp only [avg, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  exact smul_comm _ _ _

def pi {ι : Type u_ι} [Fintype ι] [DecidableEq ι] (p : ι → Law α) : Law (ι → α) where
  weight f := ∏ i, (p i).weight (f i)
  nonneg f := Finset.prod_nonneg fun i _ => (p i).nonneg _
  total := by rw [← Fintype.prod_sum]; simp only [(p _).total, Finset.prod_const_one]

lemma pi_avg_prod {ι : Type u_ι} [Fintype ι] [DecidableEq ι] (p : ι → Law α)
    (f : ι → α → ℝ) :
    (pi p).avg (fun z => ∏ i, f i (z i)) = ∏ i, (p i).avg (f i) := by
  simp only [avg, pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (p i).weight x*f i x)).symm

lemma avg_eq_sum (p : Law α) (f : α → ℝ) : p.avg f = ∑ x, p.weight x*f x := rfl

def normalize [DecidableEq α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a₀ : α) : Law α :=
  if h : ∑ x, w x = 0 then point a₀ else
  { weight := fun x => w x/(∑ y, w y)
    nonneg := fun x => div_nonneg (hw x) (Finset.sum_nonneg fun y _ => hw y)
    total := by rw [← Finset.sum_div, div_self h] }

lemma normalize_weight [DecidableEq α] (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (a₀ x : α) :
    (∑ y, w y)*(normalize w hw a₀).weight x = w x := by
  rw [normalize]
  split_ifs with h
  · have hx : w x = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hw y)).mp h x (Finset.mem_univ x)
    simp [h, hx]
  · simp only
    field_simp

section Pair
variable [DecidableEq α] [DecidableEq β]

def first (p : Law (α×β)) : Law α where
  weight x := ∑ y, p.weight (x,y)
  nonneg x := Finset.sum_nonneg fun y _ => p.nonneg (x,y)
  total := by simpa only [Fintype.sum_prod_type] using p.total

def second (p : Law (α×β)) : Law β where
  weight y := ∑ x, p.weight (x,y)
  nonneg y := Finset.sum_nonneg fun x _ => p.nonneg (x,y)
  total := by rw [Finset.sum_comm]; simpa only [Fintype.sum_prod_type] using p.total

def givenFirst (p : Law (α×β)) (b₀ : β) (x : α) : Law β :=
  normalize (fun y => p.weight (x,y)) (fun y => p.nonneg (x,y)) b₀

def givenSecond (p : Law (α×β)) (a₀ : α) (y : β) : Law α :=
  normalize (fun x => p.weight (x,y)) (fun x => p.nonneg (x,y)) a₀

omit [DecidableEq α] in
lemma first_given (p : Law (α×β)) (b₀ : β) (x : α) (y : β) :
    p.first.weight x*(p.givenFirst b₀ x).weight y = p.weight (x,y) :=
  normalize_weight _ _ _ _
omit [DecidableEq β] in
lemma second_given (p : Law (α×β)) (a₀ : α) (x : α) (y : β) :
    p.second.weight y*(p.givenSecond a₀ y).weight x = p.weight (x,y) :=
  normalize_weight _ _ _ _

omit [DecidableEq α] in
lemma disintegrate_first (p : Law (α×β)) (b₀ : β) (f : α×β → E) :
    p.avg f = p.first.avg (fun x => (p.givenFirst b₀ x).avg (fun y => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type, Finset.smul_sum, ← mul_smul, first_given]
omit [DecidableEq β] in
lemma disintegrate_second (p : Law (α×β)) (a₀ : α) (f : α×β → E) :
    p.avg f = p.second.avg (fun y => (p.givenSecond a₀ y).avg (fun x => f (x,y))) := by
  simp only [avg, Fintype.sum_prod_type, Finset.smul_sum, ← mul_smul, second_given]
  exact Finset.sum_comm
end Pair

section Pi
variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι]

lemma prod_split (f : ι → ℝ) (i : ι) :
    ∏ j, f j = f i * ∏ j : {j // j ≠ i}, f j := by
  have h := Fintype.prod_subtype_mul_prod_subtype (fun j => j=i) f
  have hd : ((default : {j : ι // j=i}) : ι) = i := (default : {j : ι // j=i}).property
  simpa [hd] using h.symm

lemma pi_weight_split (p : ι → Law α) (i : ι) (u : α) (r : {j // j ≠ i} → α) :
    (pi p).weight ((Equiv.funSplitAt i α).symm (u,r)) =
      (p i).weight u * (pi (fun j : {j // j ≠ i} => p j)).weight r := by
  change (∏ j, (p j).weight (((Equiv.funSplitAt i α).symm (u,r)) j)) = _
  rw [prod_split _ i]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_eq_left, pi]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp [j.property]

lemma pi_avg_split (p : ι → Law α) (i : ι) (f : (ι → α) → E) :
    (pi p).avg f = (p i).avg (fun u =>
      (pi (fun j : {j // j ≠ i} => p j)).avg
        (fun r => f ((Equiv.funSplitAt i α).symm (u,r)))) := by
  rw [avg, ← (Equiv.funSplitAt i α).symm.sum_comp]
  simp only [Fintype.sum_prod_type, pi_weight_split, avg, mul_smul, Finset.smul_sum]

omit [Fintype α] [Fintype ι] in
lemma split_update (i : ι) (z : ι → α) (u : α) :
    Function.update z i u = (Equiv.funSplitAt i α).symm (u, fun j => z j) := by
  ext j; by_cases h : j=i
  · subst j; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

omit [Fintype α] [Fintype ι] in
lemma update_split (i : ι) (r : {j // j ≠ i} → α) (u v : α) :
    Function.update ((Equiv.funSplitAt i α).symm (u,r)) i v =
      (Equiv.funSplitAt i α).symm (v,r) := by
  ext j; by_cases h : j=i
  · subst j; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma pi_avg_update (p : ι → Law α) (i : ι) (f : (ι → α) → E) :
    (pi p).avg (fun z => (p i).avg (fun u => f (Function.update z i u))) = (pi p).avg f := by
  rw [pi_avg_split p i, pi_avg_split p i f]
  simp only [update_split, avg_const]
  exact avg_comm _ _ _
end Pi

section Information

def kl (p q : Law α) : ℝ := p.avg (fun x => Real.log (p.weight x/q.weight x))

def Supports (p q : Law α) : Prop := ∀ x, p.weight x ≠ 0 → q.weight x ≠ 0

lemma mul_log_ratio_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : p ≠ 0 → q ≠ 0) : p-q ≤ p*Real.log (p/q) := by
  by_cases hz : p = 0
  · simp [hz, hq]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hq' : 0 < q := lt_of_le_of_ne hq (Ne.symm (hs hz))
  have h := Real.log_le_sub_one_of_pos (div_pos hq' hp')
  have h := mul_le_mul_of_nonneg_left h hp
  rw [Real.log_div hq'.ne' hp'.ne'] at h
  rw [Real.log_div hp'.ne' hq'.ne']
  have he : p*(q/p-1) = q-p := by field_simp
  rw [he] at h
  nlinarith

lemma kl_nonneg (p q : Law α) (hs : Supports p q) : 0 ≤ p.kl q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    mul_log_ratio_lower (p.nonneg x) (q.nonneg x) (hs x))
  simpa [kl, avg, Finset.sum_sub_distrib, p.total, q.total] using h

lemma kl_log_sub (p q : Law α) (hs : Supports p q) :
    p.kl q = p.avg (fun x => Real.log (p.weight x)) -
      p.avg (fun x => Real.log (q.weight x)) := by
  simp only [kl, avg, smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p.weight x = 0
  · simp [h]
  · rw [Real.log_div h (hs x h), mul_sub]

lemma map_weight_pos [DecidableEq β] (p : Law α) (f : α → β) (x : α)
    (hx : 0 < p.weight x) : 0 < (p.map f).weight (f x) := by
  have h : p.weight x ≤ (p.map f).weight (f x) := by
    change _ ≤ ∑ y, p.weight y*(point (f y)).weight (f x)
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun y _ => mul_nonneg (p.nonneg y) ((point (f y)).nonneg (f x)))
      (Finset.mem_univ x)
    simpa [point] using hh
  exact hx.trans_le h

variable {ι : Type u_ι} [Fintype ι] [DecidableEq ι] [DecidableEq α]
def marginal (p : Law (ι → α)) (i : ι) : Law α := p.map (fun z => z i)

lemma marginal_avg (p : Law (ι → α)) (i : ι) (f : α → E) :
    (p.marginal i).avg f = p.avg (fun z => f (z i)) := map_avg _ _ _

lemma supports_marginal_pi (p : Law (ι → α)) : Supports p (pi p.marginal) := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt (map_weight_pos p (fun z => z i) z
    (lt_of_le_of_ne (p.nonneg z) (Ne.symm hz)))

lemma avg_log_pi (p : Law (ι → α)) (q : ι → Law α) (hs : Supports p (pi q)) :
    p.avg (fun z => Real.log ((pi q).weight z)) =
      ∑ i, (p.marginal i).avg (fun x => Real.log ((q i).weight x)) := by
  simp_rw [marginal_avg]
  rw [← avg_sum]
  simp only [avg, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p.weight z = 0
  · simp [hz]
  have hq := hs z hz
  change (∏ i, (q i).weight (z i)) ≠ 0 at hq
  rw [pi, Real.log_prod (Finset.prod_ne_zero_iff.mp hq)]

lemma supports_marginal (p : Law (ι → α)) (q : ι → Law α)
    (hs : Supports p (pi q)) (i : ι) : Supports (p.marginal i) (q i) := by
  intro x hx
  by_contra hqx
  apply hx
  change (∑ z, p.weight z*(point (z i)).weight x) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : p.weight z = 0
  · simp [hz]
  have hne := Finset.prod_ne_zero_iff.mp (hs z hz) i (Finset.mem_univ i)
  have hzi : z i ≠ x := by intro he; rw [he, hqx] at hne; exact hne rfl
  simp [point, Ne.symm hzi]

lemma kl_tensorization (p : Law (ι → α)) (q : ι → Law α)
    (hs : Supports p (pi q)) :
    (∑ i, (p.marginal i).kl (q i)) ≤ p.kl (pi q) := by
  have h := kl_nonneg p (pi p.marginal) (supports_marginal_pi p)
  rw [kl_log_sub p _ (supports_marginal_pi p), avg_log_pi p _
    (supports_marginal_pi p)] at h
  rw [kl_log_sub p _ hs, avg_log_pi p _ hs]
  simp_rw [kl_log_sub _ _ (supports_marginal p q hs _)]
  rw [Finset.sum_sub_distrib]
  linarith

def tilt (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) : Law α where
  weight x := p.weight x*f x
  nonneg x := mul_nonneg (p.nonneg x) (hf x)
  total := ht

omit [DecidableEq α] in
lemma tilt_avg (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1)
    (g : α → ℝ) : (p.tilt f hf ht).avg g = p.avg (fun x => f x*g x) := by
  simp only [avg, tilt, smul_eq_mul, mul_assoc]

omit [DecidableEq α] in
lemma tilt_supports (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) :
    Supports (p.tilt f hf ht) p := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).1

omit [DecidableEq α] in
lemma kl_tilt (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1) :
    (p.tilt f hf ht).kl p = p.avg (fun x => f x*Real.log (f x)) := by
  simp only [kl, avg, tilt, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p.weight x = 0
  · simp [h]
  · rw [mul_div_cancel_left₀ _ h, mul_assoc]

omit [DecidableEq α] in
lemma kl_tilt_le (p : Law α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (ht : p.avg f = 1)
    {B : ℝ} (_hB : 0 < B) (hb : ∀ x, f x ≤ B) : (p.tilt f hf ht).kl p ≤ Real.log B := by
  rw [kl_tilt]
  have h := p.avg_mono (fun x => show f x*Real.log (f x) ≤ f x*Real.log B from by
    by_cases hz : f x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log
        (lt_of_le_of_ne (hf x) (Ne.symm hz)) (hb x)) (hf x))
  have he : p.avg (fun x => f x*Real.log B) = Real.log B := by
    simp only [avg, smul_eq_mul, ← mul_assoc, ← Finset.sum_mul]
    change p.avg f*Real.log B = _
    rw [ht, one_mul]
  exact h.trans_eq he

lemma avg_indicator (p : Law α) (x : α) :
    p.avg (fun y => if y=x then (1 : ℝ) else 0) = p.weight x := by
  simp [avg]

def coordDensity (q : ι → Law α) (f : (ι → α) → ℝ) (i : ι) (x : α) : ℝ :=
  (pi q).avg (fun z => f (Function.update z i x))

omit [DecidableEq α] in
lemma coordDensity_eq (q : ι → Law α) (f : (ι → α) → ℝ) (i : ι) (x : α) :
    coordDensity q f i x = (pi (fun j : {j // j ≠ i} => q j)).avg
      (fun r => f ((Equiv.funSplitAt i α).symm (x,r))) := by
  rw [coordDensity, pi_avg_split _ i]
  simp only [update_split, avg_const]

lemma marginal_density_avg (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) (g : α → ℝ) :
    (((pi q).tilt f hf ht).marginal i).avg g =
      (q i).avg (fun x => coordDensity q f i x*g x) := by
  rw [marginal_avg, tilt_avg, pi_avg_split _ i]
  congr 1
  funext x
  rw [coordDensity_eq]
  simp only [Equiv.funSplitAt_symm_apply, dite_eq_left]
  simp only [avg, smul_eq_mul, ← mul_assoc, Finset.sum_mul]

lemma marginal_density_weight (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) (x : α) :
    (((pi q).tilt f hf ht).marginal i).weight x = (q i).weight x*coordDensity q f i x := by
  have h := marginal_density_avg q f hf ht i (fun y => if y=x then (1 : ℝ) else 0)
  rw [avg_indicator] at h
  simpa [avg] using h

omit [DecidableEq α] in
lemma coordDensity_nonneg (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (i : ι) (x : α) : 0 ≤ coordDensity q f i x := (pi q).avg_nonneg fun _ => hf _

omit [DecidableEq α] in
lemma coordDensity_total (q : ι → Law α) (f : (ι → α) → ℝ)
    (ht : (pi q).avg f = 1) (i : ι) : (q i).avg (coordDensity q f i) = 1 := by
  rw [show (q i).avg (coordDensity q f i) = (pi q).avg f from by
    change (q i).avg (fun x => (pi q).avg (fun z => f (Function.update z i x))) = _
    rw [avg_comm, pi_avg_update]]
  exact ht

lemma marginal_tilt_eq (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) (i : ι) :
    ((pi q).tilt f hf ht).marginal i = (q i).tilt (coordDensity q f i)
      (coordDensity_nonneg q f hf i) (coordDensity_total q f ht i) := by
  cases he : ((pi q).tilt f hf ht).marginal i
  congr 1
  funext x
  exact (congrArg (fun p : Law α => p.weight x) he).symm.trans
    (marginal_density_weight q f hf ht i x)

lemma coord_entropy_sum_le (q : ι → Law α) (f : (ι → α) → ℝ) (hf : ∀ z, 0 ≤ f z)
    (ht : (pi q).avg f = 1) :
    (∑ i, (q i).avg (fun x => coordDensity q f i x*Real.log (coordDensity q f i x))) ≤
      (pi q).avg (fun z => f z*Real.log (f z)) := by
  have h := kl_tensorization ((pi q).tilt f hf ht) q (tilt_supports _ _ _ _)
  simp_rw [marginal_tilt_eq q f hf ht, kl_tilt] at h
  exact h

end Information

end Law
end ThresholdParallelRepetition.FiniteProbability

end

end OAI
