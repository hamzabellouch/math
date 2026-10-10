import OAI.NumberTheory.GaussianMoat.SignedGeometry

namespace OAI

universe uAlpha uBeta uGamma uOmega uDelta

namespace GaussianMoat
open MeasureTheory ProbabilityTheory
open scoped NNReal

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def entropySum {α : Type uAlpha} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

theorem gibbs_point {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (habs : q = 0 → p = 0) :
    p - q ≤ p * (Real.log p - Real.log q) := by
  by_cases hp0 : p = 0
  · simp [hp0, hq]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm (fun h => hp0 (habs h)))
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  rw [Real.log_div hp0 hqp.ne'] at h
  have h1 : q*(p/q-1) = p-q := by field_simp
  have h2 : q*(p/q*(Real.log p-Real.log q)) = p*(Real.log p-Real.log q) := by field_simp
  rwa [h1,h2] at h

theorem gibbs_sum {α : Type uAlpha} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (habs : ∀ a, q a = 0 → p a = 0) (hsum : ∑ a, p a = ∑ a, q a) :
    0 ≤ ∑ a, p a * (Real.log (p a) - Real.log (q a)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => gibbs_point (hp a) (hq a) (habs a))
  simpa [Finset.sum_sub_distrib, hsum] using h

theorem entropySum_subadd {α : Type uAlpha} {β : Type uBeta} [Fintype α] [Fintype β]
    (p : α → β → ℝ) (hp : ∀ a b, 0 ≤ p a b) :
    (∑ a, ∑ b, Real.negMulLog (p a b)) + Real.negMulLog (∑ a, ∑ b, p a b) ≤
      (∑ a, Real.negMulLog (∑ b, p a b)) + ∑ b, Real.negMulLog (∑ a, p a b) := by
  classical
  let r := fun a => ∑ b, p a b
  let c := fun b => ∑ a, p a b
  let m := ∑ a, r a
  have hr : ∀ a, 0 ≤ r a := fun a => Finset.sum_nonneg (fun b _ => hp a b)
  have hc : ∀ b, 0 ≤ c b := fun b => Finset.sum_nonneg (fun a _ => hp a b)
  have hm : 0 ≤ m := Finset.sum_nonneg (fun a _ => hr a)
  have hpr : ∀ a b, p a b ≤ r a := fun a b =>
    Finset.single_le_sum (fun b' _ => hp a b') (Finset.mem_univ b)
  have hpc : ∀ a b, p a b ≤ c b := fun a b =>
    Finset.single_le_sum (fun a' _ => hp a' b) (Finset.mem_univ a)
  have hrm : ∀ a, r a ≤ m := fun a =>
    Finset.single_le_sum (fun a' _ => hr a') (Finset.mem_univ a)
  have hcm : ∑ b, c b = m := Finset.sum_comm
  by_cases hm0 : m = 0
  · have hz : ∀ a b, p a b = 0 := fun a b => le_antisymm (by simpa [hm0] using (hpr a b).trans (hrm a)) (hp a b)
    simp [hz]
  have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  let q := fun ab : α × β => r ab.1 * c ab.2 / m
  have hq : ∀ ab, 0 ≤ q ab := fun ab => div_nonneg (mul_nonneg (hr _) (hc _)) hm
  have habs : ∀ ab : α × β, q ab = 0 → p ab.1 ab.2 = 0 := by
    intro ab hh
    by_contra h
    have hpp : 0 < p ab.1 ab.2 := lt_of_le_of_ne (hp _ _) (Ne.symm h)
    have hrp : 0 < r ab.1 := hpp.trans_le (hpr _ _)
    have hcp : 0 < c ab.2 := hpp.trans_le (hpc _ _)
    exact (div_pos (mul_pos hrp hcp) hmp).ne' hh
  have hqsum : ∑ ab, q ab = m := by
    rw [Fintype.sum_prod_type]
    change (∑ a, ∑ b, r a*c b/m) = m
    have hi : ∀ a, (∑ b, r a*c b/m) = r a := by
      intro a
      calc
        _ = (r a*(∑ b, c b))/m := by rw [Finset.mul_sum, Finset.sum_div]
        _ = r a := by rw [hcm, mul_div_cancel_right₀ _ hm0]
    simp_rw [hi]
    rfl
  have hg := gibbs_sum (fun ab : α × β => p ab.1 ab.2) q (fun _ => hp _ _) hq habs
    (by rw [hqsum, Fintype.sum_prod_type])
  have ht : ∀ a b, p a b * (Real.log (p a b) - Real.log (q (a,b))) =
      p a b*Real.log (p a b) - p a b*Real.log (r a) - p a b*Real.log (c b) + p a b*Real.log m := by
    intro a b
    by_cases hz : p a b = 0
    · simp [hz]
    have hpp : 0 < p a b := lt_of_le_of_ne (hp _ _) (Ne.symm hz)
    have hrp : 0 < r a := hpp.trans_le (hpr _ _)
    have hcp : 0 < c b := hpp.trans_le (hpc _ _)
    dsimp [q]
    rw [Real.log_div (mul_pos hrp hcp).ne' hm0, Real.log_mul hrp.ne' hcp.ne']
    ring
  have hrow : (∑ a, ∑ b, p a b * Real.log (r a)) = ∑ a, r a*Real.log (r a) := by
    simp_rw [← Finset.sum_mul]
    rfl
  have hcol : (∑ a, ∑ b, p a b * Real.log (c b)) = ∑ b, c b*Real.log (c b) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rfl
  have htot : (∑ a, ∑ b, p a b * Real.log m) = m*Real.log m := by
    simp_rw [← Finset.sum_mul]
    rfl
  rw [Fintype.sum_prod_type] at hg
  simp_rw [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hg
  rw [hrow,hcol,htot] at hg
  change (∑ a, ∑ b, Real.negMulLog (p a b)) + Real.negMulLog m ≤
    (∑ a, Real.negMulLog (r a)) + ∑ b, Real.negMulLog (c b)
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith

theorem negMulLog_sum_le {α : Type uAlpha} [Fintype α] (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    Real.negMulLog (∑ a, p a) ≤ ∑ a, Real.negMulLog (p a) := by
  have ht : ∀ a, -p a * Real.log (∑ b, p b) ≤ Real.negMulLog (p a) := by
    intro a
    by_cases hz : p a = 0
    · simp [hz]
    have hpos := lt_of_le_of_ne (hp a) (Ne.symm hz)
    have hle : p a ≤ ∑ b, p b := Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_log hpos hle) (hp a)
    unfold Real.negMulLog
    linarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ht a)
  simpa only [← Finset.sum_mul, Finset.sum_neg_distrib, Real.negMulLog] using hh

structure FinLaw (α : Type uAlpha) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  sum_one : ∑ a, mass a = 1

namespace FinLaw
variable {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} {Ω : Type uOmega} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω]

instance : CoeFun (FinLaw α) (fun _ => α → ℝ) := ⟨mass⟩

@[ext] theorem ext {p q : FinLaw α} (h : ∀ a, p a = q a) : p = q := by
  cases p; cases q; congr; exact funext h

theorem le_one (p : FinLaw α) (a : α) : p a ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.single_le_sum (fun x _ => p.nonneg x) (Finset.mem_univ a)

theorem nonempty (p : FinLaw α) : Nonempty α := by
  by_contra h
  have : IsEmpty α := not_nonempty_iff.mp h
  simpa using p.sum_one

noncomputable def entropy (p : FinLaw α) : ℝ := entropySum p

theorem entropy_nonneg (p : FinLaw α) : 0 ≤ p.entropy :=
  Finset.sum_nonneg (fun a _ => Real.negMulLog_nonneg (p.nonneg a) (p.le_one a))

theorem entropy_le_log_card (p : FinLaw α) : p.entropy ≤ Real.log (Fintype.card α) := by
  have := p.nonempty
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := gibbs_sum (fun a => p a) (fun _ => (Fintype.card α : ℝ)⁻¹) p.nonneg
    (fun _ => by positivity) (fun _ h => False.elim ((inv_pos.mpr hn).ne' h)) (by simp [p.sum_one, hn.ne'])
  have heq : (∑ a, p a * (Real.log (p a) - Real.log (Fintype.card α : ℝ)⁻¹)) =
      -p.entropy + Real.log (Fintype.card α) := by
    simp only [Real.log_inv, sub_neg_eq_add, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, p.sum_one, one_mul, entropy, entropySum, Real.negMulLog]
    rw [← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq] at h
  linarith

noncomputable def map (p : FinLaw α) (f : α → β) : FinLaw β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then p a else 0
    nonneg := fun b => Finset.sum_nonneg (fun a _ => by split_ifs; exact p.nonneg a; exact le_rfl)
    sum_one := by rw [Finset.sum_comm]; simpa using p.sum_one }

@[simp] theorem map_mass (p : FinLaw α) (f : α → β) (b : β) :
    p.map f b = ∑ a, if f a = b then p a else 0 := by
  classical
  rfl

@[simp] theorem map_id (p : FinLaw α) : p.map id = p := by
  classical
  ext a
  simp

@[simp] theorem map_comp (p : FinLaw α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  classical
  ext c
  simp only [map_mass]
  have he (b : β) : (if g b = c then ∑ a, if f a = b then p a else 0 else 0) =
      ∑ a, if f a = b ∧ g b = c then p a else 0 := by
    by_cases h : g b = c <;> simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_and]

noncomputable def H (p : FinLaw Ω) (X : Ω → α) : ℝ := (p.map X).entropy

noncomputable def condH (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  p.H (fun ω => (X ω,Y ω)) - p.H Y

theorem H_eq_sum (p : FinLaw Ω) (X : Ω → α) :
    p.H X = -∑ ω, p ω * Real.log (p.map X (X ω)) := by
  classical
  unfold H entropy entropySum
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  congr 1
  calc
    _ = ∑ a, ∑ ω, (if X ω = a then p ω else 0) * Real.log (p.map X a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [map_mass, Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      simp [ite_mul]

theorem H_eq_of_fibers (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (hf : ∀ ω ω', X ω = X ω' ↔ Y ω = Y ω') : p.H X = p.H Y := by
  rw [H_eq_sum,H_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  have hh : p.map X (X ω) = p.map Y (Y ω) := by
    simp only [map_mass]
    apply Finset.sum_congr rfl
    intro ω' _
    rw [hf]
  rw [hh]

theorem H_comp_injective (p : FinLaw Ω) (X : Ω → α) (f : α → β)
    (hf : Function.Injective f) : p.H (f ∘ X) = p.H X :=
  p.H_eq_of_fibers _ _ (fun _ _ => hf.eq_iff)

theorem H_pair_comm (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H (fun ω => (X ω,Y ω)) = p.H (fun ω => (Y ω,X ω)) := by
  apply p.H_eq_of_fibers
  simp only [Prod.mk.injEq, and_comm, implies_true]

theorem H_pair_assoc (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.H (fun ω => (X ω,(Y ω,Z ω))) = p.H (fun ω => ((X ω,Y ω),Z ω)) := by
  apply p.H_eq_of_fibers
  simp only [Prod.mk.injEq, and_assoc, implies_true]

theorem H_pair_function (p : FinLaw Ω) (X : Ω → α) (f : α → β) :
    p.H (fun ω => (X ω,f (X ω))) = p.H X := by
  apply p.H_eq_of_fibers
  intro ω ω'
  simp only [Prod.mk.injEq]
  exact ⟨And.left,fun h => ⟨h,congrArg f h⟩⟩

@[simp] theorem H_map (p : FinLaw Ω) (X : Ω → α) (f : α → β) :
    (p.map X).H f = p.H (f ∘ X) := by simp [H]

@[simp] theorem map_fst_mass (p : FinLaw (α × β)) (a : α) :
    p.map Prod.fst a = ∑ b, p (a,b) := by
  rw [map_mass,Fintype.sum_prod_type,Finset.sum_comm]
  simp

@[simp] theorem map_snd_mass (p : FinLaw (α × β)) (b : β) :
    p.map Prod.snd b = ∑ a, p (a,b) := by
  simp [map_mass,Fintype.sum_prod_type]

theorem entropy_ge_snd (p : FinLaw (α × β)) : (p.map Prod.snd).entropy ≤ p.entropy := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun b _ => negMulLog_sum_le (fun a => p (a,b)) (fun _ => p.nonneg _))
  rw [Finset.sum_comm] at h
  simpa only [entropy,entropySum,map_snd_mass,Fintype.sum_prod_type] using h

theorem entropy_subadd (p : FinLaw (α × β)) :
    p.entropy ≤ (p.map Prod.fst).entropy + (p.map Prod.snd).entropy := by
  have h := entropySum_subadd (fun a b => p (a,b)) (fun _ _ => p.nonneg _)
  have hs : (∑ a, ∑ b, p (a,b)) = 1 := by simpa only [Fintype.sum_prod_type] using p.sum_one
  rw [hs,Real.negMulLog_one,add_zero] at h
  simpa only [entropy,entropySum,map_fst_mass,map_snd_mass,Fintype.sum_prod_type] using h

theorem H_pair_ge_snd (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H Y ≤ p.H (fun ω => (X ω,Y ω)) := by
  have h := (p.map (fun ω => (X ω,Y ω))).entropy_ge_snd
  simpa only [map_comp,Function.comp_def,H] using h

theorem H_pair_subadd (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H (fun ω => (X ω,Y ω)) ≤ p.H X + p.H Y := by
  have h := (p.map (fun ω => (X ω,Y ω))).entropy_subadd
  simpa only [map_comp,Function.comp_def,H] using h

theorem condH_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : 0 ≤ p.condH X Y :=
  sub_nonneg.mpr (p.H_pair_ge_snd X Y)

theorem condH_le_H (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : p.condH X Y ≤ p.H X := by
  have h := p.H_pair_subadd X Y
  unfold condH
  linarith

theorem H_le_condH_add (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.H X ≤ p.condH X Y + p.H Y := by
  have h := p.H_pair_ge_snd Y X
  rw [p.H_pair_comm Y X] at h
  simpa only [condH,sub_add_cancel] using h

theorem entropy_strong_subadd (p : FinLaw (α × (β × γ))) :
    p.entropy + (p.map (fun x => x.2.1)).entropy ≤
      (p.map (fun x => (x.1,x.2.1))).entropy + (p.map Prod.snd).entropy := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ =>
    entropySum_subadd (fun a c => p (a,(b,c))) (fun _ _ => p.nonneg _))
  have hmid (b : β) : p.map (fun x => x.2.1) b = ∑ a, ∑ c, p (a,(b,c)) := by
    simp only [map_mass,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
    simp
  have hleft (a : α) (b : β) : p.map (fun x => (x.1,x.2.1)) (a,b) = ∑ c, p (a,(b,c)) := by
    simp [map_mass,Fintype.sum_prod_type,Prod.mk.injEq,ite_and]
    rw [Finset.sum_comm]
    simp
  have hfull : (∑ b, ∑ a, ∑ c, Real.negMulLog (p (a,(b,c)))) = p.entropy := by
    rw [Finset.sum_comm]
    simp only [entropy,entropySum,Fintype.sum_prod_type]
  have hxy : (∑ b, ∑ a, Real.negMulLog (∑ c, p (a,(b,c)))) =
      (p.map (fun x => (x.1,x.2.1))).entropy := by
    rw [Finset.sum_comm]
    simp only [entropy,entropySum,Fintype.sum_prod_type,hleft]
  simp only [Finset.sum_add_distrib] at h
  rw [hfull,hxy] at h
  simpa only [entropy,entropySum,Fintype.sum_prod_type,hmid,map_snd_mass] using h

theorem H_strong_subadd (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.H (fun ω => (X ω,(Y ω,Z ω))) + p.H Y ≤
      p.H (fun ω => (X ω,Y ω)) + p.H (fun ω => (Y ω,Z ω)) := by
  have h := (p.map (fun ω => (X ω,(Y ω,Z ω)))).entropy_strong_subadd
  simpa only [map_comp,Function.comp_def,H] using h

theorem condH_mono (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.condH X (fun ω => (Y ω,Z ω)) ≤ p.condH X Y := by
  have h := p.H_strong_subadd X Y Z
  unfold condH
  linarith

noncomputable def mutualInfo (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  p.H X - p.condH X Y

noncomputable def condMutualInfo {δ : Type uDelta} [Fintype δ] (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → δ) : ℝ :=
  p.condH X Z - p.condH X (fun ω => (Y ω,Z ω))

theorem mutualInfo_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ p.mutualInfo X Y := sub_nonneg.mpr (p.condH_le_H X Y)

theorem condH_pair_comm (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.condH X (fun ω => (Y ω,Z ω)) = p.condH X (fun ω => (Z ω,Y ω)) := by
  unfold condH
  congr 1
  · apply p.H_eq_of_fibers
    simp only [Prod.mk.injEq,and_comm,implies_true]
  · exact p.H_pair_comm Y Z

theorem condMutualInfo_nonneg (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ p.condMutualInfo X Y Z := by
  unfold condMutualInfo
  rw [condH_pair_comm]
  exact sub_nonneg.mpr (p.condH_mono X Z Y)

theorem entropySum_scale (p : α → ℝ) (c : ℝ) :
    entropySum (fun a => c*p a) = c*entropySum p + (∑ a, p a)*Real.negMulLog c := by
  simp only [entropySum, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem entropySum_le_mass_log_card (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    entropySum p ≤ (∑ a, p a)*Real.log (Fintype.card α) + Real.negMulLog (∑ a, p a) := by
  let m := ∑ a, p a
  have hm : 0 ≤ m := Finset.sum_nonneg (fun a _ => hp a)
  by_cases hm0 : m = 0
  · have hz : ∀ a, p a = 0 := by
      intro a
      have hle : p a ≤ m := Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)
      exact le_antisymm (by simpa [hm0] using hle) (hp a)
    simp [entropySum,hz]
  let q : FinLaw α := {
    mass := fun a => p a/m
    nonneg := fun a => div_nonneg (hp a) hm
    sum_one := by rw [← Finset.sum_div]; exact div_self hm0 }
  have h := mul_le_mul_of_nonneg_left q.entropy_le_log_card hm
  have he : entropySum p = m*q.entropy + Real.negMulLog m := by
    have hs : (fun a => m*q a) = p := by ext a; dsimp [q]; field_simp
    rw [← hs, entropySum_scale, q.sum_one, one_mul]
    rfl
  rw [he]
  exact add_le_add_left h _

theorem entropySum_le_mass_log_support (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (S : Finset α) (hs : ∀ a, a ∉ S → p a = 0) :
    entropySum p ≤ (∑ a, p a)*Real.log S.card + Real.negMulLog (∑ a, p a) := by
  classical
  have he : entropySum p = entropySum (fun a : S => p a) := by
    unfold entropySum
    rw [← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => Real.negMulLog (p a))]
    exact (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => by rw [hs a ha,Real.negMulLog_zero])).symm
  have hm : (∑ a, p a) = ∑ a : S, p a := by
    rw [← Finset.sum_subtype S (fun _ => Iff.rfl) p]
    exact (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hs a ha)).symm
  rw [he,hm]
  simpa using entropySum_le_mass_log_card (fun a : S => p a) (fun a => hp a)

theorem condH_le_support (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (L : β → Finset α) (hs : ∀ ω, p ω ≠ 0 → X ω ∈ L (Y ω)) :
    p.condH X Y ≤ ∑ b, p.map Y b * Real.log (L b).card := by
  classical
  let q := p.map (fun ω => (X ω,Y ω))
  have hzero : ∀ b a, a ∉ L b → q (a,b) = 0 := by
    intro b a ha
    change p.map (fun ω => (X ω,Y ω)) (a,b) = 0
    rw [map_mass]
    apply Finset.sum_eq_zero
    intro ω _
    split_ifs with he
    · have he' := Prod.mk.inj he
      by_contra hn
      have hmem := hs ω hn
      rw [he'.1,he'.2] at hmem
      exact ha hmem
    · rfl
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ =>
    entropySum_le_mass_log_support (fun a => q (a,b)) (fun a => q.nonneg _) (L b) (hzero b))
  have hm (b : β) : (∑ a, q (a,b)) = p.map Y b := by
    rw [← map_snd_mass,map_comp]
    rfl
  simp_rw [hm] at h
  rw [Finset.sum_add_distrib] at h
  have hfull : (∑ b, entropySum (fun a => q (a,b))) = p.H (fun ω => (X ω,Y ω)) := by
    unfold entropySum
    rw [Finset.sum_comm]
    simp only [H,entropy,entropySum,Fintype.sum_prod_type,q]
  rw [hfull] at h
  change p.condH X Y ≤ _
  unfold condH
  have hh : (∑ b, Real.negMulLog (p.map Y b)) = p.H Y := rfl
  rw [hh] at h
  linarith

noncomputable def mix (p : FinLaw Ω) (q : Ω → FinLaw α) : FinLaw α := {
  mass := fun a => ∑ ω, p ω * q ω a
  nonneg := fun a => Finset.sum_nonneg (fun ω _ => mul_nonneg (p.nonneg ω) ((q ω).nonneg a))
  sum_one := by rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, sum_one, mul_one]; exact p.sum_one }

@[simp] theorem mix_mass (p : FinLaw Ω) (q : Ω → FinLaw α) (a : α) :
    p.mix q a = ∑ ω, p ω * q ω a := rfl

theorem entropy_mix_ge (p : FinLaw Ω) (q : Ω → FinLaw α) :
    (∑ ω, p ω * (q ω).entropy) ≤ (p.mix q).entropy := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Real.concaveOn_negMulLog.le_map_sum (fun ω _ => p.nonneg ω) p.sum_one
      (fun ω _ => (q ω).nonneg a))
  change (∑ ω, p ω * ∑ a, Real.negMulLog (q ω a)) ≤ _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simpa only [entropy,entropySum,mix_mass,smul_eq_mul] using h

@[simp] theorem H_const (p : FinLaw Ω) (a : α) : p.H (fun _ => a) = 0 := by
  rw [H_eq_sum]
  simp [p.sum_one]

theorem H_bool (p : FinLaw Ω) (E : Ω → Bool) :
    p.H E = Real.binEntropy (p.map E true) := by
  have hs := (p.map E).sum_one
  simp only [Fintype.sum_bool] at hs
  have hf : p.map E false = 1 - p.map E true := by linarith
  simp only [H,entropy,entropySum,Fintype.sum_bool,hf,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem condH_le_reveal (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.condH X Y ≤ p.H Z + p.condH X (fun ω => (Y ω,Z ω)) := by
  have h1 := p.H_pair_ge_snd Z (fun ω => (X ω,Y ω))
  have he : p.H (fun ω => (Z ω,(X ω,Y ω))) = p.H (fun ω => (X ω,(Y ω,Z ω))) := by
    apply p.H_eq_of_fibers
    simp only [Prod.mk.injEq]
    tauto
  rw [he] at h1
  have h2 := p.H_pair_subadd Y Z
  unfold condH
  linarith

omit [Fintype α] in

theorem log_card_le_real (S : Finset α) {b : ℝ} (hb : 1 ≤ b) (hs : (S.card : ℝ) ≤ b) :
    Real.log S.card ≤ Real.log b := by
  by_cases hz : S.card = 0
  · simpa [hz] using Real.log_nonneg hb
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz) hs

theorem short_list (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (L : β → Finset α) (E : Ω → Bool) {b : ℝ} (hb : 1 ≤ b)
    (hs : ∀ ω, p ω ≠ 0 → E ω = true → X ω ∈ L (Y ω) ∧ ((L (Y ω)).card : ℝ) ≤ b) :
    p.condH X Y ≤ Real.binEntropy (p.map E true) +
      p.map E true * Real.log b + (1-p.map E true)*Real.log (Fintype.card α) := by
  classical
  let L' : β × Bool → Finset α := fun ye =>
    if ye.2 = true then if ((L ye.1).card : ℝ) ≤ b then L ye.1 else ∅ else Finset.univ
  have hs' : ∀ ω, p ω ≠ 0 → X ω ∈ L' (Y ω,E ω) := by
    intro ω hn
    by_cases he : E ω = true
    · have hh := hs ω hn he
      simpa [L',he,hh.2] using hh.1
    · simp [L',he]
  have hc := p.condH_le_support X (fun ω => (Y ω,E ω)) L' hs'
  have hcard (y : β) (e : Bool) :
      Real.log (L' (y,e)).card ≤ if e = true then Real.log b else Real.log (Fintype.card α) := by
    cases e
    · simp [L']
    · simp only [L',ite_true]
      split_ifs with hh
      · exact log_card_le_real _ hb hh
      · simpa using Real.log_nonneg hb
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun ye _ =>
    mul_le_mul_of_nonneg_left (hcard ye.1 ye.2) ((p.map (fun ω => (Y ω,E ω))).nonneg ye))
  have hm (e : Bool) : (∑ y, p.map (fun ω => (Y ω,E ω)) (y,e)) = p.map E e := by
    rw [← map_snd_mass,map_comp]
    rfl
  have hsum : (∑ ye : β × Bool, p.map (fun ω => (Y ω,E ω)) ye *
      (if ye.2 = true then Real.log b else Real.log (Fintype.card α))) =
      p.map E true*Real.log b + (1-p.map E true)*Real.log (Fintype.card α) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm,Fintype.sum_bool]
    simp only [Bool.false_eq_true,ite_false,ite_true,← Finset.sum_mul,hm]
    have htotal := (p.map E).sum_one
    simp only [Fintype.sum_bool] at htotal
    congr 2
    linarith
  rw [hsum] at hh
  have h := p.condH_le_reveal X Y E
  rw [H_bool] at h
  linarith

theorem short_list_deficit (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (L : β → Finset α) (E : Ω → Bool) {b : ℝ} (hb : 1 ≤ b)
    (hs : ∀ ω, p ω ≠ 0 → E ω = true → X ω ∈ L (Y ω) ∧ ((L (Y ω)).card : ℝ) ≤ b) :
    p.map E true * (Real.log (Fintype.card α) - Real.log b) - Real.binEntropy (p.map E true)
      ≤ Real.log (Fintype.card α) - p.condH X Y := by
  have h := p.short_list X Y L E hb hs
  nlinarith

theorem low_mass_deficit (p : FinLaw α) (S : Finset α)
    (hs : ∀ a ∈ S, p a ≤ 3 / (8 * (Fintype.card α : ℝ))) :
    (S.card : ℝ) / (8 * (Fintype.card α : ℝ)) ≤ Real.log (Fintype.card α) - p.entropy := by
  classical
  have := p.nonempty
  have hn : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  let u : ℝ := (Fintype.card α : ℝ)⁻¹
  have hu : 0 < u := inv_pos.mpr hn
  let d := fun a => p a * (Real.log (p a) - Real.log u) - p a + u
  have hd : ∀ a, 0 ≤ d a := by
    intro a
    have h := gibbs_point (p.nonneg a) hu.le (fun hz => False.elim (hu.ne' hz))
    dsimp [d]
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); norm_num at h ⊢; exact h
  have hlow : ∀ a ∈ S, u/8 ≤ d a := by
    intro a ha
    have h := gibbs_point (p.nonneg a) (show 0 ≤ u/2 by positivity)
      (fun hz => False.elim ((div_pos hu (by norm_num : (0:ℝ)<2)).ne' hz))
    rw [Real.log_div hu.ne' (by norm_num : (2:ℝ) ≠ 0)] at h
    have hlog := mul_le_mul_of_nonneg_left hlog2 (p.nonneg a)
    have hpa : p a ≤ 3*u/8 := by simpa only [u,div_eq_mul_inv,mul_inv_rev,mul_assoc] using hs a ha
    dsimp [d]
    nlinarith
  have hsum : (∑ a, d a) = Real.log (Fintype.card α) - p.entropy := by
    simp only [d, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul,p.sum_one,one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,u,Real.log_inv]
    rw [mul_inv_cancel₀ hn.ne']
    simp only [entropy,entropySum,Real.negMulLog,neg_mul,Finset.sum_neg_distrib]
    ring
  have hh := Finset.sum_le_sum (s := S) hlow
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun a _ _ => hd a)
  have hfinal := hh.trans hsub
  rw [hsum] at hfinal
  simpa only [Finset.sum_const,nsmul_eq_mul,u,div_eq_mul_inv,mul_inv_rev,mul_assoc] using hfinal

end FinLaw

end GaussianMoat

end OAI
