import OAI.Geometry.UnitDistances.Levels

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset MeasureTheory
open scoped Classical
noncomputable section
variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C]

def uniform (X : Type*) [Fintype X] [Nonempty X] : Law X where
  val _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [Fintype.card_ne_zero]

lemma uniform_avg [Nonempty X] (f : X → ℝ) :
    avg (uniform X) f = (∑ x, f x) / Fintype.card X := by
  simp [avg,uniform,div_eq_mul_inv,mul_comm,sum_mul]

lemma uniform_equiv [Nonempty X] [Nonempty Y] (e : X ≃ Y) (f : Y → ℝ) :
    avg (uniform X) (fun x => f (e x)) = avg (uniform Y) f := by
  rw [uniform_avg,uniform_avg,e.sum_comp,Fintype.card_congr e]

lemma uniform_pair [Nonempty X] [Nonempty Y] (f : X×Y → ℝ) :
    avg (uniform (X×Y)) f = avg (uniform X) (fun x => avg (uniform Y) (fun y => f (x,y))) := by
  simp only [uniform_avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [← sum_div,div_div]
  ring

omit [Fintype Y] in
lemma uniform_eval [DecidableEq X] [Nonempty C] (x : X) (f : C → ℝ) :
    avg (uniform (X → C)) (fun h => f (h x)) = avg (uniform C) f := by
  classical
  let e := Equiv.piSplitAt x (fun _ => C)
  have h := uniform_equiv e (fun z => f z.1)
  change avg (uniform (X → C)) (fun h => f (h x)) = _ at h
  rw [h, uniform_pair]
  simp_rw [avg_const]

omit [Fintype Y] in
lemma uniform_eval_two [DecidableEq X] [Nonempty C] (x y : X) (hxy : x ≠ y) (f : C → C → ℝ) :
    avg (uniform (X → C)) (fun h => f (h x) (h y)) =
      avg (uniform C) (fun a => avg (uniform C) (fun b => f a b)) := by
  classical
  let e := Equiv.piSplitAt x (fun _ => C)
  let y' : {z : X // z ≠ x} := ⟨y,hxy.symm⟩
  have h := uniform_equiv e (fun z => f z.1 (z.2 y'))
  change avg (uniform (X → C)) (fun h => f (h x) (h y)) = _ at h
  rw [h,uniform_pair]
  apply avg_congr
  intro a
  exact uniform_eval y' (f a)

omit [Fintype Y] in
lemma uniform_collision [DecidableEq X] [Nonempty C] (x y : X) (hxy : x ≠ y) :
    event (uniform (X → C)) (fun h => h x=h y) = (Fintype.card C : ℝ)⁻¹ := by
  unfold event
  have he := uniform_eval_two x y hxy (fun a b : C => if a=b then 1 else 0)
  rw [he]
  have h : ∀ a : C, avg (uniform C) (fun b => if a=b then 1 else 0) =
      (Fintype.card C : ℝ)⁻¹ := by
    intro a
    simp [uniform_avg]
  simp_rw [h]
  exact avg_const _ _

def Law.pmf (μ : Law X) : PMF X := PMF.ofFintype (fun x => ENNReal.ofReal (μ.val x)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => μ.nonneg x),μ.total,ENNReal.ofReal_one])

@[simp] lemma Law.pmf_apply (μ : Law X) (x : X) : μ.pmf x = ENNReal.ofReal (μ.val x) := rfl

lemma integral_pmf [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Law X) (f : X → ℝ) :
    (∫ x,f x ∂μ.pmf.toMeasure) = avg μ f := by
  rw [PMF.integral_eq_sum]
  simp [avg,μ.nonneg]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

attribute [local instance] Classical.propDecidable

omit [IsGalois ℚ K] in
lemma arch_average_posLog_le (x : K) :
    (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) /
      (Module.finrank ℚ K : ℝ) ≤ exactHeight K x := by
  apply div_le_div_of_nonneg_right _ (finrank_pos K).le
  exact le_add_of_nonneg_right (finsum_nonneg fun _ => posLog_nonneg)

omit [IsGalois ℚ K] in
lemma large_embedding_tail (x : K) {B : ℝ} (hB : 1 < B) :
    (∑ σ : K →ₐ[ℚ] ℂ, if B < infiniteEntry K σ x then (1 : ℝ) else 0) /
      (Module.finrank ℚ K : ℝ) ≤ exactHeight K x / log B := by
  have hlog : 0 < log B := log_pos hB
  have hh : (∑ σ : K →ₐ[ℚ] ℂ, if B < infiniteEntry K σ x then (1 : ℝ) else 0) * log B ≤
      ∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x) := by
    rw [sum_mul]
    apply sum_le_sum
    intro σ _
    split_ifs with hs
    · rw [one_mul, posLog_eq_log (by rw [abs_of_nonneg ((infiniteEntry K σ).nonneg _)]; linarith)]
      exact log_le_log (by linarith) hs.le
    · simpa using (posLog_nonneg (x := infiniteEntry K σ x))
  rw [le_div_iff₀ hlog,div_mul_eq_mul_div]
  exact (div_le_div_of_nonneg_right hh (finrank_pos K).le).trans (arch_average_posLog_le K x)

lemma small_embedding_tail (x : K) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑ σ : K →ₐ[ℚ] ℂ, if x ≠ 0 ∧ infiniteEntry K σ x < r then (1 : ℝ) else 0) /
      (Module.finrank ℚ K : ℝ) ≤ exactHeight K x / log (1/r) := by
  by_cases hx : x = 0
  · simp [hx]
  have he (σ : K →ₐ[ℚ] ℂ) :
      (x ≠ 0 ∧ infiniteEntry K σ x < r) ↔ 1/r < infiniteEntry K σ x⁻¹ := by
    rw [map_inv₀,one_div,inv_lt_inv₀ hr ((infiniteEntry K σ).pos hx)]
    exact and_iff_right hx
  simp_rw [he]
  simpa using large_embedding_tail K x⁻¹ (B := 1/r) ((one_lt_div hr).mpr hr1)

omit [IsGalois ℚ K] in
lemma random_large_embedding_tail {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → K) {B : ℝ} (hB : 1 < B) :
    (∑ ω, p ω * ((∑ σ : K →ₐ[ℚ] ℂ,
      if B < infiniteEntry K σ (X ω) then (1 : ℝ) else 0) / (Module.finrank ℚ K : ℝ))) ≤
      (∑ ω, p ω * exactHeight K (X ω)) / log B := by
  rw [sum_div]
  exact sum_le_sum fun ω _ => by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
      (large_embedding_tail K (X ω) hB) (hp ω)

lemma random_small_embedding_tail {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → K) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑ ω, p ω * ((∑ σ : K →ₐ[ℚ] ℂ,
      if X ω ≠ 0 ∧ infiniteEntry K σ (X ω) < r then (1 : ℝ) else 0) /
        (Module.finrank ℚ K : ℝ))) ≤
      (∑ ω, p ω * exactHeight K (X ω)) / log (1/r) := by
  rw [sum_div]
  exact sum_le_sum fun ω _ => by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
      (small_embedding_tail K (X ω) hr hr1) (hp ω)

end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.EmbeddingTails
open Finset FiniteLaw WeightedAbsoluteValues Real
open scoped Classical
noncomputable section
variable {K Ω I : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype Ω] [Fintype I]

abbrev Embeddings (K : Type*) [Field K] [NumberField K] := K →ₐ[ℚ] ℂ

instance : Nonempty (Embeddings K) := ⟨IsAlgClosed.lift⟩

omit [Fintype I] in
lemma large (μ : Law Ω) (X : Ω → K) {B : ℝ} (hB : 1 < B) :
    event (pair μ (uniform (Embeddings K))) (fun a => B < ‖a.2 (X a.1)‖) ≤
      avg μ (fun x => exactHeight K (X x))/log B := by
  rw [event,pair_avg]
  simp_rw [uniform_avg]
  have hh := random_large_embedding_tail K μ.val μ.nonneg X hB
  simp only [infiniteEntry_apply] at hh
  convert hh using 1
  simp only [avg,Embeddings,infiniteEntry_count]
  apply sum_congr rfl
  intro x _
  congr 1
  congr 1

omit [Fintype I] in
lemma small (μ : Law Ω) (X : Ω → K) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    event (pair μ (uniform (Embeddings K))) (fun a => X a.1 ≠ 0 ∧ ‖a.2 (X a.1)‖ < r) ≤
      avg μ (fun x => exactHeight K (X x))/log (1/r) := by
  have he (a : Ω × Embeddings K) :
      (X a.1 ≠ 0 ∧ ‖a.2 (X a.1)‖ < r) ↔ 1/r < ‖a.2 ((X a.1)⁻¹)‖ := by
    by_cases hx : X a.1=0
    · simp [hx,hr.le]
    have hn : 0 < ‖a.2 (X a.1)‖ := norm_pos_iff.mpr ((map_ne_zero a.2).mpr hx)
    rw [map_inv₀,norm_inv,one_div,inv_lt_inv₀ hr hn]
    exact and_iff_right hx
  rw [event_congr _ he]
  simpa only [exactHeight_inv] using large μ (fun x => (X x)⁻¹) ((one_lt_div hr).mpr hr₁)

lemma large_family (μ : Law Ω) (X : I → Ω → K) {B : ℝ} (hB : 1 < B) :
    event (pair μ (uniform (Embeddings K))) (fun a => ∃i,B < ‖a.2 (X i a.1)‖) ≤
      avg μ (fun x => ∑i,exactHeight K (X i x))/log B := by
  calc
    _ ≤ ∑i,event (pair μ (uniform (Embeddings K))) (fun a => B < ‖a.2 (X i a.1)‖) := event_exists_le _ _
    _ ≤ ∑i,avg μ (fun x => exactHeight K (X i x))/log B := sum_le_sum (fun i _ => large μ (X i) hB)
    _ = _ := by rw [←sum_div,avg_sum]

lemma small_family (μ : Law Ω) (X : I → Ω → K) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    event (pair μ (uniform (Embeddings K))) (fun a => ∃i,X i a.1 ≠ 0 ∧ ‖a.2 (X i a.1)‖ < r) ≤
      avg μ (fun x => ∑i,exactHeight K (X i x))/log (1/r) := by
  calc
    _ ≤ ∑i,event (pair μ (uniform (Embeddings K))) (fun a => X i a.1 ≠ 0 ∧ ‖a.2 (X i a.1)‖ < r) := event_exists_le _ _
    _ ≤ ∑i,avg μ (fun x => exactHeight K (X i x))/log (1/r) := sum_le_sum (fun i _ => small μ (X i) hr hr₁)
    _ = _ := by rw [←sum_div,avg_sum]
end
end PlanarUnitDistances.EmbeddingTails

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

omit [Fintype I] in
lemma exists_good (μ : Law Ω) (bad : Ω → Prop) (hb : event μ bad < 1) :
    ∃x,0 < μ.val x ∧ ¬bad x := by
  by_contra hn
  have he : event μ bad=1 := by
    rw [event,avg,←μ.total]
    apply sum_congr rfl
    intro x _
    by_cases hx : 0 < μ.val x
    · have hbad : bad x := by by_contra h; exact hn ⟨x,hx,h⟩
      simp [hbad,μ.total]
    · rw [le_antisymm (le_of_not_gt hx) (μ.nonneg x),zero_mul]
  linarith

lemma exists_all_good (μ : Law Ω) (bad : I → Ω → Prop) (hb : (∑i,event μ (bad i)) < 1) :
    ∃x,0 < μ.val x ∧ ∀i,¬bad i x := by
  obtain ⟨x,hx,h⟩ := exists_good μ (fun x => ∃i,bad i x) ((event_exists_le μ bad).trans_lt hb)
  exact ⟨x,hx,fun i hi => h ⟨i,hi⟩⟩
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.TemplateCollision
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

lemma collision_eq {X : Type*} [Fintype X] (μ : Law X) :
    event (pair μ μ) (fun xx => xx.1=xx.2)=∑x,μ.val x^2 := by
  simp [event,avg,pair,Fintype.sum_prod_type,pow_two]

lemma atom_le_one {X : Type*} [Fintype X] (μ : Law X) (x : X) : μ.val x≤1 := by
  simpa only [μ.total] using single_le_sum (fun y _ => μ.nonneg y) (mem_univ x)

lemma slice_collision (π : Law (P×Q)) (a : Q → Law Θ) (p : P) (θ : Θ)
    {d : ℝ} (hp : ∀q,π.val (p,q)≤d*(left π).val p) :
    (templates π a).val θ*(left (slice π a θ)).val p*
      event (pair (row (slice π a θ) p) (row (slice π a θ) p)) (fun qq => qq.1=qq.2)≤
      d*(left π).val p := by
  rw [collision_eq,mul_sum]
  calc
    _ = ∑q,π.val (p,q)*(a q).val θ*(row (slice π a θ) p).val q := by
      apply sum_congr rfl
      intro q _
      rw [pow_two,←mul_assoc,mul_assoc ((templates π a).val θ),
        row_weight,slice_weight]
    _ ≤ ∑q,(d*(left π).val p)*(row (slice π a θ) p).val q := by
      apply sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_right _ ((row (slice π a θ) p).nonneg q)
      exact (mul_le_of_le_one_right (π.nonneg (p,q)) (atom_le_one (a q) θ)).trans (hp q)
    _ = _ := by rw [←mul_sum,(row (slice π a θ) p).total,mul_one]

theorem weighted (π : Law (P×Q)) (a : Q → Law Θ) (f : P → ℝ) (hf : ∀p,0≤f p)
    {d : ℝ} (hp : ∀p q,π.val (p,q)≤d*(left π).val p) :
    avg (templates π a) (fun θ => avg (left (slice π a θ)) (fun p =>
      f p*event (pair (row (slice π a θ) p) (row (slice π a θ) p)) (fun qq => qq.1=qq.2)))≤
      (Fintype.card Θ:ℝ)*d*avg (left π) f := by
  simp only [avg,mul_sum]
  calc
    _ = ∑p,∑θ,f p*((templates π a).val θ*(left (slice π a θ)).val p*
      event (pair (row (slice π a θ) p) (row (slice π a θ) p)) (fun qq => qq.1=qq.2)) := by
      rw [sum_comm]
      apply sum_congr rfl; intro p _
      apply sum_congr rfl; intro θ _
      ring
    _ ≤ ∑p,∑_θ : Θ,f p*(d*(left π).val p) := by
      apply sum_le_sum; intro p _
      apply sum_le_sum; intro θ _
      exact mul_le_mul_of_nonneg_left (slice_collision π a p θ (hp p)) (hf p)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; apply sum_congr rfl; intro p _; ring

lemma row_weighted (π : Law (P×Q)) (f : P → ℝ) (hf : ∀p,0≤f p)
    {d : ℝ} (hp : ∀p q,π.val (p,q)≤d*(left π).val p) :
    avg (left π) (fun p => f p*event (pair (row π p) (row π p)) (fun qq => qq.1=qq.2))≤
      d*avg (left π) f := by
  simp only [avg,collision_eq,mul_sum]
  apply sum_le_sum
  intro p _
  calc
    _ = f p*∑q,π.val (p,q)*(row π p).val q := by
      rw [mul_sum]
      apply sum_congr rfl; intro q _
      rw [pow_two,←row_weight π p q]
      ring
    _ ≤ f p*∑q,(d*(left π).val p)*(row π p).val q := by
      apply mul_le_mul_of_nonneg_left _ (hf p)
      apply sum_le_sum; intro q _
      exact mul_le_mul_of_nonneg_right (hp p q) ((row π p).nonneg q)
    _ = _ := by rw [←mul_sum,(row π p).total]; ring
end
end PlanarUnitDistances.TemplateCollision

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]
lemma event_and_lower (μ : Law X) (P Q : X → Prop) :
    event μ P+event μ Q-1 ≤ event μ (fun x => P x∧Q x) := by
  have h := avg_mono μ (f := fun x => (if P x then (1:ℝ) else 0)+(if Q x then (1:ℝ) else 0)-1)
    (g := fun x => if P x∧Q x then (1:ℝ) else 0) (fun x => by split_ifs <;> simp_all)
  simpa only [avg_sub,avg_add,avg_const,avg_ite] using h
lemma event_disjoint_union (μ : Law X) (P Q : X → Prop) (h : ∀x,¬(P x∧Q x)) :
    event μ (fun x => P x∨Q x)=event μ P+event μ Q := by
  unfold event
  rw [← avg_add]
  apply avg_congr
  intro x
  have := h x
  split_ifs <;> simp_all
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteMarginalScore
open Finset FiniteLaw StrictCross CrossStructure CrossSampling StarScore
open scoped Classical
noncomputable section
variable {A B Q : Type*} [Fintype A] [Fintype B] [Fintype Q]

def collision {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) : ℝ :=
  ∑ y,(event ν (fun x => φ x=y))^2

def tau (ν : Law (A×B)) : ℝ := collision ν Prod.fst+collision ν Prod.snd-1

lemma collision_nonneg {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) :
    0≤collision ν φ := sum_nonneg fun _ _ => sq_nonneg _
lemma collision_atom {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) (a : Y) :
    event ν (fun x => φ x=a)^2 ≤ collision ν φ := by
  unfold collision
  exact single_le_sum (f := fun y => (event ν (fun x => φ x=y))^2) (fun _ _ => sq_nonneg _) (mem_univ a)
lemma collision_two {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y)
    {a b : Y} (hab : a≠b) :
    event ν (fun x => φ x=a)^2+event ν (fun x => φ x=b)^2 ≤ collision ν φ := by
  have h := sum_le_sum_of_subset_of_nonneg (show ({a,b}:Finset Y)⊆univ from subset_univ _)
    (f := fun y => event ν (fun x => φ x=y)^2) (fun _ _ _ => sq_nonneg _)
  simpa [collision,hab] using h
lemma collision_one_linear {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) (a : Y) :
    2*event ν (fun x => φ x=a)-1≤collision ν φ := by
  have h := collision_atom ν φ a
  nlinarith [sq_nonneg (event ν (fun x => φ x=a)-1)]
lemma collision_two_linear {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y)
    {a b : Y} (hab : a≠b) :
    event ν (fun x => φ x=a)+event ν (fun x => φ x=b)-1/2≤collision ν φ := by
  have h := collision_two ν φ hab
  nlinarith [sq_nonneg (event ν (fun x => φ x=a)+event ν (fun x => φ x=b)-1),
    sq_nonneg (event ν (fun x => φ x=a)-event ν (fun x => φ x=b))]

lemma tau_lower (ν : Law (A×B)) : -1≤tau ν := by
  unfold tau
  linarith [collision_nonneg ν Prod.fst,collision_nonneg ν Prod.snd]
lemma tau_row (ν : Law (A×B)) (a : A) : 2*rowMass ν a-2≤tau ν := by
  have h := collision_one_linear ν Prod.fst a
  have h' := collision_nonneg ν Prod.snd
  change 2*rowMass ν a-1≤collision ν Prod.fst at h
  unfold tau
  linarith
lemma tau_col (ν : Law (A×B)) (b : B) : 2*colMass ν b-2≤tau ν := by
  have h := collision_one_linear ν Prod.snd b
  have h' := collision_nonneg ν Prod.fst
  change 2*colMass ν b-1≤collision ν Prod.snd at h
  unfold tau
  linarith
lemma tau_cross (ν : Law (A×B)) (y : A×B) : crossMass ν y-3/2≤tau ν := by
  have hA := collision_atom ν Prod.fst y.1
  have hB := collision_atom ν Prod.snd y.2
  have hm : crossMass ν y ≤ rowMass ν y.1+colMass ν y.2 :=
    (event_mono ν (fun x hx => hx.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2))).trans
      (event_union_le ν (fun x => x.1=y.1) (fun x => x.2=y.2))
  change rowMass ν y.1 ^ 2 ≤ _ at hA
  change colMass ν y.2 ^ 2 ≤ _ at hB
  unfold tau
  nlinarith [sq_nonneg (rowMass ν y.1+colMass ν y.2-1),sq_nonneg (rowMass ν y.1-colMass ν y.2)]
lemma tau_atom (ν : Law (A×B)) (y : A×B) :
    4*event ν (fun x => x=y)-3≤tau ν := by
  have hA := collision_one_linear ν Prod.fst y.1
  have hB := collision_one_linear ν Prod.snd y.2
  have hmA := event_mono ν (fun x (hx : x=y) => congrArg Prod.fst hx)
  have hmB := event_mono ν (fun x (hx : x=y) => congrArg Prod.snd hx)
  unfold tau
  linarith
lemma tau_two (ν : Law (A×B)) {y z : A×B} (hA : y.1≠z.1) (hB : y.2≠z.2) :
    2*event ν (fun x => x=y∨x=z)-2≤tau ν := by
  have ha := collision_two_linear ν Prod.fst hA
  have hb := collision_two_linear ν Prod.snd hB
  have hmA := event_mono ν (fun x (hx : x=y∨x=z) => hx.elim
    (fun h => Or.inl (congrArg Prod.fst h)) (fun h => Or.inr (congrArg Prod.fst h)))
  have hmB := event_mono ν (fun x (hx : x=y∨x=z) => hx.elim
    (fun h => Or.inl (congrArg Prod.snd h)) (fun h => Or.inr (congrArg Prod.snd h)))
  rw [event_disjoint_union ν (fun x => x.1=y.1) (fun x => x.1=z.1)
    (fun x h => hA (h.1.symm.trans h.2))] at hmA
  rw [event_disjoint_union ν (fun x => x.2=y.2) (fun x => x.2=z.2)
    (fun x h => hB (h.1.symm.trans h.2))] at hmB
  unfold tau
  linarith

lemma two_cross_mass (ν : Law (A×B)) {ε : ℝ} {y z : A×B}
    (hy : 1-ε≤crossMass ν y) (hz : 1-ε≤crossMass ν z) :
    1-2*ε≤event ν (fun x => Adj x y∧Adj x z) := by
  have h := event_and_lower ν (fun x => Adj x y) (fun x => Adj x z)
  change crossMass ν y+crossMass ν z-1≤_ at h
  linarith
lemma three_cross_mass (ν : Law (A×B)) {ε : ℝ} {y z w : A×B}
    (hy : 1-ε≤crossMass ν y) (hz : 1-ε≤crossMass ν z) (hw : 1-ε≤crossMass ν w) :
    1-3*ε≤event ν (fun x => Adj x y∧Adj x z∧Adj x w) := by
  have h₁ := two_cross_mass ν hz hw
  have h₂ := event_and_lower ν (fun x => Adj x y) (fun x => Adj x z∧Adj x w)
  change crossMass ν y+event ν (fun x => Adj x z∧Adj x w)-1≤_ at h₂
  linarith

theorem second_slice (μ : Law Q) (bit : Q → Bool) (state : Q → A×B)
    (ν : Law (A×B)) (x : A×B) (good : Q → Prop) {ε : ℝ} (hε : 0≤ε)
    (hcons : ∀q,good q → Consistent (bit q) x (state q))
    (hprob : ∀q,good q → 1-ε≤crossMass ν (state q)) :
    variation μ bit/80000-20*(event μ (fun q => ¬good q)+ε) ≤ score μ bit state+tau ν := by
  let b := event μ (fun q => ¬good q)
  let v := variation μ bit
  let d := score μ bit state
  have hb : 0≤b := event_nonneg _ _
  have hv : v≤1/2 := variation_le_half _ _
  have hd : -v≤d := score_lower _ _ _
  have hd' : -1/2≤d := by simpa only [neg_div] using score_ge_half_neg μ bit state
  have ht := tau_lower ν
  change v/80000-20*(b+ε)≤d+tau ν
  by_cases hg : ∃q,good q
  swap
  · have he : b=1 := by
      dsimp [b]
      calc
        _ = event μ (fun _ => True) := event_congr _ (fun q => by simp only [not_exists] at hg; simp [hg q])
        _ = 1 := event_true _
    rw [he]
    linarith
  obtain ⟨q₀,hq₀⟩ := hg
  let Y := (univ.filter good).image state
  have memY {y : A×B} : y∈Y ↔ ∃q,good q ∧ state q=y := by simp only [Y,mem_image,mem_filter,mem_univ,true_and]
  have hmem (q : Q) (hq : good q) : state q∈Y := memY.mpr ⟨q,hq,rfl⟩
  have hx (y : A×B) (hy : y∈Y) : Adj x y := by
    obtain ⟨q,hq,rfl⟩ := memY.mp hy
    exact consistent_adj (hcons q hq)
  have hm (y : A×B) (hy : y∈Y) : 1-ε≤crossMass ν y := by
    obtain ⟨q,hq,rfl⟩ := memY.mp hy
    exact hprob q hq
  rcases classification Y with hs|hs|hs|hs
  · have hd₁ := constant_good μ bit state good (by
      intro q r hq hr
      have he := card_le_one.mp hs _ (hmem q hq) _ (hmem r hr)
      exact ⟨bit_unique (hcons q hq) (he ▸ hcons r hr),he⟩)
    have ht₁ := tau_cross ν (state q₀)
    have ht₂ := hprob q₀ hq₀
    change (1-1/20000:ℝ)-4*b≤d at hd₁
    linarith
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := hs
    have hn : y.2≠z.2 := by intro hh; exact hyz (Prod.ext he hh)
    have hzx : Adj x (y.1,z.2) := by simpa only [Adj,←he] using hx z hz
    have hxr : x.1=y.1 := ((same_row hn x).mp ⟨hx y hy,hzx⟩).1
    have hr : 1-2*ε≤rowMass ν y.1 := by
      refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
      intro u hu
      exact ((same_row hn u).mp ⟨hu.1,by simpa only [Adj,←he] using hu.2⟩).1
    rcases hw with hall|⟨w,hw,hwy⟩
    · have hc : ∀q,good q → bit q=true := by
        intro q hq
        exact bit_true (hcons q hq) (hxr.trans (hall _ (hmem q hq)).symm)
      have hcv := constant_bit μ bit good (fun q r hq hr => (hc q hq).trans (hc r hr).symm)
      have ht₁ := tau_row ν y.1
      change v≤2*b at hcv
      linarith
    · have ha : 1-3*ε≤event ν (fun u => u=(y.1,w.2)) := by
        refine (three_cross_mass ν (hm y hy) (hm z hz) (hm w hw)).trans (event_mono ν ?_)
        intro u hu
        exact third_off_row hn hwy.symm u hu.1 (by simpa only [Adj,←he] using hu.2.1) hu.2.2
      have ht₁ := tau_atom ν (y.1,w.2)
      linarith
  · obtain ⟨y,hy,z,hz,hyz,he,hw⟩ := hs
    have hn : y.1≠z.1 := by intro hh; exact hyz (Prod.ext hh he)
    have hzx : Adj x (z.1,y.2) := by simpa only [Adj,←he] using hx z hz
    have hxc : x.2=y.2 := ((same_column hn x).mp ⟨hx y hy,hzx⟩).1
    have hr : 1-2*ε≤colMass ν y.2 := by
      refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
      intro u hu
      exact ((same_column hn u).mp ⟨hu.1,by simpa only [Adj,←he] using hu.2⟩).1
    rcases hw with hall|⟨w,hw,hwy⟩
    · have hc : ∀q,good q → bit q=false := by
        intro q hq
        exact bit_false (hcons q hq) (hxc.trans (hall _ (hmem q hq)).symm)
      have hcv := constant_bit μ bit good (fun q r hq hr => (hc q hq).trans (hc r hr).symm)
      have ht₁ := tau_col ν y.2
      change v≤2*b at hcv
      linarith
    · have ha : 1-3*ε≤event ν (fun u => u=(w.1,y.2)) := by
        refine (three_cross_mass ν (hm y hy) (hm z hz) (hm w hw)).trans (event_mono ν ?_)
        intro u hu
        have huy := (swap_iff u y).mpr hu.1
        have huz := (swap_iff u z).mpr hu.2.1
        have huw := (swap_iff u w).mpr hu.2.2
        have he' := third_off_row hn hwy.symm u.swap huy
          (by simpa only [Prod.swap,←he] using huz) huw
        exact Prod.ext (congrArg Prod.snd he') (congrArg Prod.fst he')
      have ht₁ := tau_atom ν (w.1,y.2)
      linarith
  · obtain ⟨y,hy,z,hz,h₁,h₂,hw⟩ := hs
    rcases hw with hall|⟨w,hw,hyw,hzw,hyw',hzw'⟩
    · have ha : 1-2*ε≤event ν (fun u => u=(y.1,z.2)∨u=(z.1,y.2)) := by
        refine (two_cross_mass ν (hm y hy) (hm z hz)).trans (event_mono ν ?_)
        intro u hu
        exact (corners h₁ h₂ u).mp hu
      have ht₁ := tau_two ν (y := (y.1,z.2)) (z := (z.1,y.2)) h₁ h₂.symm
      have hinj := pair_coord_inj hall h₁ h₂
      have hdet := determined μ bit state good (by
        intro q r hq hr hbit
        exact determined_of_inj hinj x (state q) (hmem q hq) (state r) (hmem r hr)
          (bit q) (hcons q hq) (hbit ▸ hcons r hr))
      change (1/40000:ℝ)-6*b≤d at hdet
      linarith
    · exact (three_independent h₁ hyw hzw h₂ hyw' hzw' x ⟨hx y hy,hx z hz,hx w hw⟩).elim
end
end PlanarUnitDistances.FiniteMarginalScore

namespace PlanarUnitDistances.PredictionCoupling
open Finset FiniteLaw FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]

def coupling (μ : Law P) (h : P → H) : Law (P×P) :=
  mix (push μ h) (fun j => pair (cond μ h j) (cond μ h j))

lemma first (μ : Law P) (h : P → H) (f : P → ℝ) :
    avg (coupling μ h) (fun pp => f pp.1)=avg μ f := by
  rw [coupling,mix_avg]
  simp_rw [pair_fst]
  exact cond_tower μ h f
lemma second (μ : Law P) (h : P → H) (f : P → ℝ) :
    avg (coupling μ h) (fun pp => f pp.2)=avg μ f := by
  rw [coupling,mix_avg]
  simp_rw [pair_snd]
  exact cond_tower μ h f

lemma cond_diagonal (μ : Law P) (h : P → H) (j : H) {d : ℝ} (hd : 0 ≤ d)
    (hm : ∀p,μ.val p ≤ d) :
    (push μ h).val j*event (pair (cond μ h j) (cond μ h j)) (fun pp => pp.1=pp.2) ≤ d := by
  rw [TemplateCollision.collision_eq,mul_sum]
  calc
    _ = ∑p,(if h p=j then μ.val p else 0)*(cond μ h j).val p := by
      apply sum_congr rfl
      intro p _
      rw [pow_two,←mul_assoc]
      exact congrArg (fun t => t*(cond μ h j).val p) (cond_weight μ h j p)
    _ ≤ ∑p,d*(cond μ h j).val p := by
      apply sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (by split_ifs; exact hm p; exact hd) ((cond μ h j).nonneg p)
    _ = d := by rw [←mul_sum,(cond μ h j).total,mul_one]

theorem diagonal (μ : Law P) (h : P → H) {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    event (coupling μ h) (fun pp => pp.1=pp.2) ≤ (Fintype.card H:ℝ)*d := by
  unfold event
  rw [coupling,mix_avg]
  calc
    _ ≤ ∑_j : H,d := sum_le_sum (fun j _ => cond_diagonal μ h j hd hm)
    _ = _ := by simp

lemma coordinate_collision (μ : Law P) (φ : P → A) :
    event (pair μ μ) (fun pp => φ pp.1=φ pp.2)=collision μ φ := by
  unfold event
  rw [pair_avg]
  have he : (fun p => avg μ (fun q => if φ p=φ q then (1:ℝ) else 0))=
      (fun p => fiberMass μ φ (φ p)) := by
    funext p
    exact event_congr μ (fun q => eq_comm)
  rw [he,←push_avg μ φ (fun a => fiberMass μ φ a)]
  simp only [avg,push,collision,fiberMass,pow_two]

lemma collision_push (μ : Law P) (x : P → A×B) :
    collision (push μ x) Prod.fst=collision μ (fun p => (x p).1) ∧
    collision (push μ x) Prod.snd=collision μ (fun p => (x p).2) := by
  constructor <;> unfold collision event <;> simp_rw [push_avg]

lemma tau_pair (μ : Law P) (x : P → A×B) :
    avg (pair μ μ) (fun pp => (if (x pp.1).1=(x pp.2).1 then 1 else 0)+
      (if (x pp.1).2=(x pp.2).2 then 1 else 0)-1)=tau (push μ x) := by
  rw [avg_sub,avg_add,avg_const]
  change event (pair μ μ) (fun pp => (x pp.1).1=(x pp.2).1)+
    event (pair μ μ) (fun pp => (x pp.1).2=(x pp.2).2)-1=_
  rw [coordinate_collision μ (fun p => (x p).1),coordinate_collision μ (fun p => (x p).2),tau,(collision_push μ x).1,(collision_push μ x).2]

theorem tau_eq (μ : Law P) (h : P → H) (x : P → A×B) :
    avg (coupling μ h) (fun pp => (if (x pp.1).1=(x pp.2).1 then 1 else 0)+
      (if (x pp.1).2=(x pp.2).2 then 1 else 0)-1)=
      avg μ (fun p => tau (push (cond μ h (h p)) x)) := by
  rw [coupling,mix_avg]
  simp_rw [tau_pair]
  exact push_avg μ h _
end
end PlanarUnitDistances.PredictionCoupling

namespace PlanarUnitDistances.HashFeatures
open Finset Real
open scoped RealInnerProductSpace Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev Index (A B : Type*) := A ⊕ (B ⊕ A×B)
abbrev V (A B : Type*) [Fintype A] [Fintype B] := EuclideanSpace ℝ (Index A B)

def vector (x : A×B) (a b c : ℝ) : V A B := by
  classical
  exact WithLp.toLp 2 (Sum.elim (Pi.single x.1 a)
    (Sum.elim (Pi.single x.2 b) (Pi.single x c)))

lemma single_inner {T : Type*} [Fintype T] [DecidableEq T] (x y : T) (a b : ℝ) :
    (∑ i, Pi.single y b i * Pi.single x a i) = if x=y then a*b else 0 := by
  simp only [Pi.single_apply,ite_mul,mul_ite,zero_mul,mul_zero]
  by_cases h : x=y
  · subst y; simp [mul_comm]
  · simp [h]

lemma inner_vector (x y : A×B) (a b c d e f : ℝ) :
    inner ℝ (vector x a b c) (vector y d e f) =
      (if x.1=y.1 then a*d else 0)+(if x.2=y.2 then b*e else 0)+
      (if x=y then c*f else 0) := by
  classical
  rw [PiLp.inner_apply]
  simp only [vector,WithLp.ofLp_toLp,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    RCLike.inner_apply,conj_trivial]
  rw [single_inner,single_inner,single_inner]
  ring

lemma norm_vector_sq (x : A×B) (a b c : ℝ) : ‖vector x a b c‖^2 = a^2+b^2+c^2 := by
  rw [← real_inner_self_eq_norm_sq,inner_vector]
  simp only [ite_true]
  ring

lemma norm_feature (x : A×B) : ‖vector x 1 1 1‖=sqrt 3 := by
  have h := norm_vector_sq x 1 1 1
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  nlinarith [norm_nonneg (vector x 1 1 1),sqrt_nonneg 3]
lemma norm_test (x : A×B) : ‖vector x 1 1 (-2)‖=sqrt 6 := by
  have h := norm_vector_sq x 1 1 (-2)
  have hs := sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  nlinarith [norm_nonneg (vector x 1 1 (-2)),sqrt_nonneg 6]

lemma strict_cross_inner (x y : A×B) :
    inner ℝ (vector x 1 1 1) (vector y 1 1 (-2)) =
      if (x.1=y.1 ∧ x.2≠y.2) ∨ (x.1≠y.1 ∧ x.2=y.2) then 1 else 0 := by
  classical
  rw [inner_vector]
  by_cases h₁ : x.1=y.1 <;> by_cases h₂ : x.2=y.2
  · have he : x=y := Prod.ext h₁ h₂
    subst y
    norm_num
  · have hn : x≠y := fun h => h₂ (congrArg Prod.snd h)
    simp [h₁,h₂,hn]
  · have hn : x≠y := fun h => h₁ (congrArg Prod.fst h)
    simp [h₁,h₂,hn]
  · have hn : x≠y := fun h => h₁ (congrArg Prod.fst h)
    simp [h₁,h₂,hn]

lemma prediction_constant : 4*sqrt 3*sqrt 6 < (18:ℝ) := by
  have h₁ := sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have h₂ := sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
  have hp : (4*sqrt 3*sqrt 6)^2 = 288 := by rw [mul_pow,mul_pow,h₁,h₂]; norm_num
  have hn : 0 ≤ 4*sqrt 3*sqrt 6 := by positivity
  nlinarith
end
end PlanarUnitDistances.HashFeatures

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma avg_comm (μ : Law X) (ν : Law Y) (f : X → Y → ℝ) :
    avg μ (fun x => avg ν (f x)) = avg ν (fun y => avg μ (fun x => f x y)) := by
  simp only [avg,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring
lemma abs_avg_le (μ : Law X) (f : X → ℝ) : |avg μ f| ≤ avg μ (fun x => |f x|) := by
  calc
    _ ≤ ∑ x,|μ.val x*f x| := abs_sum_le_sum_abs _ _
    _ = _ := by simp [avg,abs_mul,abs_of_nonneg,μ.nonneg]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.Hashing
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [Nonempty C]

abbrev Hash (A B C : Type*) := (A → C) × (B → C)
def law : Law (Hash A B C) := pair (uniform (A → C)) (uniform (B → C))
def state (h : Hash A B C) (x : A×B) : C×C := (h.1 x.1,h.2 x.2)

def indicator (x y : A×B) : ℝ := if Adj x y then 1 else 0

omit [Fintype A] [Fintype B] [Fintype C] [Nonempty C] in
lemma error_pointwise (h : Hash A B C) (x y : A×B) :
    |indicator (state h x) (state h y) - indicator x y| ≤
      (if x.1≠y.1 ∧ h.1 x.1=h.1 y.1 then 1 else 0) +
      (if x.2≠y.2 ∧ h.2 x.2=h.2 y.2 then 1 else 0) := by
  unfold indicator Adj state
  dsimp only
  by_cases h₁ : x.1=y.1 <;> by_cases h₂ : x.2=y.2 <;>
    by_cases k₁ : h.1 x.1=h.1 y.1 <;> by_cases k₂ : h.2 x.2=h.2 y.2 <;>
      simp_all

lemma coord_error {D : Type*} [Fintype D] [DecidableEq D] (x y : D) :
    avg (uniform (D → C)) (fun h => if x≠y ∧ h x=h y then 1 else 0) ≤
      (Fintype.card C : ℝ)⁻¹ := by
  by_cases hxy : x=y
  · simp only [hxy,ne_eq,not_true_eq_false,false_and,ite_false,avg_const]
    positivity
  · simp only [hxy,ne_eq,not_false_eq_true,true_and]
    rw [avg_ite,uniform_collision x y hxy]

lemma error_bound (x y : A×B) :
    avg (law : Law (Hash A B C)) (fun h => |indicator (state h x) (state h y)-indicator x y|)
      ≤ 2/(Fintype.card C : ℝ) := by
  refine (avg_mono law (fun h => error_pointwise h x y)).trans ?_
  rw [avg_add]
  change avg (pair (uniform (A → C)) (uniform (B → C))) (fun h => if x.1≠y.1 ∧ h.1 x.1=h.1 y.1 then 1 else 0) +
    avg (pair (uniform (A → C)) (uniform (B → C))) (fun h => if x.2≠y.2 ∧ h.2 x.2=h.2 y.2 then 1 else 0) ≤ _
  rw [pair_fst (uniform (A → C)) (uniform (B → C))
    (fun h : A → C => if x.1≠y.1 ∧ h x.1=h y.1 then 1 else 0),
    pair_snd (uniform (A → C)) (uniform (B → C))
    (fun h : B → C => if x.2≠y.2 ∧ h x.2=h y.2 then 1 else 0)]
  have h₁ := coord_error (C := C) x.1 y.1
  have h₂ := coord_error (C := C) x.2 y.2
  linarith [show 2/(Fintype.card C : ℝ) = (Fintype.card C : ℝ)⁻¹+
      (Fintype.card C : ℝ)⁻¹ by ring]

lemma averaged_error (x y : A×B) :
    |avg (law : Law (Hash A B C)) (fun h => indicator (state h x) (state h y))-indicator x y|
      ≤ 2/(Fintype.card C : ℝ) := by
  rw [← avg_const (law : Law (Hash A B C)) (indicator x y),← avg_sub]
  exact (abs_avg_le law _).trans (error_bound x y)
end
end PlanarUnitDistances.Hashing

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def mixture (μ : Law X) (ν : X → Law Y) : Law Y where
  val y := avg μ (fun x => (ν x).val y)
  nonneg y := avg_nonneg μ (fun x => (ν x).nonneg y)
  total := by
    simp only [avg]
    rw [sum_comm]
    simp_rw [← mul_sum,Law.total,mul_one]
    exact μ.total

lemma mixture_avg (μ : Law X) (ν : X → Law Y) (f : Y → ℝ) :
    avg (mixture μ ν) f = avg μ (fun x => avg (ν x) f) := by
  simp only [avg,mixture,sum_mul,mul_sum,mul_assoc]
  rw [sum_comm]

lemma abs_avg_sub_le (μ : Law X) {f g : X → ℝ} {c : ℝ} (h : ∀ x,|f x-g x| ≤ c) :
    |avg μ f-avg μ g| ≤ c := by
  rw [← avg_sub]
  exact (abs_avg_le μ _).trans (avg_le_const μ h)
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CrossPrediction
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q H A B C T : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype C] [Fintype T]
  [DecidableEq H] [DecidableEq A] [DecidableEq B] [Nonempty C]

omit [Fintype H] in
lemma push_mass (μ : Law P) (h : P → H) (a : H) :
    FiniteInformation.push μ.val h a = fiberMass μ h a := by
  rw [fiberMass_eq]
  unfold FiniteInformation.push
  apply sum_congr rfl
  intro x _
  split_ifs <;> rfl

omit [Fintype H] in
lemma posterior_cond (μ : Law P) (h : P → H) (p : P) (hp : 0 < μ.val p) (r : P) :
    FiniteInformation.posterior μ.val h (h p) r = (cond μ h (h p)).val r := by
  have hm : 0 < fiberMass μ h (h p) := hp.trans_le (atom_le_fiber μ h p)
  simp only [FiniteInformation.posterior,push_mass,FiniteLaw.cond,hm,↓reduceDIte]
  split_ifs <;> simp

def actual (κ : Law Q) (w : Q → Law P) (X : P → A×B) (Z : Q → A×B) : ℝ :=
  avg κ (fun q => avg (w q) (fun p => Hashing.indicator (X p) (Z q)))

def predicted (κ : Law Q) (w : Q → Law P) (h : P → H) (X : P → A×B) (Z : Q → A×B) : ℝ :=
  avg κ (fun q => avg (w q) (fun p =>
    avg (cond (mixture κ w) h (h p)) (fun r => Hashing.indicator (X r) (Z q))))

lemma actual_hash_error (κ : Law Q) (w : Q → Law P) (X : P → A×B) (Z : Q → A×B) :
    |avg (Hashing.law : Law (Hashing.Hash A B C))
      (fun u => actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z))-actual κ w X Z|
      ≤ 2/(Fintype.card C : ℝ) := by
  unfold actual
  rw [avg_comm]
  simp_rw [avg_comm (Hashing.law : Law (Hashing.Hash A B C))]
  apply abs_avg_sub_le
  intro q
  apply abs_avg_sub_le
  intro p
  exact Hashing.averaged_error (X p) (Z q)

omit [Fintype H] [DecidableEq H] in
lemma predicted_hash_error (κ : Law Q) (w : Q → Law P) (h : P → H)
    (X : P → A×B) (Z : Q → A×B) :
    |avg (Hashing.law : Law (Hashing.Hash A B C))
      (fun u => predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z))-
          predicted κ w h X Z| ≤ 2/(Fintype.card C : ℝ) := by
  unfold predicted
  rw [avg_comm]
  simp_rw [avg_comm (Hashing.law : Law (Hashing.Hash A B C))]
  apply abs_avg_sub_le
  intro q
  apply abs_avg_sub_le
  intro p
  apply abs_avg_sub_le
  intro r
  exact Hashing.averaged_error (X r) (Z q)

lemma discrepancy_eq (κ : Law Q) (w : Q → Law P) (h : P → H)
    (hμ : ∀ p,0 < (mixture κ w).val p) (X : P → A×B) (Z : Q → A×B) :
    FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) h X
      (fun x => HashFeatures.vector x 1 1 1) (fun q => HashFeatures.vector (Z q) 1 1 (-2)) =
      |actual κ w X Z-predicted κ w h X Z| := by
  have hm : FiniteInformation.marginal κ.val (fun q => (w q).val) = (mixture κ w).val := rfl
  have hi : ∀ x y : A×B, inner ℝ (HashFeatures.vector x 1 1 1)
      (HashFeatures.vector y 1 1 (-2)) = Hashing.indicator x y := by
    intro x y
    rw [HashFeatures.strict_cross_inner]
    unfold Hashing.indicator StrictCross.Adj
    split_ifs <;> rfl
  unfold FiniteInformation.testDiscrepancy
  rw [hm]
  simp_rw [FiniteInformation.mean_posterior,posterior_cond _ _ _ (hμ _),sum_inner,
    real_inner_smul_left,inner_sub_left,sum_inner,real_inner_smul_left,
    hi]
  simp only [actual,predicted,avg]
  congr 1
  simp only [mul_sub,sum_sub_distrib]
omit [Fintype H] [DecidableEq H] in
lemma hash_transfer (κ : Law Q) (w : Q → Law P) (h : P → H)
    (X : P → A×B) (Z : Q → A×B) :
    actual κ w X Z-predicted κ w h X Z ≤
      avg (Hashing.law : Law (Hashing.Hash A B C)) (fun u =>
        |actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z)-
          predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z)|)+
        4/(Fintype.card C : ℝ) := by
  have ha := actual_hash_error (C := C) κ w X Z
  have hp := predicted_hash_error (C := C) κ w h X Z
  have he := avg_mono (Hashing.law : Law (Hashing.Hash A B C)) (fun u =>
    le_abs_self (actual κ w (Hashing.state u ∘ X) (Hashing.state u ∘ Z)-
      predicted κ w h (Hashing.state u ∘ X) (Hashing.state u ∘ Z)))
  rw [avg_sub] at he
  have ha' := (abs_le.mp ha).1
  have hp' := (abs_le.mp hp).2
  simp only [div_eq_mul_inv] at ha' hp' ⊢
  linarith

open MeasureTheory Real
lemma history_singleton (D : Type*) [MeasurableSpace D] [MeasurableSingletonClass D] (n : ℕ) :
    MeasurableSingletonClass (FiniteInformation.History D n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass PUnit)
  | succ n ih =>
    let := ih
    exact inferInstanceAs (MeasurableSingletonClass (FiniteInformation.History D n × D))

theorem exists_cross_history (κ : Law Q) (w : Q → Law P)
    (hμ : ∀ p,0 < (mixture κ w).val p) (τ : Law T)
    (X : T → P → A×B) (Z : T → Q → A×B) (K : ℕ) (hK : 0 < K) :
    ∃ n < K, ∃ h : P → FiniteInformation.History (C×C) n,
      (univ.image h).card ≤ (Fintype.card C)^(2*K) ∧
      avg τ (fun t => actual κ w (X t) (Z t)-predicted κ w h (X t) (Z t)) ≤
        4/(Fintype.card C : ℝ)+18*(FiniteInformation.KL
          (FiniteInformation.wedge κ.val (fun q => (w q).val))
          (fun pr : P×P => (mixture κ w).val pr.1 * (mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ) := by
  classical
  let : MeasurableSpace (C×C) := ⊤
  let : MeasurableSpace (T × Hashing.Hash A B C) := ⊤
  let σ : Law (T × Hashing.Hash A B C) := pair τ Hashing.law
  let code := fun tu : T × Hashing.Hash A B C => Hashing.state tu.2 ∘ X tu.1
  let feature := fun _ : T × Hashing.Hash A B C => fun c : C×C => HashFeatures.vector c 1 1 1
  let test := fun tu : T × Hashing.Hash A B C => fun q =>
    HashFeatures.vector (Hashing.state tu.2 (Z tu.1 q)) 1 1 (-2)
  have hδ : ∀ n, Measurable (fun z : (P → FiniteInformation.History (C×C) n) ×
      (T × Hashing.Hash A B C) =>
      FiniteInformation.testDiscrepancy κ.val (fun q => (w q).val) z.1
        (code z.2) (feature z.2) (test z.2)) := by
    intro n
    let := history_singleton (C×C) n
    exact measurable_of_finite _
  obtain ⟨n,hn,h,hcard,hbound⟩ := FiniteInformation.exists_prediction_history
    (ν := σ.pmf.toMeasure) κ.val (fun q => (w q).val) κ.nonneg
    (fun q => (w q).nonneg) κ.total (fun q => (w q).total)
    code feature test (fun _ => measurable_of_finite _) hδ
    (sqrt_nonneg 3) (sqrt_nonneg 6)
    (fun _ c => (HashFeatures.norm_feature c).le)
    (fun tu q => (HashFeatures.norm_test (Hashing.state tu.2 (Z tu.1 q))).le) K hK
  refine ⟨n,hn,h,?_,?_⟩
  · refine hcard.trans ?_
    rw [Fintype.card_prod,← pow_two,← pow_mul]
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  · rw [integral_pmf,pair_avg] at hbound
    dsimp [code,feature,test] at hbound
    simp_rw [discrepancy_eq κ w h hμ] at hbound
    have he := avg_mono τ (fun t => hash_transfer (C := C) κ w h (X t) (Z t))
    rw [avg_add,avg_const] at he
    have hnD : 0 ≤ (FiniteInformation.KL
        (FiniteInformation.wedge κ.val (fun q => (w q).val))
        (fun pr : P×P => (mixture κ w).val pr.1 * (mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ) :=
      rpow_nonneg (div_nonneg (FiniteInformation.KL_nonneg _ _
        (FiniteInformation.wedge_nonneg _ _ κ.nonneg (fun q => (w q).nonneg))
        (fun pr => mul_nonneg ((mixture κ w).nonneg pr.1) ((mixture κ w).nonneg pr.2))
        (FiniteInformation.wedge_sum _ _ κ.total (fun q => (w q).total))
        (by rw [Fintype.sum_prod_type,← sum_mul_sum,(mixture κ w).total,one_mul])
        (FiniteInformation.wedge_ac _ _ κ.nonneg (fun q => (w q).nonneg)))
        (Nat.cast_nonneg K)) _
    have hc := mul_le_mul_of_nonneg_right HashFeatures.prediction_constant.le hnD
    change _ ≤ 4*sqrt 3*sqrt 6*(_/(K:ℝ))^(1/4:ℝ) at hbound
    change _ ≤ 4*sqrt 3*sqrt 6*
      (FiniteInformation.KL (FiniteInformation.wedge κ.val (fun q => (w q).val))
        (fun pr : P×P => (mixture κ w).val pr.1*(mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ) at hbound
    refine he.trans ?_
    rw [add_comm (4/(Fintype.card C : ℝ))]
    exact add_le_add_left (hbound.trans hc) _
end
end PlanarUnitDistances.CrossPrediction

namespace PlanarUnitDistances.FiniteLaw
open MeasureTheory Finset Set
open scoped Classical
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
lemma sum_real_atoms (μ : Measure S) [IsFiniteMeasure μ] : ∑s,μ.real {s}=μ.real Set.univ := by
  have hi := integral_fintype (f := fun _ : S => (1:ℝ)) (μ := μ) (integrable_const 1)
  simpa only [integral_const,smul_eq_mul,mul_one] using hi.symm

def fromMeasure (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) : Law S where
  val s := μ.real {s}/μ.real Set.univ
  nonneg s := div_nonneg ENNReal.toReal_nonneg hμ.le
  total := by rw [←sum_div,sum_real_atoms,div_self hμ.ne']

lemma fromMeasure_avg (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) (f : S → ℝ) :
    avg (fromMeasure μ hμ) f=(∫s,f s ∂μ)/μ.real Set.univ := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [avg,fromMeasure,smul_eq_mul]
  rw [Finset.sum_div]
  apply sum_congr rfl; intro s _; ring

variable {Ω : Type*} [MeasurableSpace Ω]
omit [Fintype S] [MeasurableSingletonClass S] in
lemma map_real_univ (μ : Measure Ω) (c : Ω → S) (hc : Measurable c) :
    (μ.map c).real Set.univ=μ.real Set.univ := by
  simp only [Measure.real,Measure.map_apply hc MeasurableSet.univ,Set.preimage_univ]

def compress (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) : Law S :=
  fromMeasure (μ.map c) (by rwa [map_real_univ μ c hc])

lemma compress_avg (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) (f : S → ℝ) :
    avg (compress μ hμ c hc) f=(∫s,f (c s) ∂μ)/μ.real Set.univ := by
  rw [compress,fromMeasure_avg,map_real_univ μ c hc,
    integral_map hc.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CrossPrediction
open Finset FiniteLaw MeasureTheory
open scoped Classical
noncomputable section
variable {P Q A B C Ω : Type*} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  [Fintype C] [Nonempty C] [MeasurableSpace A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [MeasurableSingletonClass B] [MeasurableSpace Ω]

theorem exists_measured_history (κ : Law Q) (w : Q → Law P)
    (hμ : ∀p,0<(mixture κ w).val p) (σ : Measure Ω) [IsFiniteMeasure σ]
    (hσ : 0<σ.real Set.univ) (X : Ω → P → A×B) (Z : Ω → Q → A×B)
    (hX : ∀p,Measurable (fun s => X s p)) (hZ : ∀q,Measurable (fun s => Z s q))
    (K : ℕ) (hK : 0<K) :
    ∃ n<K, ∃ h : P → FiniteInformation.History (C×C) n,
      (univ.image h).card≤(Fintype.card C)^(2*K) ∧
      (∫s,actual κ w (X s) (Z s)-predicted κ w h (X s) (Z s) ∂σ)≤
        σ.real Set.univ*(4/(Fintype.card C:ℝ)+18*(FiniteInformation.KL
          (FiniteInformation.wedge κ.val (fun q => (w q).val))
          (fun pr : P×P => (mixture κ w).val pr.1*(mixture κ w).val pr.2)/(K:ℝ))^(1/4:ℝ)) := by
  let c : Ω → (P → A×B)×(Q → A×B) := fun s => (X s,Z s)
  have hc : Measurable c := (measurable_pi_iff.mpr hX).prodMk (measurable_pi_iff.mpr hZ)
  obtain ⟨n,hn,h,hcard,hbound⟩ := exists_cross_history (C := C) κ w hμ
    (compress σ hσ c hc) Prod.fst Prod.snd K hK
  refine ⟨n,hn,h,hcard,?_⟩
  rw [compress_avg] at hbound
  have hh := (div_le_iff₀ hσ).mp hbound
  simpa only [c,mul_comm (σ.real Set.univ)] using hh
end
end PlanarUnitDistances.CrossPrediction

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]

def triple (μ : Law X) : Law (X×(X×X)) := pair μ (pair μ μ)
def entry (x : X×(X×X)) (i : Fin 3) : X := ![x.1,x.2.1,x.2.2] i

lemma triple_coordinate (μ : Law X) (i : Fin 3) (f : X → ℝ) :
    avg (triple μ) (fun x => f (entry x i))=avg μ f := by
  fin_cases i <;> simp [entry,triple,pair_avg,avg_const]

lemma triple_pair (μ : Law X) (i j : Fin 3) (hij : i≠j) (f : X → X → ℝ) :
    avg (triple μ) (fun x => f (entry x i) (entry x j))=
      avg μ (fun x => avg μ (f x)) := by
  fin_cases i <;> fin_cases j <;> simp_all [entry,triple,pair_avg,avg_const]
  all_goals exact avg_comm μ μ _

lemma triple_collision (μ : Law X) (i j : Fin 3) (hij : i≠j) :
    event (triple μ) (fun x => entry x i=entry x j)=∑x,μ.val x^2 := by
  calc
    _ = avg μ (fun x => avg μ (fun y => if x=y then (1:ℝ) else 0)) :=
      triple_pair μ i j hij (fun x y => if x=y then (1:ℝ) else 0)
    _ = _ := by
      rw [←pair_avg μ μ (fun pp => if pp.1=pp.2 then (1:ℝ) else 0)]
      exact TemplateCollision.collision_eq μ

lemma collision_le_atom (μ : Law X) {d : ℝ} (hm : ∀x,μ.val x ≤ d) :
    (∑x,μ.val x^2) ≤ d := by
  calc
    _ ≤ ∑x,d*μ.val x := sum_le_sum (fun x _ => by
      rw [pow_two]; exact mul_le_mul_of_nonneg_right (hm x) (μ.nonneg x))
    _ = d := by rw [←mul_sum,μ.total,mul_one]
end
end PlanarUnitDistances.FiniteLaw

end OAI
