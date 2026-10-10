import OAI.Geometry.UnitDistances.Profiles

namespace OAI

namespace PlanarUnitDistances.LevelSnapshot
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]
omit [Fintype V] [Fintype E] in
lemma snapshot_swap (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : PlaceLevels.Place K S×ℝ) :
    snapshot S z w tgt src u a=snapshot S z w src tgt u a := by
  unfold snapshot
  congr 1
  funext e
  dsimp [LevelStates.bit]
  rw [AbsoluteValue.map_sub]
end
end PlanarUnitDistances.LevelSnapshot

namespace PlanarUnitDistances.ActualColumnBudget
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral FiniteStarCoupling RareRows
open scoped Classical
noncomputable section
variable {K V P Q : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q]

theorem raw (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hx : Function.Injective (z ∘ x))
    (hm : ∀p q,z (y q)-z (x p)∈S)
    (hΔ : ∀q p r,p≠r → differenceProduct (z (y q)-z (x p)) (z (y q)-z (x r))∈S) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreQ ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VQ σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*avg (right σ) (fun q => (∫a,active ε μ good label (y q) (s a) ∂LevelScale.measure S)*
      event (pair (col σ q) (col σ q)) (fun pp => pp.1=pp.2)) := by
  dsimp only
  let src : P×Q → V := fun pq => y pq.2
  let tgt : P×Q → V := fun pq => x pq.1
  have hb := ActualFamilyBudget.upper S z w src tgt u μ (right σ) (col σ)
    (fun q p => (p,q)) y good label hε hε'
    (fun _ _ _ _ => rfl)
    (fun q hq p hp => by
      have he := hu p q (by rw [←col_weight σ p q]; exact mul_pos hq hp)
      change (z (y q)-z (x p))*(w (y q)-w (x p))=1
      calc
        _ = (z (x p)-z (y q))*(w (x p)-w (y q)) := by ring
        _ = 1 := he)
    (fun _ _ _ _ _ _ hpr => hx.ne hpr)
    (fun pq => hm pq.1 pq.2)
    (fun q _ p r _ _ hpr => hΔ q p r hpr)
  have hv (a : Data V (P×Q)) : avg (right σ) (fun q => commonVariation ε μ (col σ q) (fun p => (p,q)) a)=
      (if PlaceScore.common ε (ActualSlots.frequency μ a) then VQ σ (fun p q => a.1 (p,q)) else 0) := by
    by_cases hc : PlaceScore.common ε (ActualSlots.frequency μ a)
    · simp only [commonVariation,hc,ite_true,VQ]
    · simp only [commonVariation,hc,ite_false,avg_const]
  simp_rw [hv] at hb
  dsimp [src,tgt] at hb
  simp_rw [snapshot_swap S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u] at hb
  exact hb

lemma col_weighted (π : Law (P×Q)) (f : Q → ℝ) (hf : ∀q,0 ≤ f q)
    {d : ℝ} (hp : ∀p q,π.val (p,q) ≤ d*(right π).val q) :
    avg (right π) (fun q => f q*event (pair (col π q) (col π q)) (fun pp => pp.1=pp.2)) ≤
      d*avg (right π) f := by
  simp only [avg,TemplateCollision.collision_eq,mul_sum]
  apply sum_le_sum
  intro q _
  calc
    _ = f q*∑p,π.val (p,q)*(col π q).val p := by
      rw [mul_sum]
      apply sum_congr rfl; intro p _
      rw [pow_two,←col_weight π p q]
      ring
    _ ≤ f q*∑p,(d*(right π).val q)*(col π q).val p := by
      apply mul_le_mul_of_nonneg_left _ (hf q)
      apply sum_le_sum; intro p _
      exact mul_le_mul_of_nonneg_right (hp p q) ((col π q).nonneg p)
    _ = _ := by rw [←mul_sum,(col π q).total]; ring

theorem upper (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ σ : Law (P×Q))
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<σ.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hx : Function.Injective (z ∘ x))
    (hm : ∀p q,z (y q)-z (x p)∈S)
    (hΔ : ∀q p r,p≠r → differenceProduct (z (y q)-z (x p)) (z (y q)-z (x r))∈S)
    (hd : ∀p q,σ.val (p,q) ≤ d*(right σ).val q) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫a,scoreQ ε (ActualSlots.frequency μ (s a)) σ (fun p q => (s a).1 (p,q))
      (fun p => (s a).2 (x p)) (fun q => (s a).2 (y q)) (good (s a)) (label (s a)) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*(∫a,if PlaceScore.common ε (ActualSlots.frequency μ (s a)) then
      VQ σ (fun p q => (s a).1 (p,q)) else 0 ∂LevelScale.measure S)+
    2*d*avg (right σ) (fun q => ∫a,active ε μ good label (y q) (s a) ∂LevelScale.measure S) := by
  dsimp only
  have hb := raw S z w x y u μ σ good label hε hε' hu hx hm hΔ
  have hc := col_weighted σ
    (fun q => ∫a,active ε μ good label (y q)
      (snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u a) ∂LevelScale.measure S)
    (fun q => integral_nonneg (fun a => add_nonneg (RareScore.ind_nonneg _) (RareScore.ind_nonneg _))) hd
  dsimp only at hb
  linarith
end
end PlanarUnitDistances.ActualColumnBudget

namespace PlanarUnitDistances.ActualTemplateBudget
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
  ActualBudgetIntegral FiniteLawIntegral FiniteStarCoupling RareRows TemplateCoupling
open scoped Classical
noncomputable section
variable {K V P Q Θ : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q] [Fintype Θ]

theorem upper (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ π : Law (P×Q)) (a : Q → Law Θ)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y))
    (hm : ∀p q,z (x p)-z (y q)∈S)
    (hΔ : ∀p q r,q≠r → differenceProduct (z (x p)-z (y q)) (z (x p)-z (y r))∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(left π).val p) :
    let s := snapshot S z w (fun pq => x pq.1) (fun pq => y pq.2) u
    (∫b,scoreT ε (ActualSlots.frequency μ (s b)) π a (fun p q => (s b).1 (p,q))
      (fun p => (s b).2 (x p)) (fun q => (s b).2 (y q)) (good (s b)) (label (s b)) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*(∫b,if PlaceScore.common ε (ActualSlots.frequency μ (s b)) then
      avg (templates π a) (fun θ => VP (slice π a θ) (fun p q => (s b).1 (p,q))) else 0 ∂LevelScale.measure S)+
    2*(Fintype.card Θ:ℝ)*d*avg (left π) (fun p => ∫b,active ε μ good label (x p) (s b) ∂LevelScale.measure S) := by
  dsimp only
  let src : P×Q → V := fun pq => x pq.1
  let tgt : P×Q → V := fun pq => y pq.2
  let s := snapshot S z w src tgt u
  let F (θ : Θ) (b : Data V (P×Q)) := scoreP ε (ActualSlots.frequency μ b) (slice π a θ)
    (fun p q => b.1 (p,q)) (fun p => b.2 (x p)) (fun q => b.2 (y q)) (good b) (label b)
  let G (θ : Θ) (b : Data V (P×Q)) := if PlaceScore.common ε (ActualSlots.frequency μ b) then
    VP (slice π a θ) (fun p q => b.1 (p,q)) else 0
  have hh := avg_mono_support (templates π a) (fun θ hθ => ActualRowBudget.raw S z w x y u μ (slice π a θ)
    good label hε hε' (fun p q hpq => hu p q (by
      have he := slice_weight π a θ (p,q)
      have hp := mul_pos hθ hpq
      rw [he] at hp
      exact (mul_pos_iff.mp hp).elim And.left (fun h => False.elim (not_lt_of_ge ((a q).nonneg θ) h.2)))) hy hm hΔ)
  have hF : (∫b,scoreT ε (ActualSlots.frequency μ (s b)) π a (fun p q => (s b).1 (p,q))
      (fun p => (s b).2 (x p)) (fun q => (s b).2 (y q)) (good (s b)) (label (s b)) ∂LevelScale.measure S)=
      avg (templates π a) (fun θ => ∫b,F θ (s b) ∂LevelScale.measure S) :=
    integral_avg (templates π a) _ (fun θ => integrable_value S z w src tgt u (F θ))
  have hG : (∫b,if PlaceScore.common ε (ActualSlots.frequency μ (s b)) then
      avg (templates π a) (fun θ => VP (slice π a θ) (fun p q => (s b).1 (p,q))) else 0 ∂LevelScale.measure S)=
      avg (templates π a) (fun θ => ∫b,G θ (s b) ∂LevelScale.measure S) := by
    have he (b : Data V (P×Q)) : (if PlaceScore.common ε (ActualSlots.frequency μ b) then
      avg (templates π a) (fun θ => VP (slice π a θ) (fun p q => b.1 (p,q))) else 0)=
      avg (templates π a) (fun θ => G θ b) := by
      dsimp [G]
      split_ifs with hc
      · rfl
      · simp only [avg_const]
    simp_rw [he]
    exact integral_avg (templates π a) _ (fun θ => integrable_value S z w src tgt u (G θ))
  change (∫b,scoreT ε (ActualSlots.frequency μ (s b)) π a (fun p q => (s b).1 (p,q))
      (fun p => (s b).2 (x p)) (fun q => (s b).2 (y q)) (good (s b)) (label (s b)) ∂LevelScale.measure S) ≤ _
  rw [hF,hG]
  simp only [avg_add,avg_const,avg_smul] at hh
  have hc := TemplateCollision.weighted π a
    (fun p => ∫b,active ε μ good label (x p) (s b) ∂LevelScale.measure S)
    (fun p => integral_nonneg (fun b => add_nonneg (RareScore.ind_nonneg _) (RareScore.ind_nonneg _))) hd
  change avg (templates π a) (fun θ => ∫b,F θ (s b) ∂LevelScale.measure S) ≤
    2*Real.log 2+(1/20000000:ℝ)*avg (templates π a) (fun θ => ∫b,G θ (s b) ∂LevelScale.measure S)+_ at hh
  nlinarith
end
end PlanarUnitDistances.ActualTemplateBudget

namespace PlanarUnitDistances.PredictionPairBudget
open MeasureTheory Set Finset Real PlaceLevels LevelGeometry PlaceScore
open scoped Classical
noncomputable section

lemma interval_bound {l u a b c : ℝ} (hlu : l ≤ u) (hla : l ≤ a) (hbu : b ≤ u) (hc : 0 ≤ c)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Icc l u))
    (hcap : ∀s∈Icc l u,f s ≤ (if s ≤ a+c then 1 else 0)+(if b-c ≤ s then 1 else 0)-1) :
    (∫s in Icc l u,f s) ≤ a-b+2*c := by
  let g := fun s => ind (Icc l (min u (a+c))) s+ind (Icc (max l (b-c)) u) s-ind (Icc l u) s
  have hg : Integrable g := ((ind_Icc_integrable _ _).add (ind_Icc_integrable _ _)).sub
    (ind_Icc_integrable _ _)
  have hfg : (Icc l u).indicator f ≤ g := by
    intro s
    by_cases hs : s∈Icc l u
    · have h₁ : s∈Icc l (min u (a+c)) ↔ s ≤ a+c := by simp only [Set.mem_Icc,le_min_iff]; exact ⟨fun h => h.2.2,fun h => ⟨hs.1,hs.2,h⟩⟩
      have h₂ : s∈Icc (max l (b-c)) u ↔ b-c ≤ s := by simp only [Set.mem_Icc,max_le_iff]; exact ⟨fun h => h.1.2,fun h => ⟨⟨hs.1,h⟩,hs.2⟩⟩
      simpa only [g,ind,indicator_of_mem hs,indicator_apply,h₁,h₂,hs,ite_true] using hcap s hs
    · have h₁ : s∉Icc l (min u (a+c)) := fun hh => hs ⟨hh.1,hh.2.trans (min_le_left _ _)⟩
      have h₂ : s∉Icc (max l (b-c)) u := fun hh => hs ⟨(le_max_left _ _).trans hh.1,hh.2⟩
      simp only [g,ind,indicator_of_notMem hs,indicator_of_notMem h₁,indicator_of_notMem h₂]
      norm_num
  have hb := integral_mono (hf.integrable_indicator measurableSet_Icc) hg hfg
  rw [integral_indicator measurableSet_Icc] at hb
  have hpos₁ : 0 ≤ min u (a+c)-l := sub_nonneg.mpr (le_min hlu (by linarith))
  have hpos₂ : 0 ≤ u-max l (b-c) := sub_nonneg.mpr (max_le hlu (by linarith))
  have he : (∫s,g s)=min u (a+c)-max l (b-c) := by
    change (∫s,(ind (Icc l (min u (a+c)))+ind (Icc (max l (b-c)) u)) s-ind (Icc l u) s)=_
    rw [integral_sub ((ind_Icc_integrable _ _).add (ind_Icc_integrable _ _)) (ind_Icc_integrable _ _)]
    change ((∫s,ind (Icc l (min u (a+c))) s+ind (Icc (max l (b-c)) u) s)-_)=_
    rw [integral_add (ind_Icc_integrable _ _) (ind_Icc_integrable _ _)]
    rw [ind_Icc_integral,ind_Icc_integral,ind_Icc_integral,max_eq_right hpos₁,max_eq_right hpos₂,
      max_eq_right (sub_nonneg.mpr hlu)]
    ring
  rw [he] at hb
  linarith [min_le_right u (a+c),le_max_right l (b-c)]

variable {K V : Type*} [Field K] [NumberField K] [Fintype V]

def score (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V) (a : Place K S×ℝ) : ℝ :=
  (if (LevelStates.state S z w u a x).1=(LevelStates.state S z w u a y).1 then 1 else 0)+
  (if (LevelStates.state S z w u a x).2=(LevelStates.state S z w u a y).2 then 1 else 0)-1

lemma score_bounds (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V) (a : Place K S×ℝ) :
    -1 ≤ score S z w u x y a ∧ score S z w u x y a ≤ 1 := by
  unfold score
  split_ifs <;> norm_num

lemma measurable_score (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V) : Measurable (score S z w u x y) := by
  have h (v : V) := LevelStates.state_measurable S z w u v
  exact ((measurable_const.piecewise (measurableSet_eq_fun (h x).fst (h y).fst) measurable_const).add
    (measurable_const.piecewise (measurableSet_eq_fun (h x).snd (h y).snd) measurable_const)).sub measurable_const

lemma pair_place (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V)
    (hz : z x≠z y) (hw : w x≠w y) (hZ : z x-z y∈S) (hW : w x-w y∈S)
    (v : Place K S) :
    (∫s in Icc (-radius K S v) (radius K S v),score S z w u x y (v,s)) ≤
      -log (av K v (z x-z y))-log (av K v (w x-w y))+2*allowance v := by
  apply interval_bound (neg_le_self (radius_nonneg K S v))
    (threshold_in_range K hZ v).1 (log_in_range K hW v).2 (allowance_nonneg v)
  · apply Integrable.mono' (integrable_const (1:ℝ))
      ((measurable_score S z w u x y).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun s => by
      simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using abs_le.mpr (score_bounds S z w u x y (v,s)))
  · intro s _
    have h₁ : (LevelStates.state S z w u (v,s) x).1=(LevelStates.state S z w u (v,s) y).1 →
        s ≤  -log (av K v (z x-z y))+allowance v := by
      intro hh
      linarith [first_log_bound S z w u v s x y hz hh]
    have h₂ : (LevelStates.state S z w u (v,s) x).2=(LevelStates.state S z w u (v,s) y).2 →
        log (av K v (w x-w y))-allowance v ≤ s := by
      intro hh
      linarith [second_log_bound S z w u v s x y hw hh]
    unfold score
    split_ifs <;> simp_all

theorem full_pair [IsGalois ℚ K] (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V)
    (hz : z x≠z y) (hw : w x≠w y) (hZ : z x-z y∈S) (hW : w x-w y∈S) :
    (∫a,score S z w u x y a ∂LevelScale.measure S) ≤ 2*log 2 := by
  rw [LevelScale.measure,FiniteLevels.integral_eq (LevelScale.weight K) _ _ _
    (measurable_score S z w u x y) 1 (fun a => abs_le.mpr (score_bounds S z w u x y a))]
  change (Module.finrank ℚ K:ℝ)⁻¹ * _  ≤  _
  have hb := mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun v _ => pair_place S z w u x y hz hw hZ hW v))
    (inv_nonneg.mpr (Nat.cast_nonneg (Module.finrank ℚ K)))
  refine hb.trans_eq ?_
  simp only [sum_add_distrib,sum_sub_distrib,sum_neg_distrib]
  rw [mul_add,mul_sub,mul_neg,←div_eq_inv_mul,←div_eq_inv_mul,←div_eq_inv_mul,
    sum_log_product_formula K hZ (sub_ne_zero.mpr hz),sum_log_product_formula K hW (sub_ne_zero.mpr hw),
    GlobalPairBudget.total_allowance]
  ring
end
end PlanarUnitDistances.PredictionPairBudget

namespace PlanarUnitDistances.PredictionCut
open Finset MeasureTheory FiniteLaw RareScore PredictionCoupling FiniteLawIntegral
open scoped Classical
noncomputable section
variable {P H A B Ω : Type*} [Fintype P] [Fintype H]

def pairScore (x y : A×B) : ℝ :=
  (if x.1=y.1 then 1 else 0)+(if x.2=y.2 then 1 else 0)-1
lemma pairScore_bounds (x y : A×B) : -1 ≤ pairScore x y ∧ pairScore x y ≤ 1 := by
  unfold pairScore
  split_ifs <;> norm_num
lemma pairScore_normal (r : Bool) (l x y : A×B)
    (hx : ¬exceptional r l x) (hy : ¬exceptional r l y) : 0 ≤ pairScore x y := by
  cases r <;> simp only [exceptional,Bool.false_eq_true, ↓reduceIte,not_not] at hx hy
  · have he : x.1=y.1 := hx.trans hy.symm
    unfold pairScore
    simp only [he,ite_true]
    split_ifs <;> norm_num
  · have he : x.2=y.2 := hx.trans hy.symm
    unfold pairScore
    simp only [he,ite_true]
    split_ifs <;> norm_num

lemma cut_bound (c g : Prop) (r : Bool) (l x y : A×B) :
    (if c then pairScore x y else 0) ≤ pairScore x y+
      ind (¬c ∧ g ∧ exceptional r l x)+ind (¬c ∧ g ∧ exceptional r l y)+ind (¬c ∧ ¬g) := by
  by_cases hc : c
  · simp [hc,ind]
  · by_cases hg : g
    · by_cases hx : exceptional r l x
      · simp only [hc,hg,hx,ind,↓reduceIte,true_and,not_false_eq_true,not_true_eq_false]
        have hb := (pairScore_bounds x y).1
        split_ifs <;> linarith
      · by_cases hy : exceptional r l y
        · simp only [hc,hg,hx,hy,ind,↓reduceIte,true_and,not_false_eq_true,not_true_eq_false]
          linarith [(pairScore_bounds x y).1]
        · simpa [hc,hg,hx,hy,ind] using pairScore_normal r l x y hx hy
    · simp only [hc,hg,ind,↓reduceIte,false_and,true_and,not_false_eq_true,add_zero]
      linarith [(pairScore_bounds x y).1]

variable [MeasurableSpace Ω]

theorem integrated (μ : Law P) (h : P → H) (ν : Measure Ω)
    (common good : Ω → Prop) (r : Ω → Bool) (l : Ω → A×B) (x : Ω → P → A×B)
    (C : ℝ) (hC : 0 ≤ C)
    (_hcommon : Integrable (fun a => ind (common a)) ν)
    (hbad : Integrable (fun a => ind (¬common a ∧ ¬good a)) ν)
    (hex : ∀p,Integrable (fun a => ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p))) ν)
    (hfull : ∀p q,Integrable (fun a => pairScore (x a p) (x a q)) ν)
    (hcut : ∀p q,Integrable (fun a => if common a then pairScore (x a p) (x a q) else 0) ν)
    (hbound : ∀p q,p≠q → (∫a,pairScore (x a p) (x a q) ∂ν) ≤ C)
    {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    (∫a,avg (coupling μ h) (fun pp => if common a then pairScore (x a pp.1) (x a pp.2) else 0) ∂ν) ≤
      C+2*avg μ (fun p => ∫a,ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p)) ∂ν)+
      (∫a,ind (¬common a ∧ ¬good a) ∂ν)+
      (∫a,ind (common a) ∂ν)*((Fintype.card H:ℝ)*d) := by
  let e := fun p => ∫a,ind (¬common a ∧ good a ∧ exceptional (r a) (l a) (x a p)) ∂ν
  let wb := ∫a,ind (¬common a ∧ ¬good a) ∂ν
  let wc := ∫a,ind (common a) ∂ν
  have he0 (p : P) : 0 ≤ e p := integral_nonneg (fun a => ind_nonneg _)
  have hw0 : 0 ≤ wb := integral_nonneg (fun a => ind_nonneg _)
  have hc0 : 0 ≤ wc := integral_nonneg (fun a => ind_nonneg _)
  rw [integral_avg (coupling μ h) _ (fun pp => hcut pp.1 pp.2)]
  have hb (p q : P) : (∫a,if common a then pairScore (x a p) (x a q) else 0 ∂ν) ≤
      C+e p+e q+wb+(if p=q then wc else 0) := by
    by_cases hpq : p=q
    · subst q
      have hh : (∫a,if common a then pairScore (x a p) (x a p) else 0 ∂ν)=wc := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun a => by simp [pairScore,ind])
      rw [hh,ite_eq_left rfl]
      linarith [he0 p]
    · rw [ite_eq_right hpq,add_zero]
      have hh := integral_mono (hcut p q) (((hfull p q).add (hex p)).add (hex q) |>.add hbad)
        (fun a => cut_bound (common a) (good a) (r a) (l a) (x a p) (x a q))
      have hi₁ := integral_add (hfull p q) (hex p)
      have hi₂ := integral_add ((hfull p q).add (hex p)) (hex q)
      have hi₃ := integral_add (((hfull p q).add (hex p)).add (hex q)) hbad
      simp only [Pi.add_apply] at hh hi₁ hi₂ hi₃
      rw [hi₃,hi₂,hi₁] at hh
      exact hh.trans (by dsimp only [e,wb]; linarith [hbound p q hpq])
  have hh := avg_mono (coupling μ h) (fun pp => hb pp.1 pp.2)
  simp only [avg_add,avg_const,PredictionCoupling.first,PredictionCoupling.second,avg_indicator_mul] at hh
  have hdg := mul_le_mul_of_nonneg_left (PredictionCoupling.diagonal μ h hd hm) hc0
  change _ ≤ C+2*avg μ e+wb+wc*((Fintype.card H:ℝ)*d)
  linarith
end
end PlanarUnitDistances.PredictionCut

namespace PlanarUnitDistances.ActualPredictionBudget
open Finset MeasureTheory Real FiniteLaw RareScore PredictionCoupling FiniteLawIntegral
  LevelSnapshot PlaceLevels PredictionCut
open scoped Classical
noncomputable section
variable {K V E P H : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype E] [Fintype P] [Fintype H]

theorem upper (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law P) (h : P → H) (pmap : P → V)
    (hz : Function.Injective (z ∘ pmap)) (hw : Function.Injective (w ∘ pmap))
    (hZ : ∀p q,z (pmap p)-z (pmap q)∈S) (hW : ∀p q,w (pmap p)-w (pmap q)∈S)
    (c good : Data V E → Prop) (r : Data V E → Bool)
    (l : Data V E → (V → Bool)×(V → Bool))
    {d : ℝ} (hd : 0 ≤ d) (hm : ∀p,μ.val p ≤ d) :
    let s := snapshot S z w src tgt u
    let x := fun a p => (s a).2 (pmap p)
    (∫a,(if c (s a) then avg μ (fun p => FiniteMarginalScore.tau (push (cond μ h (h p)) (x a))) else 0)
      ∂LevelScale.measure S) ≤
      2*log 2+2*avg μ (fun p => ∫a,ind (¬c (s a) ∧ good (s a) ∧
        exceptional (r (s a)) (l (s a)) (x a p)) ∂LevelScale.measure S)+
      (∫a,ind (¬c (s a) ∧ ¬good (s a)) ∂LevelScale.measure S)+
      (∫a,ind (c (s a)) ∂LevelScale.measure S)*((Fintype.card H:ℝ)*d) := by
  dsimp only
  let s := snapshot S z w src tgt u
  let x := fun a p => (s a).2 (pmap p)
  have he (a : Place K S×ℝ) :
      (if c (s a) then avg μ (fun p => FiniteMarginalScore.tau (push (cond μ h (h p)) (x a))) else 0)=
      avg (coupling μ h) (fun pp => if c (s a) then pairScore (x a pp.1) (x a pp.2) else 0) := by
    by_cases hc : c (s a)
    · simp only [hc,ite_true]
      exact (tau_eq μ h (x a)).symm
    · simp only [hc,ite_false,avg_const]
  change (∫a,(if c (s a) then avg μ (fun p => FiniteMarginalScore.tau (push (cond μ h (h p)) (x a))) else 0)
      ∂LevelScale.measure S) ≤ _
  simp_rw [he]
  apply integrated μ h (LevelScale.measure S) (c ∘ s) (good ∘ s) (r ∘ s) (l ∘ s) x
    (2*log 2) (mul_nonneg (by norm_num) (log_nonneg (by norm_num)))
  · exact integrable_value S z w src tgt u (fun a => ind (c a))
  · exact integrable_value S z w src tgt u (fun a => ind (¬c a ∧ ¬good a))
  · intro p
    exact integrable_value S z w src tgt u (fun a => ind (¬c a ∧ good a ∧ exceptional (r a) (l a) (a.2 (pmap p))))
  · intro p q
    exact integrable_value S z w src tgt u (fun a => pairScore (a.2 (pmap p)) (a.2 (pmap q)))
  · intro p q
    exact integrable_value S z w src tgt u (fun a => if c a then pairScore (a.2 (pmap p)) (a.2 (pmap q)) else 0)
  · intro p q hpq
    simpa only [PredictionPairBudget.score,pairScore,x,s,snapshot] using
      PredictionPairBudget.full_pair S z w u (pmap p) (pmap q) (hz.ne hpq) (hw.ne hpq) (hZ p q) (hW p q)
  · exact hd
  · exact hm
end
end PlanarUnitDistances.ActualPredictionBudget

namespace PlanarUnitDistances.ActualBookUpper
open MeasureTheory FiniteLaw FiniteStarCoupling LevelSnapshot ActualScoreBook ScoreBook
  RareRows RareMoments CommonTemplate TemplateCoupling RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H I : Type} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q] [Fintype H] [Fintype I]

omit [Fintype I] [Fintype H] in
theorem point (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y)) (hS : ∀v r,z v-z r∈S)
    (hΔ : ∀v r t,(z v-z r-(z v-z t))*((z v-z r)⁻¹-(z v-z t)⁻¹)∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(left π).val p) :
    let B := make S z w x y u π h ε good label hm
    B.DP ≤ B.CP/20000000+2*Real.log 2/mass S+2*d*(B.WC+B.HP) := by
  let B := make S z w x y u π h ε good label hm
  have hh := ActualRowBudget.compressed_upper S z w x y u π π good label hε hε' hu hy
    (fun p q => hS (x p) (y q)) (fun p q r _ => hΔ (x p) (y q) (y r)) hd
  dsimp only at hh ⊢
  rw [point_activity S z w x y u π h ε good label hm] at hh
  rw [average S z w x y u π h ε good label hm
      (fun a => scoreP ε (ActualSlots.frequency π a) π (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) (good a) (label a)),
    average S z w x y u π h ε good label hm
      (fun a => if PlaceScore.common ε (ActualSlots.frequency π a) then VP π (fun p q => a.1 (p,q)) else 0)] at hh
  change mass S*B.DP ≤ 2*Real.log 2+(1/20000000:ℝ)*(mass S*B.CP)+
    2*d*(mass S*(B.WC+B.HP)) at hh
  change B.DP ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*B.DP ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring

omit [Fintype I] [Fintype H] in
theorem center (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hx : Function.Injective (z ∘ x)) (hS : ∀v r,z v-z r∈S)
    (hΔ : ∀v r t,(z v-z r-(z v-z t))*((z v-z r)⁻¹-(z v-z t)⁻¹)∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(right π).val q) :
    let B := make S z w x y u π h ε good label hm
    B.DQ ≤ B.CQ/20000000+2*Real.log 2/mass S+2*d*(B.WC+B.HQ) := by
  let B := make S z w x y u π h ε good label hm
  have hh := ActualColumnBudget.upper S z w x y u π π good label hε hε' hu hx
    (fun p q => hS (y q) (x p)) (fun q p r _ => hΔ (y q) (x p) (x r)) hd
  dsimp only at hh ⊢
  rw [center_activity S z w x y u π h ε good label hm] at hh
  rw [average S z w x y u π h ε good label hm
      (fun a => scoreQ ε (ActualSlots.frequency π a) π (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) (good a) (label a)),
    average S z w x y u π h ε good label hm
      (fun a => if PlaceScore.common ε (ActualSlots.frequency π a) then VQ π (fun p q => a.1 (p,q)) else 0)] at hh
  change mass S*B.DQ ≤ 2*Real.log 2+(1/20000000:ℝ)*(mass S*B.CQ)+
    2*d*(mass S*(B.WC+B.HQ)) at hh
  change B.DQ ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*B.DQ ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring

theorem template (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    {ε d : ℝ} (hε : 0<ε) (hε' : ε<1/2)
    (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S)
    (hu : ∀p q,0<π.val (p,q) → (z (x p)-z (y q))*(w (x p)-w (y q))=1)
    (hy : Function.Injective (z ∘ y)) (hS : ∀v r,z v-z r∈S)
    (hΔ : ∀v r t,(z v-z r-(z v-z t))*((z v-z r)⁻¹-(z v-z t)⁻¹)∈S)
    (hd : ∀p q,π.val (p,q) ≤ d*(left π).val p) :
    let B := make S z w x y u π h ε good label hm
    Book.DT (I:=I) B ≤ Book.CT (I:=I) B/20000000+2*Real.log 2/mass S+
      2*(Fintype.card (I → H):ℝ)*d*(B.WC+B.HP) := by
  let B := make S z w x y u π h ε good label hm
  have hh := ActualTemplateBudget.upper S z w x y u π π (templateLaw (I:=I) π h)
    good label hε hε' hu hy
    (fun p q => hS (x p) (y q)) (fun p q r _ => hΔ (x p) (y q) (y r)) hd
  dsimp only at hh ⊢
  rw [point_activity S z w x y u π h ε good label hm] at hh
  rw [average S z w x y u π h ε good label hm
      (fun a => scoreT ε (ActualSlots.frequency π a) π (templateLaw (I:=I) π h) (fun p q => a.1 (p,q))
        (fun p => a.2 (x p)) (fun q => a.2 (y q)) (good a) (label a)),
    average S z w x y u π h ε good label hm
      (fun a => if PlaceScore.common ε (ActualSlots.frequency π a) then avg (templates π (templateLaw (I:=I) π h)) (fun θ => VP (slice π (templateLaw (I:=I) π h) θ) (fun p q => a.1 (p,q))) else 0)] at hh
  change mass S*(Book.DT (I:=I) B) ≤ 2*Real.log 2+(1/20000000:ℝ)*(mass S*(Book.CT (I:=I) B))+
    2*(Fintype.card (I → H):ℝ)*d*(mass S*(B.WC+B.HP)) at hh
  change Book.DT (I:=I) B ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*(Book.DT (I:=I) B) ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring

omit [Fintype I] in
theorem prediction (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) (hz : Function.Injective (z ∘ x)) (hw : Function.Injective (w ∘ x))
    (hZ : ∀v r,z v-z r∈S) (hW : ∀v r,w v-w r∈S)
    {d : ℝ} (hd : 0≤d) (hd' : ∀p,(left π).val p≤d) :
    let B := make S z w x y u π h ε good label hm
    B.T ≤ 2*B.HP+2*Real.log 2/mass S+B.WB+B.WC*((Fintype.card H:ℝ)*d) := by
  let B := make S z w x y u π h ε good label hm
  let c : Data V (P×Q) → Prop := fun a => PlaceScore.common ε (ActualSlots.frequency π a)
  let r : Data V (P×Q) → Bool := fun a => LevelScores.minority (ActualSlots.frequency π a)
  have hh := ActualPredictionBudget.upper S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2)
    u (left π) h x hz hw (fun p q => hZ (x p) (x q)) (fun p q => hW (x p) (x q))
    c good r label hd hd'
  dsimp only at hh ⊢
  rw [average S z w x y u π h ε good label hm
    (fun a => if c a then avg (left π) (fun p => FiniteMarginalScore.tau
      (push (cond (left π) h (h p)) (fun p => a.2 (x p)))) else 0),
    average S z w x y u π h ε good label hm (fun a => ind (¬c a ∧ ¬good a)),
    average S z w x y u π h ε good label hm (fun a => ind (c a))] at hh
  have hi (p : P) := average S z w x y u π h ε good label hm
    (fun a => ind (¬c a ∧ good a ∧ exceptional (r a) (label a) (a.2 (x p))))
  simp_rw [hi] at hh
  rw [avg_smul,avg_comm] at hh
  have hhP : avg B.levels (fun a => avg (left π) (fun p =>
      ind (¬c a ∧ good a ∧ exceptional (r a) (label a) (a.2 (x p)))))=B.HP := by
    apply avg_congr
    intro a
    have hRa : B.R a ↔ ¬c a ∧ good a := by rfl
    simp only [hRa]
    by_cases hc : c a
    · simp [hc,ind,avg_const]
    · by_cases hg : good a
      · simp only [hc,hg,not_false_eq_true,true_and,ite_true]
        rfl
      · simp [hc,hg,ind,avg_const]
  change mass S*B.T ≤ 2*Real.log 2+2*(mass S*avg B.levels (fun a => avg (left π)
    (fun p => ind (¬c a ∧ good a ∧ exceptional (r a) (label a) (a.2 (x p))))))+
    mass S*B.WB+(mass S*B.WC)*((Fintype.card H:ℝ)*d) at hh
  rw [hhP] at hh
  change B.T ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    mass S*B.T ≤ _ := hh
    _ = _ := by field_simp [hm.ne']; ring
end
end PlanarUnitDistances.ActualBookUpper

end OAI
