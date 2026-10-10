import Mathlib
import OAI.Geometry.PrescribedPotential.SobolevProduct

namespace OAI

/-! Sobolev Commutator Bound. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma product_words_asymmetric_bound (s t : ℝ) (p q : List E)
    (hp : (p.length : ℝ) ≤ s) (hq : (q.length : ℝ) ≤ t)
    (hd : (Module.finrank ℝ E : ℝ) < (s-p.length)+(t-q.length)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : 𝓢(E,ℂ),
      ‖schwartzCoord 0 (SchwartzMap.smulLeftCLM ℂ (schwartzWord p f) (schwartzWord q g))‖ ≤
        C * (‖schwartzCoord s f‖ * ‖schwartzCoord t g‖) := by
  have base (s t : ℝ) (p q : List E) (hq : (q.length : ℝ) ≤ t)
      (hd : (Module.finrank ℝ E : ℝ) < 2*(s-p.length)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : 𝓢(E,ℂ),
        ‖schwartzCoord 0 (SchwartzMap.smulLeftCLM ℂ (schwartzWord p f) (schwartzWord q g))‖ ≤
          C * (‖schwartzCoord s f‖ * ‖schwartzCoord t g‖) := by
    obtain ⟨C,hC,hc⟩ := schwartz_word_sup_bound p s hd
    obtain ⟨D,hD,hd⟩ := coreBound_word q (s:=t) (t:=0) (by linarith)
    refine ⟨C*D,mul_nonneg hC hD,fun f g => ?_⟩
    rw [schwartzCoord_product_zero]
    exact (multiply_norm_le _ _).trans (by
      have h := mul_le_mul (hc f) (hd g) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
      convert h using 1
      ring)
  by_cases h : (Module.finrank ℝ E : ℝ) < 2*(s-p.length)
  · exact base s t p q hq h
  · obtain ⟨C,hC,hb⟩ := base t s q p hp (by linarith)
    refine ⟨C,hC,fun f g => ?_⟩
    rw [schwartz_product_swap]
    simpa only [mul_comm] using hb g f

 

lemma second_order_commutator_product_bound (k : ℕ)
    (hk : Module.finrank ℝ E + 1 < k) (p q : List E)
    (hp : 0 < p.length) (hpq : p.length+q.length ≤ k) (v w : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a f : 𝓢(E,ℂ),
      ‖schwartzCoord 0 (SchwartzMap.smulLeftCLM ℂ (schwartzWord p a)
        (∂_{v} (∂_{w} (schwartzWord q f))))‖ ≤
        C * (‖schwartzCoord (k:ℝ) a‖ * ‖schwartzCoord ((k:ℝ)+1) f‖) := by
  have h := product_words_asymmetric_bound (E:=E) (k:ℝ) ((k:ℝ)+1) p (v::w::q)
    (by exact_mod_cast (show p.length ≤ k by omega))
    (by simp only [List.length_cons]; exact_mod_cast (show q.length+1+1 ≤ k+1 by omega))
    (by
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      have h1 : (Module.finrank ℝ E:ℝ)+1 < k := by exact_mod_cast hk
      have h2 : (p.length:ℝ)+q.length ≤ k := by exact_mod_cast hpq
      linarith)
  exact h

 

def commutatorWords : List E → List (List E × List E)
  | [] => []
  | v::ws => ( [v],ws ) ::
      ((commutatorWords ws).map (fun t => (v::t.1,t.2)) ++
       (commutatorWords ws).map (fun t => (t.1,v::t.2)))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma commutatorWords_orders (ws : List E) (t : List E × List E)
    (ht : t ∈ commutatorWords ws) :
    0 < t.1.length ∧ t.1.length+t.2.length = ws.length := by
  induction ws generalizing t with
  | nil => simp [commutatorWords] at ht
  | cons v ws ih =>
    simp only [commutatorWords,List.mem_cons,List.mem_append,List.mem_map] at ht
    rcases ht with rfl | ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
    · simp [Nat.add_comm]
    · obtain ⟨h1,h2⟩ := ih t ht
      simp only [List.length_cons]
      omega
    · obtain ⟨h1,h2⟩ := ih t ht
      simp only [List.length_cons]
      omega

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_word_product_commutator (ws : List E) (a f : 𝓢(E,ℂ)) :
    schwartzWord ws (SchwartzMap.smulLeftCLM ℂ a f) =
      SchwartzMap.smulLeftCLM ℂ a (schwartzWord ws f) +
      ((commutatorWords ws).map (fun t =>
        SchwartzMap.smulLeftCLM ℂ (schwartzWord t.1 a) (schwartzWord t.2 f))).sum := by
  induction ws with
  | nil => simp [schwartzWord,commutatorWords]
  | cons v ws ih =>
    change ∂_{v} (schwartzWord ws (SchwartzMap.smulLeftCLM ℂ a f)) = _
    rw [ih,lineDerivOp_add,schwartz_deriv_product]
    have he : ∂_{v} (((commutatorWords ws).map (fun t =>
        SchwartzMap.smulLeftCLM ℂ (schwartzWord t.1 a) (schwartzWord t.2 f))).sum) =
        ((commutatorWords ws).map (fun t => ∂_{v}
          (SchwartzMap.smulLeftCLM ℂ (schwartzWord t.1 a) (schwartzWord t.2 f)))).sum :=
      (List.sum_map_hom _ _ (lineDerivOpCLM ℂ 𝓢(E,ℂ) v)).symm
    rw [he]
    simp only [schwartz_deriv_product,list_sum_add,commutatorWords,List.map_cons,
      List.sum_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,
      schwartzWord,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      lineDerivOpCLM_apply]
    abel

lemma second_order_commutator_bound (k : ℕ) (hk : Module.finrank ℝ E + 1 < k)
    (ws : List E) (hws : ws.length ≤ k) (v w : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a f : 𝓢(E,ℂ),
      ‖schwartzCoord 0 (schwartzWord ws
        (SchwartzMap.smulLeftCLM ℂ a (∂_{v} (∂_{w} f))) -
        SchwartzMap.smulLeftCLM ℂ a (∂_{v} (∂_{w} (schwartzWord ws f))))‖ ≤
        C * (‖schwartzCoord (k:ℝ) a‖ * ‖schwartzCoord ((k:ℝ)+1) f‖) := by
  have hcomm (q : List E) (f : 𝓢(E,ℂ)) :
      schwartzWord q (∂_{v} (∂_{w} f)) = ∂_{v} (∂_{w} (schwartzWord q f)) := by
    rw [GlobalElliptic.word_deriv_comm,GlobalElliptic.word_deriv_comm]
  have hb (t : List E × List E) (ht : t ∈ commutatorWords ws) :=
    second_order_commutator_product_bound k hk t.1 t.2
      (commutatorWords_orders ws t ht).1
      (by rw [(commutatorWords_orders ws t ht).2]; exact hws) v w
  classical
  let C : List E × List E → ℝ := fun t =>
    if ht : t ∈ commutatorWords ws then (hb t ht).choose else 0
  have hC (t) (ht : t ∈ commutatorWords ws) : 0 ≤ C t := by
    simp only [C,dite_eq_left ht]
    exact (hb t ht).choose_spec.1
  have hB (t) (ht : t ∈ commutatorWords ws) (a f : 𝓢(E,ℂ)) :
      ‖schwartzCoord 0 (SchwartzMap.smulLeftCLM ℂ (schwartzWord t.1 a)
        (∂_{v} (∂_{w} (schwartzWord t.2 f))))‖ ≤
        C t * (‖schwartzCoord (k:ℝ) a‖ * ‖schwartzCoord ((k:ℝ)+1) f‖) := by
    simp only [C,dite_eq_left ht]
    exact (hb t ht).choose_spec.2 a f
  refine ⟨((commutatorWords ws).map C).sum,List.sum_nonneg (by simpa only
    [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂] using hC),fun a f => ?_⟩
  rw [schwartz_word_product_commutator,hcomm,add_sub_cancel_left,schwartzCoord_list_sum]
  simp_rw [hcomm]
  calc
    _ ≤ ((commutatorWords ws).map (fun t => ‖schwartzCoord 0
      (SchwartzMap.smulLeftCLM ℂ (schwartzWord t.1 a) (∂_{v} (∂_{w} (schwartzWord t.2 f))))‖)).sum :=
      by
        induction commutatorWords ws with
        | nil => simp
        | cons t ts ih =>
          simp only [List.map_cons,List.sum_cons]
          exact (norm_add_le _ _).trans (add_le_add le_rfl ih)
    _ ≤ ((commutatorWords ws).map (fun t => C t *
        (‖schwartzCoord (k:ℝ) a‖ * ‖schwartzCoord ((k:ℝ)+1) f‖))).sum :=
      List.sum_le_sum (fun t ht => hB t ht a f)
    _ = _ := by
      induction commutatorWords ws with
      | nil => simp
      | cons t ts ih => simp only [List.map_cons,List.sum_cons,ih,add_mul]

end SobolevChart

end
end

end OAI
