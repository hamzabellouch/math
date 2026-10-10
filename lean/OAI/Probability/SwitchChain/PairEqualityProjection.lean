import OAI.Probability.SwitchChain.PairFiberBridge

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def observable (i k l : Fin n) : StateSpace n d :=
  WithLp.toLp 2 (fun G => if G.val.Adj i k ↔ G.val.Adj i l then 1 else 0)

def centered (i j k l : Fin n) : StateSpace n d :=
  fluctuation n d {i,j} (observable i k l)

def active (i j k l : Fin n) (G : GraphState n d) : Prop :=
  k ∈ singletonSet G.val i j ∧ l ∈ singletonSet G.val i j

def equalitySpace (i j k l : Fin n) : Submodule ℝ (StateSpace n d) where
  carrier := {f | ∀ G : GraphState n d, ∃ c : ℝ,
    ∀ H : GraphState n d, SameFiber {i,j} G.val H.val →
      f H = c * (if active i j k l G then centered i j k l H else 0)}
  zero_mem' := by
    intro G
    exact ⟨0, fun H h => by simp⟩
  add_mem' := by
    intro f g hf hg G
    obtain ⟨c,hc⟩ := hf G
    obtain ⟨e,he⟩ := hg G
    refine ⟨c+e, fun H h => ?_⟩
    change f H + g H = _
    rw [hc H h, he H h, add_mul]
  smul_mem' := by
    intro c f hf G
    obtain ⟨e,he⟩ := hf G
    refine ⟨c*e, fun H h => ?_⟩
    change c * f H = _
    rw [he H h, mul_assoc]

def projection (i j k l : Fin n) : StateSpace n d →L[ℝ] StateSpace n d :=
  (equalitySpace i j k l).starProjection

@[simp] theorem projection_eq_self_iff (i j k l : Fin n) (f : StateSpace n d) :
    projection i j k l f = f ↔ f ∈ equalitySpace i j k l :=
  Submodule.starProjection_eq_self_iff

def crossTotal (i j k l : Fin n) (G : GraphState n d) : ℕ :=
  edgeBit G.val i k + edgeBit G.val j k +
    (edgeBit G.val i l + edgeBit G.val j l)

theorem active_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    active i j k l G ↔ active i j k l H := by
  have hh := singletonSet_eq_of_key_eq ((sameFiber_iff_key_eq i j hij G.val H.val).mp h)
  unfold active
  rw [hh]

theorem crossTotal_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    crossTotal i j k l G = crossTotal i j k l H := by
  have hh := (sameFiber_iff_key_eq i j hij G.val H.val).mp h
  exact congrArg₂ (· + ·) (key_count hh k) (key_count hh l)

theorem observable_zero_of_inactive (i j k l : Fin n)
    (hk : Outside i j k) (hl : Outside i j l) (G : GraphState n d)
    (ht : crossTotal i j k l G = 2) (ha : ¬ active i j k l G) :
    observable i k l G = 0 := by
  unfold crossTotal at ht
  simp only [active, mem_singletonSet, hk, hl, true_and] at ha
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1:ℝ) else 0) = 0
  by_cases hik : G.val.Adj i k <;> by_cases hjk : G.val.Adj j k <;>
    by_cases hil : G.val.Adj i l <;> by_cases hjl : G.val.Adj j l <;>
    simp_all [edgeBit, Xor]

theorem centered_zero_of_inactive (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (G : GraphState n d)
    (ht : crossTotal i j k l G = 2) (ha : ¬ active i j k l G) :
    centered i j k l G = 0 := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G = 0
  rw [observable_zero_of_inactive i j k l hk hl G ht ha, expectation_eq_average]
  have hz : (∑ H ∈ fiberStates {i,j} G, observable i k l H) = 0 := by
    apply Finset.sum_eq_zero
    intro H hH
    have h := (mem_fiberStates {i,j} G H).mp hH
    apply observable_zero_of_inactive i j k l hk hl H
    · rw [← crossTotal_sameFiber i j k l hij h]
      exact ht
    · exact fun hA => ha ((active_sameFiber i j k l hij h).mpr hA)
  rw [hz]
  simp

def multiply (f g : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => f G * g G)

theorem expectation_multiply (a : Finset (Fin n)) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d a) :
    expectation n d a (multiply w f) = multiply w (expectation n d a f) := by
  ext G
  rw [expectation_eq_average]
  change (∑ H ∈ fiberStates a G, w H * f H) / _ =
    w G * expectation n d a f G
  rw [expectation_eq_average]
  have heq : (∑ H ∈ fiberStates a G, w H * f H) =
      w G * ∑ H ∈ fiberStates a G, f H := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H hH
    rw [hw H G ((mem_fiberStates a G H).mp hH).symm]
  rw [heq, mul_div_assoc]

theorem fluctuation_multiply (a : Finset (Fin n)) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d a) :
    fluctuation n d a (multiply w f) = multiply w (fluctuation n d a f) := by
  rw [fluctuation_eq_sub, expectation_multiply a w f hw, fluctuation_eq_sub]
  ext G
  change w G * f G - w G * expectation n d a f G =
    w G * (f G - expectation n d a f G)
  ring

theorem multiply_centered_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    multiply w (centered i j k l) ∈ equalitySpace i j k l := by
  intro G
  refine ⟨w G, fun H h => ?_⟩
  change w H * centered i j k l H = _
  rw [hw H G h.symm]
  by_cases ha : active i j k l G
  · simp only [ite_eq_left ha]
  · simp only [ite_eq_right ha, mul_zero]
    by_cases ht : crossTotal i j k l G = 2
    · have hH : crossTotal i j k l H = 2 :=
        (crossTotal_sameFiber i j k l hij h).symm.trans ht
      have hA : ¬ active i j k l H :=
        fun hA => ha ((active_sameFiber i j k l hij h).mpr hA)
      rw [centered_zero_of_inactive i j k l hij hk hl H hH hA, mul_zero]
    · rw [hsupport G ht, zero_mul]

theorem fluctuation_weighted_observable_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    fluctuation n d {i,j} (multiply w (observable i k l)) ∈
      equalitySpace i j k l := by
  rw [fluctuation_multiply _ _ _ hw]
  exact multiply_centered_mem i j k l hij hk hl w hw hsupport

theorem fluctuation_weighted_centered_flag_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d) (c : ℝ)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    fluctuation n d {i,j}
      (multiply w (observable i k l - WithLp.toLp 2 (fun _ => c))) ∈
      equalitySpace i j k l := by
  rw [fluctuation_multiply _ _ _ hw, map_sub,
    (fluctuation_eq_zero_iff _ _).mpr (constant_mem _ c), sub_zero]
  exact multiply_centered_mem i j k l hij hk hl w hw hsupport

theorem projection_fixes_weighted_flag_fluctuation
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d) (c : ℝ)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    projection i j k l (fluctuation n d {i,j}
      (multiply w (observable i k l - WithLp.toLp 2 (fun _ => c)))) =
      fluctuation n d {i,j}
        (multiply w (observable i k l - WithLp.toLp 2 (fun _ => c))) := by
  exact (projection_eq_self_iff _ _ _ _ _).mpr
    (fluctuation_weighted_centered_flag_mem i j k l hij hk hl w c hw hsupport)

theorem line_projection_norm_le (i j k l : Fin n) (z f : StateSpace n d)
    (hz : z ∈ equalitySpace i j k l) :
    ‖(Submodule.span ℝ {z}).starProjection f‖ ≤ ‖projection i j k l f‖ := by
  have hle : Submodule.span ℝ {z} ≤ equalitySpace i j k l := by
    rw [Submodule.span_le]
    intro x hx
    have hxz : x = z := Set.mem_singleton_iff.mp hx
    subst x
    exact hz
  have hcomp := Submodule.starProjection_comp_starProjection_of_le hle
  have heq := congrArg (fun A : StateSpace n d →L[ℝ] StateSpace n d => A f) hcomp
  change (Submodule.span ℝ {z}).starProjection (projection i j k l f) =
    (Submodule.span ℝ {z}).starProjection f at heq
  rw [← heq]
  exact (Submodule.span ℝ {z}).norm_starProjection_apply_le _

end Problem315.PairEquality

end

end OAI
