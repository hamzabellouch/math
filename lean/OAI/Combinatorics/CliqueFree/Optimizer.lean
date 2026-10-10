import OAI.Combinatorics.CliqueFree.WeightedGraph

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

/-- The directed bilinear edge form (twice the quadratic mass on the diagonal). -/
noncomputable def edgeForm (G : SimpleGraph V) (a b : V → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then a u * b v else 0

lemma edgeForm_self (G : SimpleGraph V) (a : V → ℝ) : edgeForm G a a = 2 * edgeMass G a := by
  simp only [edgeForm,edgeMass,crossMass]
  ring

lemma edgeForm_symm (G : SimpleGraph V) (a b : V → ℝ) : edgeForm G a b = edgeForm G b a := by
  unfold edgeForm
  rw [sum_comm]
  simp_rw [G.adj_comm,mul_comm]

lemma edgeForm_add_left (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G (a+b) c = edgeForm G a c + edgeForm G b c := by
  unfold edgeForm
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  split_ifs <;> simp [Pi.add_apply,add_mul]

lemma edgeForm_add_right (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G a (b+c) = edgeForm G a b + edgeForm G a c := by
  rw [edgeForm_symm,edgeForm_add_left,edgeForm_symm _ b,edgeForm_symm _ c]

lemma edgeForm_neighbor (G : SimpleGraph V) (a b : V → ℝ) :
    edgeForm G a b = ∑ u, a u * neighborMass G b u := by
  simp only [edgeForm,neighborMass,mass,neighbors,sum_filter,mul_sum,mul_ite,mul_zero]

lemma edgeMass_add (G : SimpleGraph V) (a b : V → ℝ) :
    edgeMass G (a+b) = edgeMass G a + edgeMass G b + edgeForm G a b := by
  have h := edgeForm_self G (a+b)
  rw [edgeForm_add_left,edgeForm_add_right,edgeForm_add_right,edgeForm_self,edgeForm_self,
    edgeForm_symm G b a] at h
  linarith

lemma edgeForm_mono (G : SimpleGraph V) {a b c d : V → ℝ}
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, 0 ≤ b v) (hac : ∀ v, a v ≤ c v) (hbd : ∀ v, b v ≤ d v) :
    edgeForm G a b ≤ edgeForm G c d := by
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro v _
  split_ifs
  · exact mul_le_mul (hac u) (hbd v) (hb v) ((ha u).trans (hac u))
  · rfl

lemma edgeMass_mono_weight (G : SimpleGraph V) {w q : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hwq : ∀ v, w v ≤ q v) : edgeMass G w ≤ edgeMass G q := by
  have h := edgeForm_mono G hw hw hwq hwq
  rw [edgeForm_self,edgeForm_self] at h
  linarith

noncomputable def spike [DecidableEq V] (v : V) (t : ℝ) : V → ℝ := fun u ↦ if u = v then t else 0

lemma edgeForm_spike [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    edgeForm G (spike v t) w = t * neighborMass G w v := by
  rw [edgeForm_neighbor]
  simp [spike,ite_mul]

lemma edgeMass_spike [DecidableEq V] (G : SimpleGraph V) (v : V) (t : ℝ) :
    edgeMass G (spike v t) = 0 := by
  have h := edgeForm_self G (spike v t)
  rw [edgeForm_spike] at h
  have hn : neighborMass G (spike v t) v = 0 := by
    simp [neighborMass,mass,neighbors,spike]
  rw [hn] at h
  linarith

omit [Fintype V] in
lemma update_eq_add_spike [DecidableEq V] (w : V → ℝ) (v : V) (t : ℝ) :
    Function.update w v t = w + spike v (t-w v) := by
  funext u
  by_cases h : u = v <;> simp [Function.update,spike,h]

lemma edgeMass_update [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    edgeMass G (Function.update w v t) = edgeMass G w + (t-w v)*neighborMass G w v := by
  rw [update_eq_add_spike,edgeMass_add,edgeMass_spike,edgeForm_symm,edgeForm_spike]
  ring

/-- The vertex summand, with Mathlib's log(0)=0 convention. -/
def vertexPotential (t : ℝ) : ℝ := t * (1-Real.log t)

noncomputable def potential (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  ∑ v, vertexPotential (w v) - edgeMass G w

def IsOptimizer (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ q : V → ℝ, (∀ v, 0 ≤ q v) → potential G q ≤ potential G w

lemma continuous_vertexPotential : Continuous vertexPotential := by
  have h := continuous_id.sub Real.continuous_mul_log
  convert h using 1
  ext x
  simp [vertexPotential]
  ring

lemma continuous_edgeMass (G : SimpleGraph V) : Continuous (edgeMass G) := by
  classical
  unfold edgeMass crossMass
  apply Continuous.div_const
  apply continuous_finsetSum
  intro u _
  apply continuous_finsetSum
  intro v _
  split_ifs <;> fun_prop

lemma continuous_potential (G : SimpleGraph V) : Continuous (potential G) := by
  unfold potential
  apply Continuous.sub _ (continuous_edgeMass G)
  exact continuous_finsetSum _ fun v _ ↦ continuous_vertexPotential.comp (continuous_apply v)

lemma vertexPotential_le_one {t : ℝ} (ht : 0 ≤ t) : vertexPotential t ≤ 1 := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [vertexPotential]
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ht) ht.le
  rw [mul_sub,mul_inv_cancel₀ ht.ne'] at h
  unfold vertexPotential
  nlinarith

lemma potential_clamp (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    potential G w ≤ potential G (fun v ↦ min (w v) 1) := by
  have hv (v : V) : vertexPotential (w v) ≤ vertexPotential (min (w v) 1) := by
    by_cases h : w v ≤ 1
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h)]
      simpa [vertexPotential] using vertexPotential_le_one (hw v)
  have hs := sum_le_sum (s := univ) (fun v _ ↦ hv v)
  have he := edgeMass_mono_weight G (fun v ↦ le_min (hw v) zero_le_one) (fun v ↦ min_le_left (w v) 1)
  unfold potential
  linarith

lemma exists_optimizer (G : SimpleGraph V) : ∃ w : V → ℝ, IsOptimizer G w := by
  let S : Set (V → ℝ) := Set.Icc 0 1
  have hS : IsCompact S := isCompact_Icc
  have hne : S.Nonempty := ⟨0,by simp [S]⟩
  obtain ⟨w,hw,hmax⟩ := hS.exists_isMaxOn hne (continuous_potential G).continuousOn
  refine ⟨w,hw.1,?_⟩
  intro q hq
  apply (potential_clamp G hq).trans
  apply hmax
  exact ⟨fun v ↦ le_min (hq v) zero_le_one,fun v ↦ min_le_right (q v) 1⟩

lemma potential_update [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    potential G (Function.update w v t) - potential G w =
      vertexPotential t - vertexPotential (w v) - (t-w v)*neighborMass G w v := by
  have hs : (∑ u, vertexPotential (Function.update w v t u)) =
      ∑ u, vertexPotential (w u) + (vertexPotential t - vertexPotential (w v)) := by
    rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v)]
    simp only [Function.update_self]
    have h : (∑ u ∈ univ.erase v, vertexPotential (Function.update w v t u)) =
        ∑ u ∈ univ.erase v, vertexPotential (w u) := by
      apply sum_congr rfl
      intro u hu
      rw [Function.update_of_ne (by simpa using (mem_erase.1 hu).1)]
    rw [h]
    ring
  unfold potential
  rw [hs,edgeMass_update]
  ring

lemma optimizer_stationary {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w) (v : V) :
    0 < w v ∧ Real.log (1/w v) = neighborMass G w v ∧ w v ≤ 1 := by
  classical
  let N := neighborMass G w v
  let a := Real.exp (-N)
  have ha : 0 < a := Real.exp_pos _
  have hN : 0 ≤ N := neighborMass_nonneg G hw.1 v
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hloga : Real.log a = -N := Real.log_exp _
  have hmax := hw.2 (Function.update w v a) (fun u ↦ by
    by_cases h : u = v
    · subst u; simpa using ha.le
    · simpa [h] using hw.1 u)
  have heq := potential_update G w v a
  have hbound : a ≤ w v * (1-Real.log (w v)-N) := by
    rw [vertexPotential,vertexPotential,hloga] at heq
    dsimp [N] at *
    nlinarith only [hmax,heq]
  have hwv : 0 < w v := by
    have h0 := hw.1 v
    by_contra hn
    have hz : w v = 0 := le_antisymm (le_of_not_gt hn) h0
    simp only [hz,zero_mul] at hbound
    linarith
  have hwa : w v = a := by
    by_contra hn
    have hdiv : a / w v ≠ 1 := by
      intro he
      exact hn ((div_eq_one_iff_eq hwv.ne').1 he).symm
    have hl := Real.log_lt_sub_one_of_pos (div_pos ha hwv) hdiv
    rw [Real.log_div ha.ne' hwv.ne',hloga] at hl
    have hh := mul_lt_mul_of_pos_left hl hwv
    have hid : w v * (a / w v - 1) = a-w v := by field_simp
    rw [hid] at hh
    nlinarith
  refine ⟨hwv,?_,hwa ▸ ha1⟩
  rw [one_div,Real.log_inv,hwa,hloga]
  simp [N]

/-- Expansion around a stationary positive maximizer. -/
lemma optimizer_divergence {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    0 ≤ potential G w - potential G q ∧
      potential G w - potential G q =
        (∑ v, (q v * Real.log (q v / w v) - q v + w v)) + edgeMass G (q-w) := by
  refine ⟨sub_nonneg.2 (hw.2 q hq),?_⟩
  have hsum (v : V) : vertexPotential (w v) - vertexPotential (q v) +
      (q v-w v)*neighborMass G w v = q v*Real.log (q v/w v) - q v + w v := by
    obtain ⟨hwv,hstat,_⟩ := optimizer_stationary hw v
    rw [one_div,Real.log_inv] at hstat
    rcases (hq v).eq_or_lt with hz | hqv
    · simp [← hz,vertexPotential,hstat.symm]
      ring
    · rw [Real.log_div hqv.ne' hwv.ne']
      unfold vertexPotential
      rw [← hstat]
      ring
  have he := edgeMass_add G (q-w) w
  have hqw : q-w+w = q := sub_add_cancel _ _
  rw [hqw,edgeForm_neighbor] at he
  simp only [Pi.sub_apply] at he
  have hs := congrArg (fun f : V → ℝ ↦ ∑ v, f v) (funext hsum)
  simp only [sum_add_distrib,sum_sub_distrib] at hs
  unfold potential
  simp only [sum_add_distrib,sum_sub_distrib]
  linarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI
