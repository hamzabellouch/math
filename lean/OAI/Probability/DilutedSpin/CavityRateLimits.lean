import OAI.Probability.DilutedSpin.CavitySplit
import OAI.Probability.DilutedSpin.NormalizationSymmetry

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology NNReal BigOperators

lemma oneNewRate_tendsto (α : ℝ≥0) (q : ℕ) :
    Tendsto (fun N => (oneNewRate α q N:ℝ)) atTop (𝓝 ((α:ℝ)*(q+1))) := by
  have hh := ((tendsto_natCast_div_add_atTop (1:ℝ)).pow q).const_mul ((α:ℝ)*(q+1))
  simpa only [oneNewRate,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,
    NNReal.coe_pow,NNReal.coe_div,one_pow,mul_one] using hh

lemma reservoir_deficit_identity (α : ℝ≥0) (q N : ℕ) :
    (α:ℝ)*N-(reservoirRate α q N:ℝ) =
      (α:ℝ)*((N:ℝ)/(N+1))*(∑ i∈Finset.range q,((N:ℝ)/(N+1))^i) := by
  have hh := geom_sum_mul ((N:ℝ)/(N+1)) q
  have hd : (N:ℝ)+1 ≠ 0 := by positivity
  change (α:ℝ)*N-(α:ℝ)*N*((N:ℝ)/(N+1))^q = _
  have hx : ((N:ℝ)/(N+1)-1) = -1/(N+1) := by field_simp; ring
  rw [hx] at hh
  have he : 1-((N:ℝ)/(N+1))^q = (∑ i∈Finset.range q,((N:ℝ)/(N+1))^i)/(N+1) := by
    simp only [div_eq_mul_inv,neg_mul,one_mul,mul_neg] at hh ⊢
    linarith
  rw [show (α:ℝ)*N-(α:ℝ)*N*((N:ℝ)/(N+1))^q = (α:ℝ)*N*(1-((N:ℝ)/(N+1))^q) by ring,he]
  ring

lemma reservoir_deficit_tendsto (α : ℝ≥0) (q : ℕ) :
    Tendsto (fun N => (α:ℝ)*N-(reservoirRate α q N:ℝ)) atTop (𝓝 ((α:ℝ)*q)) := by
  simp_rw [reservoir_deficit_identity]
  have hh := ((tendsto_natCast_div_add_atTop (1:ℝ)).const_mul (α:ℝ)).mul
    (tendsto_finsetSum (Finset.range q) (fun i _ => (tendsto_natCast_div_add_atTop (1:ℝ)).pow i))
  simpa only [one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,mul_one] using hh

open Classical in
lemma cavity_bad_count (q N : ℕ) :
    (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (0:ℝ) else 1) =
      (N+1:ℝ)^(q+1)-(N:ℝ)^(q+1)-(q+1:ℝ)*(N:ℝ)^q := by
  have hg := sum_cavityKeep (q := q) (N := N) (fun _ => (1:ℝ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_prod,nsmul_eq_mul,mul_one,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_mul] at hg
  have he : (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (0:ℝ) else 1) =
      (∑ _x : Fin (q+1) → Fin (N+1),(1:ℝ))-
      (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (1:ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> norm_num
  rw [he,hg]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  ring

noncomputable def cavityBadRate (α : ℝ≥0) (q N : ℕ) : ℝ :=
  (α:ℝ)*(N+1)-(reservoirRate α q N:ℝ)-(oneNewRate α q N:ℝ)

open Classical in
lemma cavityBadRate_count (α : ℝ≥0) (q N : ℕ) :
    cavityBadRate α q N = (α:ℝ)*(N+1)*
      (∑ x : Fin (q+1) → Fin (N+1),if CavityGood x then (0:ℝ) else 1)/(N+1)^(q+1) := by
  rw [cavity_bad_count]
  simp only [cavityBadRate,oneNewRate,reservoirRate,NNReal.coe_mul,NNReal.coe_add,
    NNReal.coe_natCast,NNReal.coe_one,NNReal.coe_pow,NNReal.coe_div,div_pow,pow_succ]
  have hd : (N:ℝ)+1≠0 := by positivity
  field_simp

lemma cavityBadRate_nonneg (α : ℝ≥0) (q N : ℕ) : 0≤cavityBadRate α q N := by
  classical
  rw [cavityBadRate_count]
  positivity

lemma cavityBadRate_tendsto (α : ℝ≥0) (q : ℕ) :
    Tendsto (cavityBadRate α q) atTop (𝓝 0) := by
  have hh := ((tendsto_const_nhds (x := (α:ℝ))).add (reservoir_deficit_tendsto α q)).sub (oneNewRate_tendsto α q)
  have he : (α:ℝ)+(α:ℝ)*q-(α:ℝ)*(q+1)=0 := by ring
  rw [he] at hh
  convert hh using 1
  funext N
  dsimp [cavityBadRate]
  ring

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory

/-- Move the singled-out interaction coordinate to the distinguished last slot,
 preserving the relative order of all other slots. -/
def cavityCoordinateEquiv {q : ℕ} (j : Fin (q+1)) : Equiv.Perm (Fin (q+1)) where
  toFun := j.insertNth (Fin.last q) (fun i => i.castSucc)
  invFun := Fin.lastCases j (fun i => j.succAbove i)
  left_inv x := by
    refine Fin.succAboveCases j ?_ (fun i => ?_) x
    · simp only [Fin.insertNth_apply_same,Fin.lastCases_last]
    · simp only [Fin.insertNth_apply_succAbove,Fin.lastCases_castSucc]
  right_inv x := by
    refine Fin.lastCases ?_ (fun i => ?_) x
    · simp only [Fin.lastCases_last,Fin.insertNth_apply_same]
    · simp only [Fin.lastCases_castSucc,Fin.insertNth_apply_succAbove]

lemma appendSpin_castSucc {q : ℕ} (s : Fin q → Spin) (ε : Spin) (i : Fin q) :
    appendSpin (p := q+1) s ε i.castSucc = s i := by
  simp only [appendSpin,Nat.add_sub_cancel,Fin.val_castSucc,dite_eq_left i.isLt]
  rfl

lemma appendSpin_last {q : ℕ} (s : Fin q → Spin) (ε : Spin) :
    appendSpin (p := q+1) s ε (Fin.last q) = ε := by
  simp [appendSpin]

lemma cavityCoordinate_append {q : ℕ} (j : Fin (q+1)) (s : Fin q → Spin) (ε : Spin) :
    (fun l => appendSpin (p := q+1) s ε (cavityCoordinateEquiv j l)) = j.insertNth ε s := by
  funext l
  refine Fin.succAboveCases j ?_ (fun i => ?_) l
  · simp only [cavityCoordinateEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same,appendSpin_last]
  · simp only [cavityCoordinateEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_succAbove,appendSpin_castSucc]

/-- iid coordinate symmetry is sufficient for all one-new-index classes to
 have the exact same interaction as the last-coordinate cavity convention. -/
lemma cavity_coordinate_identDistrib {q : ℕ} {X : Type} [MeasurableSpace X]
    (μ : Measure X) (θ : X → Interaction (q+1))
    (hsym : ∀ e : Equiv.Perm (Fin (q+1)), IdentDistrib θ
      (fun z s => θ z (fun l => s (e l))) μ μ)
    (j : Fin (q+1)) :
    IdentDistrib (fun z (v : (Fin q → Spin) × Spin) => θ z (appendSpin v.1 v.2))
      (fun z (v : (Fin q → Spin) × Spin) => θ z (j.insertNth v.2 v.1)) μ μ := by
  have h := (hsym (cavityCoordinateEquiv j)).comp
    (show Measurable (fun t : Interaction (q+1) => fun v : (Fin q → Spin) × Spin => t (appendSpin v.1 v.2)) by fun_prop)
  simpa only [Function.comp_def,cavityCoordinate_append] using h

end DilutedSpinGlass

end

end OAI
