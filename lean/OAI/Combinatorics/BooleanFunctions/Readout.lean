import OAI.Combinatorics.BooleanFunctions.Grouping
import OAI.Combinatorics.BooleanFunctions.ReadoutCLT

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype β] in
theorem singletonSum_eq_average (f : Cube γ → ℝ) :
    singletonSum f = average (fun x => f x*cubeSum x) := by
  have hi (i : γ) : fourierCoeff f {i} = average (fun x => f x*sign (x i)) := by
    unfold fourierCoeff
    simp only [character_singleton]
    congr 1
    exact Subsingleton.elim _ _
  unfold singletonSum
  simp only [hi]
  rw [← average_sum]
  congr 1
  funext x
  exact (Finset.mul_sum _ _ _).symm

def readSign (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

theorem readSign_boolean (z : ℝ) : readSign z = -1 ∨ readSign z = 1 := by
  unfold readSign
  split_ifs <;> simp

theorem readSign_mul (z : ℝ) : readSign z*z = |z| := by
  unfold readSign
  split_ifs with h
  · rw [one_mul,abs_of_nonneg h]
  · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]

def readout (F : Cube γ → β) (x : Cube γ) : ℝ := readSign (score F x)

omit [Fintype β] in
theorem readout_boolean (F : Cube γ → β) : IsBoolean (readout F) :=
  fun _ => readSign_boolean _

theorem readout_degree (F : Cube γ → β) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) :
    fourierDegree (readout F) ≤ D := by
  exact fourierDegree_comp_observation_le F D hF
    (fun b => readSign (conditionalValue F cubeSum b))

theorem readout_sum (F : Cube γ → β) :
    singletonSum (readout F) = average (fun x => |score F x|) := by
  rw [singletonSum_eq_average]
  have hp := conditionalAverage_projection F cubeSum
    (fun b => readSign (conditionalValue F cubeSum b))
  change average (fun x => readSign (conditionalValue F cubeSum (F x))*cubeSum x) = _
  exact hp.symm.trans (by
    change average (fun x => readSign (score F x)*score F x) = _
    simp only [readSign_mul])

theorem exists_readout (F : Cube γ → β) (hv : 0 < variance F) (D : ℕ)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n × γ) → ℝ,
      IsBoolean f ∧ fourierDegree f ≤ n*D ∧
      ReadoutCLT.constant*groupScale F n < singletonSum f := by
  let : MeasurableSpace (Cube γ) := ⊤
  obtain ⟨n,hn,hg⟩ := ReadoutCLT.exists_abs_gain (standard F) (standard_zero F) (standard_sq F hv)
  refine ⟨n,hn,readout (grouped (κ := Fin n) F),readout_boolean _,?_,?_⟩
  · apply readout_degree
    intro b
    simpa only [Fintype.card_fin] using grouped_degree F D hF b
  · rw [readout_sum,grouped_score_scaled F hv hn]
    have hk : 0 < groupScale F n := mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)) (Real.sqrt_pos.mpr hv)
    simp only [abs_mul,abs_of_pos hk,average_const_mul]
    have he := average_equiv (blockCurry (Fin n) γ Bool)
      (fun x => |FiniteCLT.normalizedSum (standard F) n x|)
    change _ < groupScale F n*average (fun x => |groupStandard F n x|)
    rw [show average (fun x => |groupStandard F n x|) =
      average (fun x => |FiniteCLT.normalizedSum (standard F) n x|) from he]
    rw [mul_comm ReadoutCLT.constant]
    exact mul_lt_mul_of_pos_left hg hk

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ δ : Type*} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]

def cubeReindex (e : γ ≃ δ) : Cube δ ≃ Cube γ where
  toFun x i := x (e i)
  invFun x j := x (e.symm j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp

omit [DecidableEq γ] [DecidableEq δ] in
theorem cubeSum_reindex (e : γ ≃ δ) (x : Cube δ) :
    cubeSum (cubeReindex e x) = cubeSum x := by
  exact e.sum_comp (fun j => sign (x j))

theorem singletonSum_reindex (e : γ ≃ δ) (f : Cube γ → ℝ) :
    singletonSum (f ∘ cubeReindex e) = singletonSum f := by
  rw [singletonSum_eq_average,singletonSum_eq_average]
  have he : (fun x => (f ∘ cubeReindex e) x*cubeSum x) =
      (fun x => f x*cubeSum x) ∘ cubeReindex e := by
    funext x
    simp only [Function.comp_apply,cubeSum_reindex]
  rw [he]
  convert average_equiv (cubeReindex e) (fun x => f x*cubeSum x) using 1
  congr 1

omit [Fintype δ] [DecidableEq δ] in
theorem nonconstant_of_singletonSum_pos (f : Cube γ → ℝ) (hf : 0 < singletonSum f) :
    Nonconstant f := by
  by_contra h
  have hc : ∀ x y, f x = f y := by simpa only [Nonconstant,not_exists,not_not] using h
  have he : f = fun _ => f (fun _ => false) := funext fun x => hc x _
  rw [he,singletonSum_eq_average,average_const_mul,cubeSum_zero,mul_zero] at hf
  exact (lt_irrefl 0) hf

omit [Fintype δ] [DecidableEq δ] [DecidableEq γ] in
theorem positive_card_of_nonconstant (f : Cube γ → ℝ) (hf : Nonconstant f) :
    0 < Fintype.card γ := by
  by_contra h
  have hc : Fintype.card γ = 0 := Nat.eq_zero_of_not_pos h
  have : IsEmpty γ := Fintype.card_eq_zero_iff.mp hc
  obtain ⟨x,y,hxy⟩ := hf
  exact hxy (congrArg f (Subsingleton.elim x y))

omit [Fintype δ] [DecidableEq δ] in
theorem reindex_violation (f : Cube γ → ℝ) (C : ℝ) (hC : 0 < C)
    (hb : IsBoolean f) (hf : C*Real.sqrt (fourierDegree f) < singletonSum f) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Cube (Fin n) → ℝ,
      IsBoolean g ∧ Nonconstant g ∧ C*Real.sqrt (fourierDegree g) < singletonSum g := by
  let e := Fintype.equivFin γ
  let g := f ∘ cubeReindex e
  have hp : 0 < singletonSum f := lt_of_le_of_lt (mul_nonneg hC.le (Real.sqrt_nonneg _)) hf
  have hn := nonconstant_of_singletonSum_pos f hp
  have hg : singletonSum g = singletonSum f := singletonSum_reindex e f
  refine ⟨Fintype.card γ,positive_card_of_nonconstant f hn,g,(fun x => hb _),?_,?_⟩
  · exact nonconstant_of_singletonSum_pos g (hg.symm ▸ hp)
  · rw [hg]
    have hd : fourierDegree g ≤ fourierDegree f := fourierDegree_comp_coordinates_le f e
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hd)) hC.le).trans_lt hf

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

theorem sqrt_ratio_bound {C c v : ℝ} {D n : ℕ}
    (hC : 0 < C) (hc : 0 < c) (hv : 0 ≤ v) (hD : 0 < D) (hn : 0 < n)
    (hq : (C/c)^2 < v/D) :
    C*Real.sqrt (n*D:ℕ) < c*(Real.sqrt n*Real.sqrt v) := by
  have hd : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hq' := (lt_div_iff₀ hd).mp hq
  have hm := mul_lt_mul_of_pos_left hq' (sq_pos_of_pos hc)
  have he : c^2*((C/c)^2*(D:ℝ)) = C^2*(D:ℝ) := by
    field_simp
  rw [he] at hm
  have hs : C*Real.sqrt D < c*Real.sqrt v := by
    apply (sq_lt_sq₀ (mul_nonneg hC.le (Real.sqrt_nonneg _))
      (mul_nonneg hc.le (Real.sqrt_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt hd.le,Real.sq_sqrt hv] using hm
  rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg n)]
  have hn' : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  calc C*(Real.sqrt n*Real.sqrt D) = Real.sqrt n*(C*Real.sqrt D) := by ring
    _ < Real.sqrt n*(c*Real.sqrt v) := mul_lt_mul_of_pos_left hs hn'
    _ = c*(Real.sqrt n*Real.sqrt v) := by ring

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

theorem violation_of_observation (F : Cube γ → β) (D : ℕ) (hD : 0 < D)
    (hF : ∀ b, fourierDegree (cell F b) ≤ D) (hv : 0 < variance F)
    (C : ℝ) (hC : 0 < C) (hq : (C/ReadoutCLT.constant)^2 < variance F/D) :
    ∃ n : ℕ, 0 < n ∧ ∃ f : Cube (Fin n) → ℝ,
      IsBoolean f ∧ Nonconstant f ∧ C*Real.sqrt (fourierDegree f) < singletonSum f := by
  obtain ⟨n,hn,f,hb,hd,hs⟩ := exists_readout F hv D hF
  apply reindex_violation f C hC hb
  have ht := sqrt_ratio_bound hC ReadoutCLT.constant_pos hv.le hD hn hq
  have hb' : C*Real.sqrt (fourierDegree f) ≤ C*Real.sqrt (n*D:ℕ) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr hd)) hC.le
  exact hb'.trans_lt (ht.trans hs)

end Observations
end SquareRootDegree

end

end OAI
