import OAI.InformationTheory.QuantumCircuit.Backward
import OAI.InformationTheory.QuantumCircuit.Asymptotics
import OAI.InformationTheory.QuantumCircuit.ScaleInduction
import OAI.InformationTheory.QuantumCircuit.DepthZero

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- The uniform estimate, with the eventual quantifier outside all circuit data. -/
def UniformLocalization (d : ℕ) (s t : ℝ) : Prop :=
  ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
    ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^s))

lemma uniform_zero {s t : ℝ} (hst : s < t) : UniformLocalization 0 s t := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_power_le hst (2/Real.log 2)] with N hN
  intro U hU M D
  obtain ⟨L,rfl⟩ := hU
  have hb := M.depth_zero_bound (D.rotate L) ((N:ℝ)^t)
  rw [D.rotate_zero L] at hb
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have h := (div_le_iff₀ hlog).mp (show 2*(N:ℝ)^s/Real.log 2 ≤ (N:ℝ)^t by
    simpa only [div_mul_eq_mul_div] using hN)
  nlinarith only [h]

lemma uniform_large (d : ℕ) {s t : ℝ} (ht : 1 < t) : UniformLocalization d s t := by
  filter_upwards [eventually_power_le ht 2,Filter.eventually_ge_atTop 1] with N hN hN1
  intro U _ M D
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlimit : (N:ℝ) < (N:ℝ)^t := by rw [Real.rpow_one] at hN; linarith only [hN,hNpos]
  rw [M.high_eq_zero hlimit,zero_mul,zero_mul,norm_zero]
  exact (Real.exp_pos _).le

lemma uniform_low_propagation {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {a s t : ℝ} (ha : 0 ≤ a) (_hs : 0 ≤ s) (hat : a < t) (hst : s < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
      ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.low ((N:ℝ)^a)‖ ≤ Real.exp (-((N:ℝ)^s)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hat hst)
  have hav : a < v := (le_max_left _ _).trans_lt hv
  have hsv : s < v := (le_max_right _ _).trans_lt hv
  obtain ⟨q,hvq,hqt⟩ := exists_between hvt
  filter_upwards [ih v q (ha.trans hav.le) hvq,
    eventually_two_powers_le hqt hat,eventually_pattern_cost ha hav hsv,
    Filter.eventually_ge_atTop 1] with N hN hp hc hN1
  intro U hU M D
  exact (M.low_propagation_bound (conjugate U D.zero) hN1 (Real.exp_pos _).le hp
    (fun K => hN U hU K D)).trans hc

lemma uniform_small_support {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {u w t : ℝ} (hu : 0 ≤ u) (_hw : 0 ≤ w) (hut : u < t) (hwt : w < t) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit (d+1) U → ∀ M A : Count N,
      (A.support.card:ℝ) ≤ (N:ℝ)^u →
      ‖M.high ((N:ℝ)^t)*conjugate U A.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^w)) := by
  obtain ⟨v,hv,hvt⟩ := exists_between (max_lt hut hwt)
  have huv : u < v := (le_max_left _ _).trans_lt hv
  have hwv : w < v := (le_max_right _ _).trans_lt hv
  have hv0 : 0 < v := lt_of_le_of_lt hu huv
  obtain ⟨r₁,hvr₁,hr₁t⟩ := exists_between hvt
  obtain ⟨r₂,hr₁r₂,hr₂t⟩ := exists_between hr₁t
  filter_upwards [ih v r₁ hv0.le hvr₁,
    uniform_low_propagation ih (hv0.le.trans hvr₁.le) hv0.le hr₁r₂ (hvr₁.trans hr₁r₂),
    uniform_low_propagation ih (hv0.le.trans (hvr₁.trans hr₁r₂).le) hv0.le hr₂t hvt,
    eventually_exp_power_gap hwv huv hv0 3 1 1 (Real.log 9) (by norm_num) zero_lt_one] with N h₁ h₂ h₃ hc
  intro U hU M A hA
  obtain ⟨V,R,L,hV,rfl⟩ := hU
  have hb := small_support_layer_bound V hV.mem_unitary R L M A (Real.exp_pos _).le
    (fun D => h₁ V hV M D) (fun D => h₂ V hV M D) (fun D => h₃ V hV M D)
  have hcost : (9:ℝ)^A.support.card ≤ Real.exp (Real.log 9*(N:ℝ)^u) := by
    calc
      _ = Real.exp (Real.log 9*(A.support.card:ℝ)) := by
        rw [mul_comm,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA (Real.log_nonneg (by norm_num)))
  apply hb.trans
  calc
    _ ≤ Real.exp (Real.log 9*(N:ℝ)^u)*(3*Real.exp (-((N:ℝ)^v))) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = 3*Real.exp (Real.log 9*(N:ℝ)^u-(N:ℝ)^v) := by rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ _ := by simpa only [one_mul] using hc

lemma uniform_backward {d : ℕ}
    (ih : ∀ s t : ℝ, 0 ≤ s → s < t → UniformLocalization d s t)
    {s t a b u w : ℝ} (hs : 0 ≤ s) (hsa : s < a) (hau : a < u)
    (huw : u < w) (hwt : w < t) (htb : t < b) (hdegree : (a+b)/2 < u)
    (hnext : UniformLocalization (d+1) t b) : UniformLocalization (d+1) s t := by
  have ha : 0 < a := lt_of_le_of_lt hs hsa
  have hab : a < b := hau.trans (huw.trans (hwt.trans htb))
  filter_upwards [polynomial_approximation ha hab hdegree,
    uniform_small_support ih (ha.trans hau).le (ha.trans (hau.trans huw)).le (huw.trans hwt) hwt,
    hnext,eventually_backward_cost hs hsa hau huw hwt] with N hp hsmall htail hcost
  intro U hU M D
  obtain ⟨p,hdeg,hweight,hzero,hp⟩ := hp
  have hx := D.polynomial_transition M U p ((N:ℝ)^t) ((N:ℝ)^u) (Real.exp (-((N:ℝ)^w)))
    (Real.exp_pos _).le hdeg (fun A hA => hsmall U hU M A hA)
  have hx' : ‖M.high ((N:ℝ)^t)*conjugate U (D.polynomial p)*M.zero‖ ≤
      Real.exp ((N:ℝ)^u-(N:ℝ)^w) := by
    apply hx.trans
    calc
      _ ≤ Real.exp ((N:ℝ)^u)*Real.exp (-((N:ℝ)^w)) :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have herr := D.polynomial_error_low p (Real.exp_pos _).le hzero (fun k hk hkb =>
    hp k hk (by exact_mod_cast hkb.le.trans (Nat.le_ceil ((N:ℝ)^b))))
  have hinv := htail (star U) hU.star_mem D M
  simp only [conjugate,star_star,mul_assoc] at hinv
  have hsq := M.backward_finite D U hU.mem_unitary p ((N:ℝ)^t) ((N:ℝ)^b)
    (Real.exp ((N:ℝ)^u-(N:ℝ)^w)) (Real.exp ((N:ℝ)^u))
    (Real.exp (-((N:ℝ)^a))) (Real.exp (-((N:ℝ)^t))) hx'
    ((D.polynomial_norm_le p).trans hweight) herr (by simpa only [mul_assoc] using hinv)
  have hsq' := hsq.trans hcost
  have heq : Real.exp (-2*(N:ℝ)^s) = (Real.exp (-((N:ℝ)^s)))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [heq] at hsq'
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq'

/-- Uniform localization, proved by depth and finite scale induction. -/
theorem uniform_localization : ∀ d s t, 0 ≤ s → s < t → UniformLocalization d s t := by
  intro d
  induction d with
  | zero => intro s t _ hst; exact uniform_zero hst
  | succ d ih =>
    apply finite_scale_induction (UniformLocalization (d+1))
    · intro s t _ _ ht; exact uniform_large (d+1) ht
    · intro s t a b u w hs hsa hau huw hwt htb hdegree hnext
      exact uniform_backward ih hs hsa hau huw hwt htb hdegree hnext

/-- Uniform product-projection localization in the Euclidean operator norm. -/
theorem localization : LocalizationStatement := by
  intro d s t hs hst
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (uniform_localization d s t hs hst)
  refine ⟨N₀,?_⟩
  intro N hN U hU M D
  simpa only [conjugate,mul_assoc] using hN₀ N hN U hU M D

end QAC

end

end OAI
