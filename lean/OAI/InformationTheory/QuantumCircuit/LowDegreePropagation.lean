import OAI.InformationTheory.QuantumCircuit.Propagation

namespace OAI

/-! Low-degree propagation with subexponential norm and error bounds. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

def headLayer {N : ℕ} (l : List (AnalyticLayer N)) : AnalyticLayer N :=
  l.headD (.local (fun _ => 1))

lemma headLayer_nil_matrix {N : ℕ} : (headLayer ([] : List (AnalyticLayer N))).matrix = 1 := by
  simp [headLayer, AnalyticLayer.matrix, localMatrix]

lemma evolution_tail {N : ℕ} (l : List (AnalyticLayer N)) :
    evolution l = evolution l.tail * (headLayer l).matrix := by
  cases l with
  | nil => simp [evolution, headLayer_nil_matrix]
  | cons a l => rfl

lemma evolution_take_tail {N : ℕ} (l : List (AnalyticLayer N)) (j : ℕ) :
    evolution (l.take (j + 1)) = evolution (l.tail.take j) * (headLayer l).matrix := by
  cases l with
  | nil => simp [evolution, headLayer_nil_matrix]
  | cons a l => simp [List.take_succ_cons, evolution, headLayer]

lemma RegularTrajectory.head {m : ℕ → ℕ} {l : ∀ ν, List (AnalyticLayer (m ν))}
    {ψ : ∀ ν, State (m ν)} (hreg : RegularTrajectory m l ψ) :
    LayerRegular m (fun ν => headLayer (l ν)) ψ := by
  intro b h p hb hbh hh hp hph
  filter_upwards [hreg b h p hb hbh hh hp hph] with ν hν
  intro R hR S hS hsize
  have hj : (l ν)[0]? = some (.reflection R) := by
    cases hl : l ν with
    | nil => simp [hl, headLayer] at hR
    | cons a l => simpa [hl, headLayer] using congrArg some hR
  simpa [evolution] using hν 0 R hj S hS hsize

lemma RegularTrajectory.tail {m : ℕ → ℕ} {l : ∀ ν, List (AnalyticLayer (m ν))}
    {ψ : ∀ ν, State (m ν)} (hreg : RegularTrajectory m l ψ) :
    RegularTrajectory m (fun ν => (l ν).tail)
      (fun ν => act (headLayer (l ν)).matrix (ψ ν)) := by
  intro b h p hb hbh hh hp hph
  filter_upwards [hreg b h p hb hbh hh hp hph] with ν hν
  intro j R hj S hS hsize
  have hget : (l ν)[j + 1]? = some (.reflection R) := by
    simpa only [List.getElem?_tail] using hj
  have hh := hν (j + 1) R hget S hS hsize
  rwa [evolution_take_tail, act_mul] at hh

theorem low_degree_propagation_with_prefactor
    (hpauli : PublishedPauliExpansion) (hspec : PublishedProductSpectralResolution)
    (d : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (l : ∀ ν, List (AnalyticLayer (m ν))) (hl : ∀ ν, (l ν).length ≤ d)
    (ψ : ∀ ν, State (m ν)) (hψ : ∀ ν, ‖ψ ν‖ ≤ 1)
    (hreg : RegularTrajectory m l ψ)
    {k K : ℝ} (hk : 0 < k) (hkK : k < K) (hK : K < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ ν in atTop, ∀ E : Operator (m ν),
      HasDegreeLE E ((m ν : ℝ)^k) → ‖E‖ ≤ Real.exp ((m ν : ℝ)^k) →
      TransportOn (evolution (l ν)) (ψ ν) ((m ν : ℝ)^K) (Real.exp ((m ν : ℝ)^K))
        (ε * Real.exp (-((m ν : ℝ)^k))) E := by
  induction d generalizing l ψ k K ε with
  | zero =>
    filter_upwards [hm.eventually (eventually_ge_atTop 1)] with ν hN
    intro E hE hn
    have hl0 : l ν = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hl ν))
    have hpow : (m ν : ℝ)^k ≤ (m ν : ℝ)^K :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hkK.le
    refine ⟨E, hE.mono hpow, hn.trans (Real.exp_le_exp.mpr hpow), ?_⟩
    simp only [hl0, evolution, act_one, sub_self, norm_zero]
    positivity
  | succ d ih =>
    obtain ⟨v, hkv, hvK⟩ := exists_between hkK
    let ξ : ∀ ν, State (m ν) := fun ν => act (headLayer (l ν)).matrix (ψ ν)
    have hξ : ∀ ν, ‖ξ ν‖ ≤ 1 := by
      intro ν
      exact (act_unitary_norm (headLayer (l ν)).isCircuit.mem_unitary (ψ ν)).le.trans (hψ ν)
    have htlen : ∀ ν, (l ν).tail.length ≤ d := by
      intro ν
      have hh := hl ν
      simp only [List.length_tail]
      omega
    have htreg : RegularTrajectory m (fun ν => (l ν).tail) ξ := hreg.tail
    have hfirst := regular_layer_propagation hpauli hspec m hm
      (fun ν => headLayer (l ν)) ψ hψ hreg.head hk hkv (hvK.trans hK)
      (ε := ε / 2) (by positivity)
    have hrest := ih (fun ν => (l ν).tail) htlen ξ hξ htreg
      (hk.trans hkv) hvK hK (ε := ε / 2) (by positivity)
    filter_upwards [hfirst, hrest, hm.eventually (eventually_ge_atTop 1)] with ν hf hr hN
    intro E hE hn
    obtain ⟨E₁, hd₁, hn₁, he₁⟩ := hf E hE hn
    obtain ⟨E₂, hd₂, hn₂, he₂⟩ := hr E₁ hd₁ hn₁
    refine ⟨E₂, hd₂, hn₂, ?_⟩
    have heq : act (evolution (l ν)) (act E (ψ ν)) -
        act E₂ (act (evolution (l ν)) (ψ ν)) =
        act (evolution (l ν).tail)
          (act (headLayer (l ν)).matrix (act E (ψ ν)) - act E₁ (ξ ν)) +
        (act (evolution (l ν).tail) (act E₁ (ξ ν)) -
          act E₂ (act (evolution (l ν).tail) (ξ ν))) := by
      rw [evolution_tail]
      simp only [act_mul, act_sub_state, ξ]
      abel
    rw [heq]
    have hpow : (m ν : ℝ)^k ≤ (m ν : ℝ)^v :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hkv.le
    calc
      _ ≤ ‖act (evolution (l ν).tail)
          (act (headLayer (l ν)).matrix (act E (ψ ν)) - act E₁ (ξ ν))‖ +
          ‖act (evolution (l ν).tail) (act E₁ (ξ ν)) -
            act E₂ (act (evolution (l ν).tail) (ξ ν))‖ := norm_add_le _ _
      _ ≤ (ε / 2) * Real.exp (-((m ν : ℝ)^k)) +
          (ε / 2) * Real.exp (-((m ν : ℝ)^v)) := by
        rw [act_unitary_norm (evolution_isCircuit (l ν).tail).mem_unitary]
        exact add_le_add he₁ he₂
      _ ≤ (ε / 2) * Real.exp (-((m ν : ℝ)^k)) +
          (ε / 2) * Real.exp (-((m ν : ℝ)^k)) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hpow))
        positivity
      _ = _ := by ring

theorem low_degree_propagation
    (hpauli : PublishedPauliExpansion) (hspec : PublishedProductSpectralResolution)
    (d : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (l : ∀ ν, List (AnalyticLayer (m ν))) (hl : ∀ ν, (l ν).length ≤ d)
    (ψ : ∀ ν, State (m ν)) (hψ : ∀ ν, ‖ψ ν‖ ≤ 1)
    (hreg : RegularTrajectory m l ψ)
    {k K : ℝ} (hk : 0 < k) (hkK : k < K) (hK : K < 1) :
    ∀ᶠ ν in atTop, ∀ E : Operator (m ν),
      HasDegreeLE E ((m ν : ℝ)^k) → ‖E‖ ≤ Real.exp ((m ν : ℝ)^k) →
      ∃ E' : Operator (m ν), HasDegreeLE E' ((m ν : ℝ)^K) ∧
        ‖E'‖ ≤ Real.exp ((m ν : ℝ)^K) ∧
        ‖act (evolution (l ν)) (act E (ψ ν)) -
          act E' (act (evolution (l ν)) (ψ ν))‖ ≤ Real.exp (-((m ν : ℝ)^k)) := by
  simpa only [one_mul, TransportOn] using
    low_degree_propagation_with_prefactor hpauli hspec d m hm l hl ψ hψ hreg hk hkK hK
      (ε := 1) zero_lt_one

end QAC

end

end OAI
