import OAI.Analysis.LipschitzEquivalence.CompactLocalization

namespace OAI

universe uE uM uIndex

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.WeakSequences
open Filter Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E] in
theorem exists_large_subsequence (u : ℕ → E) (hu : ¬ Tendsto u atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ i, ε ≤ ‖u (s i)‖ := by
  rw [Metric.tendsto_atTop] at hu
  push Not at hu
  obtain ⟨ε,hε,hlarge⟩ := hu
  simp only [dist_zero_right] at hlarge
  have hstep (p : ℕ) : ∃ n : ℕ, p < n ∧ ε ≤ ‖u n‖ := by
    obtain ⟨n,hn,hun⟩ := hlarge (p+1)
    exact ⟨n,lt_of_lt_of_le (Nat.lt_succ_self p) hn,hun⟩
  let next (p : ℕ) : ℕ := Classical.choose (hstep p)
  let seq : ℕ → ℕ := fun j => Nat.rec 0 (fun _ p => next p) j
  have hseq (j : ℕ) : seq j < seq (j+1) ∧ ε ≤ ‖u (seq (j+1))‖ :=
    Classical.choose_spec (hstep (seq j))
  have hm : StrictMono seq := strictMono_nat_of_lt_succ (fun j => (hseq j).1)
  exact ⟨ε,hε,(fun i => seq (i+1)),(fun _ _ h => hm (Nat.add_lt_add_right h 1)),fun i => (hseq i).2⟩

def unitNormalize (u : ℕ → E) (i : ℕ) : E := ‖u i‖⁻¹ • u i

theorem norm_unitNormalize (u : ℕ → E) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ i, ε ≤ ‖u i‖) (i : ℕ) : ‖unitNormalize u i‖ = 1 := by
  have hn : ‖u i‖ ≠ 0 := ne_of_gt (hε.trans_le (hu i))
  simp [unitNormalize,norm_smul,hn]

theorem WeakNull.unitNormalize {u : ℕ → E} (hw : WeakNull u) {ε : ℝ} (hε : 0 < ε)
    (hu : ∀ i, ε ≤ ‖u i‖) : WeakNull (unitNormalize u) := by
  intro f
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hw f) (δ*ε) (mul_pos hδ hε)
  refine ⟨N,fun i hi => ?_⟩
  have hn : 0 < ‖u i‖ := hε.trans_le (hu i)
  have hfi := hN i hi
  simp only [dist_zero_right,Real.norm_eq_abs] at hfi ⊢
  change |f (‖u i‖⁻¹ • u i)| < δ
  rw [map_smul,smul_eq_mul,abs_mul,abs_inv,abs_norm]
  rw [← div_eq_inv_mul]
  apply (div_lt_iff₀ hn).mpr
  exact hfi.trans_le (mul_le_mul_of_nonneg_left (hu i) hδ.le)
end LipschitzCounterexample.WeakSequences

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz CoordinateSpaces LocalGeometry
open scoped NNReal InnerProductSpace
variable {M : Type uM} [MetricSpace M] [Zero M]
variable {ι : ℕ → Type uIndex} [∀ n, Fintype (ι n)]

omit [Zero M] in
theorem scalar_test_lipschitz (D : M → Hilbert (ι := ι)) {L : ℝ≥0}
    (hD : LipschitzWith L D) (b : Hilbert (ι := ι)) (hb : ‖b‖ ≤ 1) :
    LipschitzWith L (fun x => ⟪D x,b⟫_ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans (by simpa only [mul_one,← dist_eq_norm] using hD.dist_le_mul x y))

theorem scalar_test_pairing (D : M → Hilbert (ι := ι)) {L : ℝ≥0}
    (hD : LipschitzWith L D) (hD0 : D 0 = 0) (b : Hilbert (ι := ι)) (hb : ‖b‖ ≤ 1)
    (μ : FreeSpace.Space M) :
    test (normalized (fun x => ⟪D x,b⟫_ℝ) (scalar_test_lipschitz D hD b hb)) μ =
      ⟪FreeSpace.linearize D μ,b⟫_ℝ := by
  let d : M → ℝ := fun x => ⟪D x,b⟫_ℝ
  have hd : LipschitzWith L d := scalar_test_lipschitz D hD b hb
  have hd0 : d 0 = 0 := by simp [d,hD0]
  have h₁ : FreeSpace.linearize d = test (normalized d hd) :=
    FreeSpace.linearize_unique d hd hd0 _ (by
      intro x
      change d x-d 0 = d x
      rw [hd0,sub_zero])
  have h₂ : FreeSpace.linearize d = (innerSL ℝ b).comp (FreeSpace.linearize D) :=
    FreeSpace.linearize_unique d hd hd0 _ (by
      intro x
      rw [ContinuousLinearMap.comp_apply,FreeSpace.linearize_point D hD hD0]
      exact (real_inner_comm b (D x)).symm)
  have he := congrArg (fun T : FreeSpace.Space M →L[ℝ] ℝ => T μ) (h₁.symm.trans h₂)
  change test (normalized d hd) μ = ⟪FreeSpace.linearize D μ,b⟫_ℝ
  rw [he]
  exact (real_inner_comm b (FreeSpace.linearize D μ)).symm

theorem completely_continuous_of_compact_reduction [SecondCountableTopology M]
    (hcompact : FreeSpace.HasCompactReduction (M := M))
    (D : M → Hilbert (ι := ι)) {L : ℝ≥0} (hD : LipschitzWith L D) (hD0 : D 0 = 0)
    (hloc : LocalOrthogonality D) : WeakSequences.CompletelyContinuous (FreeSpace.linearize D) := by
  classical
  intro μ hw
  by_contra hn
  obtain ⟨ε,hε,s,hs,hlarge⟩ := WeakSequences.exists_large_subsequence
    (fun i => FreeSpace.linearize D (μ i)) hn
  let μ' : ℕ → FreeSpace.Space M := fun i => μ (s i)
  have hw' : WeakSequences.WeakNull μ' := hw.subseq hs
  let b := WeakSequences.unitNormalize (fun i => FreeSpace.linearize D (μ' i))
  have hwq : WeakSequences.WeakNull (fun i => FreeSpace.linearize D (μ' i)) := hw'.map _
  have hbn (i : ℕ) : ‖b i‖ = 1 := WeakSequences.norm_unitNormalize _ hε hlarge i
  have hbw : WeakSequences.WeakNull b := hwq.unitNormalize hε hlarge
  let d : ℕ → M → ℝ := fun i x => ⟪D x,b i⟫_ℝ
  have hd (i : ℕ) : LipschitzWith L (d i) := scalar_test_lipschitz D hD (b i) (hbn i).le
  have hpoint (x : M) : Tendsto (fun i => d i x) atTop (𝓝 0) := hbw (innerSL ℝ (D x))
  have hpair (i : ℕ) : test (normalized (d i) (hd i)) (μ' i) = ‖FreeSpace.linearize D (μ' i)‖ := by
    rw [scalar_test_pairing D hD hD0 (b i) (hbn i).le]
    change ⟪FreeSpace.linearize D (μ' i),‖FreeSpace.linearize D (μ' i)‖⁻¹ • FreeSpace.linearize D (μ' i)⟫_ℝ = _
    rw [inner_smul_right,real_inner_self_eq_norm_sq]
    have hn' : ‖FreeSpace.linearize D (μ' i)‖ ≠ 0 := ne_of_gt (hε.trans_le (hlarge i))
    field_simp
  by_cases hL : L = 0
  · have hdzero (i : ℕ) : d i = 0 := by
      funext x
      have ht := (hd i).dist_le_mul x 0
      simp only [hL,NNReal.coe_zero,zero_mul,dist_le_zero] at ht
      simpa [d,hD0] using ht
    have htest : test (normalized (d 0) (hd 0)) (μ' 0) = 0 := by
      change (μ' 0).1 _ = 0
      have ht : normalized (d 0) (hd 0) = 0 := by
        apply Subtype.ext
        funext x
        change d 0 x-d 0 0 = 0
        rw [hdzero]
        simp
      rw [ht,map_zero]
    rw [hpair] at htest
    linarith [hlarge 0]
  have hLpos : 0 < L := lt_of_le_of_ne (by positivity) (Ne.symm hL)
  obtain ⟨B,hBc,hBne,hB⟩ := TopologicalSpace.exists_countable_basis M
  let O : B → Set M := Subtype.val
  let : Countable B := hBc.to_subtype
  obtain ⟨a,t,ht,ha,halim⟩ := subsequence_constants O d hd
  have hbase : ∀ z : M, ∀ r : ℝ, 0 < r → ∃ j, z ∈ O j ∧ O j ⊆ Metric.ball z r := by
    intro z r hr
    obtain ⟨P,hPB,hzP,hPball⟩ := hB.exists_subset_of_mem_open (Metric.mem_ball_self hr) Metric.isOpen_ball
    exact ⟨⟨P,hPB⟩,hzP,hPball⟩
  have hbad (η : ℝ≥0) (hη : 0 < η) : (badSet O a (η : ℝ)).Finite :=
    badSet_finite D hLpos hD hloc (fun i => b (t i)) (fun i => (hbn _).le)
      (fun a => (hbw (coord a)).comp ht.tendsto_atTop) O hbase a halim hη
  have hgood : ∀ η : ℝ≥0, 0 < η → ∃ Z : Set M, Z.Finite ∧
      ∀ p, p ∉ Z → ∃ P : Set M, IsOpen P ∧ p ∈ P ∧
        ∀ᶠ i in atTop, LipschitzOnWith η (d (t i)) P := by
    intro η hη
    refine ⟨badSet O a (η : ℝ),hbad η hη,?_⟩
    intro p hp
    change ¬ (∀ j, p ∈ O j → (η : ℝ) ≤ a j) at hp
    push Not at hp
    obtain ⟨j,hpj,haj⟩ := hp
    refine ⟨O j,hB.isOpen j.property,hpj,?_⟩
    have he := (halim j).eventually (eventually_lt_nhds haj)
    filter_upwards [he] with i hi
    exact (lipschitzOn_constant (hd (t i)).lipschitzOnWith).weaken hi.le
  have hvanish := scalar_localization hcompact (hw'.subseq ht) (fun i => d (t i))
    (fun i => hd (t i)) (fun x => (hpoint x).comp ht.tendsto_atTop) hgood
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hvanish ε hε
  have hcontra := hN N le_rfl
  rw [dist_zero_right,Real.norm_eq_abs,hpair,abs_of_nonneg (norm_nonneg _)] at hcontra
  exact (not_lt_of_ge (hlarge (t N))) hcontra
end LipschitzCounterexample.LocalizedLinearization

end

end OAI
