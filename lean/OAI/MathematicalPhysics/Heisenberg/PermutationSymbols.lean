import OAI.MathematicalPhysics.Heisenberg.PinSymmetrization

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

namespace Heisenberg.Pin

variable {V : Type*} [Fintype V] [DecidableEq V]

def permutationSymbol (π : Equiv.Perm V) : MvPolynomial (V ⊕ V) ℂ :=
  ∏ i, (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (π i)))

omit [DecidableEq V] in
lemma stable_permutationSymbol (π : Equiv.Perm V) : Stable (permutationSymbol π) := by
  intro z hz
  simp only [permutationSymbol, MvPolynomial.eval_prod, map_add, MvPolynomial.eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hzero
  have hpos := add_pos (hz (Sum.inl i)) (hz (Sum.inr (π i)))
  rw [← Complex.add_im, hzero, Complex.zero_im] at hpos
  exact (lt_irrefl 0) hpos

lemma multiAffine_permutationSymbol (π : Equiv.Perm V) :
    MultiAffine (permutationSymbol π) := by
  intro j
  apply (MvPolynomial.degreeOf_prod_le j Finset.univ _).trans
  apply (Finset.sum_le_sum fun i _ => MvPolynomial.degreeOf_add_le j _ _).trans
  cases j with
  | inl j => simp [MvPolynomial.degreeOf_X]
  | inr j =>
    simp only [MvPolynomial.degreeOf_X, reduceCtorEq, ite_false, zero_le, max_eq_right,
      Sum.inr.injEq]
    simp [← π.symm_apply_eq, eq_comm]

omit [DecidableEq V] in
lemma permutationSymbol_eval_one (π : Equiv.Perm V) :
    MvPolynomial.eval (fun _ => 1) (permutationSymbol π) = 2 ^ Fintype.card V := by
  norm_num [permutationSymbol]

lemma Stable.rename {σ τ : Type*} {p : MvPolynomial σ ℂ}
    (hp : Stable p) (f : σ → τ) : Stable (MvPolynomial.rename f p) := by
  intro z hz
  rw [MvPolynomial.eval_rename]
  exact hp (z ∘ f) (fun i => hz (f i))

omit [DecidableEq V] in
lemma rename_permutationSymbol (π τ : Equiv.Perm V) :
    MvPolynomial.rename (Sum.map id τ) (permutationSymbol π) =
      permutationSymbol (τ * π) := by
  simp [permutationSymbol, map_prod, map_add,
    MvPolynomial.rename_X, Equiv.Perm.mul_apply]

omit [Fintype V] [DecidableEq V] in

lemma stable_rename_outputs {p : MvPolynomial (V ⊕ V) ℂ} (hp : Stable p)
    (τ : Equiv.Perm V) : Stable (MvPolynomial.rename (Sum.map id τ) p) :=
  hp.rename (Sum.map id τ)

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

def lawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) : MvPolynomial (V ⊕ V) ℂ :=
  ∑ ω, MvPolynomial.C (μ ω : ℂ) * permutationSymbol (π ω)

lemma multiAffine_lawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V) :
    MultiAffine (lawSymbol μ π) := by
  intro i
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
  apply Finset.sup_le
  intro ω _
  exact ((multiAffine_permutationSymbol (π ω)).const_mul (μ ω)) i

omit [DecidableEq V] in
lemma lawSymbol_eval_one (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω = 1) :
    MvPolynomial.eval (fun _ => 1) (lawSymbol μ π) = 2 ^ Fintype.card V := by
  simp only [lawSymbol, map_sum, map_mul, MvPolynomial.eval_C, permutationSymbol_eval_one]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hμ, Complex.ofReal_one, one_mul]

omit [DecidableEq V] in
lemma lawSymbol_ne_zero (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω = 1) : lawSymbol μ π ≠ 0 := by
  intro hzero
  have he := lawSymbol_eval_one μ π hμ
  rw [hzero, map_zero] at he
  exact (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)) he.symm

omit [Fintype V] in
lemma swap_output_map (i j : V) :
    Sum.map (id : V → V) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  funext k
  cases k with
  | inl k => simp [Equiv.swap_apply_def]
  | inr k =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [Equiv.swap_apply_def, hki, hkj]

lemma lawSymbol_bernoulli (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (i j : V) (u : ℝ) :
    lawSymbol (fun z : Bool × Ω => (if z.1 then u else 1 - u) * μ z.2)
      (fun z : Bool × Ω => (if z.1 then Equiv.swap i j else 1) * π z.2) =
      symmetrize (lawSymbol μ π) (Sum.inr i) (Sum.inr j) u := by
  simp only [lawSymbol, Fintype.sum_prod_type, Fintype.sum_bool, ite_true,
    Bool.false_eq_true, ite_false, one_mul]
  unfold symmetrize
  rw [map_sum, Finset.mul_sum, Finset.mul_sum]
  simp only [map_mul, MvPolynomial.rename_C]
  rw [add_comm]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro ω _
    push_cast
    rw [map_mul, mul_assoc]
  · apply Finset.sum_congr rfl
    intro ω _
    rw [← swap_output_map, rename_permutationSymbol]
    push_cast
    rw [map_mul, mul_assoc]

theorem stable_lawSymbol_bernoulli (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hs : Stable (lawSymbol μ π)) (i j : V) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Stable (lawSymbol (fun z : Bool × Ω => (if z.1 then u else 1 - u) * μ z.2)
      (fun z : Bool × Ω => (if z.1 then Equiv.swap i j else 1) * π z.2)) := by
  rw [lawSymbol_bernoulli]
  exact stable_symmetrize hs (multiAffine_lawSymbol μ π) _ _ h0 h1

omit [DecidableEq V] in
lemma lawSymbol_deterministic_output (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (τ : Equiv.Perm V) :
    lawSymbol μ (fun ω => τ * π ω) = MvPolynomial.rename (Sum.map id τ) (lawSymbol μ π) := by
  simp only [lawSymbol, map_sum, map_mul, MvPolynomial.rename_C, rename_permutationSymbol]

omit [DecidableEq V] in

theorem stable_lawSymbol_limit {ι : Type*} {φ : Filter ι} [φ.NeBot]
    (μ : ι → Ω → ℝ) (ν : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hc : ∀ ω, Filter.Tendsto (fun i => μ i ω) φ (nhds (ν ω)))
    (hν : ∑ ω, ν ω = 1) (hs : ∀ᶠ i in φ, Stable (lawSymbol (μ i) π)) :
    Stable (lawSymbol ν π) := by
  apply stable_locallyUniform_limit (lawSymbol_ne_zero ν π hν) _ hs
  simp only [lawSymbol, map_sum, map_mul, MvPolynomial.eval_C]
  apply locallyUniform_finset_sum
  intro ω _
  apply TendstoLocallyUniformlyOn.mul₀
  · exact ((Complex.continuous_ofReal.tendsto (ν ω)).comp (hc ω)).tendstoUniformlyOn_const
      Upper |>.tendstoLocallyUniformlyOn
  · exact locallyUniform_const φ _ Upper
  · exact continuousOn_const
  · exact (permutationSymbol (π ω)).continuous_eval.continuousOn

end Heisenberg.Pin

namespace Heisenberg.Pin
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

def partialSymbol (π : V → V) (U : Finset V) : MvPolynomial (V ⊕ V) ℂ :=
  ∏ i ∈ U, (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (π i)))

omit [Fintype V] in
lemma partialSymbol_insert (π : V → V) (i : V) (U : Finset V) (hi : i ∉ U) :
    partialSymbol π (insert i U) =
      (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr (π i))) * partialSymbol π U := by
  simp [partialSymbol, hi]

omit [Fintype V] in
lemma pderiv_partialSymbol (π : V → V) (i : V) (U : Finset V) :
    MvPolynomial.pderiv (Sum.inl i) (partialSymbol π U) =
      if i ∈ U then partialSymbol π (U.erase i) else 0 := by
  induction U using Finset.induction_on with
  | empty => simp [partialSymbol]
  | @insert j U hj ih =>
    rw [partialSymbol_insert π j U hj, MvPolynomial.pderiv_mul, ih]
    by_cases hij : i = j
    · subst j
      simp [hj]
    · simp only [map_add, MvPolynomial.pderiv_X_of_ne (by simpa using Ne.symm hij : (Sum.inl j : V ⊕ V) ≠ Sum.inl i),
        MvPolynomial.pderiv_X_of_ne (by simp : Sum.inr (π j) ≠ Sum.inl i),
        zero_add, zero_mul, Finset.mem_insert, hij, false_or]
      by_cases hi : i ∈ U
      · rw [ite_eq_left hi, ite_eq_left hi, Finset.erase_insert_of_ne (Ne.symm hij)]
        rw [partialSymbol_insert π j (U.erase i) (fun h => hj (Finset.mem_of_mem_erase h))]
      · simp [hi]

def partialLawSymbol (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V) :
    MvPolynomial (V ⊕ V) ℂ := ∑ ω, MvPolynomial.C (μ ω : ℂ) * partialSymbol (π ω) U

omit [Fintype V] [DecidableEq V] in
lemma partialLawSymbol_eval_one (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V) :
    MvPolynomial.eval (fun _ => 1) (partialLawSymbol μ π U) =
      ((∑ ω, μ ω : ℝ) : ℂ) * 2 ^ U.card := by
  simp only [partialLawSymbol, partialSymbol, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, map_add, MvPolynomial.eval_X, one_add_one_eq_two,
    Finset.prod_const]
  rw [← Finset.sum_mul, Complex.ofReal_sum]

omit [Fintype V] [DecidableEq V] in
lemma partialLawSymbol_ne_zero (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V)
    (hμ : ∑ ω, μ ω ≠ 0) : partialLawSymbol μ π U ≠ 0 := by
  intro hz
  have he := partialLawSymbol_eval_one μ π U
  rw [hz, map_zero] at he
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ) (pow_ne_zero _ (by norm_num)) he.symm

omit [Fintype V] in
lemma pderiv_partialLawSymbol (μ : Ω → ℝ) (π : Ω → V → V) (U : Finset V)
    (i : V) (hi : i ∈ U) :
    MvPolynomial.pderiv (Sum.inl i) (partialLawSymbol μ π U) =
      partialLawSymbol μ π (U.erase i) := by
  simp only [partialLawSymbol, map_sum, MvPolynomial.pderiv_C_mul,
    pderiv_partialSymbol, hi, ite_true]

theorem stable_partialLawSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω ≠ 0) (hs : Stable (lawSymbol μ π)) (U : Finset V) :
    Stable (partialLawSymbol μ (fun ω => π ω) U) := by
  have hall (B : Finset V) : Stable (partialLawSymbol μ (fun ω => π ω) (Finset.univ \ B)) := by
    induction B using Finset.induction_on with
    | empty => simpa [partialLawSymbol, partialSymbol, lawSymbol, permutationSymbol] using hs
    | @insert i B hi ih =>
      have hm : i ∈ Finset.univ \ B := by simp [hi]
      have he : (Finset.univ \ B).erase i = Finset.univ \ insert i B := by ext j; simp
      have hd := stable_pderiv ih (Sum.inl i)
      rw [pderiv_partialLawSymbol μ (fun ω => π ω) _ i hm, he] at hd
      exact hd.resolve_left (partialLawSymbol_ne_zero μ _ _ hμ)
  simpa using hall (Finset.univ \ U)

def outputSymbol (μ : Ω → ℝ) (π : Ω → V → V) (T : Finset V) : MvPolynomial V ℂ :=
  ∑ ω, MvPolynomial.C (μ ω : ℂ) * ∏ i ∈ T, MvPolynomial.X (π ω i)

omit [Fintype V] [DecidableEq V] in
lemma output_extraction (μ : Ω → ℝ) (π : Ω → V → V) (T : Finset V) :
    boundarySection (partialLawSymbol μ π T)
      (Sum.elim (fun _ => none) (fun i => some i)) (fun _ => 0) = outputSymbol μ π T := by
  simp [boundarySection, partialLawSymbol, partialSymbol, outputSymbol]

omit [Fintype V] [DecidableEq V] in
lemma outputSymbol_eval_one (μ : Ω → ℝ) (π : Ω → V → V) (T : Finset V) :
    MvPolynomial.eval (fun _ => 1) (outputSymbol μ π T) = ((∑ ω, μ ω : ℝ) : ℂ) := by
  simp [outputSymbol]

theorem stable_outputSymbol (μ : Ω → ℝ) (π : Ω → Equiv.Perm V)
    (hμ : ∑ ω, μ ω ≠ 0) (hs : Stable (lawSymbol μ π)) (T : Finset V) :
    Stable (outputSymbol μ (fun ω => π ω) T) := by
  have hn : outputSymbol μ (fun ω => π ω) T ≠ 0 := by
    intro hz
    have he := outputSymbol_eval_one μ (fun ω => π ω) T
    rw [hz, map_zero] at he
    exact (Complex.ofReal_ne_zero.mpr hμ) he.symm
  rw [← output_extraction] at hn ⊢
  exact stable_boundarySection (stable_partialLawSymbol μ π hμ hs T)
    _ (fun _ => 0) hn

end Heisenberg.Pin
end
end

end OAI
