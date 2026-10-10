import OAI.MathematicalPhysics.Heisenberg.ExponentialEvolution

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators

namespace Heisenberg

def finiteGenerator (d ℓ : ℕ) (Λ : Finset (Site d)) : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ :=
  SpinEvolution.generator (hamiltonian d ℓ Λ)

def commutatorTerm (d ℓ : ℕ) (e : Site d × Site d) (A : QuasiLocal d ℓ) : QuasiLocal d ℓ :=
  (-Complex.I) • (bond d ℓ e.1 e.2 * A - A * bond d ℓ e.1 e.2)

lemma norm_commutatorTerm_le (d ℓ : ℕ) (e : Site d × Site d) (A : QuasiLocal d ℓ) :
    ‖commutatorTerm d ℓ e A‖ ≤ 2*bondBound d ℓ*‖A‖ := by
  calc
    _ = ‖bond d ℓ e.1 e.2 * A - A*bond d ℓ e.1 e.2‖ := by
      simp [commutatorTerm, norm_smul]
    _ ≤ ‖bond d ℓ e.1 e.2*A‖+‖A*bond d ℓ e.1 e.2‖ := norm_sub_le _ _
    _ ≤ ‖bond d ℓ e.1 e.2‖*‖A‖+‖A‖*‖bond d ℓ e.1 e.2‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ bondBound d ℓ*‖A‖+‖A‖*bondBound d ℓ :=
      add_le_add (mul_le_mul_of_nonneg_right (norm_bond_le _ _ _ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_bond_le _ _ _ _) (norm_nonneg _))
    _ = _ := by ring

lemma finiteGenerator_eq_sum (d ℓ : ℕ) (Λ : Finset (Site d)) (A : QuasiLocal d ℓ) :
    finiteGenerator d ℓ Λ A = ∑ e ∈ volumeEdges Λ, commutatorTerm d ℓ e A := by
  simp only [finiteGenerator, SpinEvolution.generator_apply, hamiltonian,
    commutatorTerm, bond, neg_mul, mul_neg, Finset.sum_mul, Finset.mul_sum,
    smul_sub, smul_neg, Finset.smul_sum, Finset.sum_sub_distrib, neg_smul, Finset.sum_neg_distrib]

lemma commutatorTerm_mem {d ℓ : ℕ} {F : Finset (Site d)} (e : Site d × Site d)
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    commutatorTerm d ℓ e A ∈ localAlgebra d ℓ (↑(F ∪ {e.1,e.2}) : Set (Site d)) := by
  let G : Set (Site d) := ↑(F ∪ {e.1,e.2})
  have hAg : A ∈ localAlgebra d ℓ G :=
    localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hA
  have hb : bond d ℓ e.1 e.2 ∈ localAlgebra d ℓ G := bond_mem_local (by simp [G]) (by simp [G])
  exact (localAlgebra d ℓ G).smul_mem ((localAlgebra d ℓ G).sub_mem
    ((localAlgebra d ℓ G).mul_mem hb hAg) ((localAlgebra d ℓ G).mul_mem hAg hb)) _

lemma commutatorTerm_eq_zero {d ℓ : ℕ} {F : Finset (Site d)} {e : Site d × Site d}
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d)))
    (h1 : e.1 ∉ F) (h2 : e.2 ∉ F) : commutatorTerm d ℓ e A = 0 := by
  have hd : Disjoint ({e.1,e.2} : Set (Site d)) (F : Set (Site d)) := by
    simp only [Set.disjoint_left, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_coe]
    rintro x (rfl | rfl) hx <;> contradiction
  have hb : bond d ℓ e.1 e.2 ∈ localAlgebra d ℓ ({e.1,e.2} : Set (Site d)) :=
    bond_mem_local (by simp) (by simp)
  have hc := localAlgebras_commute hd hb hA
  simp only [commutatorTerm, hc.eq, sub_self, smul_zero]

def activeEdges {d : ℕ} (Λ F : Finset (Site d)) : Finset (Site d × Site d) :=
  (volumeEdges Λ).filter fun e => e.1 ∈ F ∨ e.2 ∈ F

lemma activeEdges_subset_incident {d : ℕ} (Λ F : Finset (Site d)) :
    activeEdges Λ F ⊆ incidentEdges F := by
  intro e he
  obtain ⟨hv, hm⟩ := Finset.mem_filter.mp he
  exact mem_incidentEdges (Finset.mem_filter.mp hv).2.1 hm

lemma finiteGenerator_eq_activeSum {d ℓ : ℕ} (Λ F : Finset (Site d))
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    finiteGenerator d ℓ Λ A = ∑ e ∈ activeEdges Λ F, commutatorTerm d ℓ e A := by
  rw [finiteGenerator_eq_sum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hv
  have he' : ¬ (e.1 ∈ F ∨ e.2 ∈ F) := by
    intro hm; exact hv (Finset.mem_filter.mpr ⟨he, hm⟩)
  exact commutatorTerm_eq_zero hA (not_or.mp he').1 (not_or.mp he').2

lemma card_union_edge_le {d : ℕ} (F : Finset (Site d)) {e : Site d × Site d}
    (he : e.1 ∈ F ∨ e.2 ∈ F) : (F ∪ {e.1,e.2}).card ≤ F.card+1 := by
  rcases he with h1 | h2
  · have hh : F ∪ {e.1,e.2} = insert e.2 F := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hh]; exact Finset.card_insert_le _ _
  · have hh : F ∪ {e.1,e.2} = insert e.1 F := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    rw [hh]; exact Finset.card_insert_le _ _

def SupportedOnAtMost (d ℓ k : ℕ) (A : QuasiLocal d ℓ) : Prop :=
  ∃ F : Finset (Site d), F.card ≤ k+1 ∧ A ∈ localAlgebra d ℓ (F : Set (Site d))

lemma finiteGenerator_localDecomposition (d ℓ : ℕ) (Λ : Finset (Site d)) :
    SpinEvolution.LocalDecomposition (finiteGenerator d ℓ Λ) (SupportedOnAtMost d ℓ)
      (8*d*bondBound d ℓ) := by
  constructor
  · exact mul_nonneg (by positivity) (bondBound_nonneg _ _)
  · intro k A hA
    obtain ⟨F, hk, hA⟩ := hA
    let I := activeEdges Λ F
    let e : I ≃ Fin I.card := (Fintype.equivFin I).trans (finCongr (Fintype.card_coe I))
    let g : Fin I.card → QuasiLocal d ℓ := fun j => commutatorTerm d ℓ (e.symm j) A
    have hg : ∑ j, g j = ∑ x ∈ I, commutatorTerm d ℓ x A := by
      calc
        ∑ j, g j = ∑ x : I, commutatorTerm d ℓ x A :=
          Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
        _ = _ := Finset.sum_coe_sort I (fun x => commutatorTerm d ℓ x A)
    refine ⟨I.card, g, ?_, ?_, ?_⟩
    · rw [hg]; exact finiteGenerator_eq_activeSum Λ F hA
    · intro j
      refine ⟨F ∪ {(e.symm j).val.1,(e.symm j).val.2}, ?_, commutatorTerm_mem _ hA⟩
      exact (card_union_edge_le F (Finset.mem_filter.mp (e.symm j).property).2).trans (by omega)
    · have hcard : I.card ≤ (4*d)*(k+1) :=
        ((Finset.card_le_card (activeEdges_subset_incident Λ F)).trans
          (card_incidentEdges_le F)).trans (Nat.mul_le_mul_left _ hk)
      calc
        ∑ j, ‖g j‖ ≤ ∑ _ : Fin I.card, 2*bondBound d ℓ*‖A‖ :=
          Finset.sum_le_sum (fun j _ => norm_commutatorTerm_le _ _ _ _)
        _ = (I.card : ℝ)*(2*bondBound d ℓ*‖A‖) := by simp
        _ ≤ ((4*d)*(k+1) : ℝ)*(2*bondBound d ℓ*‖A‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hcard
          · exact mul_nonneg (mul_nonneg (by norm_num) (bondBound_nonneg _ _)) (norm_nonneg _)
        _ = (8*d*bondBound d ℓ)*(k+1)*‖A‖ := by ring



lemma activeEdges_stable {d : ℕ} (Λ F : Finset (Site d))
    (hΛ : neighborhood F ⊆ Λ) : activeEdges Λ F = activeEdges (neighborhood F) F := by
  ext e
  simp only [activeEdges, volumeEdges, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hmem,hnn,hord⟩,hm⟩
    exact ⟨⟨nearestNeighbor_mem_neighborhood hnn hm,hnn,hord⟩,hm⟩
  · rintro ⟨⟨hmem,hnn,hord⟩,hm⟩
    exact ⟨⟨⟨hΛ hmem.1,hΛ hmem.2⟩,hnn,hord⟩,hm⟩

lemma finiteGenerator_stable {d ℓ : ℕ} (Λ F : Finset (Site d))
    (hΛ : neighborhood F ⊆ Λ) {A : QuasiLocal d ℓ}
    (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    finiteGenerator d ℓ Λ A = finiteGenerator d ℓ (neighborhood F) A := by
  rw [finiteGenerator_eq_activeSum Λ F hA,
    finiteGenerator_eq_activeSum (neighborhood F) F hA, activeEdges_stable Λ F hΛ]

lemma finiteGenerator_local {d ℓ : ℕ} (Λ F : Finset (Site d))
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) :
    finiteGenerator d ℓ Λ A ∈ localAlgebra d ℓ (↑(F ∪ Λ) : Set (Site d)) := by
  rw [finiteGenerator_eq_activeSum Λ F hA]
  apply Subalgebra.sum_mem
  intro e he
  have hv : e.1 ∈ Λ ∧ e.2 ∈ Λ :=
    Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
  apply localAlgebra_mono (F := (↑(F ∪ {e.1,e.2}) : Set (Site d))) ?_ (commutatorTerm_mem e hA)
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with hF | rfl | rfl
  · exact Or.inl hF
  · exact Or.inr hv.1
  · exact Or.inr hv.2

theorem eventually_mem_box {d : ℕ} (x : Site d) :
    ∀ᶠ n : ℕ in Filter.atTop, x ∈ box d n := by
  have hl (i : Fin d) : ∀ᶠ n : ℕ in Filter.atTop, (x i).natAbs ≤ n :=
    Filter.eventually_ge_atTop _
  have hh := (Filter.eventually_all).mpr hl
  filter_upwards [hh] with n hn
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h := hn i
  have hcast : ((x i).natAbs : ℤ) ≤ n := by exact_mod_cast h
  exact abs_le.mp (by simpa only [Int.natCast_natAbs] using hcast)

lemma eventually_subset_box {d : ℕ} (F : Finset (Site d)) :
    ∀ᶠ n : ℕ in Filter.atTop, F ⊆ box d n := by
  have h : ∀ x : F, ∀ᶠ n : ℕ in Filter.atTop, (x : Site d) ∈ box d n :=
    fun x => eventually_mem_box (x : Site d)
  filter_upwards [Filter.eventually_all.mpr h] with n hn
  intro x hx
  exact hn ⟨x,hx⟩

theorem local_coefficients_stabilize {d ℓ : ℕ} (F : Finset (Site d))
    {A : QuasiLocal d ℓ} (hA : A ∈ localAlgebra d ℓ (F : Set (Site d))) (n : ℕ) :
    ∃ B : QuasiLocal d ℓ, ∀ᶠ m : ℕ in Filter.atTop,
      ((finiteGenerator d ℓ (box d m))^n) A = B := by
  let : Monoid (QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) := inferInstance
  have hh : ∀ n : ℕ, ∃ (G : Finset (Site d)) (B : QuasiLocal d ℓ),
      B ∈ localAlgebra d ℓ (G : Set (Site d)) ∧
      ∀ᶠ m : ℕ in Filter.atTop, ((finiteGenerator d ℓ (box d m))^n) A = B := by
    intro n
    induction n with
    | zero => exact ⟨F,A,hA,by simp⟩
    | succ n ih =>
      obtain ⟨G,B,hB,hlim⟩ := ih
      refine ⟨G ∪ neighborhood G,finiteGenerator d ℓ (neighborhood G) B,
        finiteGenerator_local _ G hB,?_⟩
      filter_upwards [hlim,eventually_subset_box (neighborhood G)] with m hm hmG
      rw [pow_succ', mul_apply_eq_comp, hm]
      exact finiteGenerator_stable _ G hmG hB
  obtain ⟨G,B,hB,hlim⟩ := hh n
  exact ⟨B,hlim⟩

def localCore (d ℓ : ℕ) : StarSubalgebra ℂ (QuasiLocal d ℓ) :=
  StarAlgebra.adjoin ℂ {A | ∃ x a b, A = localUnit d ℓ x a b}

theorem localCore_dense (d ℓ : ℕ) : Dense (localCore d ℓ : Set (QuasiLocal d ℓ)) := by
  let B := StarAlgebra.adjoin ℂ {A : SpinOperator d ℓ | ∃ x a b, A = matrixUnit d ℓ x a b}
  let f : B →⋆ₐ[ℂ] QuasiLocal d ℓ := StarSubalgebra.inclusion B.le_topologicalClosure
  have hd : DenseRange f := by
    change DenseRange (Set.inclusion B.le_topologicalClosure)
    apply (denseRange_inclusion_iff B.le_topologicalClosure).mpr
    rw [StarSubalgebra.topologicalClosure_coe]
  have hle : B ≤ (localCore d ℓ).map (quasiLocalAlgebra d ℓ).subtype := by
    apply StarAlgebra.adjoin_le
    rintro A ⟨x,a,b,rfl⟩
    exact ⟨localUnit d ℓ x a b, StarAlgebra.subset_adjoin ℂ _ ⟨x,a,b,rfl⟩, rfl⟩
  apply Dense.mono (s₁ := Set.range f) ?_ hd
  rintro A ⟨a,rfl⟩
  obtain ⟨b,hb,he⟩ := hle a.property
  have heq : f a = b := Subtype.ext he.symm
  rwa [heq]

lemma localCore_finite_support {d ℓ : ℕ} {A : QuasiLocal d ℓ}
    (hA : A ∈ localCore d ℓ) : ∃ F : Finset (Site d), A ∈ localAlgebra d ℓ (F : Set (Site d)) := by
  induction hA using StarAlgebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨x,a,b,rfl⟩ := ha
    exact ⟨{x},localUnit_mem_localAlgebra _ _ _ (by simp) _ _⟩
  | algebraMap z => exact ⟨∅, by simpa only [Finset.coe_empty] using
      (localAlgebra d ℓ ∅).algebraMap_mem z⟩
  | add a b ha hb iha ihb =>
    obtain ⟨F,hF⟩ := iha
    obtain ⟨G,hG⟩ := ihb
    refine ⟨F ∪ G,(localAlgebra d ℓ (↑(F ∪ G) : Set (Site d))).add_mem ?_ ?_⟩
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hF
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_right _ hx) hG
  | mul a b ha hb iha ihb =>
    obtain ⟨F,hF⟩ := iha
    obtain ⟨G,hG⟩ := ihb
    refine ⟨F ∪ G,(localAlgebra d ℓ (↑(F ∪ G) : Set (Site d))).mul_mem ?_ ?_⟩
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_left _ hx) hF
    · exact localAlgebra_mono (by intro x hx; exact Finset.mem_union_right _ hx) hG
  | star a ha iha =>
    obtain ⟨F,hF⟩ := iha
    exact ⟨F,star_mem hF⟩

end Heisenberg

namespace SpinEvolution
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]

omit [CompleteSpace E] in
lemma smul_operator_pow_apply (D : E →L[ℂ] E) (z : ℂ) (n : ℕ) (A : E) :
    ((z • D)^n) A = z^n • (D^n) A := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp, smul_apply, ih, map_smul, smul_smul]
    rw [mul_comm]

lemma exponential_operator_series (D : E →L[ℂ] E) (z : ℂ) (A : E) :
    NormedSpace.exp (z • D) A =
      ∑' n : ℕ, ((n.factorial : ℂ)⁻¹ * z^n) • (D^n) A := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  change (ContinuousLinearMap.apply ℂ E A) (∑' n : ℕ,
    (n.factorial : ℂ)⁻¹ • (z • D)^n) = _
  rw [(ContinuousLinearMap.apply ℂ E A).map_tsum
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) (z • D))]
  apply tsum_congr
  intro n
  simp only [ContinuousLinearMap.apply_apply, smul_apply, smul_operator_pow_apply, smul_smul]

theorem local_exponential_converges (D : ℕ → E →L[ℂ] E) (Local : ℕ → E → Prop)
    (C : ℝ) (hD : ∀ m, LocalDecomposition (D m) Local C)
    (k : ℕ) (A : E) (hA : Local k A) (z : ℂ) (hz : ‖z‖*C < 1)
    (hstable : ∀ n : ℕ, ∃ B : E, ∀ᶠ m : ℕ in Filter.atTop, ((D m)^n) A = B) :
    ∃ B : E, Filter.Tendsto (fun m => NormedSpace.exp (z • D m) A)
      Filter.atTop (nhds B) := by
  choose B hB using hstable
  have hc : 0 ≤ C := (hD 0).nonneg
  let q : ℝ := ‖z‖*C
  have hq : 0 ≤ q := mul_nonneg (norm_nonneg _) hc
  let b : ℕ → ℝ := fun n => q^n * ((k+1).ascFactorial n : ℝ) / n.factorial * ‖A‖
  have hb : Summable b := (summable_ascFactorial hq hz k).mul_right ‖A‖
  have hterm (m n : ℕ) : ‖((n.factorial : ℂ)⁻¹ * z^n) • ((D m)^n) A‖ ≤ b n := by
    calc
      _ = ((n.factorial : ℝ)⁻¹ * ‖z‖^n) * ‖((D m)^n) A‖ := by
        simp only [norm_smul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      _ ≤ ((n.factorial : ℝ)⁻¹ * ‖z‖^n) *
          (C^n * ((k+1).ascFactorial n : ℝ) * ‖A‖) :=
        mul_le_mul_of_nonneg_left ((hD m).power_bound n k A hA) (by positivity)
      _ = b n := by dsimp [b, q]; rw [mul_pow]; ring
  refine ⟨∑' n : ℕ, ((n.factorial : ℂ)⁻¹*z^n) • B n, ?_⟩
  simp_rw [exponential_operator_series]
  apply tendsto_tsum_of_dominated_convergence hb
  · intro n
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hB n] with m hm
    exact congrArg (fun X => ((n.factorial : ℂ)⁻¹*z^n) • X) hm.symm
  · exact Filter.Eventually.of_forall hterm

end SpinEvolution
end

end OAI
