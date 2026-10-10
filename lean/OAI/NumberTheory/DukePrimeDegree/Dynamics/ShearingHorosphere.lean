import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCompactness

namespace OAI

/-!
# The horospherical shape of a normalized shearing limit

The limiting matrix differs from the identity only in the chosen row
and column, with unchanged diagonal. Its displacement is nilpotent of
order at most three. This is the precise horospherical direction used
in EKL (2006), Section 4.2, equations (4.6)--(4.8).
-/

noncomputable section
open Set Filter Matrix
open scoped BigOperators Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def RootHorosphereShape {n : ℕ} (i j : Fin n) (h : G n) : Prop :=
  ∀ r s, (r ≠ i ∧ s ≠ j) ∨ r = s → h.val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s

lemma root_conjugation_pivot_trace {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).val i i +
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).val j j = g.val i i + g.val j j := by
  rw [root_conjugation_entry, root_conjugation_entry]
  simp only [hij, hij.symm, ite_true, ite_false, false_and,
    and_false, sub_zero, add_zero]
  ring

/-- The off-root entries remain unchanged, and centrality forces the two
pivot diagonal limits to equal one. -/
theorem rootShearLimit_horospherical {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) (t : ℕ → ℝ)
    (h : G n)
    (hlim : Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
      Matrix.SpecialLinearGroup.transvection hij (-t m)) atTop (𝓝 h))
    (hcentral : h * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * h) : RootHorosphereShape i j h := by
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.val r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).val r s) atTop
      (𝓝 ((1 : G n).val r s)) := (hcont r s).tendsto 1 |>.comp hg
  have hhentry (r s : Fin n) : Tendsto (fun m =>
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).val r s)
      atTop (𝓝 (h.val r s)) := (hcont r s).tendsto h |>.comp hlim
  have hoff (r s : Fin n) (hr : r ≠ i) (hs : s ≠ j) :
      h.val r s = (1 : Matrix (Fin n) (Fin n) ℝ) r s := by
    have he : (fun m => (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)).val r s) =
        (fun m => (g m).val r s) := by
      funext m
      simp [root_conjugation_entry, hr, hs]
    exact tendsto_nhds_unique (he ▸ hhentry r s) (hgentry r s)
  have htrace : h.val i i + h.val j j = 2 := by
    have he : (fun m =>
        (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).val i i +
        (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
          Matrix.SpecialLinearGroup.transvection hij (-t m)).val j j) =
        (fun m => (g m).val i i + (g m).val j j) :=
      funext fun m => root_conjugation_pivot_trace hij (g m) (t m)
    have hgtrace : Tendsto (fun m => (g m).val i i + (g m).val j j) atTop (𝓝 (2 : ℝ)) := by
      simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq,
        show (1 + 1 : ℝ) = 2 by norm_num] using (hgentry i i).add (hgentry j j)
    exact tendsto_nhds_unique (he ▸ (hhentry i i).add (hhentry j j)) hgtrace
  have heq : h.val i i = h.val j j := ((commutes_root_one_iff hij h).mp hcentral).2.2
  intro r s hrs
  rcases hrs with hrs | rfl
  · exact hoff r s hrs.1 hrs.2
  · by_cases hri : r = i
    · subst r
      simp only [Matrix.one_apply_eq]
      linarith
    · by_cases hrj : r = j
      · subst r
        simp only [Matrix.one_apply_eq]
        linarith
      · exact hoff r r hri hrj

/-- The displacement of a root-horospherical matrix has cube zero. -/
theorem rootHorosphereShape_nilpotent {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : RootHorosphereShape i j g) :
    (g.val - 1) ^ 3 = 0 := by
  let M := g.val - 1
  have hoff (r s : Fin n) (hrs : (r ≠ i ∧ s ≠ j) ∨ r = s) : M r s = 0 := by
    change g.val r s - (1 : Matrix (Fin n) (Fin n) ℝ) r s = 0
    exact sub_eq_zero.mpr (hg r s hrs)
  have hrow (s : Fin n) : M j s = 0 := by
    by_cases hs : j = s
    · exact hoff j s (Or.inr hs)
    · exact hoff j s (Or.inl ⟨hij.symm, Ne.symm hs⟩)
  have hcol (r : Fin n) : M r i = 0 := by
    by_cases hr : r = i
    · exact hoff r i (Or.inr hr)
    · exact hoff r i (Or.inl ⟨hr, hij⟩)
  have hsq (r s : Fin n) (hs : s ≠ j) : (M * M) r s = 0 := by
    change ∑ k, M r k * M k s = 0
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · subst k
      rw [hcol, zero_mul]
    · rw [hoff k s (Or.inl ⟨hk, hs⟩), mul_zero]
  change M ^ 3 = 0
  rw [pow_succ, pow_two]
  ext r s
  change ∑ k, (M * M) r k * M k s = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = j
  · subst k
    rw [hrow, mul_zero]
  · rw [hsq r k hk, zero_mul]

/-- Normalized noncentral shearing produces a nonidentity unipotent
horospherical limit. -/
theorem exists_nontrivial_horospherical_rootShearLimit
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 < t m) (htop : Tendsto t atTop atTop)
    {a : ℝ} (ha : 0 < a)
    (hsize : ∀ m, rootShearSize hij (g m) (t m) = a)
    (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a) :
    ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧ (h.val - 1) ^ 3 = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
          Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) atTop (𝓝 h) := by
  obtain ⟨h, hne, φ, hφ, hlim, hcentral⟩ :=
    exists_nontrivial_rootShearLimit hij g hg t ht htop ha hsize hsmall
  have hshape := rootShearLimit_horospherical hij (g ∘ φ) (hg.comp hφ.tendsto_atTop)
    (t ∘ φ) h hlim (hcentral 1)
  exact ⟨h, hne, hshape, rootHorosphereShape_nilpotent hij h hshape, φ, hφ, hlim⟩

end DukePrimeDegree

end

end OAI
