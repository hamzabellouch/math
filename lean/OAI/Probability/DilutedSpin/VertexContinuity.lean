import OAI.Probability.DilutedSpin.ConcreteSelection
import OAI.Probability.DilutedSpin.DictionaryExtraction
import OAI.Probability.DilutedSpin.ScheduledGeometry

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot Filter Set
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

noncomputable def physicalBase (_model : Model p) (C H : ℝ) (N : ℕ)
    (h : RootPath ℝ N) (k : ℕ) (x : RootPath (Bond p N) k) (y : FinitePath (Fin N → Spin) (L+1)) : ℝ :=
  energy (boundedPotential C) (clipReal H) h k x (KernelTower.terminalState L y)

lemma measurable_physicalBase (M : Model p) (C H : ℝ) (N k : ℕ) (y : FinitePath (Fin N → Spin) (L+1)) :
    Measurable (fun z : RootPath ℝ N × RootPath (Bond p N) k => physicalBase M C H N z.1 k z.2 y) :=
  measurable_energy _ _ (fun σ => measurable_boundedPotential C σ) (measurable_clipReal H) k _

noncomputable def observableAt
    (D : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ) (N : ℕ) (q : K) (v : Site N)
    (x : FinitePath (Fin N → Spin) (L+1)) (y : FinitePath (A q) (L+1)) : ℝ :=
  D q (readSpin (KernelTower.terminalState L x) v) y

/-- The actual canceled-anchor covariance coefficient of one independent
site/mark insertion into the complete physical Poisson reservoir. -/
noncomputable def physicalCoefficient (S : PrescribedTree (L+1)) (anchor : S.Leaf)
    (M : Model p) (C H : ℝ) (N : ℕ) (u : K×ℕ → ℝ)
    (f : (S.Leaf → FinitePath (Fin N → Spin) (L+1)) → ℝ) (q : K) (k : ℕ) : ℝ :=
  covarianceCoefficient (fun _ : Fin N => M.field.toMeasure) (bondLaw M N) (markLaw ν N)
    ((siteLaw N).map (fun v => ((q,0),v))) (M.alpha*N) (scoreRate N) S anchor
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i => Q i.1.1) (Fin.cons 0 m) (physicalBase M C H N)
    (dictionaryFactor (observableAt D N) (observableAt E N) u)
    (siteObservable D N) (siteObservable E N) f k

lemma exponent_cons_monotone (hm : ∀ l, 0 ≤ m l) (hmono : Monotone m) : Monotone (Fin.cons 0 m) := by
  exact monotone_vecCons.mpr ⟨hm 0,hmono⟩

lemma exponent_cons_nonneg (hm : ∀ l, 0 ≤ m l) : ∀ l : Fin (L+2), 0 ≤ (Fin.cons 0 m : Fin (L+2) → ℝ) l := by
  intro l
  exact Fin.cases (by simp) (fun l => by simpa only [Fin.cons_succ] using hm l) l

/-- The concrete selected-score producer implies vanishing of every literal
coefficient at each bounded old test, on every finite prescribed tree. -/
theorem physical_coefficients_tendsto (S : PrescribedTree (L+1)) (anchor : S.Leaf)
    (M : Model p) (C H : ℝ) (Ns : ℕ → ℕ) (us : ℕ → K×ℕ → ℝ)
    (f : (n : ℕ) → (S.Leaf → FinitePath (Fin (Ns n+1) → Spin) (L+1)) → ℝ)
    (hm : ∀ l, 0 < m l) (hmono : Monotone m) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ n x, |f n x| ≤ B)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (hw : ∀ j, 0 < ν.real {j})
    (he : ∀ j, Tendsto (fun n => scoreError ν Q m D E M C H j (Ns n+1) (us n)) atTop (𝓝 0))
    (q : K) (k : ℕ) :
    Tendsto (fun n => physicalCoefficient ν Q m D E S anchor M C H (Ns n+1) (us n) (f n) q k)
      atTop (𝓝 0) := by
  have hm0 : ∀ l, 0 ≤ m l := fun l => (hm l).le
  have hh (l : Fin (L+1)) : (Fin.cons 0 m : Fin (L+2) → ℝ) l.succ ≠ 0 := by
    simpa only [Fin.cons_succ] using (hm l).ne'
  have hend' : (Fin.cons 0 m : Fin (L+2) → ℝ) (Fin.last (L+1)) = 1 := by
    change m (Fin.last L) = 1
    exact hend
  have hs (n : ℕ) : 0 < scoreRate (Ns n+1) := by
    change 0 < scoreScale (Ns n+1)
    exact Real.rpow_pos_of_pos (by positivity) _
  simp only [physicalCoefficient, Nat.cast_add, Nat.cast_one]
  apply dictionary_coefficients_tendsto
    (fun n (_ : Fin (Ns n+1)) => M.field.toMeasure) (fun n => bondLaw M (Ns n+1)) ν
    (fun n => siteLaw (Ns n+1)) (fun n => M.alpha*(Ns n+1)) (fun n => scoreRate (Ns n+1))
    S anchor (fun n => KernelTower.terminalTower (fun _ : Fin (Ns n+1) => false) FiniteLaw.uniform L)
    Q (Fin.cons 0 m) (fun n => physicalBase M C H (Ns n+1))
    (fun n => observableAt D (Ns n+1)) (fun n => observableAt E (Ns n+1)) us f
    (fun n => measurable_physicalBase M C H (Ns n+1)) hh
    (exponent_cons_monotone m hm0 hmono) (exponent_cons_nonneg m hm0) (by simp) hend'
    hB hf (fun n q v x y => hD _ _ _) (fun n q v x y => hE _ _ _) (fun q j => hw (q,j)) hs _ q k
  intro q j
  convert he (q,j) using 1
  simp only [scoreError,normalizedParameterError,Fin.cons_succ,
    scoreRate,markLaw,Nat.cast_add,Nat.cast_one]
  rfl

end DilutedSpinGlass.ConcreteReservoir
end

end

section
section
namespace DilutedSpinGlass
open scoped BigOperators
namespace PrescribedTree
variable {Ω : Type} [Fintype Ω]

lemma node_family_energy_le {h : ℕ} {ι : Type*} [Fintype ι]
    (k : ℕ+) (U V : ι → Fin k → PrescribedTree h) (a : Fin k)
    (he : ∀ t j, j ≠ a → U t j=V t j) (B : ℝ)
    (hB : ∀ (T : KernelTower Ω h) (f : FinitePath Ω h → ℝ), (∀ x, |f x| ≤ 1) →
      (∑ t, (treeMean (U t a) T f-treeMean (V t a) T f)^2) ≤ B)
    (T : KernelTower Ω (h+1)) (f : FinitePath Ω (h+1) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t, (treeMean (.node k (U t)) T f-treeMean (.node k (V t)) T f)^2) ≤ B := by
  calc
    _ ≤ ∑ t, T.1.expect (fun x =>
        (treeMean (U t a) (T.2 x) (fun y => f (x,y))-
          treeMean (V t a) (T.2 x) (fun y => f (x,y)))^2) :=
      Finset.sum_le_sum (fun t _ => treeMean_node_one_difference_sq k (U t) (V t) a (he t) T f hf)
    _ = T.1.expect (fun x => ∑ t,
        (treeMean (U t a) (T.2 x) (fun y => f (x,y))-
          treeMean (V t a) (T.2 x) (fun y => f (x,y)))^2) :=
      (FiniteLaw.expect_fintype_sum _ _).symm
    _ ≤ T.1.expect (fun _ => B) := T.1.expect_mono (fun x => hB (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
    _ = B := FiniteLaw.expect_const _ _

lemma unary_family_energy_le {h : ℕ} {ι : Type*} [Fintype ι]
    (U V : ι → PrescribedTree h) (B : ℝ)
    (hB : ∀ (T : KernelTower Ω h) (f : FinitePath Ω h → ℝ), (∀ x, |f x| ≤ 1) →
      (∑ t, (treeMean (U t) T f-treeMean (V t) T f)^2) ≤ B)
    (T : KernelTower Ω (h+1)) (f : FinitePath Ω (h+1) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t, (treeMean (unary (U t)) T f-treeMean (unary (V t)) T f)^2) ≤ B := by
  exact node_family_energy_le 1 (fun t _ => U t) (fun t _ => V t) 0
    (by intro t j hj; exact False.elim (hj (Fin.eq_zero j))) B hB T f hf

end PrescribedTree
/-- A canonical depth update, with no caller-dependent decidable-equality
instance. This is extensionally the ordinary function update. -/
noncomputable def updateCoordinate {α : Type} (q : α → ℕ) (v : α) (t : ℕ) : α → ℕ :=
  @Function.update α (fun _ => ℕ) (Classical.decEq α) q v t

@[simp] lemma updateCoordinate_self {α : Type} (v : α) (t : ℕ) (q : α → ℕ) :
    updateCoordinate q v t v=t := by
  exact @Function.update_self α (fun _ => ℕ) (Classical.decEq α) v t q

@[simp] lemma updateCoordinate_of_ne {α : Type} {a v : α} (h : a ≠ v) (t : ℕ) (q : α → ℕ) :
    updateCoordinate q v t a=q a := by
  exact @Function.update_of_ne α (fun _ => ℕ) (Classical.decEq α) a v h t q

namespace ReducedTopology
noncomputable local instance vertexContinuityDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition


def vertexArity : (S : ReducedTopology) → S.Vertex → ℕ+
  | .leaf, v => v.elim
  | .node k _ _, none => k
  | .node _ _ C, some v => vertexArity (C v.1) v.2

lemma update_root {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (t : ℕ) :
    updateCoordinate q none t = rootSchedule t (fun i v => q (some ⟨i,v⟩)) := by
  funext v
  cases v <;> simp [rootSchedule]

lemma update_desc_root {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (i : Fin k) (v : (C i).Vertex) (t : ℕ) :
    updateCoordinate q (some ⟨i,v⟩) t none = q none := by
  simp

lemma update_desc_same {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (i : Fin k) (v : (C i).Vertex) (t : ℕ) :
    (fun w => updateCoordinate q (some ⟨i,v⟩) t (some ⟨i,w⟩)) =
      updateCoordinate (fun w => q (some ⟨i,w⟩)) v t := by
  funext w
  by_cases hw : w=v
  · subst w; simp
  · have hn : (some ⟨i,w⟩ : (node k hk C).Vertex) ≠ some ⟨i,v⟩ := by
      intro hh
      have he := Option.some.inj hh
      exact hw (Sigma.mk.inj he).2.eq
    simp only [updateCoordinate_of_ne hw,updateCoordinate_of_ne hn]

lemma update_desc_other {k : ℕ+} {hk : 2 ≤ (k:ℕ)} {C : Fin k → ReducedTopology}
    (q : (node k hk C).Vertex → ℕ) (i : Fin k) (v : (C i).Vertex) (t : ℕ)
    (j : Fin k) (hj : j ≠ i) :
    (fun w => updateCoordinate q (some ⟨i,v⟩) t (some ⟨j,w⟩)) = (fun w => q (some ⟨j,w⟩)) := by
  funext w
  apply updateCoordinate_of_ne
  intro hh
  exact hj (congrArg Sigma.fst (Option.some.inj hh))

/-- Root-coordinate case at the lesser endpoint, extracted from admissible
schedules alone. The descendant-depth gap is a consequence, not an analytic
hypothesis or a presumed continuity conclusion. -/
lemma root_vertex_energy_le {Ω : Type} [Fintype Ω]
    (H d r : ℕ) (k : ℕ+) (hk : 2 ≤ (k:ℕ)) (C : Fin k → ReducedTopology)
    (q : (node k hk C).Vertex → ℕ)
    (ha : ∀ t : Fin (r+1), Admissible (node k hk C) (updateCoordinate q none (d+t.val)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t : Fin r,
      (PrescribedTree.treeMean (realize H d (node k hk C) (updateCoordinate q none (d+t.castSucc.val))) T f-
       PrescribedTree.treeMean (realize H d (node k hk C) (updateCoordinate q none (d+t.succ.val))) T f)^2) ≤ (k:ℝ)^2 := by
  have hr : r+1≤H := by
    have hh := (ha (Fin.last r)).2.1
    simp only [Fin.val_last] at hh
    simp only [updateCoordinate_self] at hh
    omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hr
  have hH : H=n+r+1 := by omega
  clear hn
  subst H
  have hQ : ∀ i v, d+r+1 ≤ q (some ⟨i,v⟩) := by
    intro i v
    have hh := (ha (Fin.last r)).2.2 i
    have hh' := admissible_lower (C i) _ hh v
    simpa [updateCoordinate] using hh'
  have he := scheduled_split_energy_le k hk C (fun i v => q (some ⟨i,v⟩)) n r d hQ T f hf
  convert he using 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [update_root (hk := hk),Fin.val_castSucc,Fin.val_succ,Nat.add_assoc]


/-- Squared one-grid-step changes at an arbitrary vertex of a scheduled
reduced topology. All other assigned depths are fixed; no ancestral context
or conditional-mean contraction is supplied as a hypothesis. -/
theorem scheduled_vertex_energy_le {Ω : Type} [Fintype Ω]
    (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    (lo r : ℕ)
    (ha : ∀ t : Fin (r+1), Admissible S (updateCoordinate q v (lo+t.val)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t : Fin r,
      (PrescribedTree.treeMean (realize H d S (updateCoordinate q v (lo+t.castSucc.val))) T f-
       PrescribedTree.treeMean (realize H d S (updateCoordinate q v (lo+t.succ.val))) T f)^2) ≤
      (vertexArity S v:ℝ)^2 := by
  induction H generalizing d S lo r with
  | zero =>
    have h := ha 0
    have hl := admissible_lower S _ h v
    have hu := admissible_upper S _ h v
    omega
  | succ H ih =>
    cases S with
    | leaf => exact v.elim
    | node k hk C =>
      cases v with
      | none =>
        have hd : d≤lo := by
          have h := (ha 0).1
          simpa using h
        by_cases he : d=lo
        · subst lo
          exact root_vertex_energy_le (H+1) d r k hk C q ha T f hf
        · have hlt : d<lo := by omega
          have hroot (t : Fin (r+1)) : d < updateCoordinate q none (lo+t.val) none := by
            simp only [updateCoordinate_self]
            omega
          have hu (t : Fin (r+1)) :
              realize (H+1) d (node k hk C) (updateCoordinate q none (lo+t.val)) =
              PrescribedTree.unary (realize H (d+1) (node k hk C) (updateCoordinate q none (lo+t.val))) := by
            rw [realize,ite_eq_left (hroot t)]
          simp_rw [hu]
          apply PrescribedTree.unary_family_energy_le _ _ _ ?_ T f hf
          intro T' f' hf'
          apply ih (d+1) (node k hk C) q none lo r ?_ T' f' hf'
          intro t
          exact ⟨hroot t,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (ha t).2⟩
      | some a =>
        obtain ⟨i,v⟩ := a
        have hd : d≤q none := by
          have h := (ha 0).1
          simpa only [update_desc_root (hk := hk)] using h
        by_cases he : d<q none
        · have hu (t : Fin (r+1)) :
              realize (H+1) d (node k hk C) (updateCoordinate q (some ⟨i,v⟩) (lo+t.val)) =
              PrescribedTree.unary (realize H (d+1) (node k hk C) (updateCoordinate q (some ⟨i,v⟩) (lo+t.val))) := by
            rw [realize,update_desc_root (hk := hk),ite_eq_left he]
          simp_rw [hu]
          apply PrescribedTree.unary_family_energy_le _ _ _ ?_ T f hf
          intro T' f' hf'
          apply ih (d+1) (node k hk C) q (some ⟨i,v⟩) lo r ?_ T' f' hf'
          intro t
          constructor
          · simpa only [update_desc_root (hk := hk)] using (Nat.succ_le_iff.mpr he)
          · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (ha t).2
        · have heq : q none=d := by omega
          have hu (t : Fin (r+1)) :
              realize (H+1) d (node k hk C) (updateCoordinate q (some ⟨i,v⟩) (lo+t.val)) =
              PrescribedTree.node k (fun j => realize H (d+1) (C j)
                (fun w => updateCoordinate q (some ⟨i,v⟩) (lo+t.val) (some ⟨j,w⟩))) := by
            rw [realize,update_desc_root (hk := hk),ite_eq_right he]
          simp_rw [hu]
          apply PrescribedTree.node_family_energy_le k _ _ i ?_ _ ?_ T f hf
          · intro t j hj
            rw [update_desc_other q i v _ j hj,update_desc_other q i v _ j hj]
          · intro T' f' hf'
            simp_rw [update_desc_same (hk := hk)]
            apply ih (d+1) (C i) (fun w => q (some ⟨i,w⟩)) v lo r ?_ T' f' hf'
            intro t
            have hh := (ha t).2.2 i
            simpa only [update_desc_root (hk := hk),update_desc_same (hk := hk),heq,Nat.add_assoc,
              Nat.add_comm,Nat.add_left_comm] using hh

end ReducedTopology
end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance realizeTranslationDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

lemma realize_translate (H d a : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) :
    realize H (d+a) S (fun v => q v+a)=realize H d S q := by
  induction H generalizing d S with
  | zero => rfl
  | succ H ih =>
    cases S with
    | leaf =>
      simp only [realize]
      rw [show d+a+1=(d+1)+a by omega, ih]
    | node k hk C =>
      simp only [realize, Nat.add_lt_add_iff_right]
      split_ifs with hd
      · rw [show d+a+1=(d+1)+a by omega,ih]
      · congr 1
        funext i
        rw [show d+a+1=(d+1)+a by omega,ih]

/-- Canonical unary delay is EXACTLY the assignment with every branching
vertex moved one later, not a surrogate shape. -/
theorem realize_delay (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d ≤ q v) :
    realize (H+1) d S (fun v => q v+1)=PrescribedTree.unary (realize H d S q) := by
  cases S with
  | leaf =>
    change PrescribedTree.unary (realize H (d+1) .leaf (fun v => q v+1)) = _
    rw [realize_translate H d 1]
  | node k hk C =>
    rw [realize,ite_eq_left (show d<q none+1 by have := hq none; omega),realize_translate H d 1]

/-- Bottom extension preserves all assigned internal depths, and supplies
precisely the old tree used opposite a delayed target in the matrix identity. -/
theorem realize_bottom (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : Admissible S q d (d+H)) :
    realize (H+1) d S q=PrescribedTree.bottomUnary (realize H d S q) := by
  induction H generalizing d S with
  | zero =>
    cases S with
    | leaf => rfl
    | node k hk C => have := hq.1; have := hq.2.1; omega
  | succ H ih =>
    cases S with
    | leaf =>
      simp only [realize,PrescribedTree.unary,PrescribedTree.bottomUnary]
      congr 1
      funext i
      exact ih (d+1) .leaf q trivial
    | node k hk C =>
      conv_lhs => rw [realize]
      conv_rhs => arg 1; rw [realize]
      split_ifs with hd
      · change PrescribedTree.node 1 _=PrescribedTree.node 1 _
        congr 1
        funext i
        apply ih
        exact ⟨hd,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2⟩
      · simp only [PrescribedTree.bottomUnary]
        congr 1
        funext i
        apply ih
        have he : q none=d := by have := hq.1; omega
        simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq.2.2 i

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
