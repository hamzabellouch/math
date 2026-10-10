import Mathlib

namespace OAI

/-! Indexed bond graphs, connectivity, percolation laws, kernels and countability. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

abbrev BondGraph (V : Type u) (E : Type v) := E → Sym2 V

 
def Adj (G : BondGraph V E) (x y : V) : Prop := ∃ e, G e = s(x, y)

 
def LocallyFinite (G : BondGraph V E) : Prop := ∀ x, {e | x ∈ G e}.Finite

 
def Connected (G : BondGraph V E) : Prop :=
  ∀ x y, Relation.ReflTransGen (Adj G) x y

 
def IsAut (G : BondGraph V E) (a : V ≃ V) (b : E ≃ E) : Prop :=
  ∀ e, G (b e) = (G e).map a

 
def QuasiTransitive (G : BondGraph V E) : Prop :=
  ∃ representatives : Finset V, ∀ x, ∃ o ∈ representatives,
    ∃ a : V ≃ V, ∃ b : E ≃ E, IsAut G a b ∧ a o = x

 
def vertexBoundary (G : BondGraph V E) (A : Finset V) : Set V :=
  {y | y ∉ A ∧ ∃ x ∈ A, Adj G x y}

 
noncomputable def hV (G : BondGraph V E) : ℝ :=
  sInf {r | ∃ A : Finset V, A.Nonempty ∧
    r = (vertexBoundary G A).ncard / (A.card : ℝ)}

 
def Conn (G : BondGraph V E) (ω : Set E) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ∃ e ∈ ω, G e = s(a, b)) x y

def cluster (G : BondGraph V E) (ω : Set E) (x : V) : Set V :=
  {y | Conn G ω x y}

 
def infiniteClusters (G : BondGraph V E) (ω : Set E) : Set (Set V) :=
  {C | C.Infinite ∧ ∃ x, C = cluster G ω x}

 
noncomputable def law (p : unitInterval) : Measure (Set E) :=
  setBernoulli Set.univ p

noncomputable def pc (G : BondGraph V E) : unitInterval :=
  sInf {p | 0 < law p {ω | (infiniteClusters G ω).Nonempty}}

noncomputable def pu (G : BondGraph V E) : unitInterval :=
  sInf {p | law p {ω | ∃! C, C ∈ infiniteClusters G ω} = 1}

noncomputable def twoPoint (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  (law p {ω | Conn G ω x y}).toReal

noncomputable abbrev Hilbert (V : Type u) := lp (fun _ : V => ℂ) 2

 
noncomputable def HasKernel [DecidableEq V]
    (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = (twoPoint G p x y : ℂ)

noncomputable def OperatorBounded (G : BondGraph V E) (p : unitInterval) : Prop := by
  classical
  exact ∃ A : Hilbert V →L[ℂ] Hilbert V, HasKernel G p A

 
noncomputable def operatorNorm (G : BondGraph V E) (p : unitInterval) : ℝ≥0∞ := by
  classical
  exact sInf {r | ∃ A : Hilbert V →L[ℂ] Hilbert V,
    HasKernel G p A ∧ r = ENNReal.ofReal ‖A‖}

noncomputable def ptwo (G : BondGraph V E) : unitInterval :=
  sSup {p | OperatorBounded G p}

 
noncomputable def labelLaw : Measure (E → unitInterval) :=
  Measure.infinitePi (fun _ => (volume : Measure unitInterval))

def openEdges (labels : E → unitInterval) (p : unitInterval) : Set E :=
  {e | labels e ≤ p}

 
def MainConclusion (G : BondGraph V E) : Prop :=
  (sSup {r | ∃ p : unitInterval, p < pc G ∧ r = operatorNorm G p} =
    operatorNorm G (pc G)) ∧
  operatorNorm G (pc G) < ⊤ ∧
  pc G < ptwo G ∧ ptwo G ≤ pu G ∧
  ∃ p₁ p₂ : unitInterval, pc G < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
    ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters G (openEdges labels p)).Infinite

 

section Deterministic
variable (G : BondGraph V E) (ω : Set E)

@[simp] theorem conn_refl (x : V) : Conn G ω x x :=
  Relation.ReflTransGen.refl

theorem conn_trans {x y z : V} (hxy : Conn G ω x y) (hyz : Conn G ω y z) :
    Conn G ω x z := hxy.trans hyz

theorem conn_symm {x y : V} (h : Conn G ω x y) : Conn G ω y x := by
  induction h with
  | refl => exact conn_refl G ω _
  | @tail y z _ hyz ih =>
    rcases hyz with ⟨e, he, hlink⟩
    exact (Relation.ReflTransGen.single ⟨e, he, hlink.trans (Sym2.eq_swap ..)⟩).trans ih

theorem conn_mono {ω₁ ω₂ : Set E} (hω : ω₁ ⊆ ω₂) {x y : V}
    (h : Conn G ω₁ x y) : Conn G ω₂ x y := by
  apply Relation.ReflTransGen.mono (r := fun a b => ∃ e ∈ ω₁, G e = s(a, b)) ?_ x y h
  rintro a b ⟨e, he, hab⟩
  exact ⟨e, hω he, hab⟩

theorem cluster_eq_of_conn {x y : V} (h : Conn G ω x y) :
    cluster G ω x = cluster G ω y := by
  ext z
  exact ⟨fun hxz => conn_trans G ω (conn_symm G ω h) hxz,
    fun hyz => conn_trans G ω h hyz⟩

@[simp] theorem mem_cluster_self (x : V) : x ∈ cluster G ω x := conn_refl G ω x

theorem clusters_eq_or_disjoint (x y : V) :
    cluster G ω x = cluster G ω y ∨ Disjoint (cluster G ω x) (cluster G ω y) := by
  by_cases h : Conn G ω x y
  · exact Or.inl (cluster_eq_of_conn G ω h)
  · right
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    exact h (conn_trans G ω hxz (conn_symm G ω hyz))

@[simp] theorem conn_empty_iff (x y : V) : Conn G ∅ x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ he _ => rcases he with ⟨e, he, _⟩; exact he.elim
  · rintro rfl
    exact conn_refl G ∅ _

@[simp] theorem cluster_empty (x : V) : cluster G ∅ x = {x} := by
  ext y
  simp [cluster, eq_comm]

@[simp] theorem infiniteClusters_empty : infiniteClusters G ∅ = ∅ := by
  ext C
  simp only [infiniteClusters, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
    not_and, not_exists]
  intro h x hx
  subst C
  simp at h

theorem conn_univ_of_connected (h : Connected G) (x y : V) : Conn G Set.univ x y := by
  apply Relation.ReflTransGen.mono (r := Adj G) ?_ x y (h x y)
  rintro a b ⟨e, he⟩
  exact ⟨e, Set.mem_univ _, he⟩

theorem cluster_univ_of_connected (h : Connected G) (x : V) :
    cluster G Set.univ x = Set.univ := by
  ext y
  simp only [cluster, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact conn_univ_of_connected G h x y

theorem infiniteClusters_univ [Infinite V] (h : Connected G) :
    infiniteClusters G Set.univ = {Set.univ} := by
  ext C
  constructor
  · rintro ⟨_, x, rfl⟩
    simp [cluster_univ_of_connected G h]
  · intro hC
    have hC' : C = Set.univ := Set.mem_singleton_iff.mp hC
    subst C
    exact ⟨Set.infinite_univ, Classical.arbitrary V,
      (cluster_univ_of_connected G h _).symm⟩

end Deterministic

section Probability
variable (G : BondGraph V E)

instance law_isProbabilityMeasure (p : unitInterval) :
    IsProbabilityMeasure (law p : Measure (Set E)) := by
  dsimp [law]
  infer_instance

@[simp] theorem law_zero : (law 0 : Measure (Set E)) = Measure.dirac ∅ := by
  simp [law]

@[simp] theorem law_one : (law 1 : Measure (Set E)) = Measure.dirac Set.univ := by
  simp [law]

@[simp] theorem twoPoint_self (p : unitInterval) (x : V) : twoPoint G p x x = 1 := by
  simp [twoPoint]

theorem twoPoint_nonneg (p : unitInterval) (x y : V) : 0 ≤ twoPoint G p x y :=
  ENNReal.toReal_nonneg

theorem twoPoint_le_one (p : unitInterval) (x y : V) : twoPoint G p x y ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using
    (prob_le_one (μ := law p) (s := {ω | Conn G ω x y})))

theorem twoPoint_symm (p : unitInterval) (x y : V) : twoPoint G p x y = twoPoint G p y x := by
  have he : {ω | Conn G ω x y} = {ω | Conn G ω y x} := by
    ext ω
    exact ⟨conn_symm G ω, conn_symm G ω⟩
  simp only [twoPoint, he]

@[simp] theorem twoPoint_zero [Countable E] [DecidableEq V] (x y : V) :
    twoPoint G 0 x y = if x = y then 1 else 0 := by
  rw [twoPoint, law_zero, Measure.dirac_apply]
  by_cases h : x = y
  · simp [h]
  · rw [Set.indicator_of_notMem (by simpa using h)]
    simp [h]

theorem twoPoint_one (h : Connected G) (x y : V) : twoPoint G 1 x y = 1 := by
  have hv : law (E := E) 1 {ω | Conn G ω x y} = 1 := by
    rw [law_one]
    exact Measure.dirac_apply_of_mem (conn_univ_of_connected G h x y)
  change (law 1 {ω | Conn G ω x y}).toReal = 1
  rw [hv]
  norm_num

end Probability

section Kernel
attribute [local instance] Classical.propDecidable

 
theorem kernel_extension_unique {K : V → V → ℂ}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : ∀ x y, (A (lp.single 2 y (1 : ℂ))) x = K x y)
    (hB : ∀ x y, (B (lp.single 2 y (1 : ℂ))) x = K x y) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro y
  apply ContinuousLinearMap.ext
  intro z
  apply lp.ext
  funext x
  have hz : lp.single (E := fun _ : V => ℂ) 2 y z =
      z • lp.single (E := fun _ : V => ℂ) 2 y (1 : ℂ) := by
    simpa using (lp.single_smul (E := fun _ : V => ℂ) 2 y z (1 : ℂ))
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    lp.singleContinuousLinearMap_apply, hz, map_smul, lp.coeFn_smul, Pi.smul_apply,
    hA, hB]

theorem HasKernel.unique {G : BondGraph V E} {p : unitInterval}
    {A B : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) (hB : HasKernel G p B) :
    A = B := kernel_extension_unique hA hB

 
theorem operatorNorm_of_hasKernel {G : BondGraph V E} {p : unitInterval}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : HasKernel G p A) :
    operatorNorm G p = ENNReal.ofReal ‖A‖ := by
  have he : {r | ∃ B : Hilbert V →L[ℂ] Hilbert V,
      HasKernel G p B ∧ r = ENNReal.ofReal ‖B‖} = {ENNReal.ofReal ‖A‖} := by
    ext r
    constructor
    · rintro ⟨B, hB, rfl⟩
      rw [hB.unique hA]
      exact Set.mem_singleton _
    · intro hr
      exact ⟨A, hA, Set.mem_singleton_iff.mp hr⟩
  change sInf _ = _
  rw [he, sInf_singleton]

theorem operatorNorm_eq_top_iff (G : BondGraph V E) (p : unitInterval) :
    operatorNorm G p = ⊤ ↔ ¬ OperatorBounded G p := by
  constructor
  · intro h ⟨A, hA⟩
    rw [operatorNorm_of_hasKernel hA] at h
    exact ENNReal.ofReal_ne_top h
  · intro h
    unfold operatorNorm
    have he : {r | ∃ A : Hilbert V →L[ℂ] Hilbert V,
        HasKernel G p A ∧ r = ENNReal.ofReal ‖A‖} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨A, hA, _⟩
      exact h ⟨A, hA⟩
    rw [he, sInf_empty]

theorem operatorNorm_lt_top_iff (G : BondGraph V E) (p : unitInterval) :
    operatorNorm G p < ⊤ ↔ OperatorBounded G p := by
  rw [lt_top_iff_ne_top, ne_eq, operatorNorm_eq_top_iff, not_not]

theorem hasKernel_zero [Countable E] (G : BondGraph V E) :
    HasKernel G 0 (ContinuousLinearMap.id ℂ (Hilbert V)) := by
  intro x y
  simp only [ContinuousLinearMap.id_apply, lp.single_apply, twoPoint_zero]
  by_cases h : x = y
  · subst y
    simp
  · simp [h]

@[simp] theorem operatorBounded_zero [Countable E] (G : BondGraph V E) :
    OperatorBounded G 0 := ⟨_, hasKernel_zero G⟩

end Kernel

section Countability

 
theorem finite_neighbors {G : BondGraph V E} (hG : LocallyFinite G) (x : V) :
    {y | Adj G x y}.Finite := by
  classical
  have hends (e : E) : {y | y ∈ G e}.Finite := by
    apply (G e).toFinset.finite_toSet.subset
    intro y hy
    exact Sym2.mem_toFinset.mpr hy
  have hs : (⋃ e ∈ {e | x ∈ G e}, {y | y ∈ G e}).Finite :=
    (hG x).biUnion (fun e _ => hends e)
  apply hs.subset
  rintro y ⟨e, he⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨e, he ▸ by simp, he ▸ by simp⟩

 
def reachBall (G : BondGraph V E) (x : V) : ℕ → Set V
  | 0 => {x}
  | n + 1 => reachBall G x n ∪ ⋃ y ∈ reachBall G x n, {z | Adj G y z}

theorem finite_reachBall {G : BondGraph V E} (hG : LocallyFinite G) (x : V) :
    ∀ n, (reachBall G x n).Finite := by
  intro n
  induction n with
  | zero => exact Set.finite_singleton x
  | succ n hn =>
    exact hn.union (hn.biUnion (fun y _ => finite_neighbors hG y))

theorem exists_mem_reachBall {G : BondGraph V E} {x y : V}
    (h : Relation.ReflTransGen (Adj G) x y) : ∃ n, y ∈ reachBall G x n := by
  induction h with
  | refl => exact ⟨0, Set.mem_singleton _⟩
  | @tail y z _ hyz ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, Or.inr ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨y, hn, hyz⟩

theorem countable_vertices [Nonempty V] {G : BondGraph V E}
    (hG : LocallyFinite G) (hconn : Connected G) : Countable V := by
  let x : V := Classical.arbitrary V
  have he : (Set.univ : Set V) = ⋃ n, reachBall G x n := by
    ext y
    simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
    exact exists_mem_reachBall (hconn x y)
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun n => (finite_reachBall hG x n).countable)

theorem countable_edges [Countable V] {G : BondGraph V E}
    (hG : LocallyFinite G) : Countable E := by
  have he : (Set.univ : Set E) = ⋃ x, {e | x ∈ G e} := by
    ext e
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨(G e).out.1, Sym2.out_fst_mem _⟩
  apply Set.countable_univ_iff.mp
  rw [he]
  exact Set.countable_iUnion (fun x => (hG x).countable)

end Countability

end Percolation

end OAI
