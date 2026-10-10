import OAI.Probability.DilutedSpin.InsertionPoint
import OAI.Probability.DilutedSpin.TowerSum

namespace OAI

section
namespace DilutedSpinGlass
namespace KernelTower
variable {Ω Λ Ω' Λ' : Type} [Fintype Ω] [Fintype Λ] [Fintype Ω'] [Fintype Λ']

lemma Projects.refl (n : ℕ) (T : KernelTower Ω n) : Projects id n T T := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨fun _ => rfl,fun a => ih (T.2 a)⟩

lemma Projects.comp {π : Ω → Λ} {ρ : Λ → Ω'} (n : ℕ)
    {T : KernelTower Ω n} {U : KernelTower Λ n} {V : KernelTower Ω' n}
    (h : Projects π n T U) (g : Projects ρ n U V) : Projects (ρ ∘ π) n T V := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (h.2 a) (g.2 (π a))⟩
    intro f
    exact (h.1 (f ∘ ρ)).trans (g.1 f)

lemma Projects.prod {π : Ω → Ω'} {ρ : Λ → Λ'} (n : ℕ)
    {T : KernelTower Ω n} {T' : KernelTower Ω' n}
    {U : KernelTower Λ n} {U' : KernelTower Λ' n}
    (h : Projects π n T T') (g : Projects ρ n U U') :
    Projects (fun z : Ω×Λ => (π z.1,ρ z.2)) n (prod n T U) (prod n T' U') := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (h.2 a.1) (g.2 a.2)⟩
    intro f
    change (T.1.bind (fun _ => U.1)).expect (fun z => f (π z.1,ρ z.2)) =
      (T'.1.bind (fun _ => U'.1)).expect f
    rw [FiniteLaw.expect_bind,FiniteLaw.expect_bind]
    have he : (fun a => U.1.expect (fun b => f (π a,ρ b)))=
        (fun a => U'.1.expect (fun b => f (π a,b))) := by
      funext a
      exact g.1 (fun b => f (π a,b))
    rw [he]
    exact h.1 (fun a => U'.1.expect (fun b => f (a,b)))

lemma pi_prod_projects {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (T : ι → KernelTower Ω n) (U : ι → KernelTower Λ n) (c : ι) :
    Projects (fun z : ι → Ω×Λ => (fun i => (z i).1,(z c).2)) n
      (pi n (fun i => prod n (T i) (U i))) (prod n (pi n T) (U c)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (fun i => (T i).2 (a i).1) (fun i => (U i).2 (a i).2)⟩
    intro f
    change (FiniteLaw.pi (fun i => (T i).1.bind (fun _ => (U i).1))).expect
      (fun z => f (fun i => (z i).1,(z c).2)) =
      ((FiniteLaw.pi (fun i => (T i).1)).bind (fun _ => (U c).1)).expect f
    rw [FiniteLaw.expect_pi_bind]
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact FiniteLaw.expect_pi_marginal (fun i => (U i).1) c (fun b => f (a,b))

lemma Projects.pi {ι : Type} [Fintype ι] [DecidableEq ι]
    {π : ι → Ω → Λ} (n : ℕ) {T : ι → KernelTower Ω n} {U : ι → KernelTower Λ n}
    (h : ∀ i,Projects (π i) n (T i) (U i)) :
    Projects (fun x i => π i (x i)) n (pi n T) (pi n U) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨FiniteLaw.Projects.pi (fun i => (h i).1),fun a => ih (fun i => (h i).2 (a i))⟩

omit [Fintype Ω] [Fintype Λ] [Fintype Ω'] in
lemma pathMap_comp (π : Ω → Λ) (ρ : Λ → Ω') (n : ℕ) (y : FinitePath Ω n) :
    pathMap (ρ ∘ π) n y=pathMap ρ n (pathMap π n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

end KernelTower
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {Ω Λ R ι : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [Fintype ι] [DecidableEq ι] {n : ℕ}

lemma prod_pi_sample_expect (S : PrescribedTree n) (T : KernelTower Ω n)
    (U : ι → KernelTower Λ n) (g : (ι → Sample Λ S) → Sample Ω S → ℝ) :
    (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n U))).expect
      (fun w => g (fun j => sampleMap (fun x : ι → Λ => x j) S (sampleSnd S w))
        (sampleFst S w)) =
    (S.sampleLaw T).expect (fun old =>
      (FiniteLaw.pi (fun j => S.sampleLaw (U j))).expect (fun fresh => g fresh old)) := by
  rw [sampleExpect_prod]
  apply FiniteLaw.expect_congr
  intro old
  rw [sampleExpect_piTower]
  apply FiniteLaw.expect_congr
  intro a
  simp only [sampleFst_pair,sampleSnd_pair,sampleMap_pi]

/-- Each new label is independently sampled, including its root, on the same
prescribed replica tree as the old system. -/
lemma common_sample_expect (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (g : (ι → R×Sample Λ S) → Sample Ω S → ℝ) :
    (FiniteLaw.pi (fun _ : ι => Q)).expect (fun r =>
      (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : ι => U (r j))))).expect
        (fun w => g (fun j => (r j,sampleMap (fun x : ι → Λ => x j) S (sampleSnd S w)))
          (sampleFst S w))) =
    (S.sampleLaw T).expect (fun old =>
      (FiniteLaw.pi (fun _ : ι => Q.bind (fun r => S.sampleLaw (U r)))).expect
        (fun fresh => g fresh old)) := by
  let H (r : ι → R) (old : Sample Ω S) :=
    (FiniteLaw.pi (fun j : ι => S.sampleLaw (U (r j)))).expect
      (fun a => g (fun j => (r j,a j)) old)
  calc
    _ = (FiniteLaw.pi (fun _ : ι => Q)).expect (fun r => (S.sampleLaw T).expect (H r)) := by
      apply FiniteLaw.expect_congr
      intro r
      exact prod_pi_sample_expect S T (fun j => U (r j))
        (fun a old => g (fun j => (r j,a j)) old)
    _ = (S.sampleLaw T).expect (fun old => (FiniteLaw.pi (fun _ : ι => Q)).expect (fun r => H r old)) :=
      FiniteLaw.expect_comm _ _ _
    _ = _ := by
      apply FiniteLaw.expect_congr
      intro old
      exact (FiniteLaw.expect_pi_bind (fun _ : ι => Q) (fun _ r => S.sampleLaw (U r))
        (fun fresh => g fresh old)).symm

omit [Fintype Ω] in
lemma leafProduct_eq_fin_prod (S : PrescribedTree n) (D : FinitePath Ω n → ℝ)
    (w : Sample Ω S) :
    leafProduct S D w=∏ a : Fin (Fintype.card S.Leaf),D (S.pathAt ((Fintype.equivFin S.Leaf).symm a) w) := by
  rw [leafProduct_eq_prod]
  exact Fintype.prod_equiv (Fintype.equivFin S.Leaf) _ _ (fun a => by simp)

noncomputable def mixedTreeD {p N : ℕ} (z : InteractionSample p) (sel : Fin p → Bool)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (r : Fin p → R) (i : Fin p → Fin N) (w : FinitePath (Ω × (Fin p → Λ)) n) : ℝ :=
  mixedFactor z sel (fun l => V (KernelTower.pathFst n w) (i l))
    (fun l => x (r l) (KernelTower.pathMap (fun a : Fin p → Λ => a l) n (KernelTower.pathSnd n w)))

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma mixedTree_leafProduct {p N : ℕ} (S : PrescribedTree n)
    (z : InteractionSample p) (sel : Fin p → Bool)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (r : Fin p → R) (i : Fin p → Fin N) (w : Sample (Ω × (Fin p → Λ)) S) :
    leafProduct S (fun y => -mixedTreeD z sel V x r i y) w=
      ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
        (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (sampleFst S w)) (i l))
        (fun l => x (r l) (S.pathAt ((Fintype.equivFin S.Leaf).symm a)
          (sampleMap (fun a : Fin p → Λ => a l) S (sampleSnd S w)))) := by
  rw [leafProduct_eq_fin_prod]
  simp only [mixedTreeD,pathAt_sampleMap,pathAt_sampleFst,pathAt_sampleSnd]

lemma common_tree_sample {p N : ℕ} [NeZero N] (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) (i : Fin p → Fin N) :
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
      (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))).expect
        (leafProduct S (fun y => -mixedTreeD z sel V x r i y))) =
    (S.sampleLaw T).expect (fun old =>
      (FiniteLaw.pi (fun _ : Fin p => Q.bind (fun r => S.sampleLaw (U r)))).expect
        (fun fresh => ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
          (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) (i l))
          (fun l => x (fresh l).1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (fresh l).2)))) := by
  rw [← common_sample_expect]
  apply FiniteLaw.expect_congr
  intro r
  apply FiniteLaw.expect_congr
  intro w
  exact mixedTree_leafProduct S z sel V x r i w

lemma common_tree_point {p N : ℕ} [NeZero N] (S : PrescribedTree n) (T : KernelTower Ω n)
    (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (z : InteractionSample p) (sel : Fin p → Bool) :
    (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect (fun i =>
      (FiniteLaw.pi (fun _ : Fin p => Q)).expect (fun r =>
        (S.sampleLaw (KernelTower.prod n T (KernelTower.piTower n (fun j : Fin p => U (r j))))).expect
          (leafProduct S (fun y => -mixedTreeD z sel V x r i y)))) =
    (S.sampleLaw T).expect (fun old => insertionPoint z
      (fun i a => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) i)
      (Q.bind (fun r => S.sampleLaw (U r)))
      (fun w a => x w.1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) w.2)) sel) := by
  let F (i : Fin p → Fin N) (old : Sample Ω S) :=
    (FiniteLaw.pi (fun _ : Fin p => Q.bind (fun r => S.sampleLaw (U r)))).expect
      (fun fresh => ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
        (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) (i l))
        (fun l => x (fresh l).1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (fresh l).2)))
  calc
    _ = (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun i => (S.sampleLaw T).expect (F i)) := by
      apply FiniteLaw.expect_congr
      intro i
      exact common_tree_sample S T Q U V x z sel i
    _ = (S.sampleLaw T).expect (fun old =>
        (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
          (fun i => F i old)) := FiniteLaw.expect_comm _ _ _
    _ = _ := by
      apply FiniteLaw.expect_congr
      intro old
      exact (FiniteLaw.expect_pi_bind
        (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))
        (fun _ _ => Q.bind (fun r => S.sampleLaw (U r)))
        (fun w => ∏ a : Fin (Fintype.card S.Leaf),-mixedFactor z sel
          (fun l => V (S.pathAt ((Fintype.equivFin S.Leaf).symm a) old) (w l).1)
          (fun l => x (w l).2.1 (S.pathAt ((Fintype.equivFin S.Leaf).symm a) (w l).2.2)))).symm

end DilutedSpinGlass.PrescribedTree

end

end OAI
