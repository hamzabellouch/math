import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace ArnoldCounterexample.Nondegenerate

noncomputable section

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev model (n : ℕ) := 𝓘(ℝ, E n)

structure ClosedManifold (n : ℕ) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
  [compact : CompactSpace carrier]
  [connected : ConnectedSpace carrier]
  [charts : ChartedSpace (E n) carrier]
  [smooth : IsManifold (model n) ∞ carrier]

attribute [instance] ClosedManifold.topology ClosedManifold.hausdorff
  ClosedManifold.secondCountable ClosedManifold.compact ClosedManifold.connected
  ClosedManifold.charts ClosedManifold.smooth

instance {n : ℕ} : CoeSort (ClosedManifold n) Type := ⟨ClosedManifold.carrier⟩

abbrev TwoForm {n : ℕ} (M : ClosedManifold n) :=
  M → (E n) [⋀^Fin 2]→L[ℝ] ℝ

noncomputable def coordinateForm {n : ℕ} {M : ClosedManifold n}
    (omega : TwoForm M) (x : M) : E n → (E n) [⋀^Fin 2]→L[ℝ] ℝ :=
  fun z => (omega ((extChartAt (model n) x).symm z)).compContinuousLinearMap
    (mfderiv (model n) (model n) (extChartAt (model n) x).symm z)

structure SymplecticForm {n : ℕ} (M : ClosedManifold n) where
  form : TwoForm M
  smooth : ∀ x : M, ContDiffOn ℝ ∞ (coordinateForm form x)
    (extChartAt (model n) x).target
  closed : ∀ (x : M) (z : E n), z ∈ (extChartAt (model n) x).target →
    extDeriv (coordinateForm form x) z = 0
  nondegenerate : ∀ (x : M) (v : E n),
    (∀ w : E n, form x ![v, w] = 0) → v = 0

def criticalSet {n : ℕ} {M : ClosedManifold n} (f : M → ℝ) : Set M :=
  {x | mfderiv (model n) 𝓘(ℝ) f x = 0}

noncomputable def hessian {n : ℕ} {M : ClosedManifold n}
    (f : M → ℝ) (x : M) : E n →L[ℝ] E n →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (model n) x).symm))
    ((extChartAt (model n) x) x)

def IsMorse {n : ℕ} {M : ClosedManifold n} (f : M → ℝ) : Prop :=
  ContMDiff (model n) 𝓘(ℝ) ∞ f ∧
    ∀ x ∈ criticalSet f, Function.Injective (hessian f x)

noncomputable def morseNumber {n : ℕ} (M : ClosedManifold n) : ℕ :=
  sInf {k : ℕ | ∃ f : M → ℝ, IsMorse f ∧
    (criticalSet f).Finite ∧ (criticalSet f).ncard = k}

noncomputable def rationalHomology {n : ℕ} (M : ClosedManifold n) (i : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) i).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of M))

noncomputable def eulerChar {n : ℕ} (M : ClosedManifold n) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
    (Module.finrank ℚ (rationalHomology M i) : ℤ)

structure Hamiltonian {n : ℕ} {M : ClosedManifold n} (omega : SymplecticForm M) where
  H : ℝ × M → ℝ
  smooth_H : ContMDiff (𝓘(ℝ).prod (model n)) 𝓘(ℝ) ∞ H
  periodic_H : ∀ (t : ℝ) (x : M), H (t + 1, x) = H (t, x)
  flow : ℝ → M → M
  smooth_flow : ContMDiff (𝓘(ℝ).prod (model n)) (model n) ∞
    (fun p : ℝ × M => flow p.1 p.2)
  flow_zero : ∀ x : M, flow 0 x = x
  flow_ode : ∀ (t : ℝ) (x : M) (w : E n),
    omega.form (flow t x) ![mfderiv 𝓘(ℝ) (model n) (fun s => flow s x) t 1, w] =
      mfderiv (model n) 𝓘(ℝ) (fun y => H (t, y)) (flow t x) w

def fixedSet {n : ℕ} {M : ClosedManifold n} {omega : SymplecticForm M}
    (H : Hamiltonian omega) : Set M := {x | H.flow 1 x = x}

def IsNondegenerate {n : ℕ} {M : ClosedManifold n} {omega : SymplecticForm M}
    (H : Hamiltonian omega) : Prop :=
  ∀ x ∈ fixedSet H, ∀ v : E n,
    mfderiv (model n) (model n) (H.flow 1) x v = v → v = 0

abbrev Interval := Set.Icc (0 : ℝ) 1

def intervalZero : Interval := ⟨0, by norm_num⟩
def intervalOne : Interval := ⟨1, by norm_num⟩

def ContractibleLoop {n : ℕ} {M : ClosedManifold n} {omega : SymplecticForm M}
    (H : Hamiltonian omega) (x : M) : Prop :=
  ∃ K : C(Interval × Interval, M),
    (∀ t : Interval, K (intervalZero, t) = H.flow t x) ∧
    (∀ t : Interval, K (intervalOne, t) = x) ∧
    (∀ s : Interval, K (s, intervalZero) = x) ∧
    (∀ s : Interval, K (s, intervalOne) = x)

def contractibleFixedSet {n : ℕ} {M : ClosedManifold n} {omega : SymplecticForm M}
    (H : Hamiltonian omega) : Set M := {x | x ∈ fixedSet H ∧ ContractibleLoop H x}

def MainConclusion {M : ClosedManifold 12} {omega : SymplecticForm M}
    (H : Hamiltonian omega) : Prop :=
  (fixedSet H).Finite ∧ IsNondegenerate H ∧
    ((fixedSet H).ncard : ℤ) = eulerChar M + 3904 ∧
    (fixedSet H).ncard < morseNumber M ∧
    (contractibleFixedSet H).ncard < morseNumber M

lemma contractibleFixedSet_subset_fixedSet {n : ℕ} {M : ClosedManifold n}
    {omega : SymplecticForm M} (H : Hamiltonian omega) :
    contractibleFixedSet H ⊆ fixedSet H := fun _ hx => hx.1

lemma contractibleFixedSet_finite {n : ℕ} {M : ClosedManifold n}
    {omega : SymplecticForm M} {H : Hamiltonian omega} (h : (fixedSet H).Finite) :
    (contractibleFixedSet H).Finite :=
  h.subset (contractibleFixedSet_subset_fixedSet H)

theorem contractibleFixedSet_ncard_le {n : ℕ} {M : ClosedManifold n}
    {omega : SymplecticForm M} {H : Hamiltonian omega} (h : (fixedSet H).Finite) :
    (contractibleFixedSet H).ncard ≤ (fixedSet H).ncard :=
  Set.ncard_le_ncard (contractibleFixedSet_subset_fixedSet H) h

theorem contractibleFixedSet_ncard_lt_morseNumber {n : ℕ} {M : ClosedManifold n}
    {omega : SymplecticForm M} {H : Hamiltonian omega} (h : (fixedSet H).Finite)
    (hlt : (fixedSet H).ncard < morseNumber M) :
    (contractibleFixedSet H).ncard < morseNumber M :=
  (contractibleFixedSet_ncard_le h).trans_lt hlt

end
end ArnoldCounterexample.Nondegenerate

end

end OAI
