import OAI.Analysis.KadisonSimilarity.Tensor.EndpointTensors
import OAI.Analysis.KadisonSimilarity.Tensor.TensorClassification

namespace OAI

/-!
# Density for unrestricted endpoints and centered tensor letters

The two endpoint variables and the finitely many centered letters have different
ambient Hilbert spaces. Nested dense matrix stages nevertheless give a common
stage, so their continuous coefficient identities extend together.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct
universe u

/-- A finite dependent tuple in nested dense stages has a common stage. -/
theorem exists_common_dependent_stage {ι : Type*} [Fintype ι] {V : ι → Type*}
    (S : ℕ → ∀ i, Set (V i)) (hmono : ∀ i, Monotone (fun n => S n i))
    (x : ∀ i, V i) (hx : ∀ i, x i ∈ ⋃ n, S n i) :
    ∃ n, ∀ i, x i ∈ S n i := by
  classical
  have hstage : ∀ i, ∃ n, x i ∈ S n i := fun i => Set.mem_iUnion.mp (hx i)
  choose stage hstage using hstage
  exact ⟨Finset.univ.sup stage, fun i =>
    hmono i (Finset.le_sup (Finset.mem_univ i)) (hstage i)⟩

/-- Dependent finite-coordinate version of continuity from nested dense stages. -/
theorem continuous_eq_of_nested_dependent_stages {ι : Type*} [Fintype ι]
    {V : ι → Type*} [∀ i, TopologicalSpace (V i)]
    (S : ℕ → ∀ i, Set (V i)) (hmono : ∀ i, Monotone (fun n => S n i))
    (hdense : ∀ i, Dense (⋃ n, S n i))
    (f g : (∀ i, V i) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hstage : ∀ n x, (∀ i, x i ∈ S n i) → f x = g x) : f = g := by
  let U (i : ι) : Set (V i) := ⋃ n, S n i
  have hd : DenseRange (Pi.map (fun i => ((↑) : U i → V i))) :=
    DenseRange.piMap (fun i => (hdense i).denseRange_val)
  apply hd.equalizer hf hg
  funext x
  obtain ⟨n, hn⟩ := exists_common_dependent_stage S hmono
    (fun i => (x i : V i)) (fun i => (x i).property)
  exact hstage n _ hn

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Continuity of the completed word, including its unrestricted endpoint. -/
theorem continuous_endpointWord (n : ℕ) :
    Continuous (fun p : E × (Fin n → F) => endpointWord p.1 p.2) := by
  have ht : Continuous (fun p : E × (Fin n → F) =>
      p.1 ⊗ₜ[ℂ] completedTensorWord p.2) :=
    TensorProduct.continuous_tmul.comp
      (continuous_fst.prodMk ((continuous_completedTensorWord n).comp continuous_snd))
  exact (UniformSpace.Completion.continuous_coe
    (α := E ⊗[ℂ] CompletedTensorWord F n)).comp ht

omit [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] in
/-- Two groups of finite coordinates can use different Hilbert spaces. -/
theorem continuous_eq_of_two_nested_stages {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : ℕ → Set E) (T : ℕ → Set F) (hS : Monotone S) (hT : Monotone T)
    (hdS : Dense (⋃ n, S n)) (hdT : Dense (⋃ n, T n))
    (f g : (ι → E) × (κ → F) → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hstage : ∀ n p, (∀ i, p.1 i ∈ S n) → (∀ j, p.2 j ∈ T n) → f p = g p) :
    f = g := by
  let U : Set E := ⋃ n, S n
  let V : Set F := ⋃ n, T n
  have hs : DenseRange (Pi.map (fun _ : ι => ((↑) : U → E))) :=
    DenseRange.piMap (fun _ => hdS.denseRange_val)
  have ht : DenseRange (Pi.map (fun _ : κ => ((↑) : V → F))) :=
    DenseRange.piMap (fun _ => hdT.denseRange_val)
  apply (hs.prodMap ht).equalizer hf hg
  funext p
  obtain ⟨m, hm⟩ := exists_common_stage S hS (fun i => (p.1 i : E))
    (fun i => (p.1 i).property)
  obtain ⟨n, hn⟩ := exists_common_stage T hT (fun i => (p.2 i : F))
    (fun i => (p.2 i).property)
  exact hstage (max m n) _ (fun i => hS (Nat.le_max_left m n) (hm i))
    (fun j => hT (Nat.le_max_right m n) (hn j))

/-- The pair of endpoint letters and all centered tail letters. -/
abbrev EndpointLetters (E F : Type u) (k l : ℕ) :=
  (Bool → E) × (Fin k ⊕ Fin l → F)

def endpointTracialCoefficient {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (J : F → F)
    (v : EndpointLetters E F k l) : ℂ :=
  inner ℂ (endpointWord (v.1 true) (fun j => J (v.2 (.inr j))))
    (Y (endpointWord (v.1 false) (fun i => v.2 (.inl i))))

theorem continuous_endpointTracialCoefficient {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (J : F → F) (hJ : Continuous J) : Continuous (endpointTracialCoefficient Y J) := by
  unfold endpointTracialCoefficient
  have htest : Continuous (fun v : EndpointLetters E F k l =>
      (v.1 true, fun j : Fin l => J (v.2 (Sum.inr j)))) :=
    ((continuous_apply true).comp continuous_fst).prodMk
      (continuous_pi (fun j => hJ.comp ((continuous_apply (Sum.inr j)).comp continuous_snd)))
  have hsource : Continuous (fun v : EndpointLetters E F k l =>
      (v.1 false, fun i : Fin k => v.2 (Sum.inl i))) :=
    ((continuous_apply false).comp continuous_fst).prodMk
      (continuous_pi (fun i => (continuous_apply (Sum.inl i)).comp continuous_snd))
  have htw := (continuous_endpointWord (E := E) (F := F) l).comp htest
  have hsw := (continuous_endpointWord (E := E) (F := F) k).comp hsource
  have hyw := Y.continuous.comp hsw
  simpa only [Function.comp_def] using htw.inner hyw

/-- Extend a stage endpoint pairing formula to all endpoints and tail letters. -/
theorem endpoint_pairing_identity_of_stages {k l : ℕ}
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (J : F → F) (hJ : Continuous J) (B : F →L[ℂ] F →L[ℂ] ℂ)
    (c : PerfectMatching (Fin k ⊕ Fin l) → ℂ)
    (S : ℕ → Set E) (T : ℕ → Set F) (hS : Monotone S) (hT : Monotone T)
    (hdS : Dense (⋃ n, S n)) (hdT : Dense (⋃ n, T n))
    (hstage : ∀ n d a v, d ∈ S n → a ∈ S n → (∀ i, v i ∈ T n) →
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v) :
    ∀ d a v,
      inner ℂ (endpointWord a (fun j => J (v (.inr j))))
        (Y (endpointWord d (fun i => v (.inl i)))) =
      inner ℂ a d * ∑ P, c P * pairingPolynomial sourceFirstRank B P v := by
  classical
  let rhs (v : EndpointLetters E F k l) := inner ℂ (v.1 true) (v.1 false) *
    ∑ P, c P * pairingPolynomial sourceFirstRank B P v.2
  have hinner : Continuous (fun v : EndpointLetters E F k l =>
      inner ℂ (v.1 true) (v.1 false)) :=
    ((continuous_apply true).comp continuous_fst).inner ((continuous_apply false).comp continuous_fst)
  have htail : Continuous (fun v : EndpointLetters E F k l =>
      v.2) :=
    continuous_snd
  have hsum : Continuous (fun v : EndpointLetters E F k l =>
      ∑ P, c P * pairingPolynomial sourceFirstRank B P v.2) :=
    continuous_finsetSum _ (fun P _ => continuous_const.mul
      ((continuous_pairingPolynomial sourceFirstRank B P).comp htail))
  have hrhs : Continuous rhs := hinner.mul hsum
  have heq := continuous_eq_of_two_nested_stages S T hS hT hdS hdT
    (endpointTracialCoefficient Y J) rhs (continuous_endpointTracialCoefficient Y J hJ) hrhs
    (fun n v hv hw => hstage n (v.1 false) (v.1 true) v.2 (hv false) (hv true) hw)
  intro d a v
  exact congrFun heq (fun b => if b then a else d, v)

end KadisonSimilarity

end

end OAI
