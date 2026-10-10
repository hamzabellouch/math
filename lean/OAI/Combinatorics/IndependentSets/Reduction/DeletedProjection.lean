import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.DiscreteBoundAuxiliary
import OAI.Combinatorics.IndependentSets.Reduction.SubchainBase
import OAI.Combinatorics.IndependentSets.Geometry.DeletedLayerEquiv

namespace OAI

namespace LargeIndependentSets

section
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal

variable {U V L R C : Type}
variable {n : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)

noncomputable def deletedProjection {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (i : B)
    (j : {j : B // j ≠ i}) :
    MixedTuple L R n (subchainBase (B.erase i.val) (deletion_nonempty hB i)).val.val →
      MixedTuple L R n j.val.val.val :=
  chainComposite lc chain _ _ (subchainBase_le _ (deletion_nonempty hB i) (deletedLayerEquiv i j))

lemma deleted_phase_reindex {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (i : B)
    {m : ℕ} (t : {j : B // j ≠ i} → Fin (m+1))
    (θ : (Sigma fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) → ℝ) :
    phase (deletedProjection lc chain hB i) (fun j => Coefficient.value (t j)) θ =
    phase (fun j => (chainView lc chain (B.erase i.val)).projection
      (subchainBase (B.erase i.val) (deletion_nonempty hB i)) j
      (subchainBase_le _ (deletion_nonempty hB i) j))
      (fun j => Coefficient.value (t ((deletedLayerEquiv i).symm j)))
      (reindex (deletedCoordEquiv (L:=L) (R:=R) i) θ) := by
  funext k
  simp only [phase]
  rw [← (deletedLayerEquiv i).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rfl

noncomputable def ruleUnion {s m : ℕ}
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    (I : Finset (Fin (n+1))) (v : SubchainView U V L R n I) : Finset (SubchainCoord L R n I) :=
  if hI : Small s I then Finset.univ.biUnion (rule I hI v) else ∅

lemma mem_ruleUnion {s m : ℕ}
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    {I : Finset (Fin (n+1))} (hI : Small s I) (v : SubchainView U V L R n I)
    (t : I → Fin (m+1)) {d : SubchainCoord L R n I} (hd : d ∈ rule I hI v t) :
    d ∈ ruleUnion rule I v := by
  simp only [ruleUnion, dite_eq_left hI]
  exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _,hd⟩

lemma aligned_excludes_deleted {s m : ℕ} {B : Finset (Fin (n+1))}
    (hB : 2 ≤ B.card) (hBs : B.card ≤ s)
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    (a : MixedTuple L R n n → Fin (n+1))
    (halign : ∀ I, I.Nonempty → I ⊆ B → ∀ x ∈
      terminalList lc chain I (ruleUnion rule I (chainView lc chain I)), a x ∈ I)
    (i : B) (t : (B.erase i.val) → Fin (m+1))
    (d : SubchainCoord L R n (B.erase i.val))
    (hd : d ∈ rule _ (deletion_small hB hBs i) (chainView lc chain _) t) :
    a (chainComposite lc chain d.1.val.val n (Nat.le_of_lt_succ d.1.val.isLt) d.2) ≠ i.val := by
  have hmem := mem_ruleUnion rule (deletion_small hB hBs i) (chainView lc chain _) t hd
  have hx := halign (B.erase i.val) (deletion_nonempty hB i) (Finset.erase_subset _ _)
    _ (Finset.mem_image.mpr ⟨d,hmem,rfl⟩)
  exact (Finset.mem_erase.mp hx).1

end

section
open MeasureTheory ProductAveraging PhaseTest
open scoped BigOperators Classical NNReal
variable {U V L R C : Type} [Fintype L] [Fintype R]
variable {n s m : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)

noncomputable def deletedRule
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (hBs : B.card ≤ s) (i : B)
    (t : {j : B // j ≠ i} → Fin (m+1)) :
    Finset (Sigma fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) :=
  (rule (B.erase i.val) (deletion_small hB hBs i) (chainView lc chain _)
    (fun j => t ((deletedLayerEquiv i).symm j))).image (deletedCoordEquiv i).symm

lemma actual_deleted_junta
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (hFm : ∀ q, Measurable (F q)) {γ : ℝ}
    (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I))
    (hjunta : ∀ I hI v t, (∫ θ, (viewFunction F hI.1 v t θ -
      average rotationLaw (rule I hI v t) (viewFunction F hI.1 v t) θ)^2
      ∂Measure.pi (fun _ : SubchainCoord L R n I => rotationLaw)) < γ^2)
    {B : Finset (Fin (n+1))} (hB : 2 ≤ B.card) (hBs : B.card ≤ s) (i : B)
    (t : {j : B // j ≠ i} → Fin (m+1)) :
    let f := fun θ => F (occurrenceQuestion lc chain
        (subchainBase (B.erase i.val) (deletion_nonempty hB i)).val)
      (phase (deletedProjection lc chain hB i) (fun j => Coefficient.value (t j)) θ)
    (∫ θ, (f θ - average rotationLaw (deletedRule lc chain rule hB hBs i t) f θ)^2
      ∂Measure.pi (fun _ : Sigma (fun j : {j : B // j ≠ i} => MixedTuple L R n j.val.val.val) => rotationLaw)) < γ^2 := by
  let c := subchainBase (B.erase i.val) (deletion_nonempty hB i)
  let v := chainView lc chain (B.erase i.val)
  let t' : (B.erase i.val) → Fin (m+1) := fun j => t ((deletedLayerEquiv i).symm j)
  let f := viewFunction F (deletion_nonempty hB i) v t'
  have hf : Measurable f := (hFm _).comp (phase_measurable _ _)
  have he : (fun θ => F (occurrenceQuestion lc chain c.val)
      (phase (deletedProjection lc chain hB i) (fun j => Coefficient.value (t j)) θ)) =
      f ∘ reindex (deletedCoordEquiv (L:=L) (R:=R) i) := by
    funext θ
    exact congrArg (F (occurrenceQuestion lc chain c.val)) (deleted_phase_reindex lc chain hB i t θ)
  have heI := congrArg (fun g : ((Sigma fun j : {j : B // j ≠ i} =>
      MixedTuple L R n j.val.val.val) → ℝ) → ℝ =>
    ∫ θ, (g θ - average rotationLaw (deletedRule lc chain rule hB hBs i t) g θ)^2
      ∂Measure.pi (fun _ => rotationLaw)) he
  apply lt_of_eq_of_lt heI
  exact (junta_error_reindex (deletedCoordEquiv (L:=L) (R:=R) i)
    (rule (B.erase i.val) (deletion_small hB hBs i) v t') f hf).trans_lt
      (hjunta (B.erase i.val) (deletion_small hB hBs i) v t')

end

open MeasureTheory ProductAveraging PhaseTest Coefficient BooleanJunta
open scoped BigOperators Classical NNReal

noncomputable def fiberSquare {U V L R C : Type} [Fintype L] [Fintype R]
    {n : ℕ} (lc : LabelCoverData U V L R C) (chain : Fin n → C)
    (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ)
    (B : Finset (Fin (n+1))) (hB : B.Nonempty) (m : ℕ) (ρ : ℝ) (k : ℕ) : ℝ :=
  ∑ t : B → Fin (m+1), mass m ρ t *
    𝔼 v : SubchainCoord L R n B → Cube k,
      (viewFunction F hB (chainView lc chain B) t (fun c => scalarCell (v c) 0))^2

theorem actual_aligned_fiber (Lip : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (m s k : ℕ) (ρ γ err : ℝ), 0 < m → 2 ≤ s → 0 ≤ ρ → 0 ≤ err → err < γ →
    (Lip:ℝ)/m < β/2 → (1-levelMass m ρ ⟨m,by omega⟩)^s < ε →
    ρ*K < ε → (s:ℝ)*(2*γ)^2/β^2 < ε → 2*Lip*s*(1/2:ℝ)^k < ε →
    ∀ (U V L R C : Type) [Fintype L] [Fintype R] (n : ℕ)
      (lc : LabelCoverData U V L R C) (chain : Fin n → C)
      (F : ∀ q : LayerQuestion U V n, (LayerAnswer L R q → Circle) → ℝ),
    (∀ q, LipschitzWith Lip (F q)) → (∀ q x, |F q x| ≤ 1) →
    (∀ q x, F q (fun z => x z + ((1/2:ℝ):Circle)) = -F q x) →
    (∀ (i j : Fin (n+1)) (hij : i ≤ j) (y : MixedTuple L R n j.val → Circle),
      |F (occurrenceQuestion lc chain i) (y ∘ chainComposite lc chain i.val j.val hij) -
        F (occurrenceQuestion lc chain j) y| ≤ err) →
    ∀ (rule : ∀ (I : Finset (Fin (n+1))), Small s I →
      SubchainView U V L R n I → (I → Fin (m+1)) → Finset (SubchainCoord L R n I)),
    (∀ I hI v t, (∫ θ, (viewFunction F hI.1 v t θ -
      average rotationLaw (rule I hI v t) (viewFunction F hI.1 v t) θ)^2
      ∂Measure.pi (fun _ : SubchainCoord L R n I => rotationLaw)) < γ^2) →
    ∀ (B : Finset (Fin (n+1))) (hB : B.Nonempty), B.card = s →
    Aligned (fun I => terminalList lc chain I (ruleUnion rule I (chainView lc chain I))) B →
      fiberSquare lc chain F B hB m ρ k < 6*ε := by
  obtain ⟨β,hβ,K,hK,HT⟩ := arbitrary_coefficient_mean_square Lip hε
  refine ⟨β,hβ,K,hK,?_⟩
  intro m s k ρ γ err hm hs hρ he heγ hstep hrare hpos hzero hgrid
    U V L R C _ _ n lc chain F hF hb hodd hcompat rule hjunta B hB hBs halign
  have hB2 : 2 ≤ B.card := by omega
  let b := subchainBase B hB
  let M : B → Type := fun j => MixedTuple L R n j.val.val
  let κ := MixedTuple L R n b.val.val
  let τ := MixedTuple L R n n
  let p : ∀ j : B, κ → M j := fun j =>
    chainComposite lc chain b.val.val j.val.val (subchainBase_le B hB j)
  let q : ∀ j : B, M j → τ := fun j =>
    chainComposite lc chain j.val.val n (Nat.le_of_lt_succ j.val.isLt)
  let r : κ → τ := chainComposite lc chain b.val.val n (Nat.le_of_lt_succ b.val.isLt)
  have hq : ∀ j x, q j (p j x) = r x := fun j x => chainComposite_comp lc chain _ _ _ _ _ x
  let c (i : B) := subchainBase (B.erase i.val) (deletion_nonempty hB2 i)
  have hbc (i : B) : b.val ≤ (c i).val :=
    B.min'_le _ ((Finset.erase_subset _ _) (c i).property)
  let κ' : B → Type := fun i => MixedTuple L R n (c i).val.val
  let e : ∀ i : B, κ → κ' i := fun i => chainComposite lc chain b.val.val (c i).val.val (hbc i)
  let p' : ∀ i : B, ∀ j : {j : B // j ≠ i}, κ' i → M j.val :=
    fun i => deletedProjection lc chain hB2 i
  have hp : ∀ i j x, p j.val x = p' i j (e i x) := by
    intro i j x
    exact (chainComposite_comp lc chain _ _ _ _ _ x).symm
  let F' : ∀ i : B, (κ' i → Circle) → ℝ := fun i => F (occurrenceQuestion lc chain (c i).val)
  let S := deletedRule lc chain rule hB2 (le_of_eq hBs)
  obtain ⟨a,haB,ha⟩ := halign
  let aa : τ → B := fun z => ⟨a z,haB z⟩
  have haux := HT B m hm ρ γ err hρ he heγ hstep (by simpa [hBs] using hrare)
    hpos (by simpa [hBs] using hzero) M κ τ p q r hq
    (F (occurrenceQuestion lc chain b.val)) (hF _)
    (fun x => hb (occurrenceQuestion lc chain b.val) x)
    (fun x => hodd (occurrenceQuestion lc chain b.val) x)
    κ' p' e hp F' (fun i => (hF (occurrenceQuestion lc chain (c i).val)).continuous.measurable)
    (fun i x => hb (occurrenceQuestion lc chain (c i).val) x)
    (fun i y => hcompat b.val (c i).val (hbc i) y) S
    (fun i t => actual_deleted_junta lc chain F (fun q => (hF q).continuous.measurable)
      rule hjunta hB2 (le_of_eq hBs) i t) aa (by
      intro i t d hd
      obtain ⟨D,hD,hD'⟩ := Finset.mem_image.mp hd
      subst d
      intro heq
      have hne := aligned_excludes_deleted lc chain hB2 (le_of_eq hBs) rule a ha i _ D hD
      exact hne (congrArg Subtype.val heq))
  have hfin := discrete_bound_of_auxiliary p q r hq aa hm hρ k
    (by simpa [hBs] using hrare) (by simpa [hBs] using hgrid)
    (F (occurrenceQuestion lc chain b.val)) (hF _)
    (fun x => hb (occurrenceQuestion lc chain b.val) x) haux
  exact hfin

end LargeIndependentSets

end OAI
