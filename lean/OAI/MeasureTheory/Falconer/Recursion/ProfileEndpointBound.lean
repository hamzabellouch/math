import OAI.MeasureTheory.Falconer.Estimates.ParentRefinedEndpointSelection
import OAI.MeasureTheory.Falconer.Incidence.ParentQuarterIncidence
import OAI.MeasureTheory.Falconer.Incidence.IncidenceProductChain

namespace OAI

/-! The induction statement retains the original reference profile. Its
single budget bounds parent mass loss, pencil regularity and pencil size ratio. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

def QuarterPencilData (δ s W m : ℝ) (P : Finset (Space 2))
    (V : Space 2 → Finset (Space 2)) : Prop :=
  ∀ x ∈ P, m ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ W*m ∧
    InBoundedLineChart (V x) ∧ FiniteSeparatedAt δ (V x) ∧
    NormalizedFiniteBallBound δ s W (V x) ∧
    ∀ l ∈ V x, |l 0| ≤ 1/2 ∧ TubeIncident δ x l

def ProfileEndpointBound (N B K : ℕ) (L : Finset (CellPath 2))
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2)
    (i j : ℕ) (s W A : ℝ) : Prop :=
  ∀ (L' : Finset (CellPath 2)) (g : CellPath 2 → List ℕ) (q : CellPath 2)
    (a₀ : ℕ) (r₀ : CellPath 2), L' ⊆ cubePaths 2 N →
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    S ⊆ prefixFiber C a₀ r₀ → ((prefixFiber C a₀ r₀).card:ℝ) ≤ W*(S.card:ℝ) →
    a₀ ≤ blockDepth N B i → ∀ p₀ ∈ S.image (List.take (blockDepth N B i)),
    ∀ m : ℝ, 0 < m → ∀ V : Space 2 → Finset (Space 2),
    let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    QuarterPencilData (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2)) s W m Z V →
    A ≤ ((Z.biUnion V).card:ℝ)/m

theorem QuarterPencilData.mono {δ s U W m : ℝ} {P P' : Finset (Space 2)}
    {V : Space 2 → Finset (Space 2)} (h : QuarterPencilData δ s U m P V)
    (hδ : 0 ≤ δ) (hm : 0 ≤ m) (hUW : U ≤ W) (hP : P' ⊆ P) :
    QuarterPencilData δ s W m P' V := by
  intro x hx
  obtain ⟨hlo,hhi,hch,hsep,hball,hinc⟩ := h x (hP hx)
  exact ⟨hlo,hhi.trans (mul_le_mul_of_nonneg_right hUW hm),hch,hsep,
    normalizedFiniteBallBound_mono_constant hδ hUW hball,hinc⟩

theorem profileEndpointBound_trivial (N B K : ℕ) (L : Finset (CellPath 2))
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2)
    (i j : ℕ) (s W : ℝ) : ProfileEndpointBound N B K L f p Q i j s W 1 := by
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  apply pencil_union_ratio_one_le hm Z V
  · exact ((prefixFiber_nonempty hp₀).image _).image _
  · intro x hx
    exact (hV x hx).1

theorem ProfileEndpointBound.mono_budget {N B K i j : ℕ} {L : Finset (CellPath 2)}
    {f : CellPath 2 → List ℕ} {p : CellPath 2} {Q : DyadicCube 2} {s U W A : ℝ}
    (h : ProfileEndpointBound N B K L f p Q i j s W A) (hUW : U ≤ W) :
    ProfileEndpointBound N B K L f p Q i j s U A := by
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  exact h L' g q a₀ r₀ hL' hsub
    (hmass.trans (mul_le_mul_of_nonneg_right hUW (Nat.cast_nonneg _))) ha₀ p₀ hp₀ m hm V
    (hV.mono (by positivity) hm.le hUW Finset.Subset.rfl)

theorem ProfileEndpointBound.mono_value {N B K i j : ℕ} {L : Finset (CellPath 2)}
    {f : CellPath 2 → List ℕ} {p : CellPath 2} {Q : DyadicCube 2} {s W A D : ℝ}
    (h : ProfileEndpointBound N B K L f p Q i j s W A) (hDA : D ≤ A) :
    ProfileEndpointBound N B K L f p Q i j s W D := by
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  exact hDA.trans (h L' g q a₀ r₀ hL' hsub hmass ha₀ p₀ hp₀ m hm V hV)

theorem profileEndpointBound_retained_subset {N B K : ℕ} {L L' : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (f g : CellPath 2 → List ℕ) (p q : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {a₀ : ℕ} (r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {W U H W' A s m : ℝ} (hW : 0 ≤ W) (hH : 0 ≤ H) (hm : 0 < m)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        W*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (ha₀ : a₀ ≤ blockDepth N B i) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    (P : Finset (Space 2)) (hP : P.Nonempty)
    (hPsub : P ⊆ quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀)
    (hsize : ((quarterEndpointSet Q
      (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
      (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤ H*(P.card:ℝ))
    (hbudget : (W*(2:ℝ)^(2*i))*((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K) ≤ W')
    (hUW : U ≤ W') (hbound : ProfileEndpointBound N B K L f p Q i j s W' A)
    (V : Space 2 → Finset (Space 2))
    (hV : QuarterPencilData (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2)) s U m P V) :
    A ≤ ((P.biUnion V).card:ℝ)/m := by
  obtain ⟨E,hES,hEN,hEC,u,hu,hT,hTne,hmassT,hTP⟩ :=
    blockClass_parent_refine_quarter_endpoint_subset hL hL' B f g K p q r₀
      hsub hW hmass Q hQ hji hi ha₀ p₀ hp₀ P hP hPsub hH hsize
  let T := classLeaves E (blockLabel E N B (fun _ => []) K)
    (blockLabel E N B (fun _ => []) K u)
  have hparent : p₀ ∈ T.image (List.take (blockDepth N B i)) := by
    obtain ⟨v,hv⟩ := hTne
    refine Finset.mem_image.mpr ⟨v,hv,?_⟩
    exact (Finset.mem_filter.mp (hES (hT hv))).2
  have hh := hbound E (fun _ => []) u (blockDepth N B i) p₀ hEN
    (hT.trans hEC) (hmassT.trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg _)))
    le_rfl p₀ hparent m hm V (hV.mono (by positivity) hm.le hUW hTP)
  exact hh.trans (div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left V hTP))) hm.le)

end Falconer

end OAI
