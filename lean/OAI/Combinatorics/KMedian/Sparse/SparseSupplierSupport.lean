import Mathlib
import OAI.Combinatorics.KMedian.Preparation.CoupledGeometry
import OAI.Combinatorics.KMedian.Preparation.CoupledReindex
import OAI.Combinatorics.KMedian.Preparation.CoupledWeights
import OAI.Combinatorics.KMedian.Preparation.RationalSupplierPreparation

namespace OAI


                                             
section
namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

theorem bindIndexed_contains (μ : SparseIntegerLaw α) (κ : Fin μ.length → SparseIntegerLaw β)
    (a : Fin μ.length) (b : Fin (κ a).length) :
    ∃ i : Fin (μ.bindIndexed κ).length, (μ.bindIndexed κ).states[i.val]=(κ a).states[b.val] := by
  let e : (Σ a : Fin μ.length, Fin (κ a).length) ≃ Fin (∑ a, (κ a).length) := finSigmaFinEquiv
  refine ⟨e ⟨a,b⟩,?_⟩
  simp only [bindIndexed,Vector.getElem_ofFn]
  change (fun z : Σ a : Fin μ.length, Fin (κ a).length => (κ z.1).states[z.2.val])
    (e.symm (e ⟨a,b⟩))=_
  rw [e.symm_apply_apply]

end MetricKMedian.SparseIntegerLaw
namespace MetricKMedian.SparsePrepared
open Finset
variable {n m f : ℕ}

theorem contains_encoded (D : Fin m → Finset (Fin n)) (a q : Fin m → ℚ) (Δ : ℕ)
    (P : Fin n → Finset (Fin f)) (y : Fin f → ℚ) (p : Fin n → ℚ)
    (ha : ∀ e, 0 ≤ a e ∧ a e ≤ 1) (hq : ∀ e, 0 ≤ q e)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t) (hm : ∀ t, ∑ i∈P t,y i=p t)
    (b : Fin (SparseOuterLaw.law D a q ha hq).length) (ξ : Fin n → Finset (Fin f))
    (hξ : 0 < (SparseRescaledInner.encodedLaw P y p
      (total D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val])).weight ξ) :
    ∃ i : Fin (law D a q Δ P y p ha hq).length,
      (law D a q Δ P y p ha hq).states[i.val]=
        ((SparseOuterLaw.law D a q ha hq).states[b.val],
          SparseBundleEncoding.decode (SparseRescaledInner.piece P y p
            (total D q Δ (SparseOuterLaw.law D a q ha hq).states[b.val])) ξ) := by
  let ν := SparseOuterLaw.law D a q ha hq
  let K := total D q Δ ν.states[b.val]
  have hK : ∀ t, K t ≤ Δ := total_le _ _ _ _
  obtain ⟨c,_hc,hc⟩ := SparseBundleEncoding.support (SparseRescaledInner.piece P y p K) K Δ
    (fun i t => ⟨SparseRescaledInner.piece_nonnegative P y p K hy hp i t,
      SparseRescaledInner.piece_cap P y p K Δ hy hp hm hK i t⟩)
    (SparseRescaledInner.piece_sum P y p K hp hm) ξ hξ
  obtain ⟨i,hi⟩ := ν.bindIndexed_contains (fun a => kernel D q Δ P y p ν.states[a.val]) b c
  refine ⟨i,hi.trans ?_⟩
  simp only [kernel,SparseIntegerLaw.map,Vector.getElem_map]
  change (ν.states[b.val],(SparseBundles.law (SparseRescaledInner.piece P y p K)).states[c.val])=_
  rw [← hc]

end MetricKMedian.SparsePrepared
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars
variable {f n : ℕ}

def physicalIndex : Fin (f+n*f) ≃ Physical (Fin f) (Fin n) :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv.symm)

def original (a : Fin (f+n*f)) : Fin f := Sum.elim id Prod.snd (physicalIndex a)

def counts (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f)) (c : Fin n → ℚ)
    (γ g : ℚ) (zG : SparseSignedPreparation.State n (size f n) × SparseCounts.Table f n)
    (a : Fin (f+n*f)) : ℕ :=
  Sum.elim (fun i => SparseOuterLaw.outsideCount (q y P A c γ g) zG.1 (index.symm (.inl i)))
    (fun ti => zG.2 ti.1 ti.2) (physicalIndex a)

theorem coupled_support (y : Fin f → ℚ) (P A : Fin n → Finset (Fin f))
    (p c : Fin n → ℚ) (γ g : ℚ) (Δ : ℕ)
    (hy : ∀ i, 0 ≤ y i) (hp : ∀ t, 0 < p t)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hm : ∀ t, ∑ i ∈ P t, y i=p t) (hc : ∀ t, ∑ i ∈ A t, y i=c t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1/8) (hunit : ∀ t, p t+c t=1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hg : 0 < g) (heven : Even Δ) (hgrid : g*(Δ:ℚ)=1) :
    let L := coupled y P A p c γ g Δ hy hp hP hm hc hc0 hc1 hunit hγ hγ1 hg heven hgrid;
    let μ := SparsePrepared.law (D A) a (q y P A c γ g) Δ P y p a_bounds
      (q_nonneg y P A c γ g hy hc0 hγ.le hg.le);
    ∀ z : L.Ω × (Fin n → Finset (Fin f)), 0 < (L.ν.joint L.κ).weight z →
      ∃ b : Fin μ.length, ∀ i,
        counts y P A c γ g μ.states[b.val] i=physicalCount L z (physicalIndex i) := by
  intro L μ z hz
  have hz' := L.ν.support_joint L.κ z hz
  obtain ⟨b,hb⟩ := SparsePrepared.contains_encoded (D A) a (q y P A c γ g) Δ P y p
    a_bounds (q_nonneg y P A c γ g hy hc0 hγ.le hg.le) hy hp hm z.1 z.2 hz'.2
  refine ⟨b,?_⟩
  intro i
  change counts y P A c γ g (SparsePrepared.law _ _ _ _ _ _ _ _ _).states[b.val] i=_
  rw [hb]
  dsimp only [counts,physicalCount,L,coupled,CoupledLaw.reindexStars,CoupledLaw.castWeights,
    SparsePrepared.coupled,SparseRescaledInner.encodedCount]
  rfl

end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
