import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPreparedBind
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.LayoutPreparationCells

namespace OAI

/-! # Computing layout-dependent sampling parameters from a stored seed

The mixer counts, order and prime widths are obtained by the counted stored
preparation. They are not evaluated implicitly while selecting a sampler.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordLayoutPreparation

variable {n : ℕ}

abbrev Layout (I : Instance n) :=
  WordSeedMeasured.Accepted (canonicalRepresentationData I).zeroSetup.layoutCoupling

abbrev Prepared (I : Instance n) (a : Layout I) :=
  {d : RepresentationLayoutPreparation.Data n //
    (LayoutPreparationCells.run I a.seed.val).1.1 = some d}

theorem source (I : Instance n) (a : Layout I) :
    (canonicalRepresentationData I).zeroSetup.layoutCoupling.bounded a.seed.val = some a.value :=
  (WordSeedRealization.successful_agrees a.seed).trans (congrArg some a.correct.symm)

theorem exists_data (I : Instance n) (a : Layout I) : Nonempty (Prepared I a) := by
  obtain ⟨d,hd,_⟩ := RepresentationLayoutPreparation.complete
    (canonicalRepresentationData I) a.seed.val a.value.1 a.value.2 (source I a)
  exact ⟨⟨d,(congrArg Prod.fst (LayoutPreparationCells.value I a.seed.val)).trans hd⟩⟩

def compute (I : Instance n) (a : Layout I) : (Prepared I a × ℕ) × ℕ :=
  let out := LayoutPreparationCells.run I a.seed.val
  match h : out.1.1 with
  | none => False.elim (by
      obtain ⟨d⟩ := exists_data I a
      cases h.symm.trans d.property)
  | some d => ((⟨d,h⟩,out.1.2+1),out.2+8)

theorem fields (I : Instance n) (a : Layout I) (d : Prepared I a) :
    (∀ i : Fin n, d.val.permutation[i.val] = a.value.1 i) ∧
    (∀ i : Fin 4, d.val.parameters.widths[i.val] =
      (canonicalRepresentationData I).zeroSetup.samplerPrimeWidths a.value i) := by
  have hd := (congrArg Prod.fst (LayoutPreparationCells.value I a.seed.val)).symm.trans d.property
  obtain ⟨e,he,hv,_,hw⟩ := RepresentationLayoutPreparation.value
    (canonicalRepresentationData I) a.seed.val d.val hd
  have heq : (e,d.val.signs.semantic) = a.value := Option.some.inj (he.symm.trans (source I a))
  constructor
  · intro i
    have hi := congrArg (fun z => z.1 i) heq
    exact (hv i).trans hi
  · intro i
    exact (hw i).trans (congrArg
      (fun z => (canonicalRepresentationData I).zeroSetup.samplerPrimeWidths z i) heq)

theorem work (I : Instance n) (hn : 10000 ≤ n) (a : Layout I) :
    (compute I a).1.2 ≤ n*n^3+10*(n+1)^2+4*n+7+
      inputScale I^6*2^mixerSize n := by
  have hw := RepresentationLayoutPreparation.work (canonicalRepresentationData I) hn a.seed.val
  change (RepresentationLayoutPreparation.run (canonicalRepresentationData I) a.seed.val).2 ≤
    n*n^3+10*(n+1)^2+4*n+6+inputScale I^6*2^mixerSize n at hw
  have hv := congrArg Prod.snd (LayoutPreparationCells.value I a.seed.val)
  rw [←hv] at hw
  obtain ⟨d⟩ := exists_data I a
  unfold compute
  dsimp only
  split
  next h => cases h.symm.trans d.property
  · dsimp only
    omega

theorem cells (I : Instance n) (hn : 10000 ≤ n) (a : Layout I) :
    (compute I a).2 ≤ inputScale I^10*(compressionDictionaryCapacity n+1)+8 := by
  have hc := LayoutPreparationCells.cells I hn a.seed.val
  obtain ⟨d⟩ := exists_data I a
  unfold compute
  dsimp only
  split
  next h => cases h.symm.trans d.property
  · dsimp only
    omega

end LowSpaceSubsetSum.WordLayoutPreparation

end

end OAI
