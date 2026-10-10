import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw256 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw256 raw256Labels = mixedMoment B node2638 node2638Labels := by
  calc
    mixedMoment B raw256 raw256Labels = mixedMoment B raw256step0 raw256step0Labels := by
      have ha : raw256step0 = (fun i j => raw256 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw256step0 raw256; decide +kernel
      have hl : raw256step0Labels = raw256Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw256 raw256Labels permutation32 permutation5
    mixedMoment B raw256step0 raw256step0Labels = mixedMoment B raw256step1 raw256step1Labels := by
      have ha : raw256step1 = raw256step0 := by apply Matrix.ext; unfold raw256step1 raw256step0; decide +kernel
      have hl : raw256step0Labels = labelEmbedding1 ∘ raw256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw256step0 raw256step0Labels raw256step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2638 node2638Labels := by rfl

def raw257 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw257Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw257step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw257 raw257Labels = mixedMoment B node353 node353Labels := by
  calc
    mixedMoment B raw257 raw257Labels = mixedMoment B raw257step0 raw257step0Labels := by
      have ha : raw257step0 = (fun i j => raw257 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw257step0 raw257; decide +kernel
      have hl : raw257step0Labels = raw257Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw257 raw257Labels permutation32 permutation5
    _ = mixedMoment B node353 node353Labels := by rfl

def raw258 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 3, -2]]
def raw258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw258step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw258 raw258Labels = mixedMoment B node2640 node2640Labels := by
  calc
    mixedMoment B raw258 raw258Labels = mixedMoment B raw258step0 raw258step0Labels := by
      have ha : raw258step0 = (fun i j => raw258 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw258step0 raw258; decide +kernel
      have hl : raw258step0Labels = raw258Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw258 raw258Labels permutation8 permutation5
    mixedMoment B raw258step0 raw258step0Labels = mixedMoment B raw258step1 raw258step1Labels := by
      have ha : raw258step1 = raw258step0 := by apply Matrix.ext; unfold raw258step1 raw258step0; decide +kernel
      have hl : raw258step0Labels = labelEmbedding1 ∘ raw258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw258step0 raw258step0Labels raw258step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2640 node2640Labels := by rfl

def raw259 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 3, -2]]
def raw259Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw259step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw259step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw259step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw259 raw259Labels = mixedMoment B node315 node315Labels := by
  calc
    mixedMoment B raw259 raw259Labels = mixedMoment B raw259step0 raw259step0Labels := by
      have ha : raw259step0 = (fun i j => raw259 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw259step0 raw259; decide +kernel
      have hl : raw259step0Labels = raw259Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw259 raw259Labels permutation31 permutation4
    mixedMoment B raw259step0 raw259step0Labels = mixedMoment B raw259step1 raw259step1Labels := by
      have ha : raw259step1 = -raw259step0 := by apply Matrix.ext; change ∀ i j, raw259step1 i j = -(raw259step0 i j); unfold raw259step1 raw259step0; decide +kernel
      have hl : raw259step1Labels = raw259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node315 node315Labels := by rfl

def raw260 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 3, -3]]
def raw260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw260step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw260 raw260Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw260 raw260Labels = mixedMoment B raw260step0 raw260step0Labels := by
      have ha : raw260step0 = (fun i j => raw260 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw260step0 raw260; decide +kernel
      have hl : raw260step0Labels = raw260Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw260 raw260Labels permutation8 permutation5
    mixedMoment B raw260step0 raw260step0Labels = mixedMoment B raw260step1 raw260step1Labels := by
      have ha : raw260step1 = raw260step0 := by apply Matrix.ext; unfold raw260step1 raw260step0; decide +kernel
      have hl : raw260step0Labels = labelEmbedding1 ∘ raw260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw260step0 raw260step0Labels raw260step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2642 node2642Labels := by rfl

def raw261 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 3, -3]]
def raw261Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw261step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw261step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw261step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw261 raw261Labels = mixedMoment B node236 node236Labels := by
  calc
    mixedMoment B raw261 raw261Labels = mixedMoment B raw261step0 raw261step0Labels := by
      have ha : raw261step0 = (fun i j => raw261 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw261step0 raw261; decide +kernel
      have hl : raw261step0Labels = raw261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw261 raw261Labels permutation31 permutation4
    mixedMoment B raw261step0 raw261step0Labels = mixedMoment B raw261step1 raw261step1Labels := by
      have ha : raw261step1 = -raw261step0 := by apply Matrix.ext; change ∀ i j, raw261step1 i j = -(raw261step0 i j); unfold raw261step1 raw261step0; decide +kernel
      have hl : raw261step1Labels = raw261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node236 node236Labels := by rfl

def raw262 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw262step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw262 raw262Labels = mixedMoment B node2644 node2644Labels := by
  calc
    mixedMoment B raw262 raw262Labels = mixedMoment B raw262step0 raw262step0Labels := by
      have ha : raw262step0 = (fun i j => raw262 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw262step0 raw262; decide +kernel
      have hl : raw262step0Labels = raw262Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw262 raw262Labels permutation8 permutation5
    mixedMoment B raw262step0 raw262step0Labels = mixedMoment B raw262step1 raw262step1Labels := by
      have ha : raw262step1 = raw262step0 := by apply Matrix.ext; unfold raw262step1 raw262step0; decide +kernel
      have hl : raw262step0Labels = labelEmbedding1 ∘ raw262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw262step0 raw262step0Labels raw262step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2644 node2644Labels := by rfl

def raw263 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw263Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw263step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw263 raw263Labels = mixedMoment B node355 node355Labels := by
  calc
    mixedMoment B raw263 raw263Labels = mixedMoment B raw263step0 raw263step0Labels := by
      have ha : raw263step0 = (fun i j => raw263 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw263step0 raw263; decide +kernel
      have hl : raw263step0Labels = raw263Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw263 raw263Labels permutation8 permutation5
    _ = mixedMoment B node355 node355Labels := by rfl

def raw264 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw264 raw264Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw264 raw264Labels = mixedMoment B raw264step0 raw264step0Labels := by
      have ha : raw264step0 = (fun i j => raw264 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw264step0 raw264; decide +kernel
      have hl : raw264step0Labels = raw264Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw264 raw264Labels permutation32 permutation5
    mixedMoment B raw264step0 raw264step0Labels = mixedMoment B raw264step1 raw264step1Labels := by
      have ha : raw264step1 = raw264step0 := by apply Matrix.ext; unfold raw264step1 raw264step0; decide +kernel
      have hl : raw264step0Labels = labelEmbedding1 ∘ raw264step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw264step0 raw264step0Labels raw264step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw265 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw265Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw265step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw265 raw265Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw265 raw265Labels = mixedMoment B raw265step0 raw265step0Labels := by
      have ha : raw265step0 = (fun i j => raw265 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw265step0 raw265; decide +kernel
      have hl : raw265step0Labels = raw265Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw265 raw265Labels permutation32 permutation5
    _ = mixedMoment B node397 node397Labels := by rfl

def raw266 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]
def raw266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw266step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw266 raw266Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw266 raw266Labels = mixedMoment B raw266step0 raw266step0Labels := by
      have ha : raw266step0 = (fun i j => raw266 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw266step0 raw266; decide +kernel
      have hl : raw266step0Labels = raw266Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw266 raw266Labels permutation8 permutation5
    mixedMoment B raw266step0 raw266step0Labels = mixedMoment B raw266step1 raw266step1Labels := by
      have ha : raw266step1 = raw266step0 := by apply Matrix.ext; unfold raw266step1 raw266step0; decide +kernel
      have hl : raw266step0Labels = labelEmbedding1 ∘ raw266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw266step0 raw266step0Labels raw266step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw267 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]
def raw267Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw267step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw267step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw267step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw267 raw267Labels = mixedMoment B node262 node262Labels := by
  calc
    mixedMoment B raw267 raw267Labels = mixedMoment B raw267step0 raw267step0Labels := by
      have ha : raw267step0 = (fun i j => raw267 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw267step0 raw267; decide +kernel
      have hl : raw267step0Labels = raw267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw267 raw267Labels permutation29 permutation4
    mixedMoment B raw267step0 raw267step0Labels = mixedMoment B raw267step1 raw267step1Labels := by
      have ha : raw267step1 = -raw267step0 := by apply Matrix.ext; change ∀ i j, raw267step1 i j = -(raw267step0 i j); unfold raw267step1 raw267step0; decide +kernel
      have hl : raw267step1Labels = raw267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node262 node262Labels := by rfl

def raw268 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw268 raw268Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw268 raw268Labels = mixedMoment B raw268step0 raw268step0Labels := by
      have ha : raw268step0 = (fun i j => raw268 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw268step0 raw268; decide +kernel
      have hl : raw268step0Labels = raw268Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw268 raw268Labels permutation32 permutation5
    mixedMoment B raw268step0 raw268step0Labels = mixedMoment B raw268step1 raw268step1Labels := by
      have ha : raw268step1 = raw268step0 := by apply Matrix.ext; unfold raw268step1 raw268step0; decide +kernel
      have hl : raw268step0Labels = labelEmbedding1 ∘ raw268step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw268step0 raw268step0Labels raw268step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw269 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw269Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw269step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw269 raw269Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw269 raw269Labels = mixedMoment B raw269step0 raw269step0Labels := by
      have ha : raw269step0 = (fun i j => raw269 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw269step0 raw269; decide +kernel
      have hl : raw269step0Labels = raw269Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw269 raw269Labels permutation32 permutation5
    _ = mixedMoment B node403 node403Labels := by rfl

def raw270 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw270step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw270 raw270Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw270 raw270Labels = mixedMoment B raw270step0 raw270step0Labels := by
      have ha : raw270step0 = (fun i j => raw270 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw270step0 raw270; decide +kernel
      have hl : raw270step0Labels = raw270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw270 raw270Labels permutation8 permutation5
    mixedMoment B raw270step0 raw270step0Labels = mixedMoment B raw270step1 raw270step1Labels := by
      have ha : raw270step1 = raw270step0 := by apply Matrix.ext; unfold raw270step1 raw270step0; decide +kernel
      have hl : raw270step0Labels = labelEmbedding1 ∘ raw270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw270step0 raw270step0Labels raw270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw271 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw271Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw271step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw271step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw271 raw271Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw271 raw271Labels = mixedMoment B raw271step0 raw271step0Labels := by
      have ha : raw271step0 = (fun i j => raw271 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw271step0 raw271; decide +kernel
      have hl : raw271step0Labels = raw271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw271 raw271Labels permutation8 permutation5
    _ = mixedMoment B node404 node404Labels := by rfl

def raw272 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw272step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw272 raw272Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw272 raw272Labels = mixedMoment B raw272step0 raw272step0Labels := by
      have ha : raw272step0 = (fun i j => raw272 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw272step0 raw272; decide +kernel
      have hl : raw272step0Labels = raw272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw272 raw272Labels permutation8 permutation5
    mixedMoment B raw272step0 raw272step0Labels = mixedMoment B raw272step1 raw272step1Labels := by
      have ha : raw272step1 = raw272step0 := by apply Matrix.ext; unfold raw272step1 raw272step0; decide +kernel
      have hl : raw272step0Labels = labelEmbedding1 ∘ raw272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw272step0 raw272step0Labels raw272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw273 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw273Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw273step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw273step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw273 raw273Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw273 raw273Labels = mixedMoment B raw273step0 raw273step0Labels := by
      have ha : raw273step0 = (fun i j => raw273 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw273step0 raw273; decide +kernel
      have hl : raw273step0Labels = raw273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw273 raw273Labels permutation8 permutation5
    _ = mixedMoment B node405 node405Labels := by rfl

def raw274 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 3, -2]]
def raw274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw274step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw274step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw274 raw274Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw274 raw274Labels = mixedMoment B raw274step0 raw274step0Labels := by
      have ha : raw274step0 = (fun i j => raw274 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw274step0 raw274; decide +kernel
      have hl : raw274step0Labels = raw274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw274 raw274Labels permutation2 permutation5
    mixedMoment B raw274step0 raw274step0Labels = mixedMoment B raw274step1 raw274step1Labels := by
      have ha : raw274step1 = raw274step0 := by apply Matrix.ext; unfold raw274step1 raw274step0; decide +kernel
      have hl : raw274step0Labels = labelEmbedding1 ∘ raw274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw274step0 raw274step0Labels raw274step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw275 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-1, 0, 1], ![-1, 3, -2]]
def raw275Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw275step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw275step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw275step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw275step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw275 raw275Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw275 raw275Labels = mixedMoment B raw275step0 raw275step0Labels := by
      have ha : raw275step0 = (fun i j => raw275 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw275step0 raw275; decide +kernel
      have hl : raw275step0Labels = raw275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw275 raw275Labels permutation7 permutation4
    mixedMoment B raw275step0 raw275step0Labels = mixedMoment B raw275step1 raw275step1Labels := by
      have ha : raw275step1 = -raw275step0 := by apply Matrix.ext; change ∀ i j, raw275step1 i j = -(raw275step0 i j); unfold raw275step1 raw275step0; decide +kernel
      have hl : raw275step1Labels = raw275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node407 node407Labels := by rfl

def raw276 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw276 raw276Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw276 raw276Labels = mixedMoment B raw276step0 raw276step0Labels := by
      have ha : raw276step0 = (fun i j => raw276 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw276step0 raw276; decide +kernel
      have hl : raw276step0Labels = raw276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw276 raw276Labels permutation32 permutation5
    mixedMoment B raw276step0 raw276step0Labels = mixedMoment B raw276step1 raw276step1Labels := by
      have ha : raw276step1 = raw276step0 := by apply Matrix.ext; unfold raw276step1 raw276step0; decide +kernel
      have hl : raw276step0Labels = labelEmbedding1 ∘ raw276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw276step0 raw276step0Labels raw276step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw277 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw277Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw277step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw277 raw277Labels = mixedMoment B node411 node411Labels := by
  calc
    mixedMoment B raw277 raw277Labels = mixedMoment B raw277step0 raw277step0Labels := by
      have ha : raw277step0 = (fun i j => raw277 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw277step0 raw277; decide +kernel
      have hl : raw277step0Labels = raw277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw277 raw277Labels permutation32 permutation5
    _ = mixedMoment B node411 node411Labels := by rfl

def raw278 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw278step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw278step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw278 raw278Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw278 raw278Labels = mixedMoment B raw278step0 raw278step0Labels := by
      have ha : raw278step0 = (fun i j => raw278 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw278step0 raw278; decide +kernel
      have hl : raw278step0Labels = raw278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw278 raw278Labels permutation8 permutation5
    mixedMoment B raw278step0 raw278step0Labels = mixedMoment B raw278step1 raw278step1Labels := by
      have ha : raw278step1 = raw278step0 := by apply Matrix.ext; unfold raw278step1 raw278step0; decide +kernel
      have hl : raw278step0Labels = labelEmbedding1 ∘ raw278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw278step0 raw278step0Labels raw278step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw279 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw279Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw279step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw279step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw279 raw279Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw279 raw279Labels = mixedMoment B raw279step0 raw279step0Labels := by
      have ha : raw279step0 = (fun i j => raw279 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw279step0 raw279; decide +kernel
      have hl : raw279step0Labels = raw279Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw279 raw279Labels permutation8 permutation5
    _ = mixedMoment B node412 node412Labels := by rfl

def raw280 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 3, -3]]
def raw280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw280step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw280step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw280 raw280Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw280 raw280Labels = mixedMoment B raw280step0 raw280step0Labels := by
      have ha : raw280step0 = (fun i j => raw280 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw280step0 raw280; decide +kernel
      have hl : raw280step0Labels = raw280Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw280 raw280Labels permutation2 permutation5
    mixedMoment B raw280step0 raw280step0Labels = mixedMoment B raw280step1 raw280step1Labels := by
      have ha : raw280step1 = raw280step0 := by apply Matrix.ext; unfold raw280step1 raw280step0; decide +kernel
      have hl : raw280step0Labels = labelEmbedding1 ∘ raw280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw280step0 raw280step0Labels raw280step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw281 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 0, 2], ![0, 3, -3]]
def raw281Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw281step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw281step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw281step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw281step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw281 raw281Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw281 raw281Labels = mixedMoment B raw281step0 raw281step0Labels := by
      have ha : raw281step0 = (fun i j => raw281 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw281step0 raw281; decide +kernel
      have hl : raw281step0Labels = raw281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw281 raw281Labels permutation7 permutation4
    mixedMoment B raw281step0 raw281step0Labels = mixedMoment B raw281step1 raw281step1Labels := by
      have ha : raw281step1 = -raw281step0 := by apply Matrix.ext; change ∀ i j, raw281step1 i j = -(raw281step0 i j); unfold raw281step1 raw281step0; decide +kernel
      have hl : raw281step1Labels = raw281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

def raw282 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw282step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw282 raw282Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw282 raw282Labels = mixedMoment B raw282step0 raw282step0Labels := by
      have ha : raw282step0 = (fun i j => raw282 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw282step0 raw282; decide +kernel
      have hl : raw282step0Labels = raw282Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw282 raw282Labels permutation8 permutation5
    mixedMoment B raw282step0 raw282step0Labels = mixedMoment B raw282step1 raw282step1Labels := by
      have ha : raw282step1 = raw282step0 := by apply Matrix.ext; unfold raw282step1 raw282step0; decide +kernel
      have hl : raw282step0Labels = labelEmbedding1 ∘ raw282step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw282step0 raw282step0Labels raw282step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw283 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -3, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw283Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw283step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw283step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw283 raw283Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw283 raw283Labels = mixedMoment B raw283step0 raw283step0Labels := by
      have ha : raw283step0 = (fun i j => raw283 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw283step0 raw283; decide +kernel
      have hl : raw283step0Labels = raw283Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw283 raw283Labels permutation8 permutation5
    _ = mixedMoment B node416 node416Labels := by rfl

def raw284 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 1, 1], ![0, 2, -2]]
def raw284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw284step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw284step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw284 raw284Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw284 raw284Labels = mixedMoment B raw284step0 raw284step0Labels := by
      have ha : raw284step0 = (fun i j => raw284 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw284step0 raw284; decide +kernel
      have hl : raw284step0Labels = raw284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw284 raw284Labels permutation2 permutation5
    mixedMoment B raw284step0 raw284step0Labels = mixedMoment B raw284step1 raw284step1Labels := by
      have ha : raw284step1 = raw284step0 := by apply Matrix.ext; unfold raw284step1 raw284step0; decide +kernel
      have hl : raw284step0Labels = labelEmbedding1 ∘ raw284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw284step0 raw284step0Labels raw284step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw285 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -3, 1], ![-2, 1, 1], ![0, 2, -2]]
def raw285Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw285step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw285step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw285 raw285Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw285 raw285Labels = mixedMoment B raw285step0 raw285step0Labels := by
      have ha : raw285step0 = (fun i j => raw285 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw285step0 raw285; decide +kernel
      have hl : raw285step0Labels = raw285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw285 raw285Labels permutation2 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

def raw286 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw286 raw286Labels = mixedMoment B node2828 node2828Labels := by
  calc
    mixedMoment B raw286 raw286Labels = mixedMoment B raw286step0 raw286step0Labels := by
      have ha : raw286step0 = (fun i j => raw286 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw286step0 raw286; decide +kernel
      have hl : raw286step0Labels = raw286Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw286 raw286Labels permutation32 permutation5
    mixedMoment B raw286step0 raw286step0Labels = mixedMoment B raw286step1 raw286step1Labels := by
      have ha : raw286step1 = raw286step0 := by apply Matrix.ext; unfold raw286step1 raw286step0; decide +kernel
      have hl : raw286step0Labels = labelEmbedding1 ∘ raw286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw286step0 raw286step0Labels raw286step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2828 node2828Labels := by rfl

def raw287 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw287Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw287step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw287 raw287Labels = mixedMoment B node273 node273Labels := by
  calc
    mixedMoment B raw287 raw287Labels = mixedMoment B raw287step0 raw287step0Labels := by
      have ha : raw287step0 = (fun i j => raw287 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw287step0 raw287; decide +kernel
      have hl : raw287step0Labels = raw287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw287 raw287Labels permutation34 permutation4
    _ = mixedMoment B node273 node273Labels := by rfl

def raw288 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw288step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw288 raw288Labels = mixedMoment B node2829 node2829Labels := by
  calc
    mixedMoment B raw288 raw288Labels = mixedMoment B raw288step0 raw288step0Labels := by
      have ha : raw288step0 = (fun i j => raw288 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw288step0 raw288; decide +kernel
      have hl : raw288step0Labels = raw288Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw288 raw288Labels permutation32 permutation5
    mixedMoment B raw288step0 raw288step0Labels = mixedMoment B raw288step1 raw288step1Labels := by
      have ha : raw288step1 = raw288step0 := by apply Matrix.ext; unfold raw288step1 raw288step0; decide +kernel
      have hl : raw288step0Labels = labelEmbedding1 ∘ raw288step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw288step0 raw288step0Labels raw288step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2829 node2829Labels := by rfl

def raw289 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw289Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw289step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw289 raw289Labels = mixedMoment B node275 node275Labels := by
  calc
    mixedMoment B raw289 raw289Labels = mixedMoment B raw289step0 raw289step0Labels := by
      have ha : raw289step0 = (fun i j => raw289 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw289step0 raw289; decide +kernel
      have hl : raw289step0Labels = raw289Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw289 raw289Labels permutation33 permutation4
    _ = mixedMoment B node275 node275Labels := by rfl

def raw290 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw290 raw290Labels = mixedMoment B node2830 node2830Labels := by
  calc
    mixedMoment B raw290 raw290Labels = mixedMoment B raw290step0 raw290step0Labels := by
      have ha : raw290step0 = (fun i j => raw290 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw290step0 raw290; decide +kernel
      have hl : raw290step0Labels = raw290Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw290 raw290Labels permutation32 permutation5
    mixedMoment B raw290step0 raw290step0Labels = mixedMoment B raw290step1 raw290step1Labels := by
      have ha : raw290step1 = raw290step0 := by apply Matrix.ext; unfold raw290step1 raw290step0; decide +kernel
      have hl : raw290step0Labels = labelEmbedding1 ∘ raw290step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw290step0 raw290step0Labels raw290step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2830 node2830Labels := by rfl

def raw291 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw291Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw291step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw291 raw291Labels = mixedMoment B node276 node276Labels := by
  calc
    mixedMoment B raw291 raw291Labels = mixedMoment B raw291step0 raw291step0Labels := by
      have ha : raw291step0 = (fun i j => raw291 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw291step0 raw291; decide +kernel
      have hl : raw291step0Labels = raw291Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw291 raw291Labels permutation32 permutation4
    _ = mixedMoment B node276 node276Labels := by rfl

def raw292 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw292step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw292 raw292Labels = mixedMoment B node2832 node2832Labels := by
  calc
    mixedMoment B raw292 raw292Labels = mixedMoment B raw292step0 raw292step0Labels := by
      have ha : raw292step0 = (fun i j => raw292 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw292step0 raw292; decide +kernel
      have hl : raw292step0Labels = raw292Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw292 raw292Labels permutation8 permutation5
    mixedMoment B raw292step0 raw292step0Labels = mixedMoment B raw292step1 raw292step1Labels := by
      have ha : raw292step1 = raw292step0 := by apply Matrix.ext; unfold raw292step1 raw292step0; decide +kernel
      have hl : raw292step0Labels = labelEmbedding1 ∘ raw292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw292step0 raw292step0Labels raw292step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2832 node2832Labels := by rfl

def raw293 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw293Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw293step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw293step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw293step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw293 raw293Labels = mixedMoment B node186 node186Labels := by
  calc
    mixedMoment B raw293 raw293Labels = mixedMoment B raw293step0 raw293step0Labels := by
      have ha : raw293step0 = (fun i j => raw293 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw293step0 raw293; decide +kernel
      have hl : raw293step0Labels = raw293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw293 raw293Labels permutation31 permutation4
    mixedMoment B raw293step0 raw293step0Labels = mixedMoment B raw293step1 raw293step1Labels := by
      have ha : raw293step1 = -raw293step0 := by apply Matrix.ext; change ∀ i j, raw293step1 i j = -(raw293step0 i j); unfold raw293step1 raw293step0; decide +kernel
      have hl : raw293step1Labels = raw293step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node186 node186Labels := by rfl

def raw294 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw294 raw294Labels = mixedMoment B node2901 node2901Labels := by
  calc
    mixedMoment B raw294 raw294Labels = mixedMoment B raw294step0 raw294step0Labels := by
      have ha : raw294step0 = (fun i j => raw294 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw294step0 raw294; decide +kernel
      have hl : raw294step0Labels = raw294Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw294 raw294Labels permutation152 permutation5
    mixedMoment B raw294step0 raw294step0Labels = mixedMoment B raw294step1 raw294step1Labels := by
      have ha : raw294step1 = raw294step0 := by apply Matrix.ext; unfold raw294step1 raw294step0; decide +kernel
      have hl : raw294step0Labels = labelEmbedding1 ∘ raw294step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw294step0 raw294step0Labels raw294step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2901 node2901Labels := by rfl

def raw295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw295Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw295step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw295step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw295 raw295Labels = mixedMoment B node206 node206Labels := by
  calc
    mixedMoment B raw295 raw295Labels = mixedMoment B raw295step0 raw295step0Labels := by
      have ha : raw295step0 = (fun i j => raw295 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw295step0 raw295; decide +kernel
      have hl : raw295step0Labels = raw295Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw295 raw295Labels permutation662 permutation4
    mixedMoment B raw295step0 raw295step0Labels = mixedMoment B raw295step1 raw295step1Labels := by
      have ha : raw295step1 = -raw295step0 := by apply Matrix.ext; change ∀ i j, raw295step1 i j = -(raw295step0 i j); unfold raw295step1 raw295step0; decide +kernel
      have hl : raw295step1Labels = raw295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node206 node206Labels := by rfl

def raw296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw296 raw296Labels = mixedMoment B node2903 node2903Labels := by
  calc
    mixedMoment B raw296 raw296Labels = mixedMoment B raw296step0 raw296step0Labels := by
      have ha : raw296step0 = (fun i j => raw296 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw296step0 raw296; decide +kernel
      have hl : raw296step0Labels = raw296Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw296 raw296Labels permutation152 permutation5
    mixedMoment B raw296step0 raw296step0Labels = mixedMoment B raw296step1 raw296step1Labels := by
      have ha : raw296step1 = raw296step0 := by apply Matrix.ext; unfold raw296step1 raw296step0; decide +kernel
      have hl : raw296step0Labels = labelEmbedding1 ∘ raw296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw296step0 raw296step0Labels raw296step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2903 node2903Labels := by rfl

def raw297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw297Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw297step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw297 raw297Labels = mixedMoment B node293 node293Labels := by
  calc
    mixedMoment B raw297 raw297Labels = mixedMoment B raw297step0 raw297step0Labels := by
      have ha : raw297step0 = (fun i j => raw297 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw297step0 raw297; decide +kernel
      have hl : raw297step0Labels = raw297Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw297 raw297Labels permutation177 permutation4
    _ = mixedMoment B node293 node293Labels := by rfl

def raw298 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw298 raw298Labels = mixedMoment B node2904 node2904Labels := by
  calc
    mixedMoment B raw298 raw298Labels = mixedMoment B raw298step0 raw298step0Labels := by
      have ha : raw298step0 = (fun i j => raw298 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw298step0 raw298; decide +kernel
      have hl : raw298step0Labels = raw298Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw298 raw298Labels permutation32 permutation5
    mixedMoment B raw298step0 raw298step0Labels = mixedMoment B raw298step1 raw298step1Labels := by
      have ha : raw298step1 = raw298step0 := by apply Matrix.ext; unfold raw298step1 raw298step0; decide +kernel
      have hl : raw298step0Labels = labelEmbedding1 ∘ raw298step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw298step0 raw298step0Labels raw298step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2904 node2904Labels := by rfl

def raw299 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw299Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw299step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw299step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw299 raw299Labels = mixedMoment B node175 node175Labels := by
  calc
    mixedMoment B raw299 raw299Labels = mixedMoment B raw299step0 raw299step0Labels := by
      have ha : raw299step0 = (fun i j => raw299 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw299step0 raw299; decide +kernel
      have hl : raw299step0Labels = raw299Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw299 raw299Labels permutation149 permutation4
    mixedMoment B raw299step0 raw299step0Labels = mixedMoment B raw299step1 raw299step1Labels := by
      have ha : raw299step1 = -raw299step0 := by apply Matrix.ext; change ∀ i j, raw299step1 i j = -(raw299step0 i j); unfold raw299step1 raw299step0; decide +kernel
      have hl : raw299step1Labels = raw299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node175 node175Labels := by rfl

def raw300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw300 raw300Labels = mixedMoment B node2932 node2932Labels := by
  calc
    mixedMoment B raw300 raw300Labels = mixedMoment B raw300step0 raw300step0Labels := by
      have ha : raw300step0 = (fun i j => raw300 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw300step0 raw300; decide +kernel
      have hl : raw300step0Labels = raw300Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw300 raw300Labels permutation152 permutation5
    mixedMoment B raw300step0 raw300step0Labels = mixedMoment B raw300step1 raw300step1Labels := by
      have ha : raw300step1 = raw300step0 := by apply Matrix.ext; unfold raw300step1 raw300step0; decide +kernel
      have hl : raw300step0Labels = labelEmbedding1 ∘ raw300step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw300step0 raw300step0Labels raw300step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2932 node2932Labels := by rfl

def raw301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw301Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw301step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw301step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw301 raw301Labels = mixedMoment B node198 node198Labels := by
  calc
    mixedMoment B raw301 raw301Labels = mixedMoment B raw301step0 raw301step0Labels := by
      have ha : raw301step0 = (fun i j => raw301 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw301step0 raw301; decide +kernel
      have hl : raw301step0Labels = raw301Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw301 raw301Labels permutation682 permutation4
    mixedMoment B raw301step0 raw301step0Labels = mixedMoment B raw301step1 raw301step1Labels := by
      have ha : raw301step1 = -raw301step0 := by apply Matrix.ext; change ∀ i j, raw301step1 i j = -(raw301step0 i j); unfold raw301step1 raw301step0; decide +kernel
      have hl : raw301step1Labels = raw301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node198 node198Labels := by rfl

def raw302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw302step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw302 raw302Labels = mixedMoment B node2936 node2936Labels := by
  calc
    mixedMoment B raw302 raw302Labels = mixedMoment B raw302step0 raw302step0Labels := by
      have ha : raw302step0 = (fun i j => raw302 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw302step0 raw302; decide +kernel
      have hl : raw302step0Labels = raw302Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw302 raw302Labels permutation152 permutation5
    mixedMoment B raw302step0 raw302step0Labels = mixedMoment B raw302step1 raw302step1Labels := by
      have ha : raw302step1 = raw302step0 := by apply Matrix.ext; unfold raw302step1 raw302step0; decide +kernel
      have hl : raw302step0Labels = labelEmbedding1 ∘ raw302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw302step0 raw302step0Labels raw302step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2936 node2936Labels := by rfl

def raw303 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw303Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw303step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw303 raw303Labels = mixedMoment B node321 node321Labels := by
  calc
    mixedMoment B raw303 raw303Labels = mixedMoment B raw303step0 raw303step0Labels := by
      have ha : raw303step0 = (fun i j => raw303 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw303step0 raw303; decide +kernel
      have hl : raw303step0Labels = raw303Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw303 raw303Labels permutation152 permutation4
    _ = mixedMoment B node321 node321Labels := by rfl

def raw304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw304 raw304Labels = mixedMoment B node2937 node2937Labels := by
  calc
    mixedMoment B raw304 raw304Labels = mixedMoment B raw304step0 raw304step0Labels := by
      have ha : raw304step0 = (fun i j => raw304 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw304step0 raw304; decide +kernel
      have hl : raw304step0Labels = raw304Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw304 raw304Labels permutation152 permutation5
    mixedMoment B raw304step0 raw304step0Labels = mixedMoment B raw304step1 raw304step1Labels := by
      have ha : raw304step1 = raw304step0 := by apply Matrix.ext; unfold raw304step1 raw304step0; decide +kernel
      have hl : raw304step0Labels = labelEmbedding1 ∘ raw304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw304step0 raw304step0Labels raw304step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2937 node2937Labels := by rfl

def raw305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw305Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw305step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw305 raw305Labels = mixedMoment B node320 node320Labels := by
  calc
    mixedMoment B raw305 raw305Labels = mixedMoment B raw305step0 raw305step0Labels := by
      have ha : raw305step0 = (fun i j => raw305 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw305step0 raw305; decide +kernel
      have hl : raw305step0Labels = raw305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw305 raw305Labels permutation154 permutation4
    _ = mixedMoment B node320 node320Labels := by rfl

def raw306 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw306 raw306Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw306 raw306Labels = mixedMoment B raw306step0 raw306step0Labels := by
      have ha : raw306step0 = (fun i j => raw306 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw306step0 raw306; decide +kernel
      have hl : raw306step0Labels = raw306Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw306 raw306Labels permutation32 permutation5
    mixedMoment B raw306step0 raw306step0Labels = mixedMoment B raw306step1 raw306step1Labels := by
      have ha : raw306step1 = raw306step0 := by apply Matrix.ext; unfold raw306step1 raw306step0; decide +kernel
      have hl : raw306step0Labels = labelEmbedding1 ∘ raw306step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw306step0 raw306step0Labels raw306step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw307 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw307Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw307step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw307step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw307 raw307Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw307 raw307Labels = mixedMoment B raw307step0 raw307step0Labels := by
      have ha : raw307step0 = (fun i j => raw307 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw307step0 raw307; decide +kernel
      have hl : raw307step0Labels = raw307Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw307 raw307Labels permutation151 permutation4
    mixedMoment B raw307step0 raw307step0Labels = mixedMoment B raw307step1 raw307step1Labels := by
      have ha : raw307step1 = -raw307step0 := by apply Matrix.ext; change ∀ i j, raw307step1 i j = -(raw307step0 i j); unfold raw307step1 raw307step0; decide +kernel
      have hl : raw307step1Labels = raw307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node303 node303Labels := by rfl

def raw308 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw308 raw308Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw308 raw308Labels = mixedMoment B raw308step0 raw308step0Labels := by
      have ha : raw308step0 = (fun i j => raw308 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw308step0 raw308; decide +kernel
      have hl : raw308step0Labels = raw308Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw308 raw308Labels permutation32 permutation5
    mixedMoment B raw308step0 raw308step0Labels = mixedMoment B raw308step1 raw308step1Labels := by
      have ha : raw308step1 = raw308step0 := by apply Matrix.ext; unfold raw308step1 raw308step0; decide +kernel
      have hl : raw308step0Labels = labelEmbedding1 ∘ raw308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw308step0 raw308step0Labels raw308step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw309 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw309Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw309step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw309step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw309 raw309Labels = mixedMoment B node222 node222Labels := by
  calc
    mixedMoment B raw309 raw309Labels = mixedMoment B raw309step0 raw309step0Labels := by
      have ha : raw309step0 = (fun i j => raw309 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw309step0 raw309; decide +kernel
      have hl : raw309step0Labels = raw309Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw309 raw309Labels permutation151 permutation4
    mixedMoment B raw309step0 raw309step0Labels = mixedMoment B raw309step1 raw309step1Labels := by
      have ha : raw309step1 = -raw309step0 := by apply Matrix.ext; change ∀ i j, raw309step1 i j = -(raw309step0 i j); unfold raw309step1 raw309step0; decide +kernel
      have hl : raw309step1Labels = raw309step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node222 node222Labels := by rfl

def raw310 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw310 raw310Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw310 raw310Labels = mixedMoment B raw310step0 raw310step0Labels := by
      have ha : raw310step0 = (fun i j => raw310 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw310step0 raw310; decide +kernel
      have hl : raw310step0Labels = raw310Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw310 raw310Labels permutation32 permutation5
    mixedMoment B raw310step0 raw310step0Labels = mixedMoment B raw310step1 raw310step1Labels := by
      have ha : raw310step1 = raw310step0 := by apply Matrix.ext; unfold raw310step1 raw310step0; decide +kernel
      have hl : raw310step0Labels = labelEmbedding1 ∘ raw310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw310step0 raw310step0Labels raw310step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw311 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw311Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw311step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw311 raw311Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw311 raw311Labels = mixedMoment B raw311step0 raw311step0Labels := by
      have ha : raw311step0 = (fun i j => raw311 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw311step0 raw311; decide +kernel
      have hl : raw311step0Labels = raw311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw311 raw311Labels permutation33 permutation4
    _ = mixedMoment B node325 node325Labels := by rfl

def raw312 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw312 raw312Labels = mixedMoment B node2948 node2948Labels := by
  calc
    mixedMoment B raw312 raw312Labels = mixedMoment B raw312step0 raw312step0Labels := by
      have ha : raw312step0 = (fun i j => raw312 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw312step0 raw312; decide +kernel
      have hl : raw312step0Labels = raw312Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw312 raw312Labels permutation32 permutation5
    mixedMoment B raw312step0 raw312step0Labels = mixedMoment B raw312step1 raw312step1Labels := by
      have ha : raw312step1 = raw312step0 := by apply Matrix.ext; unfold raw312step1 raw312step0; decide +kernel
      have hl : raw312step0Labels = labelEmbedding1 ∘ raw312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw312step0 raw312step0Labels raw312step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2948 node2948Labels := by rfl

def raw313 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw313Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw313step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw313 raw313Labels = mixedMoment B node202 node202Labels := by
  calc
    mixedMoment B raw313 raw313Labels = mixedMoment B raw313step0 raw313step0Labels := by
      have ha : raw313step0 = (fun i j => raw313 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw313step0 raw313; decide +kernel
      have hl : raw313step0Labels = raw313Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw313 raw313Labels permutation149 permutation6
    _ = mixedMoment B node202 node202Labels := by rfl

def raw314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw314 raw314Labels = mixedMoment B node2957 node2957Labels := by
  calc
    mixedMoment B raw314 raw314Labels = mixedMoment B raw314step0 raw314step0Labels := by
      have ha : raw314step0 = (fun i j => raw314 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw314step0 raw314; decide +kernel
      have hl : raw314step0Labels = raw314Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw314 raw314Labels permutation152 permutation5
    mixedMoment B raw314step0 raw314step0Labels = mixedMoment B raw314step1 raw314step1Labels := by
      have ha : raw314step1 = raw314step0 := by apply Matrix.ext; unfold raw314step1 raw314step0; decide +kernel
      have hl : raw314step0Labels = labelEmbedding1 ∘ raw314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw314step0 raw314step0Labels raw314step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2957 node2957Labels := by rfl

def raw315 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw315Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw315step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw315 raw315Labels = mixedMoment B node331 node331Labels := by
  calc
    mixedMoment B raw315 raw315Labels = mixedMoment B raw315step0 raw315step0Labels := by
      have ha : raw315step0 = (fun i j => raw315 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw315step0 raw315; decide +kernel
      have hl : raw315step0Labels = raw315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw315 raw315Labels permutation170 permutation4
    _ = mixedMoment B node331 node331Labels := by rfl

def raw316 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw316 raw316Labels = mixedMoment B node2958 node2958Labels := by
  calc
    mixedMoment B raw316 raw316Labels = mixedMoment B raw316step0 raw316step0Labels := by
      have ha : raw316step0 = (fun i j => raw316 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw316step0 raw316; decide +kernel
      have hl : raw316step0Labels = raw316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw316 raw316Labels permutation152 permutation5
    mixedMoment B raw316step0 raw316step0Labels = mixedMoment B raw316step1 raw316step1Labels := by
      have ha : raw316step1 = raw316step0 := by apply Matrix.ext; unfold raw316step1 raw316step0; decide +kernel
      have hl : raw316step0Labels = labelEmbedding1 ∘ raw316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw316step0 raw316step0Labels raw316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2958 node2958Labels := by rfl

def raw317 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw317Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw317step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw317 raw317Labels = mixedMoment B node334 node334Labels := by
  calc
    mixedMoment B raw317 raw317Labels = mixedMoment B raw317step0 raw317step0Labels := by
      have ha : raw317step0 = (fun i j => raw317 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw317step0 raw317; decide +kernel
      have hl : raw317step0Labels = raw317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw317 raw317Labels permutation168 permutation4
    _ = mixedMoment B node334 node334Labels := by rfl

def raw318 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw318 raw318Labels = mixedMoment B node2959 node2959Labels := by
  calc
    mixedMoment B raw318 raw318Labels = mixedMoment B raw318step0 raw318step0Labels := by
      have ha : raw318step0 = (fun i j => raw318 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw318step0 raw318; decide +kernel
      have hl : raw318step0Labels = raw318Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw318 raw318Labels permutation32 permutation5
    mixedMoment B raw318step0 raw318step0Labels = mixedMoment B raw318step1 raw318step1Labels := by
      have ha : raw318step1 = raw318step0 := by apply Matrix.ext; unfold raw318step1 raw318step0; decide +kernel
      have hl : raw318step0Labels = labelEmbedding1 ∘ raw318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw318step0 raw318step0Labels raw318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2959 node2959Labels := by rfl

def raw319 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw319Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw319step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw319 raw319Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw319 raw319Labels = mixedMoment B raw319step0 raw319step0Labels := by
      have ha : raw319step0 = (fun i j => raw319 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw319step0 raw319; decide +kernel
      have hl : raw319step0Labels = raw319Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw319 raw319Labels permutation32 permutation4
    _ = mixedMoment B node339 node339Labels := by rfl

def raw320 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw320 raw320Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw320 raw320Labels = mixedMoment B raw320step0 raw320step0Labels := by
      have ha : raw320step0 = (fun i j => raw320 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw320step0 raw320; decide +kernel
      have hl : raw320step0Labels = raw320Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw320 raw320Labels permutation32 permutation5
    mixedMoment B raw320step0 raw320step0Labels = mixedMoment B raw320step1 raw320step1Labels := by
      have ha : raw320step1 = raw320step0 := by apply Matrix.ext; unfold raw320step1 raw320step0; decide +kernel
      have hl : raw320step0Labels = labelEmbedding1 ∘ raw320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw320step0 raw320step0Labels raw320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw321 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw321Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw321step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw321 raw321Labels = mixedMoment B node336 node336Labels := by
  calc
    mixedMoment B raw321 raw321Labels = mixedMoment B raw321step0 raw321step0Labels := by
      have ha : raw321step0 = (fun i j => raw321 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw321step0 raw321; decide +kernel
      have hl : raw321step0Labels = raw321Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw321 raw321Labels permutation34 permutation4
    _ = mixedMoment B node336 node336Labels := by rfl

def raw322 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw322 raw322Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw322 raw322Labels = mixedMoment B raw322step0 raw322step0Labels := by
      have ha : raw322step0 = (fun i j => raw322 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw322step0 raw322; decide +kernel
      have hl : raw322step0Labels = raw322Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw322 raw322Labels permutation32 permutation5
    mixedMoment B raw322step0 raw322step0Labels = mixedMoment B raw322step1 raw322step1Labels := by
      have ha : raw322step1 = raw322step0 := by apply Matrix.ext; unfold raw322step1 raw322step0; decide +kernel
      have hl : raw322step0Labels = labelEmbedding1 ∘ raw322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw322step0 raw322step0Labels raw322step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw323 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw323Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw323step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw323 raw323Labels = mixedMoment B node332 node332Labels := by
  calc
    mixedMoment B raw323 raw323Labels = mixedMoment B raw323step0 raw323step0Labels := by
      have ha : raw323step0 = (fun i j => raw323 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw323step0 raw323; decide +kernel
      have hl : raw323step0Labels = raw323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw323 raw323Labels permutation34 permutation4
    _ = mixedMoment B node332 node332Labels := by rfl

def raw324 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw324 raw324Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw324 raw324Labels = mixedMoment B raw324step0 raw324step0Labels := by
      have ha : raw324step0 = (fun i j => raw324 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw324step0 raw324; decide +kernel
      have hl : raw324step0Labels = raw324Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw324 raw324Labels permutation32 permutation5
    mixedMoment B raw324step0 raw324step0Labels = mixedMoment B raw324step1 raw324step1Labels := by
      have ha : raw324step1 = raw324step0 := by apply Matrix.ext; unfold raw324step1 raw324step0; decide +kernel
      have hl : raw324step0Labels = labelEmbedding1 ∘ raw324step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw324step0 raw324step0Labels raw324step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw325 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw325Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw325step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw325 raw325Labels = mixedMoment B node335 node335Labels := by
  calc
    mixedMoment B raw325 raw325Labels = mixedMoment B raw325step0 raw325step0Labels := by
      have ha : raw325step0 = (fun i j => raw325 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw325step0 raw325; decide +kernel
      have hl : raw325step0Labels = raw325Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw325 raw325Labels permutation32 permutation4
    _ = mixedMoment B node335 node335Labels := by rfl

def raw326 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw326step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw326 raw326Labels = mixedMoment B node2965 node2965Labels := by
  calc
    mixedMoment B raw326 raw326Labels = mixedMoment B raw326step0 raw326step0Labels := by
      have ha : raw326step0 = (fun i j => raw326 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw326step0 raw326; decide +kernel
      have hl : raw326step0Labels = raw326Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw326 raw326Labels permutation8 permutation5
    mixedMoment B raw326step0 raw326step0Labels = mixedMoment B raw326step1 raw326step1Labels := by
      have ha : raw326step1 = raw326step0 := by apply Matrix.ext; unfold raw326step1 raw326step0; decide +kernel
      have hl : raw326step0Labels = labelEmbedding1 ∘ raw326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw326step0 raw326step0Labels raw326step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2965 node2965Labels := by rfl

def raw327 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 3, -2]]
def raw327Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw327step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw327step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw327 raw327Labels = mixedMoment B node338 node338Labels := by
  calc
    mixedMoment B raw327 raw327Labels = mixedMoment B raw327step0 raw327step0Labels := by
      have ha : raw327step0 = (fun i j => raw327 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw327step0 raw327; decide +kernel
      have hl : raw327step0Labels = raw327Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw327 raw327Labels permutation8 permutation4
    _ = mixedMoment B node338 node338Labels := by rfl

def raw328 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 3, -3]]
def raw328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw328step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw328 raw328Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw328 raw328Labels = mixedMoment B raw328step0 raw328step0Labels := by
      have ha : raw328step0 = (fun i j => raw328 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw328step0 raw328; decide +kernel
      have hl : raw328step0Labels = raw328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw328 raw328Labels permutation8 permutation5
    mixedMoment B raw328step0 raw328step0Labels = mixedMoment B raw328step1 raw328step1Labels := by
      have ha : raw328step1 = raw328step0 := by apply Matrix.ext; unfold raw328step1 raw328step0; decide +kernel
      have hl : raw328step0Labels = labelEmbedding1 ∘ raw328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw328step0 raw328step0Labels raw328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw329 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 3, -3]]
def raw329Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw329step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw329step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw329 raw329Labels = mixedMoment B node247 node247Labels := by
  calc
    mixedMoment B raw329 raw329Labels = mixedMoment B raw329step0 raw329step0Labels := by
      have ha : raw329step0 = (fun i j => raw329 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw329step0 raw329; decide +kernel
      have hl : raw329step0Labels = raw329Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw329 raw329Labels permutation31 permutation4
    mixedMoment B raw329step0 raw329step0Labels = mixedMoment B raw329step1 raw329step1Labels := by
      have ha : raw329step1 = -raw329step0 := by apply Matrix.ext; change ∀ i j, raw329step1 i j = -(raw329step0 i j); unfold raw329step1 raw329step0; decide +kernel
      have hl : raw329step1Labels = raw329step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node247 node247Labels := by rfl

def raw330 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 2, -2], ![-2, 2, 0]]
def raw330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw330 raw330Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw330 raw330Labels = mixedMoment B raw330step0 raw330step0Labels := by
      have ha : raw330step0 = (fun i j => raw330 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw330step0 raw330; decide +kernel
      have hl : raw330step0Labels = raw330Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw330 raw330Labels permutation8 permutation5
    mixedMoment B raw330step0 raw330step0Labels = mixedMoment B raw330step1 raw330step1Labels := by
      have ha : raw330step1 = raw330step0 := by apply Matrix.ext; unfold raw330step1 raw330step0; decide +kernel
      have hl : raw330step0Labels = labelEmbedding1 ∘ raw330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw330step0 raw330step0Labels raw330step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw331 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![0, 2, -2], ![-2, 2, 0]]
def raw331Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw331step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw331 raw331Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw331 raw331Labels = mixedMoment B raw331step0 raw331step0Labels := by
      have ha : raw331step0 = (fun i j => raw331 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw331step0 raw331; decide +kernel
      have hl : raw331step0Labels = raw331Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw331 raw331Labels permutation9 permutation4
    _ = mixedMoment B node343 node343Labels := by rfl

def raw332 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw332 raw332Labels = mixedMoment B node2969 node2969Labels := by
  calc
    mixedMoment B raw332 raw332Labels = mixedMoment B raw332step0 raw332step0Labels := by
      have ha : raw332step0 = (fun i j => raw332 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw332step0 raw332; decide +kernel
      have hl : raw332step0Labels = raw332Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw332 raw332Labels permutation8 permutation5
    mixedMoment B raw332step0 raw332step0Labels = mixedMoment B raw332step1 raw332step1Labels := by
      have ha : raw332step1 = raw332step0 := by apply Matrix.ext; unfold raw332step1 raw332step0; decide +kernel
      have hl : raw332step0Labels = labelEmbedding1 ∘ raw332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw332step0 raw332step0Labels raw332step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2969 node2969Labels := by rfl

def raw333 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw333Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw333step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw333 raw333Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw333 raw333Labels = mixedMoment B raw333step0 raw333step0Labels := by
      have ha : raw333step0 = (fun i j => raw333 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw333step0 raw333; decide +kernel
      have hl : raw333step0Labels = raw333Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw333 raw333Labels permutation8 permutation4
    _ = mixedMoment B node344 node344Labels := by rfl

def raw334 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw334step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw334 raw334Labels = mixedMoment B node2982 node2982Labels := by
  calc
    mixedMoment B raw334 raw334Labels = mixedMoment B raw334step0 raw334step0Labels := by
      have ha : raw334step0 = (fun i j => raw334 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw334step0 raw334; decide +kernel
      have hl : raw334step0Labels = raw334Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw334 raw334Labels permutation152 permutation5
    mixedMoment B raw334step0 raw334step0Labels = mixedMoment B raw334step1 raw334step1Labels := by
      have ha : raw334step1 = raw334step0 := by apply Matrix.ext; unfold raw334step1 raw334step0; decide +kernel
      have hl : raw334step0Labels = labelEmbedding1 ∘ raw334step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw334step0 raw334step0Labels raw334step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2982 node2982Labels := by rfl

def raw335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw335Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw335step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw335step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw335 raw335Labels = mixedMoment B node216 node216Labels := by
  calc
    mixedMoment B raw335 raw335Labels = mixedMoment B raw335step0 raw335step0Labels := by
      have ha : raw335step0 = (fun i j => raw335 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw335step0 raw335; decide +kernel
      have hl : raw335step0Labels = raw335Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw335 raw335Labels permutation682 permutation4
    mixedMoment B raw335step0 raw335step0Labels = mixedMoment B raw335step1 raw335step1Labels := by
      have ha : raw335step1 = -raw335step0 := by apply Matrix.ext; change ∀ i j, raw335step1 i j = -(raw335step0 i j); unfold raw335step1 raw335step0; decide +kernel
      have hl : raw335step1Labels = raw335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node216 node216Labels := by rfl

def raw336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw336step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw336 raw336Labels = mixedMoment B node2986 node2986Labels := by
  calc
    mixedMoment B raw336 raw336Labels = mixedMoment B raw336step0 raw336step0Labels := by
      have ha : raw336step0 = (fun i j => raw336 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw336step0 raw336; decide +kernel
      have hl : raw336step0Labels = raw336Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw336 raw336Labels permutation152 permutation5
    mixedMoment B raw336step0 raw336step0Labels = mixedMoment B raw336step1 raw336step1Labels := by
      have ha : raw336step1 = raw336step0 := by apply Matrix.ext; unfold raw336step1 raw336step0; decide +kernel
      have hl : raw336step0Labels = labelEmbedding1 ∘ raw336step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw336step0 raw336step0Labels raw336step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2986 node2986Labels := by rfl

def raw337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw337Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw337step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw337 raw337Labels = mixedMoment B node304 node304Labels := by
  calc
    mixedMoment B raw337 raw337Labels = mixedMoment B raw337step0 raw337step0Labels := by
      have ha : raw337step0 = (fun i j => raw337 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw337step0 raw337; decide +kernel
      have hl : raw337step0Labels = raw337Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw337 raw337Labels permutation152 permutation4
    _ = mixedMoment B node304 node304Labels := by rfl

def raw338 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw338 raw338Labels = mixedMoment B node2987 node2987Labels := by
  calc
    mixedMoment B raw338 raw338Labels = mixedMoment B raw338step0 raw338step0Labels := by
      have ha : raw338step0 = (fun i j => raw338 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw338step0 raw338; decide +kernel
      have hl : raw338step0Labels = raw338Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw338 raw338Labels permutation152 permutation5
    mixedMoment B raw338step0 raw338step0Labels = mixedMoment B raw338step1 raw338step1Labels := by
      have ha : raw338step1 = raw338step0 := by apply Matrix.ext; unfold raw338step1 raw338step0; decide +kernel
      have hl : raw338step0Labels = labelEmbedding1 ∘ raw338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw338step0 raw338step0Labels raw338step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2987 node2987Labels := by rfl

def raw339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw339Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw339step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw339 raw339Labels = mixedMoment B node302 node302Labels := by
  calc
    mixedMoment B raw339 raw339Labels = mixedMoment B raw339step0 raw339step0Labels := by
      have ha : raw339step0 = (fun i j => raw339 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw339step0 raw339; decide +kernel
      have hl : raw339step0Labels = raw339Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw339 raw339Labels permutation154 permutation4
    _ = mixedMoment B node302 node302Labels := by rfl

def raw340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw340step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw340 raw340Labels = mixedMoment B node2988 node2988Labels := by
  calc
    mixedMoment B raw340 raw340Labels = mixedMoment B raw340step0 raw340step0Labels := by
      have ha : raw340step0 = (fun i j => raw340 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw340step0 raw340; decide +kernel
      have hl : raw340step0Labels = raw340Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw340 raw340Labels permutation152 permutation5
    mixedMoment B raw340step0 raw340step0Labels = mixedMoment B raw340step1 raw340step1Labels := by
      have ha : raw340step1 = raw340step0 := by apply Matrix.ext; unfold raw340step1 raw340step0; decide +kernel
      have hl : raw340step0Labels = labelEmbedding1 ∘ raw340step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw340step0 raw340step0Labels raw340step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2988 node2988Labels := by rfl

def raw341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw341Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw341step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw341 raw341Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw341 raw341Labels = mixedMoment B raw341step0 raw341step0Labels := by
      have ha : raw341step0 = (fun i j => raw341 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw341step0 raw341; decide +kernel
      have hl : raw341step0Labels = raw341Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw341 raw341Labels permutation152 permutation4
    _ = mixedMoment B node301 node301Labels := by rfl

def raw342 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw342step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw342 raw342Labels = mixedMoment B node2989 node2989Labels := by
  calc
    mixedMoment B raw342 raw342Labels = mixedMoment B raw342step0 raw342step0Labels := by
      have ha : raw342step0 = (fun i j => raw342 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw342step0 raw342; decide +kernel
      have hl : raw342step0Labels = raw342Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw342 raw342Labels permutation32 permutation5
    mixedMoment B raw342step0 raw342step0Labels = mixedMoment B raw342step1 raw342step1Labels := by
      have ha : raw342step1 = raw342step0 := by apply Matrix.ext; unfold raw342step1 raw342step0; decide +kernel
      have hl : raw342step0Labels = labelEmbedding1 ∘ raw342step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw342step0 raw342step0Labels raw342step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2989 node2989Labels := by rfl

def raw343 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw343Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw343step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw343 raw343Labels = mixedMoment B node230 node230Labels := by
  calc
    mixedMoment B raw343 raw343Labels = mixedMoment B raw343step0 raw343step0Labels := by
      have ha : raw343step0 = (fun i j => raw343 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw343step0 raw343; decide +kernel
      have hl : raw343step0Labels = raw343Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw343 raw343Labels permutation145 permutation6
    _ = mixedMoment B node230 node230Labels := by rfl

def raw344 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw344step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw344 raw344Labels = mixedMoment B node2990 node2990Labels := by
  calc
    mixedMoment B raw344 raw344Labels = mixedMoment B raw344step0 raw344step0Labels := by
      have ha : raw344step0 = (fun i j => raw344 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw344step0 raw344; decide +kernel
      have hl : raw344step0Labels = raw344Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw344 raw344Labels permutation32 permutation5
    mixedMoment B raw344step0 raw344step0Labels = mixedMoment B raw344step1 raw344step1Labels := by
      have ha : raw344step1 = raw344step0 := by apply Matrix.ext; unfold raw344step1 raw344step0; decide +kernel
      have hl : raw344step0Labels = labelEmbedding1 ∘ raw344step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw344step0 raw344step0Labels raw344step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2990 node2990Labels := by rfl

def raw345 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw345Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw345step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw345 raw345Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw345 raw345Labels = mixedMoment B raw345step0 raw345step0Labels := by
      have ha : raw345step0 = (fun i j => raw345 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw345step0 raw345; decide +kernel
      have hl : raw345step0Labels = raw345Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw345 raw345Labels permutation33 permutation4
    _ = mixedMoment B node306 node306Labels := by rfl

def raw346 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw346 raw346Labels = mixedMoment B node2991 node2991Labels := by
  calc
    mixedMoment B raw346 raw346Labels = mixedMoment B raw346step0 raw346step0Labels := by
      have ha : raw346step0 = (fun i j => raw346 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw346step0 raw346; decide +kernel
      have hl : raw346step0Labels = raw346Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw346 raw346Labels permutation32 permutation5
    mixedMoment B raw346step0 raw346step0Labels = mixedMoment B raw346step1 raw346step1Labels := by
      have ha : raw346step1 = raw346step0 := by apply Matrix.ext; unfold raw346step1 raw346step0; decide +kernel
      have hl : raw346step0Labels = labelEmbedding1 ∘ raw346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw346step0 raw346step0Labels raw346step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2991 node2991Labels := by rfl

def raw347 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw347Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw347step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw347 raw347Labels = mixedMoment B node307 node307Labels := by
  calc
    mixedMoment B raw347 raw347Labels = mixedMoment B raw347step0 raw347step0Labels := by
      have ha : raw347step0 = (fun i j => raw347 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw347step0 raw347; decide +kernel
      have hl : raw347step0Labels = raw347Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw347 raw347Labels permutation32 permutation4
    _ = mixedMoment B node307 node307Labels := by rfl

def raw348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw348 raw348Labels = mixedMoment B node2996 node2996Labels := by
  calc
    mixedMoment B raw348 raw348Labels = mixedMoment B raw348step0 raw348step0Labels := by
      have ha : raw348step0 = (fun i j => raw348 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw348step0 raw348; decide +kernel
      have hl : raw348step0Labels = raw348Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw348 raw348Labels permutation152 permutation5
    mixedMoment B raw348step0 raw348step0Labels = mixedMoment B raw348step1 raw348step1Labels := by
      have ha : raw348step1 = raw348step0 := by apply Matrix.ext; unfold raw348step1 raw348step0; decide +kernel
      have hl : raw348step0Labels = labelEmbedding1 ∘ raw348step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw348step0 raw348step0Labels raw348step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2996 node2996Labels := by rfl

def raw349 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw349Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw349step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw349 raw349Labels = mixedMoment B node310 node310Labels := by
  calc
    mixedMoment B raw349 raw349Labels = mixedMoment B raw349step0 raw349step0Labels := by
      have ha : raw349step0 = (fun i j => raw349 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw349step0 raw349; decide +kernel
      have hl : raw349step0Labels = raw349Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw349 raw349Labels permutation169 permutation4
    _ = mixedMoment B node310 node310Labels := by rfl

def raw350 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw350step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw350 raw350Labels = mixedMoment B node2997 node2997Labels := by
  calc
    mixedMoment B raw350 raw350Labels = mixedMoment B raw350step0 raw350step0Labels := by
      have ha : raw350step0 = (fun i j => raw350 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw350step0 raw350; decide +kernel
      have hl : raw350step0Labels = raw350Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw350 raw350Labels permutation32 permutation5
    mixedMoment B raw350step0 raw350step0Labels = mixedMoment B raw350step1 raw350step1Labels := by
      have ha : raw350step1 = raw350step0 := by apply Matrix.ext; unfold raw350step1 raw350step0; decide +kernel
      have hl : raw350step0Labels = labelEmbedding1 ∘ raw350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw350step0 raw350step0Labels raw350step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2997 node2997Labels := by rfl

def raw351 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw351Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw351step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw351 raw351Labels = mixedMoment B node314 node314Labels := by
  calc
    mixedMoment B raw351 raw351Labels = mixedMoment B raw351step0 raw351step0Labels := by
      have ha : raw351step0 = (fun i j => raw351 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw351step0 raw351; decide +kernel
      have hl : raw351step0Labels = raw351Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw351 raw351Labels permutation34 permutation4
    _ = mixedMoment B node314 node314Labels := by rfl

def raw352 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw352 raw352Labels = mixedMoment B node2998 node2998Labels := by
  calc
    mixedMoment B raw352 raw352Labels = mixedMoment B raw352step0 raw352step0Labels := by
      have ha : raw352step0 = (fun i j => raw352 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw352step0 raw352; decide +kernel
      have hl : raw352step0Labels = raw352Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw352 raw352Labels permutation32 permutation5
    mixedMoment B raw352step0 raw352step0Labels = mixedMoment B raw352step1 raw352step1Labels := by
      have ha : raw352step1 = raw352step0 := by apply Matrix.ext; unfold raw352step1 raw352step0; decide +kernel
      have hl : raw352step0Labels = labelEmbedding1 ∘ raw352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw352step0 raw352step0Labels raw352step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2998 node2998Labels := by rfl

def raw353 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw353Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw353step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw353 raw353Labels = mixedMoment B node312 node312Labels := by
  calc
    mixedMoment B raw353 raw353Labels = mixedMoment B raw353step0 raw353step0Labels := by
      have ha : raw353step0 = (fun i j => raw353 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw353step0 raw353; decide +kernel
      have hl : raw353step0Labels = raw353Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw353 raw353Labels permutation34 permutation4
    _ = mixedMoment B node312 node312Labels := by rfl

def raw354 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw354 raw354Labels = mixedMoment B node3003 node3003Labels := by
  calc
    mixedMoment B raw354 raw354Labels = mixedMoment B raw354step0 raw354step0Labels := by
      have ha : raw354step0 = (fun i j => raw354 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw354step0 raw354; decide +kernel
      have hl : raw354step0Labels = raw354Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw354 raw354Labels permutation32 permutation5
    mixedMoment B raw354step0 raw354step0Labels = mixedMoment B raw354step1 raw354step1Labels := by
      have ha : raw354step1 = raw354step0 := by apply Matrix.ext; unfold raw354step1 raw354step0; decide +kernel
      have hl : raw354step0Labels = labelEmbedding1 ∘ raw354step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw354step0 raw354step0Labels raw354step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3003 node3003Labels := by rfl

def raw355 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw355Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw355step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw355 raw355Labels = mixedMoment B node311 node311Labels := by
  calc
    mixedMoment B raw355 raw355Labels = mixedMoment B raw355step0 raw355step0Labels := by
      have ha : raw355step0 = (fun i j => raw355 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw355step0 raw355; decide +kernel
      have hl : raw355step0Labels = raw355Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw355 raw355Labels permutation32 permutation4
    _ = mixedMoment B node311 node311Labels := by rfl

def raw356 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 2, -3], ![-2, 2, 0]]
def raw356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw356 raw356Labels = mixedMoment B node3005 node3005Labels := by
  calc
    mixedMoment B raw356 raw356Labels = mixedMoment B raw356step0 raw356step0Labels := by
      have ha : raw356step0 = (fun i j => raw356 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw356step0 raw356; decide +kernel
      have hl : raw356step0Labels = raw356Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw356 raw356Labels permutation8 permutation5
    mixedMoment B raw356step0 raw356step0Labels = mixedMoment B raw356step1 raw356step1Labels := by
      have ha : raw356step1 = raw356step0 := by apply Matrix.ext; unfold raw356step1 raw356step0; decide +kernel
      have hl : raw356step0Labels = labelEmbedding1 ∘ raw356step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw356step0 raw356step0Labels raw356step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3005 node3005Labels := by rfl

def raw357 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 2, -3], ![-2, 2, 0]]
def raw357Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw357step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw357 raw357Labels = mixedMoment B node316 node316Labels := by
  calc
    mixedMoment B raw357 raw357Labels = mixedMoment B raw357step0 raw357step0Labels := by
      have ha : raw357step0 = (fun i j => raw357 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw357step0 raw357; decide +kernel
      have hl : raw357step0Labels = raw357Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw357 raw357Labels permutation9 permutation4
    _ = mixedMoment B node316 node316Labels := by rfl

def raw358 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw358 raw358Labels = mixedMoment B node3081 node3081Labels := by
  calc
    mixedMoment B raw358 raw358Labels = mixedMoment B raw358step0 raw358step0Labels := by
      have ha : raw358step0 = (fun i j => raw358 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw358step0 raw358; decide +kernel
      have hl : raw358step0Labels = raw358Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw358 raw358Labels permutation152 permutation5
    mixedMoment B raw358step0 raw358step0Labels = mixedMoment B raw358step1 raw358step1Labels := by
      have ha : raw358step1 = raw358step0 := by apply Matrix.ext; unfold raw358step1 raw358step0; decide +kernel
      have hl : raw358step0Labels = labelEmbedding1 ∘ raw358step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw358step0 raw358step0Labels raw358step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3081 node3081Labels := by rfl

def raw359 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw359Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw359step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw359 raw359Labels = mixedMoment B node370 node370Labels := by
  calc
    mixedMoment B raw359 raw359Labels = mixedMoment B raw359step0 raw359step0Labels := by
      have ha : raw359step0 = (fun i j => raw359 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw359step0 raw359; decide +kernel
      have hl : raw359step0Labels = raw359Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw359 raw359Labels permutation182 permutation4
    _ = mixedMoment B node370 node370Labels := by rfl

def raw360 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]
def raw360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw360 raw360Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw360 raw360Labels = mixedMoment B raw360step0 raw360step0Labels := by
      have ha : raw360step0 = (fun i j => raw360 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw360step0 raw360; decide +kernel
      have hl : raw360step0Labels = raw360Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw360 raw360Labels permutation32 permutation5
    mixedMoment B raw360step0 raw360step0Labels = mixedMoment B raw360step1 raw360step1Labels := by
      have ha : raw360step1 = raw360step0 := by apply Matrix.ext; unfold raw360step1 raw360step0; decide +kernel
      have hl : raw360step0Labels = labelEmbedding1 ∘ raw360step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw360step0 raw360step0Labels raw360step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw361 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3]]
def raw361Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw361step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw361 raw361Labels = mixedMoment B node233 node233Labels := by
  calc
    mixedMoment B raw361 raw361Labels = mixedMoment B raw361step0 raw361step0Labels := by
      have ha : raw361step0 = (fun i j => raw361 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw361step0 raw361; decide +kernel
      have hl : raw361step0Labels = raw361Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw361 raw361Labels permutation137 permutation6
    _ = mixedMoment B node233 node233Labels := by rfl

def raw362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw362 raw362Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw362 raw362Labels = mixedMoment B raw362step0 raw362step0Labels := by
      have ha : raw362step0 = (fun i j => raw362 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw362step0 raw362; decide +kernel
      have hl : raw362step0Labels = raw362Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw362 raw362Labels permutation152 permutation5
    mixedMoment B raw362step0 raw362step0Labels = mixedMoment B raw362step1 raw362step1Labels := by
      have ha : raw362step1 = raw362step0 := by apply Matrix.ext; unfold raw362step1 raw362step0; decide +kernel
      have hl : raw362step0Labels = labelEmbedding1 ∘ raw362step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw362step0 raw362step0Labels raw362step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw363Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw363step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw363 raw363Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw363 raw363Labels = mixedMoment B raw363step0 raw363step0Labels := by
      have ha : raw363step0 = (fun i j => raw363 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw363step0 raw363; decide +kernel
      have hl : raw363step0Labels = raw363Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw363 raw363Labels permutation180 permutation4
    _ = mixedMoment B node376 node376Labels := by rfl

def raw364 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw364 raw364Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw364 raw364Labels = mixedMoment B raw364step0 raw364step0Labels := by
      have ha : raw364step0 = (fun i j => raw364 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw364step0 raw364; decide +kernel
      have hl : raw364step0Labels = raw364Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw364 raw364Labels permutation32 permutation5
    mixedMoment B raw364step0 raw364step0Labels = mixedMoment B raw364step1 raw364step1Labels := by
      have ha : raw364step1 = raw364step0 := by apply Matrix.ext; unfold raw364step1 raw364step0; decide +kernel
      have hl : raw364step0Labels = labelEmbedding1 ∘ raw364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw364step0 raw364step0Labels raw364step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw365 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw365Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw365step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw365 raw365Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw365 raw365Labels = mixedMoment B raw365step0 raw365step0Labels := by
      have ha : raw365step0 = (fun i j => raw365 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw365step0 raw365; decide +kernel
      have hl : raw365step0Labels = raw365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw365 raw365Labels permutation38 permutation4
    _ = mixedMoment B node378 node378Labels := by rfl

def raw366 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw366 raw366Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw366 raw366Labels = mixedMoment B raw366step0 raw366step0Labels := by
      have ha : raw366step0 = (fun i j => raw366 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw366step0 raw366; decide +kernel
      have hl : raw366step0Labels = raw366Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw366 raw366Labels permutation32 permutation5
    mixedMoment B raw366step0 raw366step0Labels = mixedMoment B raw366step1 raw366step1Labels := by
      have ha : raw366step1 = raw366step0 := by apply Matrix.ext; unfold raw366step1 raw366step0; decide +kernel
      have hl : raw366step0Labels = labelEmbedding1 ∘ raw366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw366step0 raw366step0Labels raw366step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw367 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw367Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw367step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw367 raw367Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw367 raw367Labels = mixedMoment B raw367step0 raw367step0Labels := by
      have ha : raw367step0 = (fun i j => raw367 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw367step0 raw367; decide +kernel
      have hl : raw367step0Labels = raw367Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw367 raw367Labels permutation38 permutation4
    _ = mixedMoment B node377 node377Labels := by rfl

def raw368 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 3, -2]]
def raw368Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw368step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw368step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw368 raw368Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw368 raw368Labels = mixedMoment B raw368step0 raw368step0Labels := by
      have ha : raw368step0 = (fun i j => raw368 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw368step0 raw368; decide +kernel
      have hl : raw368step0Labels = raw368Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw368 raw368Labels permutation8 permutation5
    mixedMoment B raw368step0 raw368step0Labels = mixedMoment B raw368step1 raw368step1Labels := by
      have ha : raw368step1 = raw368step0 := by apply Matrix.ext; unfold raw368step1 raw368step0; decide +kernel
      have hl : raw368step0Labels = labelEmbedding1 ∘ raw368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw368step0 raw368step0Labels raw368step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw369 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 0, 1], ![-1, 3, -2]]
def raw369Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw369step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw369step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw369 raw369Labels = mixedMoment B node379 node379Labels := by
  calc
    mixedMoment B raw369 raw369Labels = mixedMoment B raw369step0 raw369step0Labels := by
      have ha : raw369step0 = (fun i j => raw369 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw369step0 raw369; decide +kernel
      have hl : raw369step0Labels = raw369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw369 raw369Labels permutation10 permutation4
    _ = mixedMoment B node379 node379Labels := by rfl

def raw370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw370Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw370 raw370Labels = mixedMoment B node3093 node3093Labels := by
  calc
    mixedMoment B raw370 raw370Labels = mixedMoment B raw370step0 raw370step0Labels := by
      have ha : raw370step0 = (fun i j => raw370 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw370step0 raw370; decide +kernel
      have hl : raw370step0Labels = raw370Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw370 raw370Labels permutation152 permutation5
    mixedMoment B raw370step0 raw370step0Labels = mixedMoment B raw370step1 raw370step1Labels := by
      have ha : raw370step1 = raw370step0 := by apply Matrix.ext; unfold raw370step1 raw370step0; decide +kernel
      have hl : raw370step0Labels = labelEmbedding1 ∘ raw370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw370step0 raw370step0Labels raw370step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3093 node3093Labels := by rfl

def raw371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw371Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw371step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw371 raw371Labels = mixedMoment B node360 node360Labels := by
  calc
    mixedMoment B raw371 raw371Labels = mixedMoment B raw371step0 raw371step0Labels := by
      have ha : raw371step0 = (fun i j => raw371 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw371step0 raw371; decide +kernel
      have hl : raw371step0Labels = raw371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw371 raw371Labels permutation176 permutation4
    _ = mixedMoment B node360 node360Labels := by rfl

def raw372 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw372Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw372 raw372Labels = mixedMoment B node3094 node3094Labels := by
  calc
    mixedMoment B raw372 raw372Labels = mixedMoment B raw372step0 raw372step0Labels := by
      have ha : raw372step0 = (fun i j => raw372 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw372step0 raw372; decide +kernel
      have hl : raw372step0Labels = raw372Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw372 raw372Labels permutation32 permutation5
    mixedMoment B raw372step0 raw372step0Labels = mixedMoment B raw372step1 raw372step1Labels := by
      have ha : raw372step1 = raw372step0 := by apply Matrix.ext; unfold raw372step1 raw372step0; decide +kernel
      have hl : raw372step0Labels = labelEmbedding1 ∘ raw372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw372step0 raw372step0Labels raw372step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3094 node3094Labels := by rfl

def raw373 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw373Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw373step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw373 raw373Labels = mixedMoment B node361 node361Labels := by
  calc
    mixedMoment B raw373 raw373Labels = mixedMoment B raw373step0 raw373step0Labels := by
      have ha : raw373step0 = (fun i j => raw373 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw373step0 raw373; decide +kernel
      have hl : raw373step0Labels = raw373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw373 raw373Labels permutation38 permutation4
    _ = mixedMoment B node361 node361Labels := by rfl

def raw374 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]
def raw374Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw374step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw374step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw374 raw374Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw374 raw374Labels = mixedMoment B raw374step0 raw374step0Labels := by
      have ha : raw374step0 = (fun i j => raw374 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw374step0 raw374; decide +kernel
      have hl : raw374step0Labels = raw374Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw374 raw374Labels permutation8 permutation5
    mixedMoment B raw374step0 raw374step0Labels = mixedMoment B raw374step1 raw374step1Labels := by
      have ha : raw374step1 = raw374step0 := by apply Matrix.ext; unfold raw374step1 raw374step0; decide +kernel
      have hl : raw374step0Labels = labelEmbedding1 ∘ raw374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw374step0 raw374step0Labels raw374step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw375 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-2, 0, 2], ![0, 3, -3]]
def raw375Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw375step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw375step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw375 raw375Labels = mixedMoment B node237 node237Labels := by
  calc
    mixedMoment B raw375 raw375Labels = mixedMoment B raw375step0 raw375step0Labels := by
      have ha : raw375step0 = (fun i j => raw375 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw375step0 raw375; decide +kernel
      have hl : raw375step0Labels = raw375Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw375 raw375Labels permutation29 permutation6
    _ = mixedMoment B node237 node237Labels := by rfl

def raw376 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw376Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw376 raw376Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw376 raw376Labels = mixedMoment B raw376step0 raw376step0Labels := by
      have ha : raw376step0 = (fun i j => raw376 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw376step0 raw376; decide +kernel
      have hl : raw376step0Labels = raw376Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw376 raw376Labels permutation32 permutation5
    mixedMoment B raw376step0 raw376step0Labels = mixedMoment B raw376step1 raw376step1Labels := by
      have ha : raw376step1 = raw376step0 := by apply Matrix.ext; unfold raw376step1 raw376step0; decide +kernel
      have hl : raw376step0Labels = labelEmbedding1 ∘ raw376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw376step0 raw376step0Labels raw376step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw377 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw377Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw377step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw377 raw377Labels = mixedMoment B node401 node401Labels := by
  calc
    mixedMoment B raw377 raw377Labels = mixedMoment B raw377step0 raw377step0Labels := by
      have ha : raw377step0 = (fun i j => raw377 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw377step0 raw377; decide +kernel
      have hl : raw377step0Labels = raw377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw377 raw377Labels permutation36 permutation4
    _ = mixedMoment B node401 node401Labels := by rfl

def raw378 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw378Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw378 raw378Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw378 raw378Labels = mixedMoment B raw378step0 raw378step0Labels := by
      have ha : raw378step0 = (fun i j => raw378 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw378step0 raw378; decide +kernel
      have hl : raw378step0Labels = raw378Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw378 raw378Labels permutation32 permutation5
    mixedMoment B raw378step0 raw378step0Labels = mixedMoment B raw378step1 raw378step1Labels := by
      have ha : raw378step1 = raw378step0 := by apply Matrix.ext; unfold raw378step1 raw378step0; decide +kernel
      have hl : raw378step0Labels = labelEmbedding1 ∘ raw378step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw378step0 raw378step0Labels raw378step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw379 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw379Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw379step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw379 raw379Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw379 raw379Labels = mixedMoment B raw379step0 raw379step0Labels := by
      have ha : raw379step0 = (fun i j => raw379 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw379step0 raw379; decide +kernel
      have hl : raw379step0Labels = raw379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw379 raw379Labels permutation35 permutation4
    _ = mixedMoment B node403 node403Labels := by rfl

def raw380 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw380Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw380step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw380step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw380 raw380Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw380 raw380Labels = mixedMoment B raw380step0 raw380step0Labels := by
      have ha : raw380step0 = (fun i j => raw380 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw380step0 raw380; decide +kernel
      have hl : raw380step0Labels = raw380Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw380 raw380Labels permutation8 permutation5
    mixedMoment B raw380step0 raw380step0Labels = mixedMoment B raw380step1 raw380step1Labels := by
      have ha : raw380step1 = raw380step0 := by apply Matrix.ext; unfold raw380step1 raw380step0; decide +kernel
      have hl : raw380step0Labels = labelEmbedding1 ∘ raw380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw380step0 raw380step0Labels raw380step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw381 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw381Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw381step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw381step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw381 raw381Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw381 raw381Labels = mixedMoment B raw381step0 raw381step0Labels := by
      have ha : raw381step0 = (fun i j => raw381 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw381step0 raw381; decide +kernel
      have hl : raw381step0Labels = raw381Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw381 raw381Labels permutation8 permutation4
    _ = mixedMoment B node405 node405Labels := by rfl

def raw382 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw382Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw382step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw382step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw382 raw382Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw382 raw382Labels = mixedMoment B raw382step0 raw382step0Labels := by
      have ha : raw382step0 = (fun i j => raw382 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw382step0 raw382; decide +kernel
      have hl : raw382step0Labels = raw382Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw382 raw382Labels permutation8 permutation5
    mixedMoment B raw382step0 raw382step0Labels = mixedMoment B raw382step1 raw382step1Labels := by
      have ha : raw382step1 = raw382step0 := by apply Matrix.ext; unfold raw382step1 raw382step0; decide +kernel
      have hl : raw382step0Labels = labelEmbedding1 ∘ raw382step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw382step0 raw382step0Labels raw382step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw383 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw383Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw383step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw383step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw383 raw383Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw383 raw383Labels = mixedMoment B raw383step0 raw383step0Labels := by
      have ha : raw383step0 = (fun i j => raw383 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw383step0 raw383; decide +kernel
      have hl : raw383step0Labels = raw383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw383 raw383Labels permutation8 permutation4
    _ = mixedMoment B node404 node404Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
