import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38016 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw38016Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38016step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38016step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38016 raw38016Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw38016 raw38016Labels = mixedMoment B raw38016step0 raw38016step0Labels := by
      have ha : raw38016step0 = (fun i j => raw38016 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38016step0 raw38016; decide +kernel
      have hl : raw38016step0Labels = raw38016Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38016 raw38016Labels permutation8 permutation3
    _ = mixedMoment B node405 node405Labels := by rfl

def raw38017 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw38017Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38017step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38017step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38017 raw38017Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw38017 raw38017Labels = mixedMoment B raw38017step0 raw38017step0Labels := by
      have ha : raw38017step0 = (fun i j => raw38017 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38017step0 raw38017; decide +kernel
      have hl : raw38017step0Labels = raw38017Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38017 raw38017Labels permutation8 permutation3
    _ = mixedMoment B node404 node404Labels := by rfl

def raw38018 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw38018Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38018step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw38018step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38018 raw38018Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw38018 raw38018Labels = mixedMoment B raw38018step0 raw38018step0Labels := by
      have ha : raw38018step0 = (fun i j => raw38018 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38018step0 raw38018; decide +kernel
      have hl : raw38018step0Labels = raw38018Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38018 raw38018Labels permutation8 permutation3
    _ = mixedMoment B node402 node402Labels := by rfl

def raw38019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw38019Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38019step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38019 raw38019Labels = mixedMoment B node371 node371Labels := by
  calc
    mixedMoment B raw38019 raw38019Labels = mixedMoment B raw38019step0 raw38019step0Labels := by
      have ha : raw38019step0 = (fun i j => raw38019 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38019step0 raw38019; decide +kernel
      have hl : raw38019step0Labels = raw38019Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38019 raw38019Labels permutation155 permutation3
    _ = mixedMoment B node371 node371Labels := by rfl

def raw38020 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw38020Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38020step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38020 raw38020Labels = mixedMoment B node372 node372Labels := by
  calc
    mixedMoment B raw38020 raw38020Labels = mixedMoment B raw38020step0 raw38020step0Labels := by
      have ha : raw38020step0 = (fun i j => raw38020 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38020step0 raw38020; decide +kernel
      have hl : raw38020step0Labels = raw38020Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38020 raw38020Labels permutation32 permutation3
    _ = mixedMoment B node372 node372Labels := by rfl

def raw38021 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw38021Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38021step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38021 raw38021Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw38021 raw38021Labels = mixedMoment B raw38021step0 raw38021step0Labels := by
      have ha : raw38021step0 = (fun i j => raw38021 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38021step0 raw38021; decide +kernel
      have hl : raw38021step0Labels = raw38021Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38021 raw38021Labels permutation37 permutation3
    _ = mixedMoment B node387 node387Labels := by rfl

def raw38022 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw38022Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38022step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw38022step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38022 raw38022Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw38022 raw38022Labels = mixedMoment B raw38022step0 raw38022step0Labels := by
      have ha : raw38022step0 = (fun i j => raw38022 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38022step0 raw38022; decide +kernel
      have hl : raw38022step0Labels = raw38022Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38022 raw38022Labels permutation8 permutation3
    _ = mixedMoment B node390 node390Labels := by rfl

def raw38023 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw38023Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38023step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw38023step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38023 raw38023Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw38023 raw38023Labels = mixedMoment B raw38023step0 raw38023step0Labels := by
      have ha : raw38023step0 = (fun i j => raw38023 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38023step0 raw38023; decide +kernel
      have hl : raw38023step0Labels = raw38023Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38023 raw38023Labels permutation8 permutation3
    _ = mixedMoment B node388 node388Labels := by rfl

def raw38024 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw38024Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38024step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38024 raw38024Labels = mixedMoment B node368 node368Labels := by
  calc
    mixedMoment B raw38024 raw38024Labels = mixedMoment B raw38024step0 raw38024step0Labels := by
      have ha : raw38024step0 = (fun i j => raw38024 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38024step0 raw38024; decide +kernel
      have hl : raw38024step0Labels = raw38024Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38024 raw38024Labels permutation35 permutation3
    _ = mixedMoment B node368 node368Labels := by rfl

def raw38025 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw38025Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38025step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw38025step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38025 raw38025Labels = mixedMoment B node369 node369Labels := by
  calc
    mixedMoment B raw38025 raw38025Labels = mixedMoment B raw38025step0 raw38025step0Labels := by
      have ha : raw38025step0 = (fun i j => raw38025 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38025step0 raw38025; decide +kernel
      have hl : raw38025step0Labels = raw38025Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38025 raw38025Labels permutation8 permutation3
    _ = mixedMoment B node369 node369Labels := by rfl

def raw38026 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw38026Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38026step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw38026step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38026 raw38026Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw38026 raw38026Labels = mixedMoment B raw38026step0 raw38026step0Labels := by
      have ha : raw38026step0 = (fun i j => raw38026 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38026step0 raw38026; decide +kernel
      have hl : raw38026step0Labels = raw38026Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38026 raw38026Labels permutation13 permutation3
    _ = mixedMoment B node414 node414Labels := by rfl

def raw38027 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38027Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38027step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38027step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38027 raw38027Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw38027 raw38027Labels = mixedMoment B raw38027step0 raw38027step0Labels := by
      have ha : raw38027step0 = (fun i j => raw38027 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38027step0 raw38027; decide +kernel
      have hl : raw38027step0Labels = raw38027Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38027 raw38027Labels permutation11 permutation3
    _ = mixedMoment B node416 node416Labels := by rfl

def raw38028 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw38028Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38028step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw38028step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38028 raw38028Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw38028 raw38028Labels = mixedMoment B raw38028step0 raw38028step0Labels := by
      have ha : raw38028step0 = (fun i j => raw38028 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38028step0 raw38028; decide +kernel
      have hl : raw38028step0Labels = raw38028Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38028 raw38028Labels permutation2 permutation3
    _ = mixedMoment B node420 node420Labels := by rfl

def raw38029 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw38029Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38029step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw38029step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38029 raw38029Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw38029 raw38029Labels = mixedMoment B raw38029step0 raw38029step0Labels := by
      have ha : raw38029step0 = (fun i j => raw38029 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38029step0 raw38029; decide +kernel
      have hl : raw38029step0Labels = raw38029Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38029 raw38029Labels permutation2 permutation3
    _ = mixedMoment B node415 node415Labels := by rfl

def raw38030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38030Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38030step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38030 raw38030Labels = mixedMoment B node174 node174Labels := by
  calc
    mixedMoment B raw38030 raw38030Labels = mixedMoment B raw38030step0 raw38030step0Labels := by
      have ha : raw38030step0 = (fun i j => raw38030 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38030step0 raw38030; decide +kernel
      have hl : raw38030step0Labels = raw38030Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38030 raw38030Labels permutation164 permutation3
    _ = mixedMoment B node174 node174Labels := by rfl

def raw38031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38031Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38031step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38031 raw38031Labels = mixedMoment B node171 node171Labels := by
  calc
    mixedMoment B raw38031 raw38031Labels = mixedMoment B raw38031step0 raw38031step0Labels := by
      have ha : raw38031step0 = (fun i j => raw38031 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38031step0 raw38031; decide +kernel
      have hl : raw38031step0Labels = raw38031Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38031 raw38031Labels permutation160 permutation3
    _ = mixedMoment B node171 node171Labels := by rfl

def raw38032 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw38032Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38032step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38032 raw38032Labels = mixedMoment B node182 node182Labels := by
  calc
    mixedMoment B raw38032 raw38032Labels = mixedMoment B raw38032step0 raw38032step0Labels := by
      have ha : raw38032step0 = (fun i j => raw38032 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38032step0 raw38032; decide +kernel
      have hl : raw38032step0Labels = raw38032Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38032 raw38032Labels permutation33 permutation3
    _ = mixedMoment B node182 node182Labels := by rfl

def raw38033 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw38033Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38033step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38033 raw38033Labels = mixedMoment B node183 node183Labels := by
  calc
    mixedMoment B raw38033 raw38033Labels = mixedMoment B raw38033step0 raw38033step0Labels := by
      have ha : raw38033step0 = (fun i j => raw38033 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38033step0 raw38033; decide +kernel
      have hl : raw38033step0Labels = raw38033Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38033 raw38033Labels permutation32 permutation3
    _ = mixedMoment B node183 node183Labels := by rfl

def raw38034 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw38034Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38034step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38034 raw38034Labels = mixedMoment B node173 node173Labels := by
  calc
    mixedMoment B raw38034 raw38034Labels = mixedMoment B raw38034step0 raw38034step0Labels := by
      have ha : raw38034step0 = (fun i j => raw38034 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38034step0 raw38034; decide +kernel
      have hl : raw38034step0Labels = raw38034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38034 raw38034Labels permutation32 permutation3
    _ = mixedMoment B node173 node173Labels := by rfl

def raw38035 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38035Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38035step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38035 raw38035Labels = mixedMoment B node178 node178Labels := by
  calc
    mixedMoment B raw38035 raw38035Labels = mixedMoment B raw38035step0 raw38035step0Labels := by
      have ha : raw38035step0 = (fun i j => raw38035 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38035step0 raw38035; decide +kernel
      have hl : raw38035step0Labels = raw38035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38035 raw38035Labels permutation33 permutation3
    _ = mixedMoment B node178 node178Labels := by rfl

def raw38036 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, 0, -2], ![3, -3, 0]]
def raw38036Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38036step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw38036step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38036 raw38036Labels = mixedMoment B node185 node185Labels := by
  calc
    mixedMoment B raw38036 raw38036Labels = mixedMoment B raw38036step0 raw38036step0Labels := by
      have ha : raw38036step0 = (fun i j => raw38036 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38036step0 raw38036; decide +kernel
      have hl : raw38036step0Labels = raw38036Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38036 raw38036Labels permutation8 permutation3
    _ = mixedMoment B node185 node185Labels := by rfl

def raw38037 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw38037Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw38037step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38037step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38037 raw38037Labels = mixedMoment B node219 node219Labels := by
  calc
    mixedMoment B raw38037 raw38037Labels = mixedMoment B raw38037step0 raw38037step0Labels := by
      have ha : raw38037step0 = (fun i j => raw38037 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38037step0 raw38037; decide +kernel
      have hl : raw38037step0Labels = raw38037Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38037 raw38037Labels permutation151 permutation3
    mixedMoment B raw38037step0 raw38037step0Labels = mixedMoment B raw38037step1 raw38037step1Labels := by
      have ha : raw38037step1 = -raw38037step0 := by apply Matrix.ext; change ∀ i j, raw38037step1 i j = -(raw38037step0 i j); unfold raw38037step1 raw38037step0; decide +kernel
      have hl : raw38037step1Labels = raw38037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node219 node219Labels := by rfl

def raw38038 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38038Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38038step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38038step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38038 raw38038Labels = mixedMoment B node231 node231Labels := by
  calc
    mixedMoment B raw38038 raw38038Labels = mixedMoment B raw38038step0 raw38038step0Labels := by
      have ha : raw38038step0 = (fun i j => raw38038 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38038step0 raw38038; decide +kernel
      have hl : raw38038step0Labels = raw38038Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38038 raw38038Labels permutation39 permutation5
    mixedMoment B raw38038step0 raw38038step0Labels = mixedMoment B raw38038step1 raw38038step1Labels := by
      have ha : raw38038step1 = -raw38038step0 := by apply Matrix.ext; change ∀ i j, raw38038step1 i j = -(raw38038step0 i j); unfold raw38038step1 raw38038step0; decide +kernel
      have hl : raw38038step1Labels = raw38038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node231 node231Labels := by rfl

def raw38039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38039Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38039step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38039 raw38039Labels = mixedMoment B node243 node243Labels := by
  calc
    mixedMoment B raw38039 raw38039Labels = mixedMoment B raw38039step0 raw38039step0Labels := by
      have ha : raw38039step0 = (fun i j => raw38039 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38039step0 raw38039; decide +kernel
      have hl : raw38039step0Labels = raw38039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38039 raw38039Labels permutation168 permutation3
    _ = mixedMoment B node243 node243Labels := by rfl

def raw38040 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38040Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38040step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38040 raw38040Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw38040 raw38040Labels = mixedMoment B raw38040step0 raw38040step0Labels := by
      have ha : raw38040step0 = (fun i j => raw38040 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38040step0 raw38040; decide +kernel
      have hl : raw38040step0Labels = raw38040Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38040 raw38040Labels permutation32 permutation3
    _ = mixedMoment B node248 node248Labels := by rfl

def raw38041 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38041Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38041step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38041 raw38041Labels = mixedMoment B node245 node245Labels := by
  calc
    mixedMoment B raw38041 raw38041Labels = mixedMoment B raw38041step0 raw38041step0Labels := by
      have ha : raw38041step0 = (fun i j => raw38041 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38041step0 raw38041; decide +kernel
      have hl : raw38041step0Labels = raw38041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38041 raw38041Labels permutation34 permutation3
    _ = mixedMoment B node245 node245Labels := by rfl

def raw38042 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38042Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38042step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38042 raw38042Labels = mixedMoment B node244 node244Labels := by
  calc
    mixedMoment B raw38042 raw38042Labels = mixedMoment B raw38042step0 raw38042step0Labels := by
      have ha : raw38042step0 = (fun i j => raw38042 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38042step0 raw38042; decide +kernel
      have hl : raw38042step0Labels = raw38042Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38042 raw38042Labels permutation32 permutation3
    _ = mixedMoment B node244 node244Labels := by rfl

def raw38043 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw38043Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38043step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38043step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38043 raw38043Labels = mixedMoment B node241 node241Labels := by
  calc
    mixedMoment B raw38043 raw38043Labels = mixedMoment B raw38043step0 raw38043step0Labels := by
      have ha : raw38043step0 = (fun i j => raw38043 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38043step0 raw38043; decide +kernel
      have hl : raw38043step0Labels = raw38043Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38043 raw38043Labels permutation8 permutation3
    _ = mixedMoment B node241 node241Labels := by rfl

def raw38044 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw38044Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38044step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38044step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38044 raw38044Labels = mixedMoment B node251 node251Labels := by
  calc
    mixedMoment B raw38044 raw38044Labels = mixedMoment B raw38044step0 raw38044step0Labels := by
      have ha : raw38044step0 = (fun i j => raw38044 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38044step0 raw38044; decide +kernel
      have hl : raw38044step0Labels = raw38044Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38044 raw38044Labels permutation9 permutation3
    _ = mixedMoment B node251 node251Labels := by rfl

def raw38045 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw38045Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38045step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38045step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38045 raw38045Labels = mixedMoment B node252 node252Labels := by
  calc
    mixedMoment B raw38045 raw38045Labels = mixedMoment B raw38045step0 raw38045step0Labels := by
      have ha : raw38045step0 = (fun i j => raw38045 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38045step0 raw38045; decide +kernel
      have hl : raw38045step0Labels = raw38045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38045 raw38045Labels permutation8 permutation3
    _ = mixedMoment B node252 node252Labels := by rfl

def raw38046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw38046Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38046step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38046 raw38046Labels = mixedMoment B node209 node209Labels := by
  calc
    mixedMoment B raw38046 raw38046Labels = mixedMoment B raw38046step0 raw38046step0Labels := by
      have ha : raw38046step0 = (fun i j => raw38046 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38046step0 raw38046; decide +kernel
      have hl : raw38046step0Labels = raw38046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38046 raw38046Labels permutation153 permutation3
    _ = mixedMoment B node209 node209Labels := by rfl

def raw38047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw38047Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38047step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38047 raw38047Labels = mixedMoment B node210 node210Labels := by
  calc
    mixedMoment B raw38047 raw38047Labels = mixedMoment B raw38047step0 raw38047step0Labels := by
      have ha : raw38047step0 = (fun i j => raw38047 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38047step0 raw38047; decide +kernel
      have hl : raw38047step0Labels = raw38047Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38047 raw38047Labels permutation152 permutation3
    _ = mixedMoment B node210 node210Labels := by rfl

def raw38048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw38048Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38048step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38048 raw38048Labels = mixedMoment B node205 node205Labels := by
  calc
    mixedMoment B raw38048 raw38048Labels = mixedMoment B raw38048step0 raw38048step0Labels := by
      have ha : raw38048step0 = (fun i j => raw38048 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38048step0 raw38048; decide +kernel
      have hl : raw38048step0Labels = raw38048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38048 raw38048Labels permutation152 permutation3
    _ = mixedMoment B node205 node205Labels := by rfl

def raw38049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw38049Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38049step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38049 raw38049Labels = mixedMoment B node215 node215Labels := by
  calc
    mixedMoment B raw38049 raw38049Labels = mixedMoment B raw38049step0 raw38049step0Labels := by
      have ha : raw38049step0 = (fun i j => raw38049 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38049step0 raw38049; decide +kernel
      have hl : raw38049step0Labels = raw38049Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38049 raw38049Labels permutation158 permutation3
    _ = mixedMoment B node215 node215Labels := by rfl

def raw38050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38050Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38050step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38050 raw38050Labels = mixedMoment B node217 node217Labels := by
  calc
    mixedMoment B raw38050 raw38050Labels = mixedMoment B raw38050step0 raw38050step0Labels := by
      have ha : raw38050step0 = (fun i j => raw38050 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38050step0 raw38050; decide +kernel
      have hl : raw38050step0Labels = raw38050Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38050 raw38050Labels permutation159 permutation3
    _ = mixedMoment B node217 node217Labels := by rfl

def raw38051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38051Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38051step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38051 raw38051Labels = mixedMoment B node223 node223Labels := by
  calc
    mixedMoment B raw38051 raw38051Labels = mixedMoment B raw38051step0 raw38051step0Labels := by
      have ha : raw38051step0 = (fun i j => raw38051 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38051step0 raw38051; decide +kernel
      have hl : raw38051step0Labels = raw38051Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38051 raw38051Labels permutation152 permutation3
    _ = mixedMoment B node223 node223Labels := by rfl

def raw38052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38052Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38052step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38052 raw38052Labels = mixedMoment B node221 node221Labels := by
  calc
    mixedMoment B raw38052 raw38052Labels = mixedMoment B raw38052step0 raw38052step0Labels := by
      have ha : raw38052step0 = (fun i j => raw38052 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38052step0 raw38052; decide +kernel
      have hl : raw38052step0Labels = raw38052Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38052 raw38052Labels permutation154 permutation3
    _ = mixedMoment B node221 node221Labels := by rfl

def raw38053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38053Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38053step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38053 raw38053Labels = mixedMoment B node220 node220Labels := by
  calc
    mixedMoment B raw38053 raw38053Labels = mixedMoment B raw38053step0 raw38053step0Labels := by
      have ha : raw38053step0 = (fun i j => raw38053 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38053step0 raw38053; decide +kernel
      have hl : raw38053step0Labels = raw38053Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38053 raw38053Labels permutation152 permutation3
    _ = mixedMoment B node220 node220Labels := by rfl

def raw38054 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw38054Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38054step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38054 raw38054Labels = mixedMoment B node226 node226Labels := by
  calc
    mixedMoment B raw38054 raw38054Labels = mixedMoment B raw38054step0 raw38054step0Labels := by
      have ha : raw38054step0 = (fun i j => raw38054 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38054step0 raw38054; decide +kernel
      have hl : raw38054step0Labels = raw38054Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38054 raw38054Labels permutation33 permutation3
    _ = mixedMoment B node226 node226Labels := by rfl

def raw38055 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw38055Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38055step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38055 raw38055Labels = mixedMoment B node227 node227Labels := by
  calc
    mixedMoment B raw38055 raw38055Labels = mixedMoment B raw38055step0 raw38055step0Labels := by
      have ha : raw38055step0 = (fun i j => raw38055 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38055step0 raw38055; decide +kernel
      have hl : raw38055step0Labels = raw38055Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38055 raw38055Labels permutation32 permutation3
    _ = mixedMoment B node227 node227Labels := by rfl

def raw38056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38056Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38056step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38056 raw38056Labels = mixedMoment B node232 node232Labels := by
  calc
    mixedMoment B raw38056 raw38056Labels = mixedMoment B raw38056step0 raw38056step0Labels := by
      have ha : raw38056step0 = (fun i j => raw38056 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38056step0 raw38056; decide +kernel
      have hl : raw38056step0Labels = raw38056Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38056 raw38056Labels permutation169 permutation3
    _ = mixedMoment B node232 node232Labels := by rfl

def raw38057 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw38057Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38057step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38057 raw38057Labels = mixedMoment B node235 node235Labels := by
  calc
    mixedMoment B raw38057 raw38057Labels = mixedMoment B raw38057step0 raw38057step0Labels := by
      have ha : raw38057step0 = (fun i j => raw38057 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38057step0 raw38057; decide +kernel
      have hl : raw38057step0Labels = raw38057Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38057 raw38057Labels permutation34 permutation3
    _ = mixedMoment B node235 node235Labels := by rfl

def raw38058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw38058Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38058step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38058 raw38058Labels = mixedMoment B node234 node234Labels := by
  calc
    mixedMoment B raw38058 raw38058Labels = mixedMoment B raw38058step0 raw38058step0Labels := by
      have ha : raw38058step0 = (fun i j => raw38058 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38058step0 raw38058; decide +kernel
      have hl : raw38058step0Labels = raw38058Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38058 raw38058Labels permutation34 permutation3
    _ = mixedMoment B node234 node234Labels := by rfl

def raw38059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38059Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw38059step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38059step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38059 raw38059Labels = mixedMoment B node200 node200Labels := by
  calc
    mixedMoment B raw38059 raw38059Labels = mixedMoment B raw38059step0 raw38059step0Labels := by
      have ha : raw38059step0 = (fun i j => raw38059 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38059step0 raw38059; decide +kernel
      have hl : raw38059step0Labels = raw38059Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38059 raw38059Labels permutation160 permutation5
    mixedMoment B raw38059step0 raw38059step0Labels = mixedMoment B raw38059step1 raw38059step1Labels := by
      have ha : raw38059step1 = -raw38059step0 := by apply Matrix.ext; change ∀ i j, raw38059step1 i j = -(raw38059step0 i j); unfold raw38059step1 raw38059step0; decide +kernel
      have hl : raw38059step1Labels = raw38059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node200 node200Labels := by rfl

def raw38060 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw38060Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38060step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38060 raw38060Labels = mixedMoment B node204 node204Labels := by
  calc
    mixedMoment B raw38060 raw38060Labels = mixedMoment B raw38060step0 raw38060step0Labels := by
      have ha : raw38060step0 = (fun i j => raw38060 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38060step0 raw38060; decide +kernel
      have hl : raw38060step0Labels = raw38060Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38060 raw38060Labels permutation33 permutation3
    _ = mixedMoment B node204 node204Labels := by rfl

def raw38061 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38061Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw38061step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38061step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38061 raw38061Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw38061 raw38061Labels = mixedMoment B raw38061step0 raw38061step0Labels := by
      have ha : raw38061step0 = (fun i j => raw38061 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38061step0 raw38061; decide +kernel
      have hl : raw38061step0Labels = raw38061Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38061 raw38061Labels permutation49 permutation5
    mixedMoment B raw38061step0 raw38061step0Labels = mixedMoment B raw38061step1 raw38061step1Labels := by
      have ha : raw38061step1 = -raw38061step0 := by apply Matrix.ext; change ∀ i j, raw38061step1 i j = -(raw38061step0 i j); unfold raw38061step1 raw38061step0; decide +kernel
      have hl : raw38061step1Labels = raw38061step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node261 node261Labels := by rfl

def raw38062 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw38062Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38062step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw38062step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38062 raw38062Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw38062 raw38062Labels = mixedMoment B raw38062step0 raw38062step0Labels := by
      have ha : raw38062step0 = (fun i j => raw38062 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38062step0 raw38062; decide +kernel
      have hl : raw38062step0Labels = raw38062Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38062 raw38062Labels permutation8 permutation3
    _ = mixedMoment B node269 node269Labels := by rfl

def raw38063 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw38063Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38063step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw38063step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38063step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38063 raw38063Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw38063 raw38063Labels = mixedMoment B raw38063step0 raw38063step0Labels := by
      have ha : raw38063step0 = (fun i j => raw38063 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38063step0 raw38063; decide +kernel
      have hl : raw38063step0Labels = raw38063Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38063 raw38063Labels permutation11 permutation5
    mixedMoment B raw38063step0 raw38063step0Labels = mixedMoment B raw38063step1 raw38063step1Labels := by
      have ha : raw38063step1 = -raw38063step0 := by apply Matrix.ext; change ∀ i j, raw38063step1 i j = -(raw38063step0 i j); unfold raw38063step1 raw38063step0; decide +kernel
      have hl : raw38063step1Labels = raw38063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

def raw38064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38064Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38064step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38064 raw38064Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw38064 raw38064Labels = mixedMoment B raw38064step0 raw38064step0Labels := by
      have ha : raw38064step0 = (fun i j => raw38064 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38064step0 raw38064; decide +kernel
      have hl : raw38064step0Labels = raw38064Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38064 raw38064Labels permutation155 permutation3
    _ = mixedMoment B node259 node259Labels := by rfl

def raw38065 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw38065Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38065step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38065 raw38065Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw38065 raw38065Labels = mixedMoment B raw38065step0 raw38065step0Labels := by
      have ha : raw38065step0 = (fun i j => raw38065 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38065step0 raw38065; decide +kernel
      have hl : raw38065step0Labels = raw38065Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38065 raw38065Labels permutation32 permutation3
    _ = mixedMoment B node260 node260Labels := by rfl

def raw38066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38066Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw38066step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38066step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38066 raw38066Labels = mixedMoment B node424 node424Labels := by
  calc
    mixedMoment B raw38066 raw38066Labels = mixedMoment B raw38066step0 raw38066step0Labels := by
      have ha : raw38066step0 = (fun i j => raw38066 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38066step0 raw38066; decide +kernel
      have hl : raw38066step0Labels = raw38066Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38066 raw38066Labels permutation588 permutation3
    mixedMoment B raw38066step0 raw38066step0Labels = mixedMoment B raw38066step1 raw38066step1Labels := by
      have ha : raw38066step1 = -raw38066step0 := by apply Matrix.ext; change ∀ i j, raw38066step1 i j = -(raw38066step0 i j); unfold raw38066step1 raw38066step0; decide +kernel
      have hl : raw38066step1Labels = raw38066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node424 node424Labels := by rfl

def raw38067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw38067Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38067step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38067 raw38067Labels = mixedMoment B node442 node442Labels := by
  calc
    mixedMoment B raw38067 raw38067Labels = mixedMoment B raw38067step0 raw38067step0Labels := by
      have ha : raw38067step0 = (fun i j => raw38067 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38067step0 raw38067; decide +kernel
      have hl : raw38067step0Labels = raw38067Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38067 raw38067Labels permutation265 permutation3
    _ = mixedMoment B node442 node442Labels := by rfl

def raw38068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw38068Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38068step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38068 raw38068Labels = mixedMoment B node441 node441Labels := by
  calc
    mixedMoment B raw38068 raw38068Labels = mixedMoment B raw38068step0 raw38068step0Labels := by
      have ha : raw38068step0 = (fun i j => raw38068 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38068step0 raw38068; decide +kernel
      have hl : raw38068step0Labels = raw38068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38068 raw38068Labels permutation267 permutation3
    _ = mixedMoment B node441 node441Labels := by rfl

def raw38069 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38069Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw38069step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38069step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38069 raw38069Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw38069 raw38069Labels = mixedMoment B raw38069step0 raw38069step0Labels := by
      have ha : raw38069step0 = (fun i j => raw38069 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38069step0 raw38069; decide +kernel
      have hl : raw38069step0Labels = raw38069Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38069 raw38069Labels permutation126 permutation3
    mixedMoment B raw38069step0 raw38069step0Labels = mixedMoment B raw38069step1 raw38069step1Labels := by
      have ha : raw38069step1 = -raw38069step0 := by apply Matrix.ext; change ∀ i j, raw38069step1 i j = -(raw38069step0 i j); unfold raw38069step1 raw38069step0; decide +kernel
      have hl : raw38069step1Labels = raw38069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node432 node432Labels := by rfl

def raw38070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38070Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38070step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38070 raw38070Labels = mixedMoment B node445 node445Labels := by
  calc
    mixedMoment B raw38070 raw38070Labels = mixedMoment B raw38070step0 raw38070step0Labels := by
      have ha : raw38070step0 = (fun i j => raw38070 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38070step0 raw38070; decide +kernel
      have hl : raw38070step0Labels = raw38070Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38070 raw38070Labels permutation283 permutation3
    _ = mixedMoment B node445 node445Labels := by rfl

def raw38071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38071Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38071 raw38071Labels = mixedMoment B node448 node448Labels := by
  calc
    _ = mixedMoment B node448 node448Labels := by rfl

def raw38072 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38072Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38072 raw38072Labels = mixedMoment B node449 node449Labels := by
  calc
    _ = mixedMoment B node449 node449Labels := by rfl

def raw38073 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38073Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38073 raw38073Labels = mixedMoment B node450 node450Labels := by
  calc
    _ = mixedMoment B node450 node450Labels := by rfl

def raw38074 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw38074Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38074step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38074 raw38074Labels = mixedMoment B node446 node446Labels := by
  calc
    mixedMoment B raw38074 raw38074Labels = mixedMoment B raw38074step0 raw38074step0Labels := by
      have ha : raw38074step0 = (fun i j => raw38074 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38074step0 raw38074; decide +kernel
      have hl : raw38074step0Labels = raw38074Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38074 raw38074Labels permutation58 permutation3
    _ = mixedMoment B node446 node446Labels := by rfl

def raw38075 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38075Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38075step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38075 raw38075Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw38075 raw38075Labels = mixedMoment B raw38075step0 raw38075step0Labels := by
      have ha : raw38075step0 = (fun i j => raw38075 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38075step0 raw38075; decide +kernel
      have hl : raw38075step0Labels = raw38075Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38075 raw38075Labels permutation56 permutation3
    _ = mixedMoment B node449 node449Labels := by rfl

def raw38076 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw38076Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38076 raw38076Labels = mixedMoment B node451 node451Labels := by
  calc
    _ = mixedMoment B node451 node451Labels := by rfl

def raw38077 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw38077Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38077 raw38077Labels = mixedMoment B node452 node452Labels := by
  calc
    _ = mixedMoment B node452 node452Labels := by rfl

def raw38078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38078Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw38078step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38078step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38078 raw38078Labels = mixedMoment B node431 node431Labels := by
  calc
    mixedMoment B raw38078 raw38078Labels = mixedMoment B raw38078step0 raw38078step0Labels := by
      have ha : raw38078step0 = (fun i j => raw38078 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38078step0 raw38078; decide +kernel
      have hl : raw38078step0Labels = raw38078Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38078 raw38078Labels permutation587 permutation3
    mixedMoment B raw38078step0 raw38078step0Labels = mixedMoment B raw38078step1 raw38078step1Labels := by
      have ha : raw38078step1 = -raw38078step0 := by apply Matrix.ext; change ∀ i j, raw38078step1 i j = -(raw38078step0 i j); unfold raw38078step1 raw38078step0; decide +kernel
      have hl : raw38078step1Labels = raw38078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node431 node431Labels := by rfl

def raw38079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38079Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38079 raw38079Labels = mixedMoment B node471 node471Labels := by
  calc
    _ = mixedMoment B node471 node471Labels := by rfl

def raw38080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38080Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38080 raw38080Labels = mixedMoment B node472 node472Labels := by
  calc
    _ = mixedMoment B node472 node472Labels := by rfl

def raw38081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw38081Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw38081step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38081step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38081 raw38081Labels = mixedMoment B node459 node459Labels := by
  calc
    mixedMoment B raw38081 raw38081Labels = mixedMoment B raw38081step0 raw38081step0Labels := by
      have ha : raw38081step0 = (fun i j => raw38081 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38081step0 raw38081; decide +kernel
      have hl : raw38081step0Labels = raw38081Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38081 raw38081Labels permutation662 permutation3
    mixedMoment B raw38081step0 raw38081step0Labels = mixedMoment B raw38081step1 raw38081step1Labels := by
      have ha : raw38081step1 = -raw38081step0 := by apply Matrix.ext; change ∀ i j, raw38081step1 i j = -(raw38081step0 i j); unfold raw38081step1 raw38081step0; decide +kernel
      have hl : raw38081step1Labels = raw38081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node459 node459Labels := by rfl

def raw38082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38082Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38082 raw38082Labels = mixedMoment B node473 node473Labels := by
  calc
    _ = mixedMoment B node473 node473Labels := by rfl

def raw38083 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw38083Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38083 raw38083Labels = mixedMoment B node474 node474Labels := by
  calc
    _ = mixedMoment B node474 node474Labels := by rfl

def raw38084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw38084Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38084 raw38084Labels = mixedMoment B node477 node477Labels := by
  calc
    _ = mixedMoment B node477 node477Labels := by rfl

def raw38085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw38085Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw38085step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38085step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38085 raw38085Labels = mixedMoment B node455 node455Labels := by
  calc
    mixedMoment B raw38085 raw38085Labels = mixedMoment B raw38085step0 raw38085step0Labels := by
      have ha : raw38085step0 = (fun i j => raw38085 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38085step0 raw38085; decide +kernel
      have hl : raw38085step0Labels = raw38085Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38085 raw38085Labels permutation662 permutation3
    mixedMoment B raw38085step0 raw38085step0Labels = mixedMoment B raw38085step1 raw38085step1Labels := by
      have ha : raw38085step1 = -raw38085step0 := by apply Matrix.ext; change ∀ i j, raw38085step1 i j = -(raw38085step0 i j); unfold raw38085step1 raw38085step0; decide +kernel
      have hl : raw38085step1Labels = raw38085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node455 node455Labels := by rfl

def raw38086 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38086Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw38086step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38086step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38086 raw38086Labels = mixedMoment B node438 node438Labels := by
  calc
    mixedMoment B raw38086 raw38086Labels = mixedMoment B raw38086step0 raw38086step0Labels := by
      have ha : raw38086step0 = (fun i j => raw38086 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38086step0 raw38086; decide +kernel
      have hl : raw38086step0Labels = raw38086Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38086 raw38086Labels permutation125 permutation3
    mixedMoment B raw38086step0 raw38086step0Labels = mixedMoment B raw38086step1 raw38086step1Labels := by
      have ha : raw38086step1 = -raw38086step0 := by apply Matrix.ext; change ∀ i j, raw38086step1 i j = -(raw38086step0 i j); unfold raw38086step1 raw38086step0; decide +kernel
      have hl : raw38086step1Labels = raw38086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node438 node438Labels := by rfl

def raw38087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw38087Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw38087step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38087step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38087 raw38087Labels = mixedMoment B node462 node462Labels := by
  calc
    mixedMoment B raw38087 raw38087Labels = mixedMoment B raw38087step0 raw38087step0Labels := by
      have ha : raw38087step0 = (fun i j => raw38087 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38087step0 raw38087; decide +kernel
      have hl : raw38087step0Labels = raw38087Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38087 raw38087Labels permutation682 permutation3
    mixedMoment B raw38087step0 raw38087step0Labels = mixedMoment B raw38087step1 raw38087step1Labels := by
      have ha : raw38087step1 = -raw38087step0 := by apply Matrix.ext; change ∀ i j, raw38087step1 i j = -(raw38087step0 i j); unfold raw38087step1 raw38087step0; decide +kernel
      have hl : raw38087step1Labels = raw38087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node462 node462Labels := by rfl

def raw38088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38088Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38088 raw38088Labels = mixedMoment B node488 node488Labels := by
  calc
    _ = mixedMoment B node488 node488Labels := by rfl

def raw38089 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38089Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38089 raw38089Labels = mixedMoment B node489 node489Labels := by
  calc
    _ = mixedMoment B node489 node489Labels := by rfl

def raw38090 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38090Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38090 raw38090Labels = mixedMoment B node490 node490Labels := by
  calc
    _ = mixedMoment B node490 node490Labels := by rfl

def raw38091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw38091Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38091 raw38091Labels = mixedMoment B node492 node492Labels := by
  calc
    _ = mixedMoment B node492 node492Labels := by rfl

def raw38092 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw38092Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw38092step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw38092step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38092 raw38092Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw38092 raw38092Labels = mixedMoment B raw38092step0 raw38092step0Labels := by
      have ha : raw38092step0 = (fun i j => raw38092 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38092step0 raw38092; decide +kernel
      have hl : raw38092step0Labels = raw38092Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38092 raw38092Labels permutation151 permutation3
    mixedMoment B raw38092step0 raw38092step0Labels = mixedMoment B raw38092step1 raw38092step1Labels := by
      have ha : raw38092step1 = -raw38092step0 := by apply Matrix.ext; change ∀ i j, raw38092step1 i j = -(raw38092step0 i j); unfold raw38092step1 raw38092step0; decide +kernel
      have hl : raw38092step1Labels = raw38092step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node468 node468Labels := by rfl

def raw38093 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38093Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38093 raw38093Labels = mixedMoment B node494 node494Labels := by
  calc
    _ = mixedMoment B node494 node494Labels := by rfl

def raw38094 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw38094Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38094 raw38094Labels = mixedMoment B node496 node496Labels := by
  calc
    _ = mixedMoment B node496 node496Labels := by rfl

def raw38095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw38095Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38095 raw38095Labels = mixedMoment B node499 node499Labels := by
  calc
    _ = mixedMoment B node499 node499Labels := by rfl

def raw38096 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw38096Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw38096step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38096step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38096 raw38096Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw38096 raw38096Labels = mixedMoment B raw38096step0 raw38096step0Labels := by
      have ha : raw38096step0 = (fun i j => raw38096 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38096step0 raw38096; decide +kernel
      have hl : raw38096step0Labels = raw38096Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38096 raw38096Labels permutation151 permutation3
    mixedMoment B raw38096step0 raw38096step0Labels = mixedMoment B raw38096step1 raw38096step1Labels := by
      have ha : raw38096step1 = -raw38096step0 := by apply Matrix.ext; change ∀ i j, raw38096step1 i j = -(raw38096step0 i j); unfold raw38096step1 raw38096step0; decide +kernel
      have hl : raw38096step1Labels = raw38096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

def raw38097 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38097Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38097 raw38097Labels = mixedMoment B node502 node502Labels := by
  calc
    _ = mixedMoment B node502 node502Labels := by rfl

def raw38098 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38098Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38098 raw38098Labels = mixedMoment B node503 node503Labels := by
  calc
    _ = mixedMoment B node503 node503Labels := by rfl

def raw38099 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38099Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38099step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw38099step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw38099step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38099 raw38099Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw38099 raw38099Labels = mixedMoment B raw38099step0 raw38099step0Labels := by
      have ha : raw38099step0 = (fun i j => raw38099 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38099step0 raw38099; decide +kernel
      have hl : raw38099step0Labels = raw38099Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38099 raw38099Labels permutation31 permutation3
    mixedMoment B raw38099step0 raw38099step0Labels = mixedMoment B raw38099step1 raw38099step1Labels := by
      have ha : raw38099step1 = -raw38099step0 := by apply Matrix.ext; change ∀ i j, raw38099step1 i j = -(raw38099step0 i j); unfold raw38099step1 raw38099step0; decide +kernel
      have hl : raw38099step1Labels = raw38099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

def raw38100 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw38100Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38100 raw38100Labels = mixedMoment B node504 node504Labels := by
  calc
    _ = mixedMoment B node504 node504Labels := by rfl

def raw38101 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw38101Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38101 raw38101Labels = mixedMoment B node505 node505Labels := by
  calc
    _ = mixedMoment B node505 node505Labels := by rfl

def raw38102 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw38102Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38102step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw38102step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38102 raw38102Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw38102 raw38102Labels = mixedMoment B raw38102step0 raw38102step0Labels := by
      have ha : raw38102step0 = (fun i j => raw38102 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw38102step0 raw38102; decide +kernel
      have hl : raw38102step0Labels = raw38102Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38102 raw38102Labels permutation17 permutation6
    _ = mixedMoment B node505 node505Labels := by rfl

def raw38103 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw38103Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38103 raw38103Labels = mixedMoment B node507 node507Labels := by
  calc
    _ = mixedMoment B node507 node507Labels := by rfl

def raw38104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38104Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw38104step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38104step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38104 raw38104Labels = mixedMoment B node425 node425Labels := by
  calc
    mixedMoment B raw38104 raw38104Labels = mixedMoment B raw38104step0 raw38104step0Labels := by
      have ha : raw38104step0 = (fun i j => raw38104 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38104step0 raw38104; decide +kernel
      have hl : raw38104step0Labels = raw38104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38104 raw38104Labels permutation588 permutation3
    mixedMoment B raw38104step0 raw38104step0Labels = mixedMoment B raw38104step1 raw38104step1Labels := by
      have ha : raw38104step1 = -raw38104step0 := by apply Matrix.ext; change ∀ i j, raw38104step1 i j = -(raw38104step0 i j); unfold raw38104step1 raw38104step0; decide +kernel
      have hl : raw38104step1Labels = raw38104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node425 node425Labels := by rfl

def raw38105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw38105Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw38105step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38105step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38105 raw38105Labels = mixedMoment B node453 node453Labels := by
  calc
    mixedMoment B raw38105 raw38105Labels = mixedMoment B raw38105step0 raw38105step0Labels := by
      have ha : raw38105step0 = (fun i j => raw38105 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38105step0 raw38105; decide +kernel
      have hl : raw38105step0Labels = raw38105Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38105 raw38105Labels permutation663 permutation3
    mixedMoment B raw38105step0 raw38105step0Labels = mixedMoment B raw38105step1 raw38105step1Labels := by
      have ha : raw38105step1 = -raw38105step0 := by apply Matrix.ext; change ∀ i j, raw38105step1 i j = -(raw38105step0 i j); unfold raw38105step1 raw38105step0; decide +kernel
      have hl : raw38105step1Labels = raw38105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node453 node453Labels := by rfl

def raw38106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw38106Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw38106step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38106step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38106 raw38106Labels = mixedMoment B node433 node433Labels := by
  calc
    mixedMoment B raw38106 raw38106Labels = mixedMoment B raw38106step0 raw38106step0Labels := by
      have ha : raw38106step0 = (fun i j => raw38106 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38106step0 raw38106; decide +kernel
      have hl : raw38106step0Labels = raw38106Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38106 raw38106Labels permutation126 permutation3
    mixedMoment B raw38106step0 raw38106step0Labels = mixedMoment B raw38106step1 raw38106step1Labels := by
      have ha : raw38106step1 = -raw38106step0 := by apply Matrix.ext; change ∀ i j, raw38106step1 i j = -(raw38106step0 i j); unfold raw38106step1 raw38106step0; decide +kernel
      have hl : raw38106step1Labels = raw38106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node433 node433Labels := by rfl

def raw38107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38107Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38107 raw38107Labels = mixedMoment B node508 node508Labels := by
  calc
    _ = mixedMoment B node508 node508Labels := by rfl

def raw38108 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38108Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38108 raw38108Labels = mixedMoment B node509 node509Labels := by
  calc
    _ = mixedMoment B node509 node509Labels := by rfl

def raw38109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw38109Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw38109step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38109step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38109 raw38109Labels = mixedMoment B node460 node460Labels := by
  calc
    mixedMoment B raw38109 raw38109Labels = mixedMoment B raw38109step0 raw38109step0Labels := by
      have ha : raw38109step0 = (fun i j => raw38109 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38109step0 raw38109; decide +kernel
      have hl : raw38109step0Labels = raw38109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38109 raw38109Labels permutation144 permutation3
    mixedMoment B raw38109step0 raw38109step0Labels = mixedMoment B raw38109step1 raw38109step1Labels := by
      have ha : raw38109step1 = -raw38109step0 := by apply Matrix.ext; change ∀ i j, raw38109step1 i j = -(raw38109step0 i j); unfold raw38109step1 raw38109step0; decide +kernel
      have hl : raw38109step1Labels = raw38109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node460 node460Labels := by rfl

def raw38110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38110Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw38110step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw38110step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38110 raw38110Labels = mixedMoment B node474 node474Labels := by
  calc
    mixedMoment B raw38110 raw38110Labels = mixedMoment B raw38110step0 raw38110step0Labels := by
      have ha : raw38110step0 = (fun i j => raw38110 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38110step0 raw38110; decide +kernel
      have hl : raw38110step0Labels = raw38110Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38110 raw38110Labels permutation144 permutation3
    mixedMoment B raw38110step0 raw38110step0Labels = mixedMoment B raw38110step1 raw38110step1Labels := by
      have ha : raw38110step1 = -raw38110step0 := by apply Matrix.ext; change ∀ i j, raw38110step1 i j = -(raw38110step0 i j); unfold raw38110step1 raw38110step0; decide +kernel
      have hl : raw38110step1Labels = raw38110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node474 node474Labels := by rfl

def raw38111 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw38111Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38111 raw38111Labels = mixedMoment B node510 node510Labels := by
  calc
    _ = mixedMoment B node510 node510Labels := by rfl

def raw38112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38112Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38112step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38112 raw38112Labels = mixedMoment B node430 node430Labels := by
  calc
    mixedMoment B raw38112 raw38112Labels = mixedMoment B raw38112step0 raw38112step0Labels := by
      have ha : raw38112step0 = (fun i j => raw38112 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38112step0 raw38112; decide +kernel
      have hl : raw38112step0Labels = raw38112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38112 raw38112Labels permutation267 permutation3
    _ = mixedMoment B node430 node430Labels := by rfl

def raw38113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38113Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38113step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38113 raw38113Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw38113 raw38113Labels = mixedMoment B raw38113step0 raw38113step0Labels := by
      have ha : raw38113step0 = (fun i j => raw38113 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38113step0 raw38113; decide +kernel
      have hl : raw38113step0Labels = raw38113Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38113 raw38113Labels permutation265 permutation3
    _ = mixedMoment B node429 node429Labels := by rfl

def raw38114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38114Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38114step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38114 raw38114Labels = mixedMoment B node436 node436Labels := by
  calc
    mixedMoment B raw38114 raw38114Labels = mixedMoment B raw38114step0 raw38114step0Labels := by
      have ha : raw38114step0 = (fun i j => raw38114 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38114step0 raw38114; decide +kernel
      have hl : raw38114step0Labels = raw38114Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38114 raw38114Labels permutation282 permutation3
    _ = mixedMoment B node436 node436Labels := by rfl

def raw38115 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw38115Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38115step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38115 raw38115Labels = mixedMoment B node437 node437Labels := by
  calc
    mixedMoment B raw38115 raw38115Labels = mixedMoment B raw38115step0 raw38115step0Labels := by
      have ha : raw38115step0 = (fun i j => raw38115 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38115step0 raw38115; decide +kernel
      have hl : raw38115step0Labels = raw38115Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38115 raw38115Labels permutation58 permutation3
    _ = mixedMoment B node437 node437Labels := by rfl

def raw38116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38116Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38116 raw38116Labels = mixedMoment B node517 node517Labels := by
  calc
    _ = mixedMoment B node517 node517Labels := by rfl

def raw38117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw38117Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw38117step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38117step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38117 raw38117Labels = mixedMoment B node457 node457Labels := by
  calc
    mixedMoment B raw38117 raw38117Labels = mixedMoment B raw38117step0 raw38117step0Labels := by
      have ha : raw38117step0 = (fun i j => raw38117 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38117step0 raw38117; decide +kernel
      have hl : raw38117step0Labels = raw38117Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38117 raw38117Labels permutation662 permutation3
    mixedMoment B raw38117step0 raw38117step0Labels = mixedMoment B raw38117step1 raw38117step1Labels := by
      have ha : raw38117step1 = -raw38117step0 := by apply Matrix.ext; change ∀ i j, raw38117step1 i j = -(raw38117step0 i j); unfold raw38117step1 raw38117step0; decide +kernel
      have hl : raw38117step1Labels = raw38117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node457 node457Labels := by rfl

def raw38118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38118Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw38118step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38118step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38118 raw38118Labels = mixedMoment B node472 node472Labels := by
  calc
    mixedMoment B raw38118 raw38118Labels = mixedMoment B raw38118step0 raw38118step0Labels := by
      have ha : raw38118step0 = (fun i j => raw38118 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38118step0 raw38118; decide +kernel
      have hl : raw38118step0Labels = raw38118Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38118 raw38118Labels permutation662 permutation3
    mixedMoment B raw38118step0 raw38118step0Labels = mixedMoment B raw38118step1 raw38118step1Labels := by
      have ha : raw38118step1 = -raw38118step0 := by apply Matrix.ext; change ∀ i j, raw38118step1 i j = -(raw38118step0 i j); unfold raw38118step1 raw38118step0; decide +kernel
      have hl : raw38118step1Labels = raw38118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node472 node472Labels := by rfl

def raw38119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw38119Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38119step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38119 raw38119Labels = mixedMoment B node511 node511Labels := by
  calc
    mixedMoment B raw38119 raw38119Labels = mixedMoment B raw38119step0 raw38119step0Labels := by
      have ha : raw38119step0 = (fun i j => raw38119 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38119step0 raw38119; decide +kernel
      have hl : raw38119step0Labels = raw38119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38119 raw38119Labels permutation176 permutation3
    _ = mixedMoment B node511 node511Labels := by rfl

def raw38120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw38120Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw38120step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38120step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38120 raw38120Labels = mixedMoment B node454 node454Labels := by
  calc
    mixedMoment B raw38120 raw38120Labels = mixedMoment B raw38120step0 raw38120step0Labels := by
      have ha : raw38120step0 = (fun i j => raw38120 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38120step0 raw38120; decide +kernel
      have hl : raw38120step0Labels = raw38120Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38120 raw38120Labels permutation662 permutation3
    mixedMoment B raw38120step0 raw38120step0Labels = mixedMoment B raw38120step1 raw38120step1Labels := by
      have ha : raw38120step1 = -raw38120step0 := by apply Matrix.ext; change ∀ i j, raw38120step1 i j = -(raw38120step0 i j); unfold raw38120step1 raw38120step0; decide +kernel
      have hl : raw38120step1Labels = raw38120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node454 node454Labels := by rfl

def raw38121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw38121Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw38121step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38121step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38121 raw38121Labels = mixedMoment B node461 node461Labels := by
  calc
    mixedMoment B raw38121 raw38121Labels = mixedMoment B raw38121step0 raw38121step0Labels := by
      have ha : raw38121step0 = (fun i j => raw38121 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38121step0 raw38121; decide +kernel
      have hl : raw38121step0Labels = raw38121Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38121 raw38121Labels permutation682 permutation3
    mixedMoment B raw38121step0 raw38121step0Labels = mixedMoment B raw38121step1 raw38121step1Labels := by
      have ha : raw38121step1 = -raw38121step0 := by apply Matrix.ext; change ∀ i j, raw38121step1 i j = -(raw38121step0 i j); unfold raw38121step1 raw38121step0; decide +kernel
      have hl : raw38121step1Labels = raw38121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node461 node461Labels := by rfl

def raw38122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38122Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38122 raw38122Labels = mixedMoment B node520 node520Labels := by
  calc
    _ = mixedMoment B node520 node520Labels := by rfl

def raw38123 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38123Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38123 raw38123Labels = mixedMoment B node521 node521Labels := by
  calc
    _ = mixedMoment B node521 node521Labels := by rfl

def raw38124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38124Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw38124step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38124step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38124 raw38124Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw38124 raw38124Labels = mixedMoment B raw38124step0 raw38124step0Labels := by
      have ha : raw38124step0 = (fun i j => raw38124 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38124step0 raw38124; decide +kernel
      have hl : raw38124step0Labels = raw38124Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38124 raw38124Labels permutation151 permutation3
    mixedMoment B raw38124step0 raw38124step0Labels = mixedMoment B raw38124step1 raw38124step1Labels := by
      have ha : raw38124step1 = -raw38124step0 := by apply Matrix.ext; change ∀ i j, raw38124step1 i j = -(raw38124step0 i j); unfold raw38124step1 raw38124step0; decide +kernel
      have hl : raw38124step1Labels = raw38124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

def raw38125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38125Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38125 raw38125Labels = mixedMoment B node523 node523Labels := by
  calc
    _ = mixedMoment B node523 node523Labels := by rfl

def raw38126 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw38126Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38126step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw38126step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38126step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38126 raw38126Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw38126 raw38126Labels = mixedMoment B raw38126step0 raw38126step0Labels := by
      have ha : raw38126step0 = (fun i j => raw38126 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38126step0 raw38126; decide +kernel
      have hl : raw38126step0Labels = raw38126Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38126 raw38126Labels permutation31 permutation3
    mixedMoment B raw38126step0 raw38126step0Labels = mixedMoment B raw38126step1 raw38126step1Labels := by
      have ha : raw38126step1 = -raw38126step0 := by apply Matrix.ext; change ∀ i j, raw38126step1 i j = -(raw38126step0 i j); unfold raw38126step1 raw38126step0; decide +kernel
      have hl : raw38126step1Labels = raw38126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node503 node503Labels := by rfl

def raw38127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38127Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38127step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38127step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38127 raw38127Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw38127 raw38127Labels = mixedMoment B raw38127step0 raw38127step0Labels := by
      have ha : raw38127step0 = (fun i j => raw38127 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38127step0 raw38127; decide +kernel
      have hl : raw38127step0Labels = raw38127Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38127 raw38127Labels permutation682 permutation3
    mixedMoment B raw38127step0 raw38127step0Labels = mixedMoment B raw38127step1 raw38127step1Labels := by
      have ha : raw38127step1 = -raw38127step0 := by apply Matrix.ext; change ∀ i j, raw38127step1 i j = -(raw38127step0 i j); unfold raw38127step1 raw38127step0; decide +kernel
      have hl : raw38127step1Labels = raw38127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

def raw38128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38128Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38128step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38128 raw38128Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw38128 raw38128Labels = mixedMoment B raw38128step0 raw38128step0Labels := by
      have ha : raw38128step0 = (fun i j => raw38128 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38128step0 raw38128; decide +kernel
      have hl : raw38128step0Labels = raw38128Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38128 raw38128Labels permutation155 permutation3
    _ = mixedMoment B node520 node520Labels := by rfl

def raw38129 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw38129Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw38129step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38129 raw38129Labels = mixedMoment B node493 node493Labels := by
  calc
    mixedMoment B raw38129 raw38129Labels = mixedMoment B raw38129step0 raw38129step0Labels := by
      have ha : raw38129step0 = (fun i j => raw38129 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38129step0 raw38129; decide +kernel
      have hl : raw38129step0Labels = raw38129Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38129 raw38129Labels permutation145 permutation5
    _ = mixedMoment B node493 node493Labels := by rfl

def raw38130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw38130Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38130step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38130 raw38130Labels = mixedMoment B node519 node519Labels := by
  calc
    mixedMoment B raw38130 raw38130Labels = mixedMoment B raw38130step0 raw38130step0Labels := by
      have ha : raw38130step0 = (fun i j => raw38130 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38130step0 raw38130; decide +kernel
      have hl : raw38130step0Labels = raw38130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38130 raw38130Labels permutation157 permutation3
    _ = mixedMoment B node519 node519Labels := by rfl

def raw38131 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw38131Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38131step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38131step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38131 raw38131Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw38131 raw38131Labels = mixedMoment B raw38131step0 raw38131step0Labels := by
      have ha : raw38131step0 = (fun i j => raw38131 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38131step0 raw38131; decide +kernel
      have hl : raw38131step0Labels = raw38131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38131 raw38131Labels permutation151 permutation3
    mixedMoment B raw38131step0 raw38131step0Labels = mixedMoment B raw38131step1 raw38131step1Labels := by
      have ha : raw38131step1 = -raw38131step0 := by apply Matrix.ext; change ∀ i j, raw38131step1 i j = -(raw38131step0 i j); unfold raw38131step1 raw38131step0; decide +kernel
      have hl : raw38131step1Labels = raw38131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node514 node514Labels := by rfl

def raw38132 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw38132Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw38132step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38132 raw38132Labels = mixedMoment B node522 node522Labels := by
  calc
    mixedMoment B raw38132 raw38132Labels = mixedMoment B raw38132step0 raw38132step0Labels := by
      have ha : raw38132step0 = (fun i j => raw38132 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38132step0 raw38132; decide +kernel
      have hl : raw38132step0Labels = raw38132Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38132 raw38132Labels permutation37 permutation3
    _ = mixedMoment B node522 node522Labels := by rfl

def raw38133 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38133Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38133step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38133 raw38133Labels = mixedMoment B node523 node523Labels := by
  calc
    mixedMoment B raw38133 raw38133Labels = mixedMoment B raw38133step0 raw38133step0Labels := by
      have ha : raw38133step0 = (fun i j => raw38133 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38133step0 raw38133; decide +kernel
      have hl : raw38133step0Labels = raw38133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38133 raw38133Labels permutation35 permutation3
    _ = mixedMoment B node523 node523Labels := by rfl

def raw38134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38134Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38134step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38134 raw38134Labels = mixedMoment B node513 node513Labels := by
  calc
    mixedMoment B raw38134 raw38134Labels = mixedMoment B raw38134step0 raw38134step0Labels := by
      have ha : raw38134step0 = (fun i j => raw38134 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38134step0 raw38134; decide +kernel
      have hl : raw38134step0Labels = raw38134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38134 raw38134Labels permutation156 permutation3
    _ = mixedMoment B node513 node513Labels := by rfl

def raw38135 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw38135Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38135step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw38135step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38135 raw38135Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw38135 raw38135Labels = mixedMoment B raw38135step0 raw38135step0Labels := by
      have ha : raw38135step0 = (fun i j => raw38135 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38135step0 raw38135; decide +kernel
      have hl : raw38135step0Labels = raw38135Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38135 raw38135Labels permutation151 permutation3
    mixedMoment B raw38135step0 raw38135step0Labels = mixedMoment B raw38135step1 raw38135step1Labels := by
      have ha : raw38135step1 = -raw38135step0 := by apply Matrix.ext; change ∀ i j, raw38135step1 i j = -(raw38135step0 i j); unfold raw38135step1 raw38135step0; decide +kernel
      have hl : raw38135step1Labels = raw38135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

def raw38136 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw38136Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38136step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw38136step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38136 raw38136Labels = mixedMoment B node516 node516Labels := by
  calc
    mixedMoment B raw38136 raw38136Labels = mixedMoment B raw38136step0 raw38136step0Labels := by
      have ha : raw38136step0 = (fun i j => raw38136 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38136step0 raw38136; decide +kernel
      have hl : raw38136step0Labels = raw38136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38136 raw38136Labels permutation8 permutation3
    _ = mixedMoment B node516 node516Labels := by rfl

def raw38137 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw38137Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38137step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38137 raw38137Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw38137 raw38137Labels = mixedMoment B raw38137step0 raw38137step0Labels := by
      have ha : raw38137step0 = (fun i j => raw38137 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38137step0 raw38137; decide +kernel
      have hl : raw38137step0Labels = raw38137Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38137 raw38137Labels permutation137 permutation5
    _ = mixedMoment B node494 node494Labels := by rfl

def raw38138 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw38138Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38138 raw38138Labels = mixedMoment B node526 node526Labels := by
  calc
    _ = mixedMoment B node526 node526Labels := by rfl

def raw38139 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw38139Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38139 raw38139Labels = mixedMoment B node527 node527Labels := by
  calc
    _ = mixedMoment B node527 node527Labels := by rfl

def raw38140 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw38140Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38140 raw38140Labels = mixedMoment B node528 node528Labels := by
  calc
    _ = mixedMoment B node528 node528Labels := by rfl

def raw38141 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw38141Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38141step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw38141step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38141 raw38141Labels = mixedMoment B node528 node528Labels := by
  calc
    mixedMoment B raw38141 raw38141Labels = mixedMoment B raw38141step0 raw38141step0Labels := by
      have ha : raw38141step0 = (fun i j => raw38141 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38141step0 raw38141; decide +kernel
      have hl : raw38141step0Labels = raw38141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38141 raw38141Labels permutation9 permutation3
    _ = mixedMoment B node528 node528Labels := by rfl

def raw38142 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw38142Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38142 raw38142Labels = mixedMoment B node530 node530Labels := by
  calc
    _ = mixedMoment B node530 node530Labels := by rfl

def raw38143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38143Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38143step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38143 raw38143Labels = mixedMoment B node456 node456Labels := by
  calc
    mixedMoment B raw38143 raw38143Labels = mixedMoment B raw38143step0 raw38143step0Labels := by
      have ha : raw38143step0 = (fun i j => raw38143 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38143step0 raw38143; decide +kernel
      have hl : raw38143step0Labels = raw38143Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38143 raw38143Labels permutation176 permutation3
    _ = mixedMoment B node456 node456Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
