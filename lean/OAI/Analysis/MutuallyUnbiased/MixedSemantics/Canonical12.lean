import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1536step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1536 raw1536Labels = mixedMoment B node4660 node4660Labels := by
  calc
    mixedMoment B raw1536 raw1536Labels = mixedMoment B raw1536step0 raw1536step0Labels := by
      have ha : raw1536step0 = (fun i j => raw1536 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1536step0 raw1536; decide +kernel
      have hl : raw1536step0Labels = raw1536Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1536 raw1536Labels permutation152 permutation4
    mixedMoment B raw1536step0 raw1536step0Labels = mixedMoment B raw1536step1 raw1536step1Labels := by
      have ha : raw1536step1 = raw1536step0 := by apply Matrix.ext; unfold raw1536step1 raw1536step0; decide +kernel
      have hl : raw1536step0Labels = labelEmbedding7 ∘ raw1536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1536step0 raw1536step0Labels raw1536step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4660 node4660Labels := by rfl

def raw1537 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1537 raw1537Labels = mixedMoment B node1786 node1786Labels := by
  calc
    mixedMoment B raw1537 raw1537Labels = mixedMoment B raw1537step0 raw1537step0Labels := by
      have ha : raw1537step0 = (fun i j => raw1537 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1537step0 raw1537; decide +kernel
      have hl : raw1537step0Labels = raw1537Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1537 raw1537Labels permutation152 permutation4
    _ = mixedMoment B node1786 node1786Labels := by rfl

def raw1538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1538Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1538step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1538 raw1538Labels = mixedMoment B node1982 node1982Labels := by
  calc
    mixedMoment B raw1538 raw1538Labels = mixedMoment B raw1538step0 raw1538step0Labels := by
      have ha : raw1538step0 = (fun i j => raw1538 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1538step0 raw1538; decide +kernel
      have hl : raw1538step0Labels = raw1538Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1538 raw1538Labels permutation176 permutation6
    mixedMoment B raw1538step0 raw1538step0Labels = mixedMoment B raw1538step1 raw1538step1Labels := by
      have ha : raw1538step1 = -raw1538step0 := by apply Matrix.ext; change ∀ i j, raw1538step1 i j = -(raw1538step0 i j); unfold raw1538step1 raw1538step0; decide +kernel
      have hl : raw1538step1Labels = raw1538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1538step1 raw1538step1Labels = mixedMoment B raw1538step2 raw1538step2Labels := by
      have ha : raw1538step2 = raw1538step1 := by apply Matrix.ext; unfold raw1538step2 raw1538step1; decide +kernel
      have hl : raw1538step1Labels = labelEmbedding1 ∘ raw1538step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1538step1 raw1538step1Labels raw1538step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1982 node1982Labels := by rfl

def raw1539 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1539step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1539 raw1539Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw1539 raw1539Labels = mixedMoment B raw1539step0 raw1539step0Labels := by
      have ha : raw1539step0 = (fun i j => raw1539 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1539step0 raw1539; decide +kernel
      have hl : raw1539step0Labels = raw1539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1539 raw1539Labels permutation152 permutation4
    mixedMoment B raw1539step0 raw1539step0Labels = mixedMoment B raw1539step1 raw1539step1Labels := by
      have ha : raw1539step1 = raw1539step0 := by apply Matrix.ext; unfold raw1539step1 raw1539step0; decide +kernel
      have hl : raw1539step0Labels = labelEmbedding7 ∘ raw1539step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1539step0 raw1539step0Labels raw1539step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

def raw1540 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1540 raw1540Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw1540 raw1540Labels = mixedMoment B raw1540step0 raw1540step0Labels := by
      have ha : raw1540step0 = (fun i j => raw1540 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1540step0 raw1540; decide +kernel
      have hl : raw1540step0Labels = raw1540Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1540 raw1540Labels permutation152 permutation4
    _ = mixedMoment B node1787 node1787Labels := by rfl

def raw1541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1541Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1541step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1541step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1541 raw1541Labels = mixedMoment B node1983 node1983Labels := by
  calc
    mixedMoment B raw1541 raw1541Labels = mixedMoment B raw1541step0 raw1541step0Labels := by
      have ha : raw1541step0 = (fun i j => raw1541 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1541step0 raw1541; decide +kernel
      have hl : raw1541step0Labels = raw1541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1541 raw1541Labels permutation176 permutation6
    mixedMoment B raw1541step0 raw1541step0Labels = mixedMoment B raw1541step1 raw1541step1Labels := by
      have ha : raw1541step1 = -raw1541step0 := by apply Matrix.ext; change ∀ i j, raw1541step1 i j = -(raw1541step0 i j); unfold raw1541step1 raw1541step0; decide +kernel
      have hl : raw1541step1Labels = raw1541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1541step1 raw1541step1Labels = mixedMoment B raw1541step2 raw1541step2Labels := by
      have ha : raw1541step2 = raw1541step1 := by apply Matrix.ext; unfold raw1541step2 raw1541step1; decide +kernel
      have hl : raw1541step1Labels = labelEmbedding1 ∘ raw1541step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1541step1 raw1541step1Labels raw1541step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1983 node1983Labels := by rfl

def raw1542 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1542step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1542 raw1542Labels = mixedMoment B node4662 node4662Labels := by
  calc
    mixedMoment B raw1542 raw1542Labels = mixedMoment B raw1542step0 raw1542step0Labels := by
      have ha : raw1542step0 = (fun i j => raw1542 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1542step0 raw1542; decide +kernel
      have hl : raw1542step0Labels = raw1542Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1542 raw1542Labels permutation32 permutation4
    mixedMoment B raw1542step0 raw1542step0Labels = mixedMoment B raw1542step1 raw1542step1Labels := by
      have ha : raw1542step1 = raw1542step0 := by apply Matrix.ext; unfold raw1542step1 raw1542step0; decide +kernel
      have hl : raw1542step0Labels = labelEmbedding7 ∘ raw1542step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1542step0 raw1542step0Labels raw1542step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4662 node4662Labels := by rfl

def raw1543 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1543 raw1543Labels = mixedMoment B node1788 node1788Labels := by
  calc
    mixedMoment B raw1543 raw1543Labels = mixedMoment B raw1543step0 raw1543step0Labels := by
      have ha : raw1543step0 = (fun i j => raw1543 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1543step0 raw1543; decide +kernel
      have hl : raw1543step0Labels = raw1543Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1543 raw1543Labels permutation32 permutation4
    _ = mixedMoment B node1788 node1788Labels := by rfl

def raw1544 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1544Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, -1, 3]]
def raw1544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw1544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw1544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1544 raw1544Labels = mixedMoment B node1984 node1984Labels := by
  calc
    mixedMoment B raw1544 raw1544Labels = mixedMoment B raw1544step0 raw1544step0Labels := by
      have ha : raw1544step0 = (fun i j => raw1544 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1544step0 raw1544; decide +kernel
      have hl : raw1544step0Labels = raw1544Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1544 raw1544Labels permutation38 permutation6
    mixedMoment B raw1544step0 raw1544step0Labels = mixedMoment B raw1544step1 raw1544step1Labels := by
      have ha : raw1544step1 = -raw1544step0 := by apply Matrix.ext; change ∀ i j, raw1544step1 i j = -(raw1544step0 i j); unfold raw1544step1 raw1544step0; decide +kernel
      have hl : raw1544step1Labels = raw1544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1544step1 raw1544step1Labels = mixedMoment B raw1544step2 raw1544step2Labels := by
      have ha : raw1544step2 = raw1544step1 := by apply Matrix.ext; unfold raw1544step2 raw1544step1; decide +kernel
      have hl : raw1544step1Labels = labelEmbedding1 ∘ raw1544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1544step1 raw1544step1Labels raw1544step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1984 node1984Labels := by rfl

def raw1545 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1545step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1545 raw1545Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw1545 raw1545Labels = mixedMoment B raw1545step0 raw1545step0Labels := by
      have ha : raw1545step0 = (fun i j => raw1545 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1545step0 raw1545; decide +kernel
      have hl : raw1545step0Labels = raw1545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1545 raw1545Labels permutation152 permutation4
    mixedMoment B raw1545step0 raw1545step0Labels = mixedMoment B raw1545step1 raw1545step1Labels := by
      have ha : raw1545step1 = raw1545step0 := by apply Matrix.ext; unfold raw1545step1 raw1545step0; decide +kernel
      have hl : raw1545step0Labels = labelEmbedding7 ∘ raw1545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1545step0 raw1545step0Labels raw1545step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

def raw1546 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1546Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1546step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1546 raw1546Labels = mixedMoment B node1798 node1798Labels := by
  calc
    mixedMoment B raw1546 raw1546Labels = mixedMoment B raw1546step0 raw1546step0Labels := by
      have ha : raw1546step0 = (fun i j => raw1546 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1546step0 raw1546; decide +kernel
      have hl : raw1546step0Labels = raw1546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1546 raw1546Labels permutation152 permutation4
    _ = mixedMoment B node1798 node1798Labels := by rfl

def raw1547 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1547Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1547step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1547step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1547 raw1547Labels = mixedMoment B node2067 node2067Labels := by
  calc
    mixedMoment B raw1547 raw1547Labels = mixedMoment B raw1547step0 raw1547step0Labels := by
      have ha : raw1547step0 = (fun i j => raw1547 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1547step0 raw1547; decide +kernel
      have hl : raw1547step0Labels = raw1547Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1547 raw1547Labels permutation176 permutation6
    mixedMoment B raw1547step0 raw1547step0Labels = mixedMoment B raw1547step1 raw1547step1Labels := by
      have ha : raw1547step1 = -raw1547step0 := by apply Matrix.ext; change ∀ i j, raw1547step1 i j = -(raw1547step0 i j); unfold raw1547step1 raw1547step0; decide +kernel
      have hl : raw1547step1Labels = raw1547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1547step1 raw1547step1Labels = mixedMoment B raw1547step2 raw1547step2Labels := by
      have ha : raw1547step2 = raw1547step1 := by apply Matrix.ext; unfold raw1547step2 raw1547step1; decide +kernel
      have hl : raw1547step1Labels = labelEmbedding1 ∘ raw1547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1547step1 raw1547step1Labels raw1547step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2067 node2067Labels := by rfl

def raw1548 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1548step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1548 raw1548Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw1548 raw1548Labels = mixedMoment B raw1548step0 raw1548step0Labels := by
      have ha : raw1548step0 = (fun i j => raw1548 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1548step0 raw1548; decide +kernel
      have hl : raw1548step0Labels = raw1548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1548 raw1548Labels permutation32 permutation4
    mixedMoment B raw1548step0 raw1548step0Labels = mixedMoment B raw1548step1 raw1548step1Labels := by
      have ha : raw1548step1 = raw1548step0 := by apply Matrix.ext; unfold raw1548step1 raw1548step0; decide +kernel
      have hl : raw1548step0Labels = labelEmbedding7 ∘ raw1548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1548step0 raw1548step0Labels raw1548step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4673 node4673Labels := by rfl

def raw1549 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1549 raw1549Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw1549 raw1549Labels = mixedMoment B raw1549step0 raw1549step0Labels := by
      have ha : raw1549step0 = (fun i j => raw1549 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1549step0 raw1549; decide +kernel
      have hl : raw1549step0Labels = raw1549Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1549 raw1549Labels permutation32 permutation4
    _ = mixedMoment B node1799 node1799Labels := by rfl

def raw1550 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1550Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw1550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw1550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1550 raw1550Labels = mixedMoment B node1920 node1920Labels := by
  calc
    mixedMoment B raw1550 raw1550Labels = mixedMoment B raw1550step0 raw1550step0Labels := by
      have ha : raw1550step0 = (fun i j => raw1550 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1550step0 raw1550; decide +kernel
      have hl : raw1550step0Labels = raw1550Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1550 raw1550Labels permutation149 permutation6
    mixedMoment B raw1550step0 raw1550step0Labels = mixedMoment B raw1550step1 raw1550step1Labels := by
      have ha : raw1550step1 = raw1550step0 := by apply Matrix.ext; unfold raw1550step1 raw1550step0; decide +kernel
      have hl : raw1550step0Labels = labelEmbedding1 ∘ raw1550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1550step0 raw1550step0Labels raw1550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1920 node1920Labels := by rfl

def raw1551 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1551step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1551 raw1551Labels = mixedMoment B node4674 node4674Labels := by
  calc
    mixedMoment B raw1551 raw1551Labels = mixedMoment B raw1551step0 raw1551step0Labels := by
      have ha : raw1551step0 = (fun i j => raw1551 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1551step0 raw1551; decide +kernel
      have hl : raw1551step0Labels = raw1551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1551 raw1551Labels permutation32 permutation4
    mixedMoment B raw1551step0 raw1551step0Labels = mixedMoment B raw1551step1 raw1551step1Labels := by
      have ha : raw1551step1 = raw1551step0 := by apply Matrix.ext; unfold raw1551step1 raw1551step0; decide +kernel
      have hl : raw1551step0Labels = labelEmbedding7 ∘ raw1551step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1551step0 raw1551step0Labels raw1551step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4674 node4674Labels := by rfl

def raw1552 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1552 raw1552Labels = mixedMoment B node1800 node1800Labels := by
  calc
    mixedMoment B raw1552 raw1552Labels = mixedMoment B raw1552step0 raw1552step0Labels := by
      have ha : raw1552step0 = (fun i j => raw1552 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1552step0 raw1552; decide +kernel
      have hl : raw1552step0Labels = raw1552Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1552 raw1552Labels permutation32 permutation4
    _ = mixedMoment B node1800 node1800Labels := by rfl

def raw1553 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1553Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw1553step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1553step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1553 raw1553Labels = mixedMoment B node2068 node2068Labels := by
  calc
    mixedMoment B raw1553 raw1553Labels = mixedMoment B raw1553step0 raw1553step0Labels := by
      have ha : raw1553step0 = (fun i j => raw1553 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1553step0 raw1553; decide +kernel
      have hl : raw1553step0Labels = raw1553Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1553 raw1553Labels permutation38 permutation6
    mixedMoment B raw1553step0 raw1553step0Labels = mixedMoment B raw1553step1 raw1553step1Labels := by
      have ha : raw1553step1 = -raw1553step0 := by apply Matrix.ext; change ∀ i j, raw1553step1 i j = -(raw1553step0 i j); unfold raw1553step1 raw1553step0; decide +kernel
      have hl : raw1553step1Labels = raw1553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1553step1 raw1553step1Labels = mixedMoment B raw1553step2 raw1553step2Labels := by
      have ha : raw1553step2 = raw1553step1 := by apply Matrix.ext; unfold raw1553step2 raw1553step1; decide +kernel
      have hl : raw1553step1Labels = labelEmbedding1 ∘ raw1553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1553step1 raw1553step1Labels raw1553step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2068 node2068Labels := by rfl

def raw1554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1554step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1554 raw1554Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw1554 raw1554Labels = mixedMoment B raw1554step0 raw1554step0Labels := by
      have ha : raw1554step0 = (fun i j => raw1554 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1554step0 raw1554; decide +kernel
      have hl : raw1554step0Labels = raw1554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1554 raw1554Labels permutation152 permutation4
    mixedMoment B raw1554step0 raw1554step0Labels = mixedMoment B raw1554step1 raw1554step1Labels := by
      have ha : raw1554step1 = raw1554step0 := by apply Matrix.ext; unfold raw1554step1 raw1554step0; decide +kernel
      have hl : raw1554step0Labels = labelEmbedding7 ∘ raw1554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1554step0 raw1554step0Labels raw1554step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw1555 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1555 raw1555Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw1555 raw1555Labels = mixedMoment B raw1555step0 raw1555step0Labels := by
      have ha : raw1555step0 = (fun i j => raw1555 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1555step0 raw1555; decide +kernel
      have hl : raw1555step0Labels = raw1555Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1555 raw1555Labels permutation152 permutation4
    _ = mixedMoment B node1802 node1802Labels := by rfl

def raw1556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1556Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1556 raw1556Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw1556 raw1556Labels = mixedMoment B raw1556step0 raw1556step0Labels := by
      have ha : raw1556step0 = (fun i j => raw1556 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1556step0 raw1556; decide +kernel
      have hl : raw1556step0Labels = raw1556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1556 raw1556Labels permutation152 permutation6
    mixedMoment B raw1556step0 raw1556step0Labels = mixedMoment B raw1556step1 raw1556step1Labels := by
      have ha : raw1556step1 = -raw1556step0 := by apply Matrix.ext; change ∀ i j, raw1556step1 i j = -(raw1556step0 i j); unfold raw1556step1 raw1556step0; decide +kernel
      have hl : raw1556step1Labels = raw1556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1556step1 raw1556step1Labels = mixedMoment B raw1556step2 raw1556step2Labels := by
      have ha : raw1556step2 = raw1556step1 := by apply Matrix.ext; unfold raw1556step2 raw1556step1; decide +kernel
      have hl : raw1556step1Labels = labelEmbedding1 ∘ raw1556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1556step1 raw1556step1Labels raw1556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

def raw1557 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1557step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1557 raw1557Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw1557 raw1557Labels = mixedMoment B raw1557step0 raw1557step0Labels := by
      have ha : raw1557step0 = (fun i j => raw1557 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1557step0 raw1557; decide +kernel
      have hl : raw1557step0Labels = raw1557Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1557 raw1557Labels permutation32 permutation4
    mixedMoment B raw1557step0 raw1557step0Labels = mixedMoment B raw1557step1 raw1557step1Labels := by
      have ha : raw1557step1 = raw1557step0 := by apply Matrix.ext; unfold raw1557step1 raw1557step0; decide +kernel
      have hl : raw1557step0Labels = labelEmbedding7 ∘ raw1557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1557step0 raw1557step0Labels raw1557step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw1558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1558 raw1558Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw1558 raw1558Labels = mixedMoment B raw1558step0 raw1558step0Labels := by
      have ha : raw1558step0 = (fun i j => raw1558 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1558step0 raw1558; decide +kernel
      have hl : raw1558step0Labels = raw1558Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1558 raw1558Labels permutation32 permutation4
    _ = mixedMoment B node1804 node1804Labels := by rfl

def raw1559 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1559Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw1559step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1559 raw1559Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw1559 raw1559Labels = mixedMoment B raw1559step0 raw1559step0Labels := by
      have ha : raw1559step0 = (fun i j => raw1559 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1559step0 raw1559; decide +kernel
      have hl : raw1559step0Labels = raw1559Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1559 raw1559Labels permutation32 permutation6
    mixedMoment B raw1559step0 raw1559step0Labels = mixedMoment B raw1559step1 raw1559step1Labels := by
      have ha : raw1559step1 = -raw1559step0 := by apply Matrix.ext; change ∀ i j, raw1559step1 i j = -(raw1559step0 i j); unfold raw1559step1 raw1559step0; decide +kernel
      have hl : raw1559step1Labels = raw1559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1559step1 raw1559step1Labels = mixedMoment B raw1559step2 raw1559step2Labels := by
      have ha : raw1559step2 = raw1559step1 := by apply Matrix.ext; unfold raw1559step2 raw1559step1; decide +kernel
      have hl : raw1559step1Labels = labelEmbedding1 ∘ raw1559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1559step1 raw1559step1Labels raw1559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw1560 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1560step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1560 raw1560Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw1560 raw1560Labels = mixedMoment B raw1560step0 raw1560step0Labels := by
      have ha : raw1560step0 = (fun i j => raw1560 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1560step0 raw1560; decide +kernel
      have hl : raw1560step0Labels = raw1560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1560 raw1560Labels permutation152 permutation4
    mixedMoment B raw1560step0 raw1560step0Labels = mixedMoment B raw1560step1 raw1560step1Labels := by
      have ha : raw1560step1 = raw1560step0 := by apply Matrix.ext; unfold raw1560step1 raw1560step0; decide +kernel
      have hl : raw1560step0Labels = labelEmbedding7 ∘ raw1560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1560step0 raw1560step0Labels raw1560step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw1561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1561 raw1561Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw1561 raw1561Labels = mixedMoment B raw1561step0 raw1561step0Labels := by
      have ha : raw1561step0 = (fun i j => raw1561 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1561step0 raw1561; decide +kernel
      have hl : raw1561step0Labels = raw1561Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1561 raw1561Labels permutation152 permutation4
    _ = mixedMoment B node1805 node1805Labels := by rfl

def raw1562 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1562Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1562step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1562 raw1562Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw1562 raw1562Labels = mixedMoment B raw1562step0 raw1562step0Labels := by
      have ha : raw1562step0 = (fun i j => raw1562 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1562step0 raw1562; decide +kernel
      have hl : raw1562step0Labels = raw1562Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1562 raw1562Labels permutation152 permutation6
    mixedMoment B raw1562step0 raw1562step0Labels = mixedMoment B raw1562step1 raw1562step1Labels := by
      have ha : raw1562step1 = -raw1562step0 := by apply Matrix.ext; change ∀ i j, raw1562step1 i j = -(raw1562step0 i j); unfold raw1562step1 raw1562step0; decide +kernel
      have hl : raw1562step1Labels = raw1562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1562step1 raw1562step1Labels = mixedMoment B raw1562step2 raw1562step2Labels := by
      have ha : raw1562step2 = raw1562step1 := by apply Matrix.ext; unfold raw1562step2 raw1562step1; decide +kernel
      have hl : raw1562step1Labels = labelEmbedding1 ∘ raw1562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1562step1 raw1562step1Labels raw1562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

def raw1563 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1563step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1563 raw1563Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw1563 raw1563Labels = mixedMoment B raw1563step0 raw1563step0Labels := by
      have ha : raw1563step0 = (fun i j => raw1563 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1563step0 raw1563; decide +kernel
      have hl : raw1563step0Labels = raw1563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1563 raw1563Labels permutation32 permutation4
    mixedMoment B raw1563step0 raw1563step0Labels = mixedMoment B raw1563step1 raw1563step1Labels := by
      have ha : raw1563step1 = raw1563step0 := by apply Matrix.ext; unfold raw1563step1 raw1563step0; decide +kernel
      have hl : raw1563step0Labels = labelEmbedding7 ∘ raw1563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1563step0 raw1563step0Labels raw1563step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw1564 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1564 raw1564Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw1564 raw1564Labels = mixedMoment B raw1564step0 raw1564step0Labels := by
      have ha : raw1564step0 = (fun i j => raw1564 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1564step0 raw1564; decide +kernel
      have hl : raw1564step0Labels = raw1564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1564 raw1564Labels permutation32 permutation4
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw1565 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1565Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1565step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1565 raw1565Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw1565 raw1565Labels = mixedMoment B raw1565step0 raw1565step0Labels := by
      have ha : raw1565step0 = (fun i j => raw1565 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1565step0 raw1565; decide +kernel
      have hl : raw1565step0Labels = raw1565Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1565 raw1565Labels permutation32 permutation6
    mixedMoment B raw1565step0 raw1565step0Labels = mixedMoment B raw1565step1 raw1565step1Labels := by
      have ha : raw1565step1 = -raw1565step0 := by apply Matrix.ext; change ∀ i j, raw1565step1 i j = -(raw1565step0 i j); unfold raw1565step1 raw1565step0; decide +kernel
      have hl : raw1565step1Labels = raw1565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1565step1 raw1565step1Labels = mixedMoment B raw1565step2 raw1565step2Labels := by
      have ha : raw1565step2 = raw1565step1 := by apply Matrix.ext; unfold raw1565step2 raw1565step1; decide +kernel
      have hl : raw1565step1Labels = labelEmbedding1 ∘ raw1565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1565step1 raw1565step1Labels raw1565step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw1566 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1566step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1566 raw1566Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw1566 raw1566Labels = mixedMoment B raw1566step0 raw1566step0Labels := by
      have ha : raw1566step0 = (fun i j => raw1566 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1566step0 raw1566; decide +kernel
      have hl : raw1566step0Labels = raw1566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1566 raw1566Labels permutation32 permutation4
    mixedMoment B raw1566step0 raw1566step0Labels = mixedMoment B raw1566step1 raw1566step1Labels := by
      have ha : raw1566step1 = raw1566step0 := by apply Matrix.ext; unfold raw1566step1 raw1566step0; decide +kernel
      have hl : raw1566step0Labels = labelEmbedding7 ∘ raw1566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1566step0 raw1566step0Labels raw1566step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw1567 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1567 raw1567Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw1567 raw1567Labels = mixedMoment B raw1567step0 raw1567step0Labels := by
      have ha : raw1567step0 = (fun i j => raw1567 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1567step0 raw1567; decide +kernel
      have hl : raw1567step0Labels = raw1567Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1567 raw1567Labels permutation32 permutation4
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw1568 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1568Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1568 raw1568Labels = mixedMoment B node2152 node2152Labels := by
  calc
    mixedMoment B raw1568 raw1568Labels = mixedMoment B raw1568step0 raw1568step0Labels := by
      have ha : raw1568step0 = (fun i j => raw1568 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1568step0 raw1568; decide +kernel
      have hl : raw1568step0Labels = raw1568Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1568 raw1568Labels permutation32 permutation6
    mixedMoment B raw1568step0 raw1568step0Labels = mixedMoment B raw1568step1 raw1568step1Labels := by
      have ha : raw1568step1 = -raw1568step0 := by apply Matrix.ext; change ∀ i j, raw1568step1 i j = -(raw1568step0 i j); unfold raw1568step1 raw1568step0; decide +kernel
      have hl : raw1568step1Labels = raw1568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1568step1 raw1568step1Labels = mixedMoment B raw1568step2 raw1568step2Labels := by
      have ha : raw1568step2 = raw1568step1 := by apply Matrix.ext; unfold raw1568step2 raw1568step1; decide +kernel
      have hl : raw1568step1Labels = labelEmbedding1 ∘ raw1568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1568step1 raw1568step1Labels raw1568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2152 node2152Labels := by rfl

def raw1569 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1569step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1569 raw1569Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw1569 raw1569Labels = mixedMoment B raw1569step0 raw1569step0Labels := by
      have ha : raw1569step0 = (fun i j => raw1569 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1569step0 raw1569; decide +kernel
      have hl : raw1569step0Labels = raw1569Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1569 raw1569Labels permutation152 permutation4
    mixedMoment B raw1569step0 raw1569step0Labels = mixedMoment B raw1569step1 raw1569step1Labels := by
      have ha : raw1569step1 = raw1569step0 := by apply Matrix.ext; unfold raw1569step1 raw1569step0; decide +kernel
      have hl : raw1569step0Labels = labelEmbedding7 ∘ raw1569step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1569step0 raw1569step0Labels raw1569step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4685 node4685Labels := by rfl

def raw1570 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1570 raw1570Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw1570 raw1570Labels = mixedMoment B raw1570step0 raw1570step0Labels := by
      have ha : raw1570step0 = (fun i j => raw1570 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1570step0 raw1570; decide +kernel
      have hl : raw1570step0Labels = raw1570Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1570 raw1570Labels permutation152 permutation4
    _ = mixedMoment B node1811 node1811Labels := by rfl

def raw1571 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1571Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1571 raw1571Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw1571 raw1571Labels = mixedMoment B raw1571step0 raw1571step0Labels := by
      have ha : raw1571step0 = (fun i j => raw1571 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1571step0 raw1571; decide +kernel
      have hl : raw1571step0Labels = raw1571Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1571 raw1571Labels permutation170 permutation6
    mixedMoment B raw1571step0 raw1571step0Labels = mixedMoment B raw1571step1 raw1571step1Labels := by
      have ha : raw1571step1 = -raw1571step0 := by apply Matrix.ext; change ∀ i j, raw1571step1 i j = -(raw1571step0 i j); unfold raw1571step1 raw1571step0; decide +kernel
      have hl : raw1571step1Labels = raw1571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1571step1 raw1571step1Labels = mixedMoment B raw1571step2 raw1571step2Labels := by
      have ha : raw1571step2 = raw1571step1 := by apply Matrix.ext; unfold raw1571step2 raw1571step1; decide +kernel
      have hl : raw1571step1Labels = labelEmbedding1 ∘ raw1571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1571step1 raw1571step1Labels raw1571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

def raw1572 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1572step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1572 raw1572Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw1572 raw1572Labels = mixedMoment B raw1572step0 raw1572step0Labels := by
      have ha : raw1572step0 = (fun i j => raw1572 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1572step0 raw1572; decide +kernel
      have hl : raw1572step0Labels = raw1572Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1572 raw1572Labels permutation32 permutation4
    mixedMoment B raw1572step0 raw1572step0Labels = mixedMoment B raw1572step1 raw1572step1Labels := by
      have ha : raw1572step1 = raw1572step0 := by apply Matrix.ext; unfold raw1572step1 raw1572step0; decide +kernel
      have hl : raw1572step0Labels = labelEmbedding7 ∘ raw1572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1572step0 raw1572step0Labels raw1572step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw1573 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1573 raw1573Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw1573 raw1573Labels = mixedMoment B raw1573step0 raw1573step0Labels := by
      have ha : raw1573step0 = (fun i j => raw1573 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1573step0 raw1573; decide +kernel
      have hl : raw1573step0Labels = raw1573Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1573 raw1573Labels permutation32 permutation4
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw1574 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1574Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1574step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1574 raw1574Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw1574 raw1574Labels = mixedMoment B raw1574step0 raw1574step0Labels := by
      have ha : raw1574step0 = (fun i j => raw1574 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1574step0 raw1574; decide +kernel
      have hl : raw1574step0Labels = raw1574Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1574 raw1574Labels permutation32 permutation6
    mixedMoment B raw1574step0 raw1574step0Labels = mixedMoment B raw1574step1 raw1574step1Labels := by
      have ha : raw1574step1 = -raw1574step0 := by apply Matrix.ext; change ∀ i j, raw1574step1 i j = -(raw1574step0 i j); unfold raw1574step1 raw1574step0; decide +kernel
      have hl : raw1574step1Labels = raw1574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1574step1 raw1574step1Labels = mixedMoment B raw1574step2 raw1574step2Labels := by
      have ha : raw1574step2 = raw1574step1 := by apply Matrix.ext; unfold raw1574step2 raw1574step1; decide +kernel
      have hl : raw1574step1Labels = labelEmbedding1 ∘ raw1574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1574step1 raw1574step1Labels raw1574step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2165 node2165Labels := by rfl

def raw1575 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1575step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1575 raw1575Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw1575 raw1575Labels = mixedMoment B raw1575step0 raw1575step0Labels := by
      have ha : raw1575step0 = (fun i j => raw1575 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1575step0 raw1575; decide +kernel
      have hl : raw1575step0Labels = raw1575Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1575 raw1575Labels permutation32 permutation4
    mixedMoment B raw1575step0 raw1575step0Labels = mixedMoment B raw1575step1 raw1575step1Labels := by
      have ha : raw1575step1 = raw1575step0 := by apply Matrix.ext; unfold raw1575step1 raw1575step0; decide +kernel
      have hl : raw1575step0Labels = labelEmbedding7 ∘ raw1575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1575step0 raw1575step0Labels raw1575step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw1576 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1576 raw1576Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw1576 raw1576Labels = mixedMoment B raw1576step0 raw1576step0Labels := by
      have ha : raw1576step0 = (fun i j => raw1576 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1576step0 raw1576; decide +kernel
      have hl : raw1576step0Labels = raw1576Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1576 raw1576Labels permutation32 permutation4
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw1577 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1577Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1577step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1577step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1577 raw1577Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw1577 raw1577Labels = mixedMoment B raw1577step0 raw1577step0Labels := by
      have ha : raw1577step0 = (fun i j => raw1577 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1577step0 raw1577; decide +kernel
      have hl : raw1577step0Labels = raw1577Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1577 raw1577Labels permutation34 permutation6
    mixedMoment B raw1577step0 raw1577step0Labels = mixedMoment B raw1577step1 raw1577step1Labels := by
      have ha : raw1577step1 = -raw1577step0 := by apply Matrix.ext; change ∀ i j, raw1577step1 i j = -(raw1577step0 i j); unfold raw1577step1 raw1577step0; decide +kernel
      have hl : raw1577step1Labels = raw1577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1577step1 raw1577step1Labels = mixedMoment B raw1577step2 raw1577step2Labels := by
      have ha : raw1577step2 = raw1577step1 := by apply Matrix.ext; unfold raw1577step2 raw1577step1; decide +kernel
      have hl : raw1577step1Labels = labelEmbedding1 ∘ raw1577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1577step1 raw1577step1Labels raw1577step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

def raw1578 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1578step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1578 raw1578Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw1578 raw1578Labels = mixedMoment B raw1578step0 raw1578step0Labels := by
      have ha : raw1578step0 = (fun i j => raw1578 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1578step0 raw1578; decide +kernel
      have hl : raw1578step0Labels = raw1578Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1578 raw1578Labels permutation32 permutation4
    mixedMoment B raw1578step0 raw1578step0Labels = mixedMoment B raw1578step1 raw1578step1Labels := by
      have ha : raw1578step1 = raw1578step0 := by apply Matrix.ext; unfold raw1578step1 raw1578step0; decide +kernel
      have hl : raw1578step0Labels = labelEmbedding7 ∘ raw1578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1578step0 raw1578step0Labels raw1578step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw1579 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1579Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1579 raw1579Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw1579 raw1579Labels = mixedMoment B raw1579step0 raw1579step0Labels := by
      have ha : raw1579step0 = (fun i j => raw1579 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1579step0 raw1579; decide +kernel
      have hl : raw1579step0Labels = raw1579Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1579 raw1579Labels permutation32 permutation4
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw1580 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1580Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1580 raw1580Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw1580 raw1580Labels = mixedMoment B raw1580step0 raw1580step0Labels := by
      have ha : raw1580step0 = (fun i j => raw1580 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1580step0 raw1580; decide +kernel
      have hl : raw1580step0Labels = raw1580Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1580 raw1580Labels permutation32 permutation6
    mixedMoment B raw1580step0 raw1580step0Labels = mixedMoment B raw1580step1 raw1580step1Labels := by
      have ha : raw1580step1 = -raw1580step0 := by apply Matrix.ext; change ∀ i j, raw1580step1 i j = -(raw1580step0 i j); unfold raw1580step1 raw1580step0; decide +kernel
      have hl : raw1580step1Labels = raw1580step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1580step1 raw1580step1Labels = mixedMoment B raw1580step2 raw1580step2Labels := by
      have ha : raw1580step2 = raw1580step1 := by apply Matrix.ext; unfold raw1580step2 raw1580step1; decide +kernel
      have hl : raw1580step1Labels = labelEmbedding1 ∘ raw1580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1580step1 raw1580step1Labels raw1580step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

def raw1581 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1581step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1581step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1581 raw1581Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw1581 raw1581Labels = mixedMoment B raw1581step0 raw1581step0Labels := by
      have ha : raw1581step0 = (fun i j => raw1581 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1581step0 raw1581; decide +kernel
      have hl : raw1581step0Labels = raw1581Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1581 raw1581Labels permutation8 permutation4
    mixedMoment B raw1581step0 raw1581step0Labels = mixedMoment B raw1581step1 raw1581step1Labels := by
      have ha : raw1581step1 = raw1581step0 := by apply Matrix.ext; unfold raw1581step1 raw1581step0; decide +kernel
      have hl : raw1581step0Labels = labelEmbedding7 ∘ raw1581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1581step0 raw1581step0Labels raw1581step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4691 node4691Labels := by rfl

def raw1582 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1582Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1582step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1582 raw1582Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw1582 raw1582Labels = mixedMoment B raw1582step0 raw1582step0Labels := by
      have ha : raw1582step0 = (fun i j => raw1582 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1582step0 raw1582; decide +kernel
      have hl : raw1582step0Labels = raw1582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1582 raw1582Labels permutation8 permutation4
    _ = mixedMoment B node1817 node1817Labels := by rfl

def raw1583 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1583Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1583step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw1583step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw1583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1583 raw1583Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw1583 raw1583Labels = mixedMoment B raw1583step0 raw1583step0Labels := by
      have ha : raw1583step0 = (fun i j => raw1583 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1583step0 raw1583; decide +kernel
      have hl : raw1583step0Labels = raw1583Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1583 raw1583Labels permutation31 permutation6
    mixedMoment B raw1583step0 raw1583step0Labels = mixedMoment B raw1583step1 raw1583step1Labels := by
      have ha : raw1583step1 = raw1583step0 := by apply Matrix.ext; unfold raw1583step1 raw1583step0; decide +kernel
      have hl : raw1583step0Labels = labelEmbedding1 ∘ raw1583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1583step0 raw1583step0Labels raw1583step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2159 node2159Labels := by rfl

def raw1584 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1584step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1584step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1584 raw1584Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw1584 raw1584Labels = mixedMoment B raw1584step0 raw1584step0Labels := by
      have ha : raw1584step0 = (fun i j => raw1584 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1584step0 raw1584; decide +kernel
      have hl : raw1584step0Labels = raw1584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1584 raw1584Labels permutation8 permutation4
    mixedMoment B raw1584step0 raw1584step0Labels = mixedMoment B raw1584step1 raw1584step1Labels := by
      have ha : raw1584step1 = raw1584step0 := by apply Matrix.ext; unfold raw1584step1 raw1584step0; decide +kernel
      have hl : raw1584step0Labels = labelEmbedding7 ∘ raw1584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1584step0 raw1584step0Labels raw1584step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw1585 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1585Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1585step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1585 raw1585Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw1585 raw1585Labels = mixedMoment B raw1585step0 raw1585step0Labels := by
      have ha : raw1585step0 = (fun i j => raw1585 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1585step0 raw1585; decide +kernel
      have hl : raw1585step0Labels = raw1585Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1585 raw1585Labels permutation8 permutation4
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw1586 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1586Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1586step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw1586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw1586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1586 raw1586Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw1586 raw1586Labels = mixedMoment B raw1586step0 raw1586step0Labels := by
      have ha : raw1586step0 = (fun i j => raw1586 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1586step0 raw1586; decide +kernel
      have hl : raw1586step0Labels = raw1586Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1586 raw1586Labels permutation8 permutation6
    mixedMoment B raw1586step0 raw1586step0Labels = mixedMoment B raw1586step1 raw1586step1Labels := by
      have ha : raw1586step1 = -raw1586step0 := by apply Matrix.ext; change ∀ i j, raw1586step1 i j = -(raw1586step0 i j); unfold raw1586step1 raw1586step0; decide +kernel
      have hl : raw1586step1Labels = raw1586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1586step1 raw1586step1Labels = mixedMoment B raw1586step2 raw1586step2Labels := by
      have ha : raw1586step2 = raw1586step1 := by apply Matrix.ext; unfold raw1586step2 raw1586step1; decide +kernel
      have hl : raw1586step1Labels = labelEmbedding1 ∘ raw1586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1586step1 raw1586step1Labels raw1586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw1587 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1587step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1587step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1587 raw1587Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw1587 raw1587Labels = mixedMoment B raw1587step0 raw1587step0Labels := by
      have ha : raw1587step0 = (fun i j => raw1587 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1587step0 raw1587; decide +kernel
      have hl : raw1587step0Labels = raw1587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1587 raw1587Labels permutation8 permutation4
    mixedMoment B raw1587step0 raw1587step0Labels = mixedMoment B raw1587step1 raw1587step1Labels := by
      have ha : raw1587step1 = raw1587step0 := by apply Matrix.ext; unfold raw1587step1 raw1587step0; decide +kernel
      have hl : raw1587step0Labels = labelEmbedding7 ∘ raw1587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1587step0 raw1587step0Labels raw1587step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw1588 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1588Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1588step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1588 raw1588Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw1588 raw1588Labels = mixedMoment B raw1588step0 raw1588step0Labels := by
      have ha : raw1588step0 = (fun i j => raw1588 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1588step0 raw1588; decide +kernel
      have hl : raw1588step0Labels = raw1588Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1588 raw1588Labels permutation8 permutation4
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw1589 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1589Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1589step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw1589step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1589step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw1589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1589 raw1589Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw1589 raw1589Labels = mixedMoment B raw1589step0 raw1589step0Labels := by
      have ha : raw1589step0 = (fun i j => raw1589 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1589step0 raw1589; decide +kernel
      have hl : raw1589step0Labels = raw1589Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1589 raw1589Labels permutation9 permutation6
    mixedMoment B raw1589step0 raw1589step0Labels = mixedMoment B raw1589step1 raw1589step1Labels := by
      have ha : raw1589step1 = -raw1589step0 := by apply Matrix.ext; change ∀ i j, raw1589step1 i j = -(raw1589step0 i j); unfold raw1589step1 raw1589step0; decide +kernel
      have hl : raw1589step1Labels = raw1589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1589step1 raw1589step1Labels = mixedMoment B raw1589step2 raw1589step2Labels := by
      have ha : raw1589step2 = raw1589step1 := by apply Matrix.ext; unfold raw1589step2 raw1589step1; decide +kernel
      have hl : raw1589step1Labels = labelEmbedding1 ∘ raw1589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1589step1 raw1589step1Labels raw1589step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2169 node2169Labels := by rfl

def raw1590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1590step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1590 raw1590Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw1590 raw1590Labels = mixedMoment B raw1590step0 raw1590step0Labels := by
      have ha : raw1590step0 = (fun i j => raw1590 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1590step0 raw1590; decide +kernel
      have hl : raw1590step0Labels = raw1590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1590 raw1590Labels permutation152 permutation4
    mixedMoment B raw1590step0 raw1590step0Labels = mixedMoment B raw1590step1 raw1590step1Labels := by
      have ha : raw1590step1 = raw1590step0 := by apply Matrix.ext; unfold raw1590step1 raw1590step0; decide +kernel
      have hl : raw1590step0Labels = labelEmbedding7 ∘ raw1590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1590step0 raw1590step0Labels raw1590step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

def raw1591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1591Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1591 raw1591Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw1591 raw1591Labels = mixedMoment B raw1591step0 raw1591step0Labels := by
      have ha : raw1591step0 = (fun i j => raw1591 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1591step0 raw1591; decide +kernel
      have hl : raw1591step0Labels = raw1591Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1591 raw1591Labels permutation152 permutation4
    _ = mixedMoment B node1860 node1860Labels := by rfl

def raw1592 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1592Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1592step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1592 raw1592Labels = mixedMoment B node1888 node1888Labels := by
  calc
    mixedMoment B raw1592 raw1592Labels = mixedMoment B raw1592step0 raw1592step0Labels := by
      have ha : raw1592step0 = (fun i j => raw1592 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1592step0 raw1592; decide +kernel
      have hl : raw1592step0Labels = raw1592Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1592 raw1592Labels permutation152 permutation6
    mixedMoment B raw1592step0 raw1592step0Labels = mixedMoment B raw1592step1 raw1592step1Labels := by
      have ha : raw1592step1 = -raw1592step0 := by apply Matrix.ext; change ∀ i j, raw1592step1 i j = -(raw1592step0 i j); unfold raw1592step1 raw1592step0; decide +kernel
      have hl : raw1592step1Labels = raw1592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1592step1 raw1592step1Labels = mixedMoment B raw1592step2 raw1592step2Labels := by
      have ha : raw1592step2 = raw1592step1 := by apply Matrix.ext; unfold raw1592step2 raw1592step1; decide +kernel
      have hl : raw1592step1Labels = labelEmbedding1 ∘ raw1592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1592step1 raw1592step1Labels raw1592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1888 node1888Labels := by rfl

def raw1593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1593step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1593 raw1593Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw1593 raw1593Labels = mixedMoment B raw1593step0 raw1593step0Labels := by
      have ha : raw1593step0 = (fun i j => raw1593 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1593step0 raw1593; decide +kernel
      have hl : raw1593step0Labels = raw1593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1593 raw1593Labels permutation152 permutation4
    mixedMoment B raw1593step0 raw1593step0Labels = mixedMoment B raw1593step1 raw1593step1Labels := by
      have ha : raw1593step1 = raw1593step0 := by apply Matrix.ext; unfold raw1593step1 raw1593step0; decide +kernel
      have hl : raw1593step0Labels = labelEmbedding7 ∘ raw1593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1593step0 raw1593step0Labels raw1593step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

def raw1594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1594 raw1594Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw1594 raw1594Labels = mixedMoment B raw1594step0 raw1594step0Labels := by
      have ha : raw1594step0 = (fun i j => raw1594 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1594step0 raw1594; decide +kernel
      have hl : raw1594step0Labels = raw1594Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1594 raw1594Labels permutation152 permutation4
    _ = mixedMoment B node1861 node1861Labels := by rfl

def raw1595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1595Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw1595step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1595step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1595 raw1595Labels = mixedMoment B node1889 node1889Labels := by
  calc
    mixedMoment B raw1595 raw1595Labels = mixedMoment B raw1595step0 raw1595step0Labels := by
      have ha : raw1595step0 = (fun i j => raw1595 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1595step0 raw1595; decide +kernel
      have hl : raw1595step0Labels = raw1595Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1595 raw1595Labels permutation153 permutation6
    mixedMoment B raw1595step0 raw1595step0Labels = mixedMoment B raw1595step1 raw1595step1Labels := by
      have ha : raw1595step1 = -raw1595step0 := by apply Matrix.ext; change ∀ i j, raw1595step1 i j = -(raw1595step0 i j); unfold raw1595step1 raw1595step0; decide +kernel
      have hl : raw1595step1Labels = raw1595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1595step1 raw1595step1Labels = mixedMoment B raw1595step2 raw1595step2Labels := by
      have ha : raw1595step2 = raw1595step1 := by apply Matrix.ext; unfold raw1595step2 raw1595step1; decide +kernel
      have hl : raw1595step1Labels = labelEmbedding1 ∘ raw1595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1595step1 raw1595step1Labels raw1595step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1889 node1889Labels := by rfl

def raw1596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1596step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1596 raw1596Labels = mixedMoment B node4709 node4709Labels := by
  calc
    mixedMoment B raw1596 raw1596Labels = mixedMoment B raw1596step0 raw1596step0Labels := by
      have ha : raw1596step0 = (fun i j => raw1596 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1596step0 raw1596; decide +kernel
      have hl : raw1596step0Labels = raw1596Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1596 raw1596Labels permutation152 permutation4
    mixedMoment B raw1596step0 raw1596step0Labels = mixedMoment B raw1596step1 raw1596step1Labels := by
      have ha : raw1596step1 = raw1596step0 := by apply Matrix.ext; unfold raw1596step1 raw1596step0; decide +kernel
      have hl : raw1596step0Labels = labelEmbedding7 ∘ raw1596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1596step0 raw1596step0Labels raw1596step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4709 node4709Labels := by rfl

def raw1597 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1597 raw1597Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw1597 raw1597Labels = mixedMoment B raw1597step0 raw1597step0Labels := by
      have ha : raw1597step0 = (fun i j => raw1597 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1597step0 raw1597; decide +kernel
      have hl : raw1597step0Labels = raw1597Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1597 raw1597Labels permutation152 permutation4
    _ = mixedMoment B node1863 node1863Labels := by rfl

def raw1598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1598Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1598 raw1598Labels = mixedMoment B node1883 node1883Labels := by
  calc
    mixedMoment B raw1598 raw1598Labels = mixedMoment B raw1598step0 raw1598step0Labels := by
      have ha : raw1598step0 = (fun i j => raw1598 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1598step0 raw1598; decide +kernel
      have hl : raw1598step0Labels = raw1598Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1598 raw1598Labels permutation152 permutation6
    mixedMoment B raw1598step0 raw1598step0Labels = mixedMoment B raw1598step1 raw1598step1Labels := by
      have ha : raw1598step1 = -raw1598step0 := by apply Matrix.ext; change ∀ i j, raw1598step1 i j = -(raw1598step0 i j); unfold raw1598step1 raw1598step0; decide +kernel
      have hl : raw1598step1Labels = raw1598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1598step1 raw1598step1Labels = mixedMoment B raw1598step2 raw1598step2Labels := by
      have ha : raw1598step2 = raw1598step1 := by apply Matrix.ext; unfold raw1598step2 raw1598step1; decide +kernel
      have hl : raw1598step1Labels = labelEmbedding1 ∘ raw1598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1598step1 raw1598step1Labels raw1598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1883 node1883Labels := by rfl

def raw1599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1599step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1599 raw1599Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw1599 raw1599Labels = mixedMoment B raw1599step0 raw1599step0Labels := by
      have ha : raw1599step0 = (fun i j => raw1599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1599step0 raw1599; decide +kernel
      have hl : raw1599step0Labels = raw1599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1599 raw1599Labels permutation152 permutation4
    mixedMoment B raw1599step0 raw1599step0Labels = mixedMoment B raw1599step1 raw1599step1Labels := by
      have ha : raw1599step1 = raw1599step0 := by apply Matrix.ext; unfold raw1599step1 raw1599step0; decide +kernel
      have hl : raw1599step0Labels = labelEmbedding7 ∘ raw1599step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1599step0 raw1599step0Labels raw1599step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

def raw1600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1600 raw1600Labels = mixedMoment B node1864 node1864Labels := by
  calc
    mixedMoment B raw1600 raw1600Labels = mixedMoment B raw1600step0 raw1600step0Labels := by
      have ha : raw1600step0 = (fun i j => raw1600 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1600step0 raw1600; decide +kernel
      have hl : raw1600step0Labels = raw1600Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1600 raw1600Labels permutation152 permutation4
    _ = mixedMoment B node1864 node1864Labels := by rfl

def raw1601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1601Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw1601step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1601step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1601step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1601 raw1601Labels = mixedMoment B node1882 node1882Labels := by
  calc
    mixedMoment B raw1601 raw1601Labels = mixedMoment B raw1601step0 raw1601step0Labels := by
      have ha : raw1601step0 = (fun i j => raw1601 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1601step0 raw1601; decide +kernel
      have hl : raw1601step0Labels = raw1601Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1601 raw1601Labels permutation152 permutation6
    mixedMoment B raw1601step0 raw1601step0Labels = mixedMoment B raw1601step1 raw1601step1Labels := by
      have ha : raw1601step1 = -raw1601step0 := by apply Matrix.ext; change ∀ i j, raw1601step1 i j = -(raw1601step0 i j); unfold raw1601step1 raw1601step0; decide +kernel
      have hl : raw1601step1Labels = raw1601step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1601step1 raw1601step1Labels = mixedMoment B raw1601step2 raw1601step2Labels := by
      have ha : raw1601step2 = raw1601step1 := by apply Matrix.ext; unfold raw1601step2 raw1601step1; decide +kernel
      have hl : raw1601step1Labels = labelEmbedding1 ∘ raw1601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1601step1 raw1601step1Labels raw1601step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1882 node1882Labels := by rfl

def raw1602 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1602step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1602 raw1602Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw1602 raw1602Labels = mixedMoment B raw1602step0 raw1602step0Labels := by
      have ha : raw1602step0 = (fun i j => raw1602 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1602step0 raw1602; decide +kernel
      have hl : raw1602step0Labels = raw1602Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1602 raw1602Labels permutation152 permutation4
    mixedMoment B raw1602step0 raw1602step0Labels = mixedMoment B raw1602step1 raw1602step1Labels := by
      have ha : raw1602step1 = raw1602step0 := by apply Matrix.ext; unfold raw1602step1 raw1602step0; decide +kernel
      have hl : raw1602step0Labels = labelEmbedding7 ∘ raw1602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1602step0 raw1602step0Labels raw1602step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

def raw1603 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1603Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1603 raw1603Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw1603 raw1603Labels = mixedMoment B raw1603step0 raw1603step0Labels := by
      have ha : raw1603step0 = (fun i j => raw1603 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1603step0 raw1603; decide +kernel
      have hl : raw1603step0Labels = raw1603Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1603 raw1603Labels permutation152 permutation4
    _ = mixedMoment B node1867 node1867Labels := by rfl

def raw1604 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1604Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1604 raw1604Labels = mixedMoment B node1891 node1891Labels := by
  calc
    mixedMoment B raw1604 raw1604Labels = mixedMoment B raw1604step0 raw1604step0Labels := by
      have ha : raw1604step0 = (fun i j => raw1604 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1604step0 raw1604; decide +kernel
      have hl : raw1604step0Labels = raw1604Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1604 raw1604Labels permutation153 permutation6
    mixedMoment B raw1604step0 raw1604step0Labels = mixedMoment B raw1604step1 raw1604step1Labels := by
      have ha : raw1604step1 = -raw1604step0 := by apply Matrix.ext; change ∀ i j, raw1604step1 i j = -(raw1604step0 i j); unfold raw1604step1 raw1604step0; decide +kernel
      have hl : raw1604step1Labels = raw1604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1604step1 raw1604step1Labels = mixedMoment B raw1604step2 raw1604step2Labels := by
      have ha : raw1604step2 = raw1604step1 := by apply Matrix.ext; unfold raw1604step2 raw1604step1; decide +kernel
      have hl : raw1604step1Labels = labelEmbedding1 ∘ raw1604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1604step1 raw1604step1Labels raw1604step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1891 node1891Labels := by rfl

def raw1605 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1605step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1605 raw1605Labels = mixedMoment B node4714 node4714Labels := by
  calc
    mixedMoment B raw1605 raw1605Labels = mixedMoment B raw1605step0 raw1605step0Labels := by
      have ha : raw1605step0 = (fun i j => raw1605 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1605step0 raw1605; decide +kernel
      have hl : raw1605step0Labels = raw1605Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1605 raw1605Labels permutation152 permutation4
    mixedMoment B raw1605step0 raw1605step0Labels = mixedMoment B raw1605step1 raw1605step1Labels := by
      have ha : raw1605step1 = raw1605step0 := by apply Matrix.ext; unfold raw1605step1 raw1605step0; decide +kernel
      have hl : raw1605step0Labels = labelEmbedding7 ∘ raw1605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1605step0 raw1605step0Labels raw1605step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4714 node4714Labels := by rfl

def raw1606 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1606Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1606 raw1606Labels = mixedMoment B node1868 node1868Labels := by
  calc
    mixedMoment B raw1606 raw1606Labels = mixedMoment B raw1606step0 raw1606step0Labels := by
      have ha : raw1606step0 = (fun i j => raw1606 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1606step0 raw1606; decide +kernel
      have hl : raw1606step0Labels = raw1606Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1606 raw1606Labels permutation152 permutation4
    _ = mixedMoment B node1868 node1868Labels := by rfl

def raw1607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1607Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw1607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw1607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw1607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1607 raw1607Labels = mixedMoment B node1885 node1885Labels := by
  calc
    mixedMoment B raw1607 raw1607Labels = mixedMoment B raw1607step0 raw1607step0Labels := by
      have ha : raw1607step0 = (fun i j => raw1607 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1607step0 raw1607; decide +kernel
      have hl : raw1607step0Labels = raw1607Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1607 raw1607Labels permutation154 permutation6
    mixedMoment B raw1607step0 raw1607step0Labels = mixedMoment B raw1607step1 raw1607step1Labels := by
      have ha : raw1607step1 = -raw1607step0 := by apply Matrix.ext; change ∀ i j, raw1607step1 i j = -(raw1607step0 i j); unfold raw1607step1 raw1607step0; decide +kernel
      have hl : raw1607step1Labels = raw1607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1607step1 raw1607step1Labels = mixedMoment B raw1607step2 raw1607step2Labels := by
      have ha : raw1607step2 = raw1607step1 := by apply Matrix.ext; unfold raw1607step2 raw1607step1; decide +kernel
      have hl : raw1607step1Labels = labelEmbedding1 ∘ raw1607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1607step1 raw1607step1Labels raw1607step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1885 node1885Labels := by rfl

def raw1608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1608step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1608 raw1608Labels = mixedMoment B node4716 node4716Labels := by
  calc
    mixedMoment B raw1608 raw1608Labels = mixedMoment B raw1608step0 raw1608step0Labels := by
      have ha : raw1608step0 = (fun i j => raw1608 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1608step0 raw1608; decide +kernel
      have hl : raw1608step0Labels = raw1608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1608 raw1608Labels permutation152 permutation4
    mixedMoment B raw1608step0 raw1608step0Labels = mixedMoment B raw1608step1 raw1608step1Labels := by
      have ha : raw1608step1 = raw1608step0 := by apply Matrix.ext; unfold raw1608step1 raw1608step0; decide +kernel
      have hl : raw1608step0Labels = labelEmbedding7 ∘ raw1608step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1608step0 raw1608step0Labels raw1608step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4716 node4716Labels := by rfl

def raw1609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1609Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1609 raw1609Labels = mixedMoment B node1870 node1870Labels := by
  calc
    mixedMoment B raw1609 raw1609Labels = mixedMoment B raw1609step0 raw1609step0Labels := by
      have ha : raw1609step0 = (fun i j => raw1609 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1609step0 raw1609; decide +kernel
      have hl : raw1609step0Labels = raw1609Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1609 raw1609Labels permutation152 permutation4
    _ = mixedMoment B node1870 node1870Labels := by rfl

def raw1610 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1610Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw1610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1610 raw1610Labels = mixedMoment B node1886 node1886Labels := by
  calc
    mixedMoment B raw1610 raw1610Labels = mixedMoment B raw1610step0 raw1610step0Labels := by
      have ha : raw1610step0 = (fun i j => raw1610 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1610step0 raw1610; decide +kernel
      have hl : raw1610step0Labels = raw1610Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1610 raw1610Labels permutation154 permutation6
    mixedMoment B raw1610step0 raw1610step0Labels = mixedMoment B raw1610step1 raw1610step1Labels := by
      have ha : raw1610step1 = -raw1610step0 := by apply Matrix.ext; change ∀ i j, raw1610step1 i j = -(raw1610step0 i j); unfold raw1610step1 raw1610step0; decide +kernel
      have hl : raw1610step1Labels = raw1610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1610step1 raw1610step1Labels = mixedMoment B raw1610step2 raw1610step2Labels := by
      have ha : raw1610step2 = raw1610step1 := by apply Matrix.ext; unfold raw1610step2 raw1610step1; decide +kernel
      have hl : raw1610step1Labels = labelEmbedding1 ∘ raw1610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1610step1 raw1610step1Labels raw1610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1886 node1886Labels := by rfl

def raw1611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1611step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1611 raw1611Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw1611 raw1611Labels = mixedMoment B raw1611step0 raw1611step0Labels := by
      have ha : raw1611step0 = (fun i j => raw1611 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1611step0 raw1611; decide +kernel
      have hl : raw1611step0Labels = raw1611Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1611 raw1611Labels permutation152 permutation4
    mixedMoment B raw1611step0 raw1611step0Labels = mixedMoment B raw1611step1 raw1611step1Labels := by
      have ha : raw1611step1 = raw1611step0 := by apply Matrix.ext; unfold raw1611step1 raw1611step0; decide +kernel
      have hl : raw1611step0Labels = labelEmbedding7 ∘ raw1611step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1611step0 raw1611step0Labels raw1611step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

def raw1612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1612 raw1612Labels = mixedMoment B node1871 node1871Labels := by
  calc
    mixedMoment B raw1612 raw1612Labels = mixedMoment B raw1612step0 raw1612step0Labels := by
      have ha : raw1612step0 = (fun i j => raw1612 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1612step0 raw1612; decide +kernel
      have hl : raw1612step0Labels = raw1612Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1612 raw1612Labels permutation152 permutation4
    _ = mixedMoment B node1871 node1871Labels := by rfl

def raw1613 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1613Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw1613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1613 raw1613Labels = mixedMoment B node1892 node1892Labels := by
  calc
    mixedMoment B raw1613 raw1613Labels = mixedMoment B raw1613step0 raw1613step0Labels := by
      have ha : raw1613step0 = (fun i j => raw1613 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1613step0 raw1613; decide +kernel
      have hl : raw1613step0Labels = raw1613Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1613 raw1613Labels permutation155 permutation6
    mixedMoment B raw1613step0 raw1613step0Labels = mixedMoment B raw1613step1 raw1613step1Labels := by
      have ha : raw1613step1 = -raw1613step0 := by apply Matrix.ext; change ∀ i j, raw1613step1 i j = -(raw1613step0 i j); unfold raw1613step1 raw1613step0; decide +kernel
      have hl : raw1613step1Labels = raw1613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1613step1 raw1613step1Labels = mixedMoment B raw1613step2 raw1613step2Labels := by
      have ha : raw1613step2 = raw1613step1 := by apply Matrix.ext; unfold raw1613step2 raw1613step1; decide +kernel
      have hl : raw1613step1Labels = labelEmbedding1 ∘ raw1613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1613step1 raw1613step1Labels raw1613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1892 node1892Labels := by rfl

def raw1614 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw1614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw1614step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw1614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1614 raw1614Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw1614 raw1614Labels = mixedMoment B raw1614step0 raw1614step0Labels := by
      have ha : raw1614step0 = (fun i j => raw1614 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1614step0 raw1614; decide +kernel
      have hl : raw1614step0Labels = raw1614Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1614 raw1614Labels permutation32 permutation4
    mixedMoment B raw1614step0 raw1614step0Labels = mixedMoment B raw1614step1 raw1614step1Labels := by
      have ha : raw1614step1 = raw1614step0 := by apply Matrix.ext; unfold raw1614step1 raw1614step0; decide +kernel
      have hl : raw1614step0Labels = labelEmbedding7 ∘ raw1614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1614step0 raw1614step0Labels raw1614step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

def raw1615 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw1615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw1615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1615 raw1615Labels = mixedMoment B node1873 node1873Labels := by
  calc
    mixedMoment B raw1615 raw1615Labels = mixedMoment B raw1615step0 raw1615step0Labels := by
      have ha : raw1615step0 = (fun i j => raw1615 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1615step0 raw1615; decide +kernel
      have hl : raw1615step0Labels = raw1615Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1615 raw1615Labels permutation32 permutation4
    _ = mixedMoment B node1873 node1873Labels := by rfl

def raw1616 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw1616Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw1616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw1616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1616 raw1616Labels = mixedMoment B node1893 node1893Labels := by
  calc
    mixedMoment B raw1616 raw1616Labels = mixedMoment B raw1616step0 raw1616step0Labels := by
      have ha : raw1616step0 = (fun i j => raw1616 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1616step0 raw1616; decide +kernel
      have hl : raw1616step0Labels = raw1616Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1616 raw1616Labels permutation33 permutation6
    mixedMoment B raw1616step0 raw1616step0Labels = mixedMoment B raw1616step1 raw1616step1Labels := by
      have ha : raw1616step1 = -raw1616step0 := by apply Matrix.ext; change ∀ i j, raw1616step1 i j = -(raw1616step0 i j); unfold raw1616step1 raw1616step0; decide +kernel
      have hl : raw1616step1Labels = raw1616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1616step1 raw1616step1Labels = mixedMoment B raw1616step2 raw1616step2Labels := by
      have ha : raw1616step2 = raw1616step1 := by apply Matrix.ext; unfold raw1616step2 raw1616step1; decide +kernel
      have hl : raw1616step1Labels = labelEmbedding1 ∘ raw1616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1616step1 raw1616step1Labels raw1616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1893 node1893Labels := by rfl

def raw1617 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1617step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1617 raw1617Labels = mixedMoment B node4720 node4720Labels := by
  calc
    mixedMoment B raw1617 raw1617Labels = mixedMoment B raw1617step0 raw1617step0Labels := by
      have ha : raw1617step0 = (fun i j => raw1617 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1617step0 raw1617; decide +kernel
      have hl : raw1617step0Labels = raw1617Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1617 raw1617Labels permutation152 permutation4
    mixedMoment B raw1617step0 raw1617step0Labels = mixedMoment B raw1617step1 raw1617step1Labels := by
      have ha : raw1617step1 = raw1617step0 := by apply Matrix.ext; unfold raw1617step1 raw1617step0; decide +kernel
      have hl : raw1617step0Labels = labelEmbedding7 ∘ raw1617step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1617step0 raw1617step0Labels raw1617step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4720 node4720Labels := by rfl

def raw1618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1618Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1618 raw1618Labels = mixedMoment B node1874 node1874Labels := by
  calc
    mixedMoment B raw1618 raw1618Labels = mixedMoment B raw1618step0 raw1618step0Labels := by
      have ha : raw1618step0 = (fun i j => raw1618 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1618step0 raw1618; decide +kernel
      have hl : raw1618step0Labels = raw1618Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1618 raw1618Labels permutation152 permutation4
    _ = mixedMoment B node1874 node1874Labels := by rfl

def raw1619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1619Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw1619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1619 raw1619Labels = mixedMoment B node1896 node1896Labels := by
  calc
    mixedMoment B raw1619 raw1619Labels = mixedMoment B raw1619step0 raw1619step0Labels := by
      have ha : raw1619step0 = (fun i j => raw1619 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1619step0 raw1619; decide +kernel
      have hl : raw1619step0Labels = raw1619Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1619 raw1619Labels permutation160 permutation6
    mixedMoment B raw1619step0 raw1619step0Labels = mixedMoment B raw1619step1 raw1619step1Labels := by
      have ha : raw1619step1 = -raw1619step0 := by apply Matrix.ext; change ∀ i j, raw1619step1 i j = -(raw1619step0 i j); unfold raw1619step1 raw1619step0; decide +kernel
      have hl : raw1619step1Labels = raw1619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1619step1 raw1619step1Labels = mixedMoment B raw1619step2 raw1619step2Labels := by
      have ha : raw1619step2 = raw1619step1 := by apply Matrix.ext; unfold raw1619step2 raw1619step1; decide +kernel
      have hl : raw1619step1Labels = labelEmbedding1 ∘ raw1619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1619step1 raw1619step1Labels raw1619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1896 node1896Labels := by rfl

def raw1620 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1620step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1620 raw1620Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw1620 raw1620Labels = mixedMoment B raw1620step0 raw1620step0Labels := by
      have ha : raw1620step0 = (fun i j => raw1620 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1620step0 raw1620; decide +kernel
      have hl : raw1620step0Labels = raw1620Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1620 raw1620Labels permutation152 permutation4
    mixedMoment B raw1620step0 raw1620step0Labels = mixedMoment B raw1620step1 raw1620step1Labels := by
      have ha : raw1620step1 = raw1620step0 := by apply Matrix.ext; unfold raw1620step1 raw1620step0; decide +kernel
      have hl : raw1620step0Labels = labelEmbedding7 ∘ raw1620step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1620step0 raw1620step0Labels raw1620step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

def raw1621 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1621Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1621 raw1621Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw1621 raw1621Labels = mixedMoment B raw1621step0 raw1621step0Labels := by
      have ha : raw1621step0 = (fun i j => raw1621 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1621step0 raw1621; decide +kernel
      have hl : raw1621step0Labels = raw1621Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1621 raw1621Labels permutation152 permutation4
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw1622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1622Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1622 raw1622Labels = mixedMoment B node1905 node1905Labels := by
  calc
    mixedMoment B raw1622 raw1622Labels = mixedMoment B raw1622step0 raw1622step0Labels := by
      have ha : raw1622step0 = (fun i j => raw1622 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1622step0 raw1622; decide +kernel
      have hl : raw1622step0Labels = raw1622Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1622 raw1622Labels permutation158 permutation6
    mixedMoment B raw1622step0 raw1622step0Labels = mixedMoment B raw1622step1 raw1622step1Labels := by
      have ha : raw1622step1 = -raw1622step0 := by apply Matrix.ext; change ∀ i j, raw1622step1 i j = -(raw1622step0 i j); unfold raw1622step1 raw1622step0; decide +kernel
      have hl : raw1622step1Labels = raw1622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1622step1 raw1622step1Labels = mixedMoment B raw1622step2 raw1622step2Labels := by
      have ha : raw1622step2 = raw1622step1 := by apply Matrix.ext; unfold raw1622step2 raw1622step1; decide +kernel
      have hl : raw1622step1Labels = labelEmbedding1 ∘ raw1622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1622step1 raw1622step1Labels raw1622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1905 node1905Labels := by rfl

def raw1623 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1623step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1623 raw1623Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw1623 raw1623Labels = mixedMoment B raw1623step0 raw1623step0Labels := by
      have ha : raw1623step0 = (fun i j => raw1623 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1623step0 raw1623; decide +kernel
      have hl : raw1623step0Labels = raw1623Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1623 raw1623Labels permutation152 permutation4
    mixedMoment B raw1623step0 raw1623step0Labels = mixedMoment B raw1623step1 raw1623step1Labels := by
      have ha : raw1623step1 = raw1623step0 := by apply Matrix.ext; unfold raw1623step1 raw1623step0; decide +kernel
      have hl : raw1623step0Labels = labelEmbedding7 ∘ raw1623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1623step0 raw1623step0Labels raw1623step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

def raw1624 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1624Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1624 raw1624Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw1624 raw1624Labels = mixedMoment B raw1624step0 raw1624step0Labels := by
      have ha : raw1624step0 = (fun i j => raw1624 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1624step0 raw1624; decide +kernel
      have hl : raw1624step0Labels = raw1624Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1624 raw1624Labels permutation152 permutation4
    _ = mixedMoment B node1876 node1876Labels := by rfl

def raw1625 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1625Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1625 raw1625Labels = mixedMoment B node1906 node1906Labels := by
  calc
    mixedMoment B raw1625 raw1625Labels = mixedMoment B raw1625step0 raw1625step0Labels := by
      have ha : raw1625step0 = (fun i j => raw1625 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1625step0 raw1625; decide +kernel
      have hl : raw1625step0Labels = raw1625Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1625 raw1625Labels permutation158 permutation6
    mixedMoment B raw1625step0 raw1625step0Labels = mixedMoment B raw1625step1 raw1625step1Labels := by
      have ha : raw1625step1 = -raw1625step0 := by apply Matrix.ext; change ∀ i j, raw1625step1 i j = -(raw1625step0 i j); unfold raw1625step1 raw1625step0; decide +kernel
      have hl : raw1625step1Labels = raw1625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1625step1 raw1625step1Labels = mixedMoment B raw1625step2 raw1625step2Labels := by
      have ha : raw1625step2 = raw1625step1 := by apply Matrix.ext; unfold raw1625step2 raw1625step1; decide +kernel
      have hl : raw1625step1Labels = labelEmbedding1 ∘ raw1625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1625step1 raw1625step1Labels raw1625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1906 node1906Labels := by rfl

def raw1626 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1626step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1626 raw1626Labels = mixedMoment B node4723 node4723Labels := by
  calc
    mixedMoment B raw1626 raw1626Labels = mixedMoment B raw1626step0 raw1626step0Labels := by
      have ha : raw1626step0 = (fun i j => raw1626 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1626step0 raw1626; decide +kernel
      have hl : raw1626step0Labels = raw1626Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1626 raw1626Labels permutation152 permutation4
    mixedMoment B raw1626step0 raw1626step0Labels = mixedMoment B raw1626step1 raw1626step1Labels := by
      have ha : raw1626step1 = raw1626step0 := by apply Matrix.ext; unfold raw1626step1 raw1626step0; decide +kernel
      have hl : raw1626step0Labels = labelEmbedding7 ∘ raw1626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1626step0 raw1626step0Labels raw1626step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4723 node4723Labels := by rfl

def raw1627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1627Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1627 raw1627Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw1627 raw1627Labels = mixedMoment B raw1627step0 raw1627step0Labels := by
      have ha : raw1627step0 = (fun i j => raw1627 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1627step0 raw1627; decide +kernel
      have hl : raw1627step0Labels = raw1627Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1627 raw1627Labels permutation152 permutation4
    _ = mixedMoment B node1877 node1877Labels := by rfl

def raw1628 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1628Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1628 raw1628Labels = mixedMoment B node1935 node1935Labels := by
  calc
    mixedMoment B raw1628 raw1628Labels = mixedMoment B raw1628step0 raw1628step0Labels := by
      have ha : raw1628step0 = (fun i j => raw1628 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1628step0 raw1628; decide +kernel
      have hl : raw1628step0Labels = raw1628Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1628 raw1628Labels permutation152 permutation6
    mixedMoment B raw1628step0 raw1628step0Labels = mixedMoment B raw1628step1 raw1628step1Labels := by
      have ha : raw1628step1 = -raw1628step0 := by apply Matrix.ext; change ∀ i j, raw1628step1 i j = -(raw1628step0 i j); unfold raw1628step1 raw1628step0; decide +kernel
      have hl : raw1628step1Labels = raw1628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1628step1 raw1628step1Labels = mixedMoment B raw1628step2 raw1628step2Labels := by
      have ha : raw1628step2 = raw1628step1 := by apply Matrix.ext; unfold raw1628step2 raw1628step1; decide +kernel
      have hl : raw1628step1Labels = labelEmbedding1 ∘ raw1628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1628step1 raw1628step1Labels raw1628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1935 node1935Labels := by rfl

def raw1629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1629step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1629 raw1629Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw1629 raw1629Labels = mixedMoment B raw1629step0 raw1629step0Labels := by
      have ha : raw1629step0 = (fun i j => raw1629 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1629step0 raw1629; decide +kernel
      have hl : raw1629step0Labels = raw1629Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1629 raw1629Labels permutation152 permutation4
    mixedMoment B raw1629step0 raw1629step0Labels = mixedMoment B raw1629step1 raw1629step1Labels := by
      have ha : raw1629step1 = raw1629step0 := by apply Matrix.ext; unfold raw1629step1 raw1629step0; decide +kernel
      have hl : raw1629step0Labels = labelEmbedding7 ∘ raw1629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1629step0 raw1629step0Labels raw1629step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

def raw1630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1630 raw1630Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw1630 raw1630Labels = mixedMoment B raw1630step0 raw1630step0Labels := by
      have ha : raw1630step0 = (fun i j => raw1630 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1630step0 raw1630; decide +kernel
      have hl : raw1630step0Labels = raw1630Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1630 raw1630Labels permutation152 permutation4
    _ = mixedMoment B node1878 node1878Labels := by rfl

def raw1631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1631Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1631step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1631 raw1631Labels = mixedMoment B node1919 node1919Labels := by
  calc
    mixedMoment B raw1631 raw1631Labels = mixedMoment B raw1631step0 raw1631step0Labels := by
      have ha : raw1631step0 = (fun i j => raw1631 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1631step0 raw1631; decide +kernel
      have hl : raw1631step0Labels = raw1631Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1631 raw1631Labels permutation164 permutation6
    mixedMoment B raw1631step0 raw1631step0Labels = mixedMoment B raw1631step1 raw1631step1Labels := by
      have ha : raw1631step1 = -raw1631step0 := by apply Matrix.ext; change ∀ i j, raw1631step1 i j = -(raw1631step0 i j); unfold raw1631step1 raw1631step0; decide +kernel
      have hl : raw1631step1Labels = raw1631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1631step1 raw1631step1Labels = mixedMoment B raw1631step2 raw1631step2Labels := by
      have ha : raw1631step2 = raw1631step1 := by apply Matrix.ext; unfold raw1631step2 raw1631step1; decide +kernel
      have hl : raw1631step1Labels = labelEmbedding1 ∘ raw1631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1631step1 raw1631step1Labels raw1631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1919 node1919Labels := by rfl

def raw1632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1632step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1632 raw1632Labels = mixedMoment B node4725 node4725Labels := by
  calc
    mixedMoment B raw1632 raw1632Labels = mixedMoment B raw1632step0 raw1632step0Labels := by
      have ha : raw1632step0 = (fun i j => raw1632 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1632step0 raw1632; decide +kernel
      have hl : raw1632step0Labels = raw1632Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1632 raw1632Labels permutation152 permutation4
    mixedMoment B raw1632step0 raw1632step0Labels = mixedMoment B raw1632step1 raw1632step1Labels := by
      have ha : raw1632step1 = raw1632step0 := by apply Matrix.ext; unfold raw1632step1 raw1632step0; decide +kernel
      have hl : raw1632step0Labels = labelEmbedding7 ∘ raw1632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1632step0 raw1632step0Labels raw1632step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4725 node4725Labels := by rfl

def raw1633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1633 raw1633Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw1633 raw1633Labels = mixedMoment B raw1633step0 raw1633step0Labels := by
      have ha : raw1633step0 = (fun i j => raw1633 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1633step0 raw1633; decide +kernel
      have hl : raw1633step0Labels = raw1633Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1633 raw1633Labels permutation152 permutation4
    _ = mixedMoment B node1879 node1879Labels := by rfl

def raw1634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1634Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1634 raw1634Labels = mixedMoment B node1936 node1936Labels := by
  calc
    mixedMoment B raw1634 raw1634Labels = mixedMoment B raw1634step0 raw1634step0Labels := by
      have ha : raw1634step0 = (fun i j => raw1634 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1634step0 raw1634; decide +kernel
      have hl : raw1634step0Labels = raw1634Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1634 raw1634Labels permutation152 permutation6
    mixedMoment B raw1634step0 raw1634step0Labels = mixedMoment B raw1634step1 raw1634step1Labels := by
      have ha : raw1634step1 = -raw1634step0 := by apply Matrix.ext; change ∀ i j, raw1634step1 i j = -(raw1634step0 i j); unfold raw1634step1 raw1634step0; decide +kernel
      have hl : raw1634step1Labels = raw1634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1634step1 raw1634step1Labels = mixedMoment B raw1634step2 raw1634step2Labels := by
      have ha : raw1634step2 = raw1634step1 := by apply Matrix.ext; unfold raw1634step2 raw1634step1; decide +kernel
      have hl : raw1634step1Labels = labelEmbedding1 ∘ raw1634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1634step1 raw1634step1Labels raw1634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1936 node1936Labels := by rfl

def raw1635 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1635step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1635 raw1635Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw1635 raw1635Labels = mixedMoment B raw1635step0 raw1635step0Labels := by
      have ha : raw1635step0 = (fun i j => raw1635 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1635step0 raw1635; decide +kernel
      have hl : raw1635step0Labels = raw1635Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1635 raw1635Labels permutation32 permutation4
    mixedMoment B raw1635step0 raw1635step0Labels = mixedMoment B raw1635step1 raw1635step1Labels := by
      have ha : raw1635step1 = raw1635step0 := by apply Matrix.ext; unfold raw1635step1 raw1635step0; decide +kernel
      have hl : raw1635step0Labels = labelEmbedding7 ∘ raw1635step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1635step0 raw1635step0Labels raw1635step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw1636 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1636 raw1636Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw1636 raw1636Labels = mixedMoment B raw1636step0 raw1636step0Labels := by
      have ha : raw1636step0 = (fun i j => raw1636 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1636step0 raw1636; decide +kernel
      have hl : raw1636step0Labels = raw1636Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1636 raw1636Labels permutation32 permutation4
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw1637 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1637Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1637step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1637step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1637 raw1637Labels = mixedMoment B node1938 node1938Labels := by
  calc
    mixedMoment B raw1637 raw1637Labels = mixedMoment B raw1637step0 raw1637step0Labels := by
      have ha : raw1637step0 = (fun i j => raw1637 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1637step0 raw1637; decide +kernel
      have hl : raw1637step0Labels = raw1637Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1637 raw1637Labels permutation32 permutation6
    mixedMoment B raw1637step0 raw1637step0Labels = mixedMoment B raw1637step1 raw1637step1Labels := by
      have ha : raw1637step1 = -raw1637step0 := by apply Matrix.ext; change ∀ i j, raw1637step1 i j = -(raw1637step0 i j); unfold raw1637step1 raw1637step0; decide +kernel
      have hl : raw1637step1Labels = raw1637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1637step1 raw1637step1Labels = mixedMoment B raw1637step2 raw1637step2Labels := by
      have ha : raw1637step2 = raw1637step1 := by apply Matrix.ext; unfold raw1637step2 raw1637step1; decide +kernel
      have hl : raw1637step1Labels = labelEmbedding1 ∘ raw1637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1637step1 raw1637step1Labels raw1637step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1938 node1938Labels := by rfl

def raw1638 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1638step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1638 raw1638Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw1638 raw1638Labels = mixedMoment B raw1638step0 raw1638step0Labels := by
      have ha : raw1638step0 = (fun i j => raw1638 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1638step0 raw1638; decide +kernel
      have hl : raw1638step0Labels = raw1638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1638 raw1638Labels permutation32 permutation4
    mixedMoment B raw1638step0 raw1638step0Labels = mixedMoment B raw1638step1 raw1638step1Labels := by
      have ha : raw1638step1 = raw1638step0 := by apply Matrix.ext; unfold raw1638step1 raw1638step0; decide +kernel
      have hl : raw1638step0Labels = labelEmbedding7 ∘ raw1638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1638step0 raw1638step0Labels raw1638step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

def raw1639 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1639 raw1639Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw1639 raw1639Labels = mixedMoment B raw1639step0 raw1639step0Labels := by
      have ha : raw1639step0 = (fun i j => raw1639 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1639step0 raw1639; decide +kernel
      have hl : raw1639step0Labels = raw1639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1639 raw1639Labels permutation32 permutation4
    _ = mixedMoment B node1881 node1881Labels := by rfl

def raw1640 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1640Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1640 raw1640Labels = mixedMoment B node1939 node1939Labels := by
  calc
    mixedMoment B raw1640 raw1640Labels = mixedMoment B raw1640step0 raw1640step0Labels := by
      have ha : raw1640step0 = (fun i j => raw1640 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1640step0 raw1640; decide +kernel
      have hl : raw1640step0Labels = raw1640Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1640 raw1640Labels permutation33 permutation6
    mixedMoment B raw1640step0 raw1640step0Labels = mixedMoment B raw1640step1 raw1640step1Labels := by
      have ha : raw1640step1 = -raw1640step0 := by apply Matrix.ext; change ∀ i j, raw1640step1 i j = -(raw1640step0 i j); unfold raw1640step1 raw1640step0; decide +kernel
      have hl : raw1640step1Labels = raw1640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1640step1 raw1640step1Labels = mixedMoment B raw1640step2 raw1640step2Labels := by
      have ha : raw1640step2 = raw1640step1 := by apply Matrix.ext; unfold raw1640step2 raw1640step1; decide +kernel
      have hl : raw1640step1Labels = labelEmbedding1 ∘ raw1640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1640step1 raw1640step1Labels raw1640step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1939 node1939Labels := by rfl

def raw1641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1641step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1641 raw1641Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw1641 raw1641Labels = mixedMoment B raw1641step0 raw1641step0Labels := by
      have ha : raw1641step0 = (fun i j => raw1641 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1641step0 raw1641; decide +kernel
      have hl : raw1641step0Labels = raw1641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1641 raw1641Labels permutation152 permutation4
    mixedMoment B raw1641step0 raw1641step0Labels = mixedMoment B raw1641step1 raw1641step1Labels := by
      have ha : raw1641step1 = raw1641step0 := by apply Matrix.ext; unfold raw1641step1 raw1641step0; decide +kernel
      have hl : raw1641step0Labels = labelEmbedding7 ∘ raw1641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1641step0 raw1641step0Labels raw1641step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw1642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1642 raw1642Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw1642 raw1642Labels = mixedMoment B raw1642step0 raw1642step0Labels := by
      have ha : raw1642step0 = (fun i j => raw1642 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1642step0 raw1642; decide +kernel
      have hl : raw1642step0Labels = raw1642Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1642 raw1642Labels permutation152 permutation4
    _ = mixedMoment B node1897 node1897Labels := by rfl

def raw1643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1643Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw1643step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1643step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1643 raw1643Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw1643 raw1643Labels = mixedMoment B raw1643step0 raw1643step0Labels := by
      have ha : raw1643step0 = (fun i j => raw1643 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1643step0 raw1643; decide +kernel
      have hl : raw1643step0Labels = raw1643Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1643 raw1643Labels permutation164 permutation6
    mixedMoment B raw1643step0 raw1643step0Labels = mixedMoment B raw1643step1 raw1643step1Labels := by
      have ha : raw1643step1 = -raw1643step0 := by apply Matrix.ext; change ∀ i j, raw1643step1 i j = -(raw1643step0 i j); unfold raw1643step1 raw1643step0; decide +kernel
      have hl : raw1643step1Labels = raw1643step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1643step1 raw1643step1Labels = mixedMoment B raw1643step2 raw1643step2Labels := by
      have ha : raw1643step2 = raw1643step1 := by apply Matrix.ext; unfold raw1643step2 raw1643step1; decide +kernel
      have hl : raw1643step1Labels = labelEmbedding1 ∘ raw1643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1643step1 raw1643step1Labels raw1643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1907 node1907Labels := by rfl

def raw1644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1644step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1644 raw1644Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw1644 raw1644Labels = mixedMoment B raw1644step0 raw1644step0Labels := by
      have ha : raw1644step0 = (fun i j => raw1644 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1644step0 raw1644; decide +kernel
      have hl : raw1644step0Labels = raw1644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1644 raw1644Labels permutation152 permutation4
    mixedMoment B raw1644step0 raw1644step0Labels = mixedMoment B raw1644step1 raw1644step1Labels := by
      have ha : raw1644step1 = raw1644step0 := by apply Matrix.ext; unfold raw1644step1 raw1644step0; decide +kernel
      have hl : raw1644step0Labels = labelEmbedding7 ∘ raw1644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1644step0 raw1644step0Labels raw1644step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw1645 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1645 raw1645Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw1645 raw1645Labels = mixedMoment B raw1645step0 raw1645step0Labels := by
      have ha : raw1645step0 = (fun i j => raw1645 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1645step0 raw1645; decide +kernel
      have hl : raw1645step0Labels = raw1645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1645 raw1645Labels permutation152 permutation4
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw1646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1646Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw1646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1646 raw1646Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw1646 raw1646Labels = mixedMoment B raw1646step0 raw1646step0Labels := by
      have ha : raw1646step0 = (fun i j => raw1646 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1646step0 raw1646; decide +kernel
      have hl : raw1646step0Labels = raw1646Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1646 raw1646Labels permutation152 permutation6
    mixedMoment B raw1646step0 raw1646step0Labels = mixedMoment B raw1646step1 raw1646step1Labels := by
      have ha : raw1646step1 = -raw1646step0 := by apply Matrix.ext; change ∀ i j, raw1646step1 i j = -(raw1646step0 i j); unfold raw1646step1 raw1646step0; decide +kernel
      have hl : raw1646step1Labels = raw1646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1646step1 raw1646step1Labels = mixedMoment B raw1646step2 raw1646step2Labels := by
      have ha : raw1646step2 = raw1646step1 := by apply Matrix.ext; unfold raw1646step2 raw1646step1; decide +kernel
      have hl : raw1646step1Labels = labelEmbedding1 ∘ raw1646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1646step1 raw1646step1Labels raw1646step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1940 node1940Labels := by rfl

def raw1647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1647step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1647 raw1647Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw1647 raw1647Labels = mixedMoment B raw1647step0 raw1647step0Labels := by
      have ha : raw1647step0 = (fun i j => raw1647 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1647step0 raw1647; decide +kernel
      have hl : raw1647step0Labels = raw1647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1647 raw1647Labels permutation152 permutation4
    mixedMoment B raw1647step0 raw1647step0Labels = mixedMoment B raw1647step1 raw1647step1Labels := by
      have ha : raw1647step1 = raw1647step0 := by apply Matrix.ext; unfold raw1647step1 raw1647step0; decide +kernel
      have hl : raw1647step0Labels = labelEmbedding7 ∘ raw1647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1647step0 raw1647step0Labels raw1647step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

def raw1648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1648 raw1648Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw1648 raw1648Labels = mixedMoment B raw1648step0 raw1648step0Labels := by
      have ha : raw1648step0 = (fun i j => raw1648 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1648step0 raw1648; decide +kernel
      have hl : raw1648step0Labels = raw1648Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1648 raw1648Labels permutation152 permutation4
    _ = mixedMoment B node1900 node1900Labels := by rfl

def raw1649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1649Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw1649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1649 raw1649Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw1649 raw1649Labels = mixedMoment B raw1649step0 raw1649step0Labels := by
      have ha : raw1649step0 = (fun i j => raw1649 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1649step0 raw1649; decide +kernel
      have hl : raw1649step0Labels = raw1649Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1649 raw1649Labels permutation164 permutation6
    mixedMoment B raw1649step0 raw1649step0Labels = mixedMoment B raw1649step1 raw1649step1Labels := by
      have ha : raw1649step1 = -raw1649step0 := by apply Matrix.ext; change ∀ i j, raw1649step1 i j = -(raw1649step0 i j); unfold raw1649step1 raw1649step0; decide +kernel
      have hl : raw1649step1Labels = raw1649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1649step1 raw1649step1Labels = mixedMoment B raw1649step2 raw1649step2Labels := by
      have ha : raw1649step2 = raw1649step1 := by apply Matrix.ext; unfold raw1649step2 raw1649step1; decide +kernel
      have hl : raw1649step1Labels = labelEmbedding1 ∘ raw1649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1649step1 raw1649step1Labels raw1649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1921 node1921Labels := by rfl

def raw1650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1650step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1650 raw1650Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw1650 raw1650Labels = mixedMoment B raw1650step0 raw1650step0Labels := by
      have ha : raw1650step0 = (fun i j => raw1650 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1650step0 raw1650; decide +kernel
      have hl : raw1650step0Labels = raw1650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1650 raw1650Labels permutation152 permutation4
    mixedMoment B raw1650step0 raw1650step0Labels = mixedMoment B raw1650step1 raw1650step1Labels := by
      have ha : raw1650step1 = raw1650step0 := by apply Matrix.ext; unfold raw1650step1 raw1650step0; decide +kernel
      have hl : raw1650step0Labels = labelEmbedding7 ∘ raw1650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1650step0 raw1650step0Labels raw1650step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

def raw1651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1651 raw1651Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw1651 raw1651Labels = mixedMoment B raw1651step0 raw1651step0Labels := by
      have ha : raw1651step0 = (fun i j => raw1651 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1651step0 raw1651; decide +kernel
      have hl : raw1651step0Labels = raw1651Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1651 raw1651Labels permutation152 permutation4
    _ = mixedMoment B node1901 node1901Labels := by rfl

def raw1652 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1652Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1652step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1652step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1652 raw1652Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw1652 raw1652Labels = mixedMoment B raw1652step0 raw1652step0Labels := by
      have ha : raw1652step0 = (fun i j => raw1652 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1652step0 raw1652; decide +kernel
      have hl : raw1652step0Labels = raw1652Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1652 raw1652Labels permutation152 permutation6
    mixedMoment B raw1652step0 raw1652step0Labels = mixedMoment B raw1652step1 raw1652step1Labels := by
      have ha : raw1652step1 = -raw1652step0 := by apply Matrix.ext; change ∀ i j, raw1652step1 i j = -(raw1652step0 i j); unfold raw1652step1 raw1652step0; decide +kernel
      have hl : raw1652step1Labels = raw1652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1652step1 raw1652step1Labels = mixedMoment B raw1652step2 raw1652step2Labels := by
      have ha : raw1652step2 = raw1652step1 := by apply Matrix.ext; unfold raw1652step2 raw1652step1; decide +kernel
      have hl : raw1652step1Labels = labelEmbedding1 ∘ raw1652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1652step1 raw1652step1Labels raw1652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1941 node1941Labels := by rfl

def raw1653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1653step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1653 raw1653Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw1653 raw1653Labels = mixedMoment B raw1653step0 raw1653step0Labels := by
      have ha : raw1653step0 = (fun i j => raw1653 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1653step0 raw1653; decide +kernel
      have hl : raw1653step0Labels = raw1653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1653 raw1653Labels permutation152 permutation4
    mixedMoment B raw1653step0 raw1653step0Labels = mixedMoment B raw1653step1 raw1653step1Labels := by
      have ha : raw1653step1 = raw1653step0 := by apply Matrix.ext; unfold raw1653step1 raw1653step0; decide +kernel
      have hl : raw1653step0Labels = labelEmbedding7 ∘ raw1653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1653step0 raw1653step0Labels raw1653step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw1654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1654 raw1654Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1654 raw1654Labels = mixedMoment B raw1654step0 raw1654step0Labels := by
      have ha : raw1654step0 = (fun i j => raw1654 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1654step0 raw1654; decide +kernel
      have hl : raw1654step0Labels = raw1654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1654 raw1654Labels permutation152 permutation4
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw1655 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1655Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw1655step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1655step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1655 raw1655Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw1655 raw1655Labels = mixedMoment B raw1655step0 raw1655step0Labels := by
      have ha : raw1655step0 = (fun i j => raw1655 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1655step0 raw1655; decide +kernel
      have hl : raw1655step0Labels = raw1655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1655 raw1655Labels permutation159 permutation6
    mixedMoment B raw1655step0 raw1655step0Labels = mixedMoment B raw1655step1 raw1655step1Labels := by
      have ha : raw1655step1 = -raw1655step0 := by apply Matrix.ext; change ∀ i j, raw1655step1 i j = -(raw1655step0 i j); unfold raw1655step1 raw1655step0; decide +kernel
      have hl : raw1655step1Labels = raw1655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1655step1 raw1655step1Labels = mixedMoment B raw1655step2 raw1655step2Labels := by
      have ha : raw1655step2 = raw1655step1 := by apply Matrix.ext; unfold raw1655step2 raw1655step1; decide +kernel
      have hl : raw1655step1Labels = labelEmbedding1 ∘ raw1655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1655step1 raw1655step1Labels raw1655step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw1656 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1656step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1656 raw1656Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw1656 raw1656Labels = mixedMoment B raw1656step0 raw1656step0Labels := by
      have ha : raw1656step0 = (fun i j => raw1656 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1656step0 raw1656; decide +kernel
      have hl : raw1656step0Labels = raw1656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1656 raw1656Labels permutation152 permutation4
    mixedMoment B raw1656step0 raw1656step0Labels = mixedMoment B raw1656step1 raw1656step1Labels := by
      have ha : raw1656step1 = raw1656step0 := by apply Matrix.ext; unfold raw1656step1 raw1656step0; decide +kernel
      have hl : raw1656step0Labels = labelEmbedding7 ∘ raw1656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1656step0 raw1656step0Labels raw1656step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw1657 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1657 raw1657Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw1657 raw1657Labels = mixedMoment B raw1657step0 raw1657step0Labels := by
      have ha : raw1657step0 = (fun i j => raw1657 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1657step0 raw1657; decide +kernel
      have hl : raw1657step0Labels = raw1657Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1657 raw1657Labels permutation152 permutation4
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw1658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1658Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw1658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1658 raw1658Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw1658 raw1658Labels = mixedMoment B raw1658step0 raw1658step0Labels := by
      have ha : raw1658step0 = (fun i j => raw1658 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1658step0 raw1658; decide +kernel
      have hl : raw1658step0Labels = raw1658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1658 raw1658Labels permutation170 permutation6
    mixedMoment B raw1658step0 raw1658step0Labels = mixedMoment B raw1658step1 raw1658step1Labels := by
      have ha : raw1658step1 = -raw1658step0 := by apply Matrix.ext; change ∀ i j, raw1658step1 i j = -(raw1658step0 i j); unfold raw1658step1 raw1658step0; decide +kernel
      have hl : raw1658step1Labels = raw1658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1658step1 raw1658step1Labels = mixedMoment B raw1658step2 raw1658step2Labels := by
      have ha : raw1658step2 = raw1658step1 := by apply Matrix.ext; unfold raw1658step2 raw1658step1; decide +kernel
      have hl : raw1658step1Labels = labelEmbedding1 ∘ raw1658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1658step1 raw1658step1Labels raw1658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1922 node1922Labels := by rfl

def raw1659 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1659step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1659 raw1659Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw1659 raw1659Labels = mixedMoment B raw1659step0 raw1659step0Labels := by
      have ha : raw1659step0 = (fun i j => raw1659 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1659step0 raw1659; decide +kernel
      have hl : raw1659step0Labels = raw1659Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1659 raw1659Labels permutation32 permutation4
    mixedMoment B raw1659step0 raw1659step0Labels = mixedMoment B raw1659step1 raw1659step1Labels := by
      have ha : raw1659step1 = raw1659step0 := by apply Matrix.ext; unfold raw1659step1 raw1659step0; decide +kernel
      have hl : raw1659step0Labels = labelEmbedding7 ∘ raw1659step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1659step0 raw1659step0Labels raw1659step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw1660 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1660 raw1660Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw1660 raw1660Labels = mixedMoment B raw1660step0 raw1660step0Labels := by
      have ha : raw1660step0 = (fun i j => raw1660 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1660step0 raw1660; decide +kernel
      have hl : raw1660step0Labels = raw1660Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1660 raw1660Labels permutation32 permutation4
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw1661 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1661Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw1661step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw1661step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw1661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1661 raw1661Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw1661 raw1661Labels = mixedMoment B raw1661step0 raw1661step0Labels := by
      have ha : raw1661step0 = (fun i j => raw1661 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1661step0 raw1661; decide +kernel
      have hl : raw1661step0Labels = raw1661Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1661 raw1661Labels permutation33 permutation6
    mixedMoment B raw1661step0 raw1661step0Labels = mixedMoment B raw1661step1 raw1661step1Labels := by
      have ha : raw1661step1 = -raw1661step0 := by apply Matrix.ext; change ∀ i j, raw1661step1 i j = -(raw1661step0 i j); unfold raw1661step1 raw1661step0; decide +kernel
      have hl : raw1661step1Labels = raw1661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1661step1 raw1661step1Labels = mixedMoment B raw1661step2 raw1661step2Labels := by
      have ha : raw1661step2 = raw1661step1 := by apply Matrix.ext; unfold raw1661step2 raw1661step1; decide +kernel
      have hl : raw1661step1Labels = labelEmbedding1 ∘ raw1661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1661step1 raw1661step1Labels raw1661step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw1662 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1662step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1662 raw1662Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw1662 raw1662Labels = mixedMoment B raw1662step0 raw1662step0Labels := by
      have ha : raw1662step0 = (fun i j => raw1662 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1662step0 raw1662; decide +kernel
      have hl : raw1662step0Labels = raw1662Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1662 raw1662Labels permutation32 permutation4
    mixedMoment B raw1662step0 raw1662step0Labels = mixedMoment B raw1662step1 raw1662step1Labels := by
      have ha : raw1662step1 = raw1662step0 := by apply Matrix.ext; unfold raw1662step1 raw1662step0; decide +kernel
      have hl : raw1662step0Labels = labelEmbedding7 ∘ raw1662step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1662step0 raw1662step0Labels raw1662step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw1663 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1663 raw1663Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw1663 raw1663Labels = mixedMoment B raw1663step0 raw1663step0Labels := by
      have ha : raw1663step0 = (fun i j => raw1663 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1663step0 raw1663; decide +kernel
      have hl : raw1663step0Labels = raw1663Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1663 raw1663Labels permutation32 permutation4
    _ = mixedMoment B node1917 node1917Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
