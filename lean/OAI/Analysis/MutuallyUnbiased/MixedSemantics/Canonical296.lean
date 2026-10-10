import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37888Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37888step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37888 raw37888Labels = mixedMoment B node91 node91Labels := by
  calc
    mixedMoment B raw37888 raw37888Labels = mixedMoment B raw37888step0 raw37888step0Labels := by
      have ha : raw37888step0 = (fun i j => raw37888 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37888step0 raw37888; decide +kernel
      have hl : raw37888step0Labels = raw37888Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37888 raw37888Labels permutation168 permutation3
    _ = mixedMoment B node91 node91Labels := by rfl

def raw37889 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37889Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37889step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37889 raw37889Labels = mixedMoment B node95 node95Labels := by
  calc
    mixedMoment B raw37889 raw37889Labels = mixedMoment B raw37889step0 raw37889step0Labels := by
      have ha : raw37889step0 = (fun i j => raw37889 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37889step0 raw37889; decide +kernel
      have hl : raw37889step0Labels = raw37889Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37889 raw37889Labels permutation32 permutation3
    _ = mixedMoment B node95 node95Labels := by rfl

def raw37890 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37890Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37890step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37890 raw37890Labels = mixedMoment B node93 node93Labels := by
  calc
    mixedMoment B raw37890 raw37890Labels = mixedMoment B raw37890step0 raw37890step0Labels := by
      have ha : raw37890step0 = (fun i j => raw37890 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37890step0 raw37890; decide +kernel
      have hl : raw37890step0Labels = raw37890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37890 raw37890Labels permutation34 permutation3
    _ = mixedMoment B node93 node93Labels := by rfl

def raw37891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37891Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37891step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37891 raw37891Labels = mixedMoment B node89 node89Labels := by
  calc
    mixedMoment B raw37891 raw37891Labels = mixedMoment B raw37891step0 raw37891step0Labels := by
      have ha : raw37891step0 = (fun i j => raw37891 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37891step0 raw37891; decide +kernel
      have hl : raw37891step0Labels = raw37891Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37891 raw37891Labels permutation34 permutation3
    _ = mixedMoment B node89 node89Labels := by rfl

def raw37892 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw37892Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37892step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37892step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37892 raw37892Labels = mixedMoment B node96 node96Labels := by
  calc
    mixedMoment B raw37892 raw37892Labels = mixedMoment B raw37892step0 raw37892step0Labels := by
      have ha : raw37892step0 = (fun i j => raw37892 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37892step0 raw37892; decide +kernel
      have hl : raw37892step0Labels = raw37892Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37892 raw37892Labels permutation8 permutation3
    _ = mixedMoment B node96 node96Labels := by rfl

def raw37893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37893Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37893step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37893 raw37893Labels = mixedMoment B node92 node92Labels := by
  calc
    mixedMoment B raw37893 raw37893Labels = mixedMoment B raw37893step0 raw37893step0Labels := by
      have ha : raw37893step0 = (fun i j => raw37893 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37893step0 raw37893; decide +kernel
      have hl : raw37893step0Labels = raw37893Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37893 raw37893Labels permutation32 permutation3
    _ = mixedMoment B node92 node92Labels := by rfl

def raw37894 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw37894Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37894step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw37894step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37894 raw37894Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw37894 raw37894Labels = mixedMoment B raw37894step0 raw37894step0Labels := by
      have ha : raw37894step0 = (fun i j => raw37894 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37894step0 raw37894; decide +kernel
      have hl : raw37894step0Labels = raw37894Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37894 raw37894Labels permutation8 permutation3
    _ = mixedMoment B node94 node94Labels := by rfl

def raw37895 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw37895Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37895step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw37895step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37895 raw37895Labels = mixedMoment B node90 node90Labels := by
  calc
    mixedMoment B raw37895 raw37895Labels = mixedMoment B raw37895step0 raw37895step0Labels := by
      have ha : raw37895step0 = (fun i j => raw37895 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37895step0 raw37895; decide +kernel
      have hl : raw37895step0Labels = raw37895Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37895 raw37895Labels permutation8 permutation3
    _ = mixedMoment B node90 node90Labels := by rfl

def raw37896 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw37896Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37896step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37896step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37896 raw37896Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw37896 raw37896Labels = mixedMoment B raw37896step0 raw37896step0Labels := by
      have ha : raw37896step0 = (fun i j => raw37896 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37896step0 raw37896; decide +kernel
      have hl : raw37896step0Labels = raw37896Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37896 raw37896Labels permutation9 permutation3
    _ = mixedMoment B node98 node98Labels := by rfl

def raw37897 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw37897Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37897step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37897 raw37897Labels = mixedMoment B node99 node99Labels := by
  calc
    mixedMoment B raw37897 raw37897Labels = mixedMoment B raw37897step0 raw37897step0Labels := by
      have ha : raw37897step0 = (fun i j => raw37897 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37897step0 raw37897; decide +kernel
      have hl : raw37897step0Labels = raw37897Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37897 raw37897Labels permutation8 permutation3
    _ = mixedMoment B node99 node99Labels := by rfl

def raw37898 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw37898Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37898step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37898 raw37898Labels = mixedMoment B node84 node84Labels := by
  calc
    mixedMoment B raw37898 raw37898Labels = mixedMoment B raw37898step0 raw37898step0Labels := by
      have ha : raw37898step0 = (fun i j => raw37898 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37898step0 raw37898; decide +kernel
      have hl : raw37898step0Labels = raw37898Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37898 raw37898Labels permutation34 permutation3
    _ = mixedMoment B node84 node84Labels := by rfl

def raw37899 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw37899Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw37899step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37899 raw37899Labels = mixedMoment B node83 node83Labels := by
  calc
    mixedMoment B raw37899 raw37899Labels = mixedMoment B raw37899step0 raw37899step0Labels := by
      have ha : raw37899step0 = (fun i j => raw37899 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37899step0 raw37899; decide +kernel
      have hl : raw37899step0Labels = raw37899Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37899 raw37899Labels permutation34 permutation3
    _ = mixedMoment B node83 node83Labels := by rfl

def raw37900 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw37900Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37900step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw37900step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37900 raw37900Labels = mixedMoment B node85 node85Labels := by
  calc
    mixedMoment B raw37900 raw37900Labels = mixedMoment B raw37900step0 raw37900step0Labels := by
      have ha : raw37900step0 = (fun i j => raw37900 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37900step0 raw37900; decide +kernel
      have hl : raw37900step0Labels = raw37900Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37900 raw37900Labels permutation8 permutation3
    _ = mixedMoment B node85 node85Labels := by rfl

def raw37901 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw37901Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37901step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw37901step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37901 raw37901Labels = mixedMoment B node86 node86Labels := by
  calc
    mixedMoment B raw37901 raw37901Labels = mixedMoment B raw37901step0 raw37901step0Labels := by
      have ha : raw37901step0 = (fun i j => raw37901 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37901step0 raw37901; decide +kernel
      have hl : raw37901step0Labels = raw37901Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37901 raw37901Labels permutation9 permutation3
    _ = mixedMoment B node86 node86Labels := by rfl

def raw37902 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37902Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37902step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37902 raw37902Labels = mixedMoment B node108 node108Labels := by
  calc
    mixedMoment B raw37902 raw37902Labels = mixedMoment B raw37902step0 raw37902step0Labels := by
      have ha : raw37902step0 = (fun i j => raw37902 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37902step0 raw37902; decide +kernel
      have hl : raw37902step0Labels = raw37902Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37902 raw37902Labels permutation49 permutation3
    _ = mixedMoment B node108 node108Labels := by rfl

def raw37903 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw37903Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37903step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37903step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37903 raw37903Labels = mixedMoment B node111 node111Labels := by
  calc
    mixedMoment B raw37903 raw37903Labels = mixedMoment B raw37903step0 raw37903step0Labels := by
      have ha : raw37903step0 = (fun i j => raw37903 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37903step0 raw37903; decide +kernel
      have hl : raw37903step0Labels = raw37903Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37903 raw37903Labels permutation10 permutation3
    _ = mixedMoment B node111 node111Labels := by rfl

def raw37904 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw37904Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37904step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37904step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37904 raw37904Labels = mixedMoment B node110 node110Labels := by
  calc
    mixedMoment B raw37904 raw37904Labels = mixedMoment B raw37904step0 raw37904step0Labels := by
      have ha : raw37904step0 = (fun i j => raw37904 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37904step0 raw37904; decide +kernel
      have hl : raw37904step0Labels = raw37904Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37904 raw37904Labels permutation10 permutation3
    _ = mixedMoment B node110 node110Labels := by rfl

def raw37905 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw37905Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw37905step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37905 raw37905Labels = mixedMoment B node106 node106Labels := by
  calc
    mixedMoment B raw37905 raw37905Labels = mixedMoment B raw37905step0 raw37905step0Labels := by
      have ha : raw37905step0 = (fun i j => raw37905 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37905step0 raw37905; decide +kernel
      have hl : raw37905step0Labels = raw37905Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37905 raw37905Labels permutation10 permutation3
    _ = mixedMoment B node106 node106Labels := by rfl

def raw37906 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw37906Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37906step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw37906step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37906 raw37906Labels = mixedMoment B node112 node112Labels := by
  calc
    mixedMoment B raw37906 raw37906Labels = mixedMoment B raw37906step0 raw37906step0Labels := by
      have ha : raw37906step0 = (fun i j => raw37906 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37906step0 raw37906; decide +kernel
      have hl : raw37906step0Labels = raw37906Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37906 raw37906Labels permutation2 permutation3
    _ = mixedMoment B node112 node112Labels := by rfl

def raw37907 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw37907Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37907step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw37907step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37907 raw37907Labels = mixedMoment B node105 node105Labels := by
  calc
    mixedMoment B raw37907 raw37907Labels = mixedMoment B raw37907step0 raw37907step0Labels := by
      have ha : raw37907step0 = (fun i j => raw37907 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37907step0 raw37907; decide +kernel
      have hl : raw37907step0Labels = raw37907Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37907 raw37907Labels permutation10 permutation3
    _ = mixedMoment B node105 node105Labels := by rfl

def raw37908 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37908Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37908step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw37908step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37908 raw37908Labels = mixedMoment B node109 node109Labels := by
  calc
    mixedMoment B raw37908 raw37908Labels = mixedMoment B raw37908step0 raw37908step0Labels := by
      have ha : raw37908step0 = (fun i j => raw37908 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37908step0 raw37908; decide +kernel
      have hl : raw37908step0Labels = raw37908Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37908 raw37908Labels permutation8 permutation3
    _ = mixedMoment B node109 node109Labels := by rfl

def raw37909 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw37909Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37909step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw37909step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37909 raw37909Labels = mixedMoment B node107 node107Labels := by
  calc
    mixedMoment B raw37909 raw37909Labels = mixedMoment B raw37909step0 raw37909step0Labels := by
      have ha : raw37909step0 = (fun i j => raw37909 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37909step0 raw37909; decide +kernel
      have hl : raw37909step0Labels = raw37909Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37909 raw37909Labels permutation2 permutation3
    _ = mixedMoment B node107 node107Labels := by rfl

def raw37910 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw37910Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37910step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw37910step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37910 raw37910Labels = mixedMoment B node113 node113Labels := by
  calc
    mixedMoment B raw37910 raw37910Labels = mixedMoment B raw37910step0 raw37910step0Labels := by
      have ha : raw37910step0 = (fun i j => raw37910 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37910step0 raw37910; decide +kernel
      have hl : raw37910step0Labels = raw37910Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37910 raw37910Labels permutation3 permutation3
    _ = mixedMoment B node113 node113Labels := by rfl

def raw37911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37911Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw37911step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw37911step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37911 raw37911Labels = mixedMoment B node51 node51Labels := by
  calc
    mixedMoment B raw37911 raw37911Labels = mixedMoment B raw37911step0 raw37911step0Labels := by
      have ha : raw37911step0 = (fun i j => raw37911 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37911step0 raw37911; decide +kernel
      have hl : raw37911step0Labels = raw37911Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37911 raw37911Labels permutation47 permutation5
    mixedMoment B raw37911step0 raw37911step0Labels = mixedMoment B raw37911step1 raw37911step1Labels := by
      have ha : raw37911step1 = -raw37911step0 := by apply Matrix.ext; change ∀ i j, raw37911step1 i j = -(raw37911step0 i j); unfold raw37911step1 raw37911step0; decide +kernel
      have hl : raw37911step1Labels = raw37911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node51 node51Labels := by rfl

def raw37912 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw37912Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37912step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37912step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37912 raw37912Labels = mixedMoment B node54 node54Labels := by
  calc
    mixedMoment B raw37912 raw37912Labels = mixedMoment B raw37912step0 raw37912step0Labels := by
      have ha : raw37912step0 = (fun i j => raw37912 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37912step0 raw37912; decide +kernel
      have hl : raw37912step0Labels = raw37912Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37912 raw37912Labels permutation8 permutation3
    _ = mixedMoment B node54 node54Labels := by rfl

def raw37913 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37913Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw37913step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37913step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37913 raw37913Labels = mixedMoment B node47 node47Labels := by
  calc
    mixedMoment B raw37913 raw37913Labels = mixedMoment B raw37913step0 raw37913step0Labels := by
      have ha : raw37913step0 = (fun i j => raw37913 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37913step0 raw37913; decide +kernel
      have hl : raw37913step0Labels = raw37913Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37913 raw37913Labels permutation40 permutation5
    mixedMoment B raw37913step0 raw37913step0Labels = mixedMoment B raw37913step1 raw37913step1Labels := by
      have ha : raw37913step1 = -raw37913step0 := by apply Matrix.ext; change ∀ i j, raw37913step1 i j = -(raw37913step0 i j); unfold raw37913step1 raw37913step0; decide +kernel
      have hl : raw37913step1Labels = raw37913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node47 node47Labels := by rfl

def raw37914 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw37914Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37914step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw37914step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw37914step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37914 raw37914Labels = mixedMoment B node53 node53Labels := by
  calc
    mixedMoment B raw37914 raw37914Labels = mixedMoment B raw37914step0 raw37914step0Labels := by
      have ha : raw37914step0 = (fun i j => raw37914 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37914step0 raw37914; decide +kernel
      have hl : raw37914step0Labels = raw37914Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37914 raw37914Labels permutation10 permutation5
    mixedMoment B raw37914step0 raw37914step0Labels = mixedMoment B raw37914step1 raw37914step1Labels := by
      have ha : raw37914step1 = -raw37914step0 := by apply Matrix.ext; change ∀ i j, raw37914step1 i j = -(raw37914step0 i j); unfold raw37914step1 raw37914step0; decide +kernel
      have hl : raw37914step1Labels = raw37914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node53 node53Labels := by rfl

def raw37915 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw37915Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw37915step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37915 raw37915Labels = mixedMoment B node55 node55Labels := by
  calc
    mixedMoment B raw37915 raw37915Labels = mixedMoment B raw37915step0 raw37915step0Labels := by
      have ha : raw37915step0 = (fun i j => raw37915 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37915step0 raw37915; decide +kernel
      have hl : raw37915step0Labels = raw37915Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37915 raw37915Labels permutation9 permutation3
    _ = mixedMoment B node55 node55Labels := by rfl

def raw37916 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw37916Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37916step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37916step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37916 raw37916Labels = mixedMoment B node56 node56Labels := by
  calc
    mixedMoment B raw37916 raw37916Labels = mixedMoment B raw37916step0 raw37916step0Labels := by
      have ha : raw37916step0 = (fun i j => raw37916 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37916step0 raw37916; decide +kernel
      have hl : raw37916step0Labels = raw37916Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37916 raw37916Labels permutation8 permutation3
    _ = mixedMoment B node56 node56Labels := by rfl

def raw37917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37917Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37917step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37917 raw37917Labels = mixedMoment B node44 node44Labels := by
  calc
    mixedMoment B raw37917 raw37917Labels = mixedMoment B raw37917step0 raw37917step0Labels := by
      have ha : raw37917step0 = (fun i j => raw37917 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37917step0 raw37917; decide +kernel
      have hl : raw37917step0Labels = raw37917Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37917 raw37917Labels permutation154 permutation3
    _ = mixedMoment B node44 node44Labels := by rfl

def raw37918 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw37918Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37918step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37918 raw37918Labels = mixedMoment B node46 node46Labels := by
  calc
    mixedMoment B raw37918 raw37918Labels = mixedMoment B raw37918step0 raw37918step0Labels := by
      have ha : raw37918step0 = (fun i j => raw37918 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37918step0 raw37918; decide +kernel
      have hl : raw37918step0Labels = raw37918Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37918 raw37918Labels permutation32 permutation3
    _ = mixedMoment B node46 node46Labels := by rfl

def raw37919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37919Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37919step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37919 raw37919Labels = mixedMoment B node43 node43Labels := by
  calc
    mixedMoment B raw37919 raw37919Labels = mixedMoment B raw37919step0 raw37919step0Labels := by
      have ha : raw37919step0 = (fun i j => raw37919 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37919step0 raw37919; decide +kernel
      have hl : raw37919step0Labels = raw37919Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37919 raw37919Labels permutation152 permutation3
    _ = mixedMoment B node43 node43Labels := by rfl

def raw37920 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw37920Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw37920step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37920 raw37920Labels = mixedMoment B node45 node45Labels := by
  calc
    mixedMoment B raw37920 raw37920Labels = mixedMoment B raw37920step0 raw37920step0Labels := by
      have ha : raw37920step0 = (fun i j => raw37920 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37920step0 raw37920; decide +kernel
      have hl : raw37920step0Labels = raw37920Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37920 raw37920Labels permutation32 permutation3
    _ = mixedMoment B node45 node45Labels := by rfl

def raw37921 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw37921Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37921step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37921 raw37921Labels = mixedMoment B node48 node48Labels := by
  calc
    mixedMoment B raw37921 raw37921Labels = mixedMoment B raw37921step0 raw37921step0Labels := by
      have ha : raw37921step0 = (fun i j => raw37921 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37921step0 raw37921; decide +kernel
      have hl : raw37921step0Labels = raw37921Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37921 raw37921Labels permutation32 permutation3
    _ = mixedMoment B node48 node48Labels := by rfl

def raw37922 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw37922Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37922step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37922 raw37922Labels = mixedMoment B node50 node50Labels := by
  calc
    mixedMoment B raw37922 raw37922Labels = mixedMoment B raw37922step0 raw37922step0Labels := by
      have ha : raw37922step0 = (fun i j => raw37922 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37922step0 raw37922; decide +kernel
      have hl : raw37922step0Labels = raw37922Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37922 raw37922Labels permutation34 permutation3
    _ = mixedMoment B node50 node50Labels := by rfl

def raw37923 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw37923Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw37923step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37923 raw37923Labels = mixedMoment B node52 node52Labels := by
  calc
    mixedMoment B raw37923 raw37923Labels = mixedMoment B raw37923step0 raw37923step0Labels := by
      have ha : raw37923step0 = (fun i j => raw37923 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37923step0 raw37923; decide +kernel
      have hl : raw37923step0Labels = raw37923Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37923 raw37923Labels permutation8 permutation3
    _ = mixedMoment B node52 node52Labels := by rfl

def raw37924 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37924Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37924 raw37924Labels = mixedMoment B node284 node284Labels := by
  calc
    _ = mixedMoment B node284 node284Labels := by rfl

def raw37925 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw37925Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37925 raw37925Labels = mixedMoment B node285 node285Labels := by
  calc
    _ = mixedMoment B node285 node285Labels := by rfl

def raw37926 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37926Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37926 raw37926Labels = mixedMoment B node286 node286Labels := by
  calc
    _ = mixedMoment B node286 node286Labels := by rfl

def raw37927 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37927Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37927 raw37927Labels = mixedMoment B node287 node287Labels := by
  calc
    _ = mixedMoment B node287 node287Labels := by rfl

def raw37928 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, 0, -2], ![3, -3, 0]]
def raw37928Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37928step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw37928step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw37928step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37928 raw37928Labels = mixedMoment B node187 node187Labels := by
  calc
    mixedMoment B raw37928 raw37928Labels = mixedMoment B raw37928step0 raw37928step0Labels := by
      have ha : raw37928step0 = (fun i j => raw37928 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37928step0 raw37928; decide +kernel
      have hl : raw37928step0Labels = raw37928Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37928 raw37928Labels permutation31 permutation3
    mixedMoment B raw37928step0 raw37928step0Labels = mixedMoment B raw37928step1 raw37928step1Labels := by
      have ha : raw37928step1 = -raw37928step0 := by apply Matrix.ext; change ∀ i j, raw37928step1 i j = -(raw37928step0 i j); unfold raw37928step1 raw37928step0; decide +kernel
      have hl : raw37928step1Labels = raw37928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node187 node187Labels := by rfl

def raw37929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw37929Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37929step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37929step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37929 raw37929Labels = mixedMoment B node294 node294Labels := by
  calc
    mixedMoment B raw37929 raw37929Labels = mixedMoment B raw37929step0 raw37929step0Labels := by
      have ha : raw37929step0 = (fun i j => raw37929 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37929step0 raw37929; decide +kernel
      have hl : raw37929step0Labels = raw37929Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37929 raw37929Labels permutation662 permutation3
    mixedMoment B raw37929step0 raw37929step0Labels = mixedMoment B raw37929step1 raw37929step1Labels := by
      have ha : raw37929step1 = -raw37929step0 := by apply Matrix.ext; change ∀ i j, raw37929step1 i j = -(raw37929step0 i j); unfold raw37929step1 raw37929step0; decide +kernel
      have hl : raw37929step1Labels = raw37929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node294 node294Labels := by rfl

def raw37930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37930Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37930 raw37930Labels = mixedMoment B node317 node317Labels := by
  calc
    _ = mixedMoment B node317 node317Labels := by rfl

def raw37931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37931Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37931step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37931step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37931 raw37931Labels = mixedMoment B node207 node207Labels := by
  calc
    mixedMoment B raw37931 raw37931Labels = mixedMoment B raw37931step0 raw37931step0Labels := by
      have ha : raw37931step0 = (fun i j => raw37931 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37931step0 raw37931; decide +kernel
      have hl : raw37931step0Labels = raw37931Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37931 raw37931Labels permutation662 permutation3
    mixedMoment B raw37931step0 raw37931step0Labels = mixedMoment B raw37931step1 raw37931step1Labels := by
      have ha : raw37931step1 = -raw37931step0 := by apply Matrix.ext; change ∀ i j, raw37931step1 i j = -(raw37931step0 i j); unfold raw37931step1 raw37931step0; decide +kernel
      have hl : raw37931step1Labels = raw37931step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node207 node207Labels := by rfl

def raw37932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37932Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37932 raw37932Labels = mixedMoment B node318 node318Labels := by
  calc
    _ = mixedMoment B node318 node318Labels := by rfl

def raw37933 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw37933Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37933step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37933step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37933 raw37933Labels = mixedMoment B node274 node274Labels := by
  calc
    mixedMoment B raw37933 raw37933Labels = mixedMoment B raw37933step0 raw37933step0Labels := by
      have ha : raw37933step0 = (fun i j => raw37933 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37933step0 raw37933; decide +kernel
      have hl : raw37933step0Labels = raw37933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37933 raw37933Labels permutation149 permutation3
    mixedMoment B raw37933step0 raw37933step0Labels = mixedMoment B raw37933step1 raw37933step1Labels := by
      have ha : raw37933step1 = -raw37933step0 := by apply Matrix.ext; change ∀ i j, raw37933step1 i j = -(raw37933step0 i j); unfold raw37933step1 raw37933step0; decide +kernel
      have hl : raw37933step1Labels = raw37933step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node274 node274Labels := by rfl

def raw37934 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw37934Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37934step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37934step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37934 raw37934Labels = mixedMoment B node180 node180Labels := by
  calc
    mixedMoment B raw37934 raw37934Labels = mixedMoment B raw37934step0 raw37934step0Labels := by
      have ha : raw37934step0 = (fun i j => raw37934 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37934step0 raw37934; decide +kernel
      have hl : raw37934step0Labels = raw37934Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37934 raw37934Labels permutation149 permutation3
    mixedMoment B raw37934step0 raw37934step0Labels = mixedMoment B raw37934step1 raw37934step1Labels := by
      have ha : raw37934step1 = -raw37934step0 := by apply Matrix.ext; change ∀ i j, raw37934step1 i j = -(raw37934step0 i j); unfold raw37934step1 raw37934step0; decide +kernel
      have hl : raw37934step1Labels = raw37934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node180 node180Labels := by rfl

def raw37935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw37935Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37935step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37935step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37935 raw37935Labels = mixedMoment B node199 node199Labels := by
  calc
    mixedMoment B raw37935 raw37935Labels = mixedMoment B raw37935step0 raw37935step0Labels := by
      have ha : raw37935step0 = (fun i j => raw37935 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37935step0 raw37935; decide +kernel
      have hl : raw37935step0Labels = raw37935Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37935 raw37935Labels permutation682 permutation3
    mixedMoment B raw37935step0 raw37935step0Labels = mixedMoment B raw37935step1 raw37935step1Labels := by
      have ha : raw37935step1 = -raw37935step0 := by apply Matrix.ext; change ∀ i j, raw37935step1 i j = -(raw37935step0 i j); unfold raw37935step1 raw37935step0; decide +kernel
      have hl : raw37935step1Labels = raw37935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node199 node199Labels := by rfl

def raw37936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw37936Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37936 raw37936Labels = mixedMoment B node326 node326Labels := by
  calc
    _ = mixedMoment B node326 node326Labels := by rfl

def raw37937 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw37937Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37937step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37937step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37937 raw37937Labels = mixedMoment B node305 node305Labels := by
  calc
    mixedMoment B raw37937 raw37937Labels = mixedMoment B raw37937step0 raw37937step0Labels := by
      have ha : raw37937step0 = (fun i j => raw37937 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37937step0 raw37937; decide +kernel
      have hl : raw37937step0Labels = raw37937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37937 raw37937Labels permutation151 permutation3
    mixedMoment B raw37937step0 raw37937step0Labels = mixedMoment B raw37937step1 raw37937step1Labels := by
      have ha : raw37937step1 = -raw37937step0 := by apply Matrix.ext; change ∀ i j, raw37937step1 i j = -(raw37937step0 i j); unfold raw37937step1 raw37937step0; decide +kernel
      have hl : raw37937step1Labels = raw37937step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node305 node305Labels := by rfl

def raw37938 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37938Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37938step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37938step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37938 raw37938Labels = mixedMoment B node224 node224Labels := by
  calc
    mixedMoment B raw37938 raw37938Labels = mixedMoment B raw37938step0 raw37938step0Labels := by
      have ha : raw37938step0 = (fun i j => raw37938 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37938step0 raw37938; decide +kernel
      have hl : raw37938step0Labels = raw37938Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37938 raw37938Labels permutation151 permutation3
    mixedMoment B raw37938step0 raw37938step0Labels = mixedMoment B raw37938step1 raw37938step1Labels := by
      have ha : raw37938step1 = -raw37938step0 := by apply Matrix.ext; change ∀ i j, raw37938step1 i j = -(raw37938step0 i j); unfold raw37938step1 raw37938step0; decide +kernel
      have hl : raw37938step1Labels = raw37938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node224 node224Labels := by rfl

def raw37939 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37939Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37939 raw37939Labels = mixedMoment B node329 node329Labels := by
  calc
    _ = mixedMoment B node329 node329Labels := by rfl

def raw37940 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw37940Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw37940step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37940step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37940 raw37940Labels = mixedMoment B node203 node203Labels := by
  calc
    mixedMoment B raw37940 raw37940Labels = mixedMoment B raw37940step0 raw37940step0Labels := by
      have ha : raw37940step0 = (fun i j => raw37940 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37940step0 raw37940; decide +kernel
      have hl : raw37940step0Labels = raw37940Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37940 raw37940Labels permutation151 permutation3
    mixedMoment B raw37940step0 raw37940step0Labels = mixedMoment B raw37940step1 raw37940step1Labels := by
      have ha : raw37940step1 = -raw37940step0 := by apply Matrix.ext; change ∀ i j, raw37940step1 i j = -(raw37940step0 i j); unfold raw37940step1 raw37940step0; decide +kernel
      have hl : raw37940step1Labels = raw37940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node203 node203Labels := by rfl

def raw37941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37941Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37941 raw37941Labels = mixedMoment B node334 node334Labels := by
  calc
    _ = mixedMoment B node334 node334Labels := by rfl

def raw37942 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37942Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37942 raw37942Labels = mixedMoment B node335 node335Labels := by
  calc
    _ = mixedMoment B node335 node335Labels := by rfl

def raw37943 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37943Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37943 raw37943Labels = mixedMoment B node336 node336Labels := by
  calc
    _ = mixedMoment B node336 node336Labels := by rfl

def raw37944 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37944Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37944 raw37944Labels = mixedMoment B node337 node337Labels := by
  calc
    _ = mixedMoment B node337 node337Labels := by rfl

def raw37945 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37945Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37945 raw37945Labels = mixedMoment B node338 node338Labels := by
  calc
    _ = mixedMoment B node338 node338Labels := by rfl

def raw37946 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37946Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37946 raw37946Labels = mixedMoment B node339 node339Labels := by
  calc
    _ = mixedMoment B node339 node339Labels := by rfl

def raw37947 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw37947Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37947 raw37947Labels = mixedMoment B node341 node341Labels := by
  calc
    _ = mixedMoment B node341 node341Labels := by rfl

def raw37948 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw37948Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37948step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw37948step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw37948step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37948 raw37948Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw37948 raw37948Labels = mixedMoment B raw37948step0 raw37948step0Labels := by
      have ha : raw37948step0 = (fun i j => raw37948 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37948step0 raw37948; decide +kernel
      have hl : raw37948step0Labels = raw37948Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37948 raw37948Labels permutation31 permutation3
    mixedMoment B raw37948step0 raw37948step0Labels = mixedMoment B raw37948step1 raw37948step1Labels := by
      have ha : raw37948step1 = -raw37948step0 := by apply Matrix.ext; change ∀ i j, raw37948step1 i j = -(raw37948step0 i j); unfold raw37948step1 raw37948step0; decide +kernel
      have hl : raw37948step1Labels = raw37948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node249 node249Labels := by rfl

def raw37949 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37949Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37949 raw37949Labels = mixedMoment B node343 node343Labels := by
  calc
    _ = mixedMoment B node343 node343Labels := by rfl

def raw37950 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37950Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37950 raw37950Labels = mixedMoment B node344 node344Labels := by
  calc
    _ = mixedMoment B node344 node344Labels := by rfl

def raw37951 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw37951Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw37951step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw37951step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37951 raw37951Labels = mixedMoment B node201 node201Labels := by
  calc
    mixedMoment B raw37951 raw37951Labels = mixedMoment B raw37951step0 raw37951step0Labels := by
      have ha : raw37951step0 = (fun i j => raw37951 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37951step0 raw37951; decide +kernel
      have hl : raw37951step0Labels = raw37951Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37951 raw37951Labels permutation151 permutation3
    mixedMoment B raw37951step0 raw37951step0Labels = mixedMoment B raw37951step1 raw37951step1Labels := by
      have ha : raw37951step1 = -raw37951step0 := by apply Matrix.ext; change ∀ i j, raw37951step1 i j = -(raw37951step0 i j); unfold raw37951step1 raw37951step0; decide +kernel
      have hl : raw37951step1Labels = raw37951step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node201 node201Labels := by rfl

def raw37952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37952Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37952 raw37952Labels = mixedMoment B node351 node351Labels := by
  calc
    _ = mixedMoment B node351 node351Labels := by rfl

def raw37953 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw37953Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37953 raw37953Labels = mixedMoment B node352 node352Labels := by
  calc
    _ = mixedMoment B node352 node352Labels := by rfl

def raw37954 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw37954Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37954 raw37954Labels = mixedMoment B node353 node353Labels := by
  calc
    _ = mixedMoment B node353 node353Labels := by rfl

def raw37955 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw37955Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw37955step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw37955step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37955 raw37955Labels = mixedMoment B node315 node315Labels := by
  calc
    mixedMoment B raw37955 raw37955Labels = mixedMoment B raw37955step0 raw37955step0Labels := by
      have ha : raw37955step0 = (fun i j => raw37955 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37955step0 raw37955; decide +kernel
      have hl : raw37955step0Labels = raw37955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37955 raw37955Labels permutation31 permutation3
    mixedMoment B raw37955step0 raw37955step0Labels = mixedMoment B raw37955step1 raw37955step1Labels := by
      have ha : raw37955step1 = -raw37955step0 := by apply Matrix.ext; change ∀ i j, raw37955step1 i j = -(raw37955step0 i j); unfold raw37955step1 raw37955step0; decide +kernel
      have hl : raw37955step1Labels = raw37955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node315 node315Labels := by rfl

def raw37956 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37956Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37956step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw37956step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw37956step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37956 raw37956Labels = mixedMoment B node236 node236Labels := by
  calc
    mixedMoment B raw37956 raw37956Labels = mixedMoment B raw37956step0 raw37956step0Labels := by
      have ha : raw37956step0 = (fun i j => raw37956 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37956step0 raw37956; decide +kernel
      have hl : raw37956step0Labels = raw37956Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37956 raw37956Labels permutation31 permutation3
    mixedMoment B raw37956step0 raw37956step0Labels = mixedMoment B raw37956step1 raw37956step1Labels := by
      have ha : raw37956step1 = -raw37956step0 := by apply Matrix.ext; change ∀ i j, raw37956step1 i j = -(raw37956step0 i j); unfold raw37956step1 raw37956step0; decide +kernel
      have hl : raw37956step1Labels = raw37956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node236 node236Labels := by rfl

def raw37957 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37957Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37957 raw37957Labels = mixedMoment B node355 node355Labels := by
  calc
    _ = mixedMoment B node355 node355Labels := by rfl

def raw37958 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw37958Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37958 raw37958Labels = mixedMoment B node397 node397Labels := by
  calc
    _ = mixedMoment B node397 node397Labels := by rfl

def raw37959 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw37959Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw37959step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw37959step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37959 raw37959Labels = mixedMoment B node262 node262Labels := by
  calc
    mixedMoment B raw37959 raw37959Labels = mixedMoment B raw37959step0 raw37959step0Labels := by
      have ha : raw37959step0 = (fun i j => raw37959 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37959step0 raw37959; decide +kernel
      have hl : raw37959step0Labels = raw37959Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37959 raw37959Labels permutation29 permutation3
    mixedMoment B raw37959step0 raw37959step0Labels = mixedMoment B raw37959step1 raw37959step1Labels := by
      have ha : raw37959step1 = -raw37959step0 := by apply Matrix.ext; change ∀ i j, raw37959step1 i j = -(raw37959step0 i j); unfold raw37959step1 raw37959step0; decide +kernel
      have hl : raw37959step1Labels = raw37959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node262 node262Labels := by rfl

def raw37960 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37960Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37960 raw37960Labels = mixedMoment B node403 node403Labels := by
  calc
    _ = mixedMoment B node403 node403Labels := by rfl

def raw37961 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw37961Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37961 raw37961Labels = mixedMoment B node404 node404Labels := by
  calc
    _ = mixedMoment B node404 node404Labels := by rfl

def raw37962 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37962Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37962 raw37962Labels = mixedMoment B node405 node405Labels := by
  calc
    _ = mixedMoment B node405 node405Labels := by rfl

def raw37963 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw37963Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37963 raw37963Labels = mixedMoment B node407 node407Labels := by
  calc
    _ = mixedMoment B node407 node407Labels := by rfl

def raw37964 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37964Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37964 raw37964Labels = mixedMoment B node411 node411Labels := by
  calc
    _ = mixedMoment B node411 node411Labels := by rfl

def raw37965 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw37965Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37965 raw37965Labels = mixedMoment B node412 node412Labels := by
  calc
    _ = mixedMoment B node412 node412Labels := by rfl

def raw37966 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw37966Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37966step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw37966step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37966step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw37966step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37966 raw37966Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw37966 raw37966Labels = mixedMoment B raw37966step0 raw37966step0Labels := by
      have ha : raw37966step0 = (fun i j => raw37966 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37966step0 raw37966; decide +kernel
      have hl : raw37966step0Labels = raw37966Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37966 raw37966Labels permutation7 permutation3
    mixedMoment B raw37966step0 raw37966step0Labels = mixedMoment B raw37966step1 raw37966step1Labels := by
      have ha : raw37966step1 = -raw37966step0 := by apply Matrix.ext; change ∀ i j, raw37966step1 i j = -(raw37966step0 i j); unfold raw37966step1 raw37966step0; decide +kernel
      have hl : raw37966step1Labels = raw37966step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

def raw37967 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37967Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37967 raw37967Labels = mixedMoment B node416 node416Labels := by
  calc
    _ = mixedMoment B node416 node416Labels := by rfl

def raw37968 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw37968Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37968 raw37968Labels = mixedMoment B node420 node420Labels := by
  calc
    _ = mixedMoment B node420 node420Labels := by rfl

def raw37969 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw37969Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw37969step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37969 raw37969Labels = mixedMoment B node273 node273Labels := by
  calc
    mixedMoment B raw37969 raw37969Labels = mixedMoment B raw37969step0 raw37969step0Labels := by
      have ha : raw37969step0 = (fun i j => raw37969 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37969step0 raw37969; decide +kernel
      have hl : raw37969step0Labels = raw37969Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37969 raw37969Labels permutation34 permutation3
    _ = mixedMoment B node273 node273Labels := by rfl

def raw37970 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37970Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37970step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37970 raw37970Labels = mixedMoment B node275 node275Labels := by
  calc
    mixedMoment B raw37970 raw37970Labels = mixedMoment B raw37970step0 raw37970step0Labels := by
      have ha : raw37970step0 = (fun i j => raw37970 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37970step0 raw37970; decide +kernel
      have hl : raw37970step0Labels = raw37970Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37970 raw37970Labels permutation33 permutation3
    _ = mixedMoment B node275 node275Labels := by rfl

def raw37971 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37971Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37971step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37971 raw37971Labels = mixedMoment B node276 node276Labels := by
  calc
    mixedMoment B raw37971 raw37971Labels = mixedMoment B raw37971step0 raw37971step0Labels := by
      have ha : raw37971step0 = (fun i j => raw37971 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37971step0 raw37971; decide +kernel
      have hl : raw37971step0Labels = raw37971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37971 raw37971Labels permutation32 permutation3
    _ = mixedMoment B node276 node276Labels := by rfl

def raw37972 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, 0, -2], ![3, -3, 0]]
def raw37972Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37972step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw37972step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw37972step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37972 raw37972Labels = mixedMoment B node186 node186Labels := by
  calc
    mixedMoment B raw37972 raw37972Labels = mixedMoment B raw37972step0 raw37972step0Labels := by
      have ha : raw37972step0 = (fun i j => raw37972 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37972step0 raw37972; decide +kernel
      have hl : raw37972step0Labels = raw37972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37972 raw37972Labels permutation31 permutation3
    mixedMoment B raw37972step0 raw37972step0Labels = mixedMoment B raw37972step1 raw37972step1Labels := by
      have ha : raw37972step1 = -raw37972step0 := by apply Matrix.ext; change ∀ i j, raw37972step1 i j = -(raw37972step0 i j); unfold raw37972step1 raw37972step0; decide +kernel
      have hl : raw37972step1Labels = raw37972step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node186 node186Labels := by rfl

def raw37973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37973Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw37973step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw37973step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37973 raw37973Labels = mixedMoment B node206 node206Labels := by
  calc
    mixedMoment B raw37973 raw37973Labels = mixedMoment B raw37973step0 raw37973step0Labels := by
      have ha : raw37973step0 = (fun i j => raw37973 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37973step0 raw37973; decide +kernel
      have hl : raw37973step0Labels = raw37973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37973 raw37973Labels permutation662 permutation3
    mixedMoment B raw37973step0 raw37973step0Labels = mixedMoment B raw37973step1 raw37973step1Labels := by
      have ha : raw37973step1 = -raw37973step0 := by apply Matrix.ext; change ∀ i j, raw37973step1 i j = -(raw37973step0 i j); unfold raw37973step1 raw37973step0; decide +kernel
      have hl : raw37973step1Labels = raw37973step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node206 node206Labels := by rfl

def raw37974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37974Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw37974step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37974 raw37974Labels = mixedMoment B node293 node293Labels := by
  calc
    mixedMoment B raw37974 raw37974Labels = mixedMoment B raw37974step0 raw37974step0Labels := by
      have ha : raw37974step0 = (fun i j => raw37974 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37974step0 raw37974; decide +kernel
      have hl : raw37974step0Labels = raw37974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37974 raw37974Labels permutation177 permutation3
    _ = mixedMoment B node293 node293Labels := by rfl

def raw37975 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw37975Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw37975step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw37975step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37975 raw37975Labels = mixedMoment B node175 node175Labels := by
  calc
    mixedMoment B raw37975 raw37975Labels = mixedMoment B raw37975step0 raw37975step0Labels := by
      have ha : raw37975step0 = (fun i j => raw37975 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37975step0 raw37975; decide +kernel
      have hl : raw37975step0Labels = raw37975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37975 raw37975Labels permutation149 permutation3
    mixedMoment B raw37975step0 raw37975step0Labels = mixedMoment B raw37975step1 raw37975step1Labels := by
      have ha : raw37975step1 = -raw37975step0 := by apply Matrix.ext; change ∀ i j, raw37975step1 i j = -(raw37975step0 i j); unfold raw37975step1 raw37975step0; decide +kernel
      have hl : raw37975step1Labels = raw37975step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node175 node175Labels := by rfl

def raw37976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw37976Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw37976step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37976step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw37976step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37976 raw37976Labels = mixedMoment B node198 node198Labels := by
  calc
    mixedMoment B raw37976 raw37976Labels = mixedMoment B raw37976step0 raw37976step0Labels := by
      have ha : raw37976step0 = (fun i j => raw37976 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37976step0 raw37976; decide +kernel
      have hl : raw37976step0Labels = raw37976Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37976 raw37976Labels permutation682 permutation3
    mixedMoment B raw37976step0 raw37976step0Labels = mixedMoment B raw37976step1 raw37976step1Labels := by
      have ha : raw37976step1 = -raw37976step0 := by apply Matrix.ext; change ∀ i j, raw37976step1 i j = -(raw37976step0 i j); unfold raw37976step1 raw37976step0; decide +kernel
      have hl : raw37976step1Labels = raw37976step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node198 node198Labels := by rfl

def raw37977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw37977Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37977step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37977 raw37977Labels = mixedMoment B node321 node321Labels := by
  calc
    mixedMoment B raw37977 raw37977Labels = mixedMoment B raw37977step0 raw37977step0Labels := by
      have ha : raw37977step0 = (fun i j => raw37977 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37977step0 raw37977; decide +kernel
      have hl : raw37977step0Labels = raw37977Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37977 raw37977Labels permutation152 permutation3
    _ = mixedMoment B node321 node321Labels := by rfl

def raw37978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw37978Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37978step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37978 raw37978Labels = mixedMoment B node320 node320Labels := by
  calc
    mixedMoment B raw37978 raw37978Labels = mixedMoment B raw37978step0 raw37978step0Labels := by
      have ha : raw37978step0 = (fun i j => raw37978 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37978step0 raw37978; decide +kernel
      have hl : raw37978step0Labels = raw37978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37978 raw37978Labels permutation154 permutation3
    _ = mixedMoment B node320 node320Labels := by rfl

def raw37979 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw37979Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw37979step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw37979step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37979 raw37979Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw37979 raw37979Labels = mixedMoment B raw37979step0 raw37979step0Labels := by
      have ha : raw37979step0 = (fun i j => raw37979 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37979step0 raw37979; decide +kernel
      have hl : raw37979step0Labels = raw37979Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37979 raw37979Labels permutation151 permutation3
    mixedMoment B raw37979step0 raw37979step0Labels = mixedMoment B raw37979step1 raw37979step1Labels := by
      have ha : raw37979step1 = -raw37979step0 := by apply Matrix.ext; change ∀ i j, raw37979step1 i j = -(raw37979step0 i j); unfold raw37979step1 raw37979step0; decide +kernel
      have hl : raw37979step1Labels = raw37979step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node303 node303Labels := by rfl

def raw37980 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37980Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw37980step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw37980step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37980 raw37980Labels = mixedMoment B node222 node222Labels := by
  calc
    mixedMoment B raw37980 raw37980Labels = mixedMoment B raw37980step0 raw37980step0Labels := by
      have ha : raw37980step0 = (fun i j => raw37980 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37980step0 raw37980; decide +kernel
      have hl : raw37980step0Labels = raw37980Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37980 raw37980Labels permutation151 permutation3
    mixedMoment B raw37980step0 raw37980step0Labels = mixedMoment B raw37980step1 raw37980step1Labels := by
      have ha : raw37980step1 = -raw37980step0 := by apply Matrix.ext; change ∀ i j, raw37980step1 i j = -(raw37980step0 i j); unfold raw37980step1 raw37980step0; decide +kernel
      have hl : raw37980step1Labels = raw37980step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node222 node222Labels := by rfl

def raw37981 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw37981Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw37981step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37981 raw37981Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw37981 raw37981Labels = mixedMoment B raw37981step0 raw37981step0Labels := by
      have ha : raw37981step0 = (fun i j => raw37981 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37981step0 raw37981; decide +kernel
      have hl : raw37981step0Labels = raw37981Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37981 raw37981Labels permutation33 permutation3
    _ = mixedMoment B node325 node325Labels := by rfl

def raw37982 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw37982Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw37982step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37982 raw37982Labels = mixedMoment B node202 node202Labels := by
  calc
    mixedMoment B raw37982 raw37982Labels = mixedMoment B raw37982step0 raw37982step0Labels := by
      have ha : raw37982step0 = (fun i j => raw37982 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37982step0 raw37982; decide +kernel
      have hl : raw37982step0Labels = raw37982Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37982 raw37982Labels permutation149 permutation5
    _ = mixedMoment B node202 node202Labels := by rfl

def raw37983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37983Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37983step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37983 raw37983Labels = mixedMoment B node331 node331Labels := by
  calc
    mixedMoment B raw37983 raw37983Labels = mixedMoment B raw37983step0 raw37983step0Labels := by
      have ha : raw37983step0 = (fun i j => raw37983 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37983step0 raw37983; decide +kernel
      have hl : raw37983step0Labels = raw37983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37983 raw37983Labels permutation170 permutation3
    _ = mixedMoment B node331 node331Labels := by rfl

def raw37984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37984Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37984step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37984 raw37984Labels = mixedMoment B node334 node334Labels := by
  calc
    mixedMoment B raw37984 raw37984Labels = mixedMoment B raw37984step0 raw37984step0Labels := by
      have ha : raw37984step0 = (fun i j => raw37984 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37984step0 raw37984; decide +kernel
      have hl : raw37984step0Labels = raw37984Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37984 raw37984Labels permutation168 permutation3
    _ = mixedMoment B node334 node334Labels := by rfl

def raw37985 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37985Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37985step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37985 raw37985Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw37985 raw37985Labels = mixedMoment B raw37985step0 raw37985step0Labels := by
      have ha : raw37985step0 = (fun i j => raw37985 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37985step0 raw37985; decide +kernel
      have hl : raw37985step0Labels = raw37985Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37985 raw37985Labels permutation32 permutation3
    _ = mixedMoment B node339 node339Labels := by rfl

def raw37986 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37986Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37986step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37986 raw37986Labels = mixedMoment B node336 node336Labels := by
  calc
    mixedMoment B raw37986 raw37986Labels = mixedMoment B raw37986step0 raw37986step0Labels := by
      have ha : raw37986step0 = (fun i j => raw37986 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37986step0 raw37986; decide +kernel
      have hl : raw37986step0Labels = raw37986Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37986 raw37986Labels permutation34 permutation3
    _ = mixedMoment B node336 node336Labels := by rfl

def raw37987 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw37987Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37987step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37987 raw37987Labels = mixedMoment B node332 node332Labels := by
  calc
    mixedMoment B raw37987 raw37987Labels = mixedMoment B raw37987step0 raw37987step0Labels := by
      have ha : raw37987step0 = (fun i j => raw37987 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37987step0 raw37987; decide +kernel
      have hl : raw37987step0Labels = raw37987Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37987 raw37987Labels permutation34 permutation3
    _ = mixedMoment B node332 node332Labels := by rfl

def raw37988 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37988Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37988step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37988 raw37988Labels = mixedMoment B node335 node335Labels := by
  calc
    mixedMoment B raw37988 raw37988Labels = mixedMoment B raw37988step0 raw37988step0Labels := by
      have ha : raw37988step0 = (fun i j => raw37988 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37988step0 raw37988; decide +kernel
      have hl : raw37988step0Labels = raw37988Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37988 raw37988Labels permutation32 permutation3
    _ = mixedMoment B node335 node335Labels := by rfl

def raw37989 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw37989Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw37989step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37989 raw37989Labels = mixedMoment B node338 node338Labels := by
  calc
    mixedMoment B raw37989 raw37989Labels = mixedMoment B raw37989step0 raw37989step0Labels := by
      have ha : raw37989step0 = (fun i j => raw37989 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37989step0 raw37989; decide +kernel
      have hl : raw37989step0Labels = raw37989Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37989 raw37989Labels permutation8 permutation3
    _ = mixedMoment B node338 node338Labels := by rfl

def raw37990 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw37990Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37990step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw37990step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw37990step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37990 raw37990Labels = mixedMoment B node247 node247Labels := by
  calc
    mixedMoment B raw37990 raw37990Labels = mixedMoment B raw37990step0 raw37990step0Labels := by
      have ha : raw37990step0 = (fun i j => raw37990 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37990step0 raw37990; decide +kernel
      have hl : raw37990step0Labels = raw37990Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37990 raw37990Labels permutation31 permutation3
    mixedMoment B raw37990step0 raw37990step0Labels = mixedMoment B raw37990step1 raw37990step1Labels := by
      have ha : raw37990step1 = -raw37990step0 := by apply Matrix.ext; change ∀ i j, raw37990step1 i j = -(raw37990step0 i j); unfold raw37990step1 raw37990step0; decide +kernel
      have hl : raw37990step1Labels = raw37990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node247 node247Labels := by rfl

def raw37991 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw37991Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37991step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37991step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37991 raw37991Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw37991 raw37991Labels = mixedMoment B raw37991step0 raw37991step0Labels := by
      have ha : raw37991step0 = (fun i j => raw37991 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37991step0 raw37991; decide +kernel
      have hl : raw37991step0Labels = raw37991Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37991 raw37991Labels permutation9 permutation3
    _ = mixedMoment B node343 node343Labels := by rfl

def raw37992 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw37992Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37992step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37992step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37992 raw37992Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw37992 raw37992Labels = mixedMoment B raw37992step0 raw37992step0Labels := by
      have ha : raw37992step0 = (fun i j => raw37992 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37992step0 raw37992; decide +kernel
      have hl : raw37992step0Labels = raw37992Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37992 raw37992Labels permutation8 permutation3
    _ = mixedMoment B node344 node344Labels := by rfl

def raw37993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw37993Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw37993step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw37993step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37993 raw37993Labels = mixedMoment B node216 node216Labels := by
  calc
    mixedMoment B raw37993 raw37993Labels = mixedMoment B raw37993step0 raw37993step0Labels := by
      have ha : raw37993step0 = (fun i j => raw37993 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37993step0 raw37993; decide +kernel
      have hl : raw37993step0Labels = raw37993Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37993 raw37993Labels permutation682 permutation3
    mixedMoment B raw37993step0 raw37993step0Labels = mixedMoment B raw37993step1 raw37993step1Labels := by
      have ha : raw37993step1 = -raw37993step0 := by apply Matrix.ext; change ∀ i j, raw37993step1 i j = -(raw37993step0 i j); unfold raw37993step1 raw37993step0; decide +kernel
      have hl : raw37993step1Labels = raw37993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node216 node216Labels := by rfl

def raw37994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37994Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37994step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37994 raw37994Labels = mixedMoment B node304 node304Labels := by
  calc
    mixedMoment B raw37994 raw37994Labels = mixedMoment B raw37994step0 raw37994step0Labels := by
      have ha : raw37994step0 = (fun i j => raw37994 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37994step0 raw37994; decide +kernel
      have hl : raw37994step0Labels = raw37994Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37994 raw37994Labels permutation152 permutation3
    _ = mixedMoment B node304 node304Labels := by rfl

def raw37995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37995Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37995step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37995 raw37995Labels = mixedMoment B node302 node302Labels := by
  calc
    mixedMoment B raw37995 raw37995Labels = mixedMoment B raw37995step0 raw37995step0Labels := by
      have ha : raw37995step0 = (fun i j => raw37995 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37995step0 raw37995; decide +kernel
      have hl : raw37995step0Labels = raw37995Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37995 raw37995Labels permutation154 permutation3
    _ = mixedMoment B node302 node302Labels := by rfl

def raw37996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37996Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37996step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37996 raw37996Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw37996 raw37996Labels = mixedMoment B raw37996step0 raw37996step0Labels := by
      have ha : raw37996step0 = (fun i j => raw37996 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37996step0 raw37996; decide +kernel
      have hl : raw37996step0Labels = raw37996Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37996 raw37996Labels permutation152 permutation3
    _ = mixedMoment B node301 node301Labels := by rfl

def raw37997 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw37997Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw37997step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37997 raw37997Labels = mixedMoment B node230 node230Labels := by
  calc
    mixedMoment B raw37997 raw37997Labels = mixedMoment B raw37997step0 raw37997step0Labels := by
      have ha : raw37997step0 = (fun i j => raw37997 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37997step0 raw37997; decide +kernel
      have hl : raw37997step0Labels = raw37997Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37997 raw37997Labels permutation145 permutation5
    _ = mixedMoment B node230 node230Labels := by rfl

def raw37998 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw37998Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37998step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37998 raw37998Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw37998 raw37998Labels = mixedMoment B raw37998step0 raw37998step0Labels := by
      have ha : raw37998step0 = (fun i j => raw37998 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37998step0 raw37998; decide +kernel
      have hl : raw37998step0Labels = raw37998Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37998 raw37998Labels permutation33 permutation3
    _ = mixedMoment B node306 node306Labels := by rfl

def raw37999 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw37999Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw37999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37999step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical37999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37999 raw37999Labels = mixedMoment B node307 node307Labels := by
  calc
    mixedMoment B raw37999 raw37999Labels = mixedMoment B raw37999step0 raw37999step0Labels := by
      have ha : raw37999step0 = (fun i j => raw37999 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37999step0 raw37999; decide +kernel
      have hl : raw37999step0Labels = raw37999Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37999 raw37999Labels permutation32 permutation3
    _ = mixedMoment B node307 node307Labels := by rfl

def raw38000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38000Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38000step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38000 raw38000Labels = mixedMoment B node310 node310Labels := by
  calc
    mixedMoment B raw38000 raw38000Labels = mixedMoment B raw38000step0 raw38000step0Labels := by
      have ha : raw38000step0 = (fun i j => raw38000 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38000step0 raw38000; decide +kernel
      have hl : raw38000step0Labels = raw38000Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38000 raw38000Labels permutation169 permutation3
    _ = mixedMoment B node310 node310Labels := by rfl

def raw38001 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw38001Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38001step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38001 raw38001Labels = mixedMoment B node314 node314Labels := by
  calc
    mixedMoment B raw38001 raw38001Labels = mixedMoment B raw38001step0 raw38001step0Labels := by
      have ha : raw38001step0 = (fun i j => raw38001 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38001step0 raw38001; decide +kernel
      have hl : raw38001step0Labels = raw38001Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38001 raw38001Labels permutation34 permutation3
    _ = mixedMoment B node314 node314Labels := by rfl

def raw38002 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw38002Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38002step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38002 raw38002Labels = mixedMoment B node312 node312Labels := by
  calc
    mixedMoment B raw38002 raw38002Labels = mixedMoment B raw38002step0 raw38002step0Labels := by
      have ha : raw38002step0 = (fun i j => raw38002 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38002step0 raw38002; decide +kernel
      have hl : raw38002step0Labels = raw38002Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38002 raw38002Labels permutation34 permutation3
    _ = mixedMoment B node312 node312Labels := by rfl

def raw38003 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw38003Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38003step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38003 raw38003Labels = mixedMoment B node311 node311Labels := by
  calc
    mixedMoment B raw38003 raw38003Labels = mixedMoment B raw38003step0 raw38003step0Labels := by
      have ha : raw38003step0 = (fun i j => raw38003 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38003step0 raw38003; decide +kernel
      have hl : raw38003step0Labels = raw38003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38003 raw38003Labels permutation32 permutation3
    _ = mixedMoment B node311 node311Labels := by rfl

def raw38004 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw38004Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38004step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw38004step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38004 raw38004Labels = mixedMoment B node316 node316Labels := by
  calc
    mixedMoment B raw38004 raw38004Labels = mixedMoment B raw38004step0 raw38004step0Labels := by
      have ha : raw38004step0 = (fun i j => raw38004 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38004step0 raw38004; decide +kernel
      have hl : raw38004step0Labels = raw38004Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38004 raw38004Labels permutation9 permutation3
    _ = mixedMoment B node316 node316Labels := by rfl

def raw38005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw38005Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38005step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38005 raw38005Labels = mixedMoment B node370 node370Labels := by
  calc
    mixedMoment B raw38005 raw38005Labels = mixedMoment B raw38005step0 raw38005step0Labels := by
      have ha : raw38005step0 = (fun i j => raw38005 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38005step0 raw38005; decide +kernel
      have hl : raw38005step0Labels = raw38005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38005 raw38005Labels permutation182 permutation3
    _ = mixedMoment B node370 node370Labels := by rfl

def raw38006 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw38006Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38006step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38006 raw38006Labels = mixedMoment B node233 node233Labels := by
  calc
    mixedMoment B raw38006 raw38006Labels = mixedMoment B raw38006step0 raw38006step0Labels := by
      have ha : raw38006step0 = (fun i j => raw38006 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38006step0 raw38006; decide +kernel
      have hl : raw38006step0Labels = raw38006Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38006 raw38006Labels permutation137 permutation5
    _ = mixedMoment B node233 node233Labels := by rfl

def raw38007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38007Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38007step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38007 raw38007Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw38007 raw38007Labels = mixedMoment B raw38007step0 raw38007step0Labels := by
      have ha : raw38007step0 = (fun i j => raw38007 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38007step0 raw38007; decide +kernel
      have hl : raw38007step0Labels = raw38007Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38007 raw38007Labels permutation180 permutation3
    _ = mixedMoment B node376 node376Labels := by rfl

def raw38008 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw38008Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38008step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38008 raw38008Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw38008 raw38008Labels = mixedMoment B raw38008step0 raw38008step0Labels := by
      have ha : raw38008step0 = (fun i j => raw38008 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38008step0 raw38008; decide +kernel
      have hl : raw38008step0Labels = raw38008Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38008 raw38008Labels permutation38 permutation3
    _ = mixedMoment B node378 node378Labels := by rfl

def raw38009 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38009Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw38009step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38009 raw38009Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw38009 raw38009Labels = mixedMoment B raw38009step0 raw38009step0Labels := by
      have ha : raw38009step0 = (fun i j => raw38009 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38009step0 raw38009; decide +kernel
      have hl : raw38009step0Labels = raw38009Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38009 raw38009Labels permutation38 permutation3
    _ = mixedMoment B node377 node377Labels := by rfl

def raw38010 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw38010Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38010step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw38010step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38010 raw38010Labels = mixedMoment B node379 node379Labels := by
  calc
    mixedMoment B raw38010 raw38010Labels = mixedMoment B raw38010step0 raw38010step0Labels := by
      have ha : raw38010step0 = (fun i j => raw38010 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38010step0 raw38010; decide +kernel
      have hl : raw38010step0Labels = raw38010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38010 raw38010Labels permutation10 permutation3
    _ = mixedMoment B node379 node379Labels := by rfl

def raw38011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw38011Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38011step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38011 raw38011Labels = mixedMoment B node360 node360Labels := by
  calc
    mixedMoment B raw38011 raw38011Labels = mixedMoment B raw38011step0 raw38011step0Labels := by
      have ha : raw38011step0 = (fun i j => raw38011 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38011step0 raw38011; decide +kernel
      have hl : raw38011step0Labels = raw38011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38011 raw38011Labels permutation176 permutation3
    _ = mixedMoment B node360 node360Labels := by rfl

def raw38012 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw38012Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38012step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38012 raw38012Labels = mixedMoment B node361 node361Labels := by
  calc
    mixedMoment B raw38012 raw38012Labels = mixedMoment B raw38012step0 raw38012step0Labels := by
      have ha : raw38012step0 = (fun i j => raw38012 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38012step0 raw38012; decide +kernel
      have hl : raw38012step0Labels = raw38012Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38012 raw38012Labels permutation38 permutation3
    _ = mixedMoment B node361 node361Labels := by rfl

def raw38013 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw38013Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38013step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw38013step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38013 raw38013Labels = mixedMoment B node237 node237Labels := by
  calc
    mixedMoment B raw38013 raw38013Labels = mixedMoment B raw38013step0 raw38013step0Labels := by
      have ha : raw38013step0 = (fun i j => raw38013 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw38013step0 raw38013; decide +kernel
      have hl : raw38013step0Labels = raw38013Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38013 raw38013Labels permutation29 permutation5
    _ = mixedMoment B node237 node237Labels := by rfl

def raw38014 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw38014Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38014step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38014 raw38014Labels = mixedMoment B node401 node401Labels := by
  calc
    mixedMoment B raw38014 raw38014Labels = mixedMoment B raw38014step0 raw38014step0Labels := by
      have ha : raw38014step0 = (fun i j => raw38014 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38014step0 raw38014; decide +kernel
      have hl : raw38014step0Labels = raw38014Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38014 raw38014Labels permutation36 permutation3
    _ = mixedMoment B node401 node401Labels := by rfl

def raw38015 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38015Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw38015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw38015step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical38015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38015 raw38015Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw38015 raw38015Labels = mixedMoment B raw38015step0 raw38015step0Labels := by
      have ha : raw38015step0 = (fun i j => raw38015 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw38015step0 raw38015; decide +kernel
      have hl : raw38015step0Labels = raw38015Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38015 raw38015Labels permutation35 permutation3
    _ = mixedMoment B node403 node403Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
