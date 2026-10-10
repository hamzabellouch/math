import Mathlib
import OAI.Combinatorics.StripMass.PatchReplacement

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

 

def rootTable : Config → Fin 12 → Fin 12
  | (.vacant,.vacant,.vacant) => ![0,1,2,3,4,5,6,7,8,9,10,11]
  | (.vacant,.vacant,.cup) => ![0,1,2,3,4,5,6,7,8,9,10,10]
  | (.vacant,.vertical₀,.vacant) => ![0,1,2,3,4,5,4,7,8,9,10,11]
  | (.vacant,.vertical₀,.cup) => ![0,1,2,3,4,5,4,7,8,9,10,10]
  | (.vacant,.diagonal₀,.vertical₀) => ![0,1,2,3,4,5,6,4,4,9,4,11]
  | (.vacant,.diagonal₀,.diagonal₀) => ![0,1,2,3,4,5,6,4,4,9,10,4]
  | (.vacant,.cup,.vertical₀) => ![0,1,2,3,4,5,6,6,6,9,6,11]
  | (.vacant,.cup,.diagonal₀) => ![0,1,2,3,4,5,6,6,6,9,10,6]
  | (.vertical₀,.vertical₁,.vertical₀) => ![0,1,0,3,4,0,6,0,0,9,0,11]
  | (.vertical₀,.vertical₁,.diagonal₀) => ![0,1,0,3,4,0,6,0,0,9,10,0]
  | (.vertical₀,.diagonal₁,.vacant) => ![0,1,0,3,4,0,0,7,8,9,10,11]
  | (.vertical₀,.diagonal₁,.cup) => ![0,1,0,3,4,0,0,7,8,9,10,10]
  | (.vertical₀,.cap,.vacant) => ![0,1,0,3,0,0,6,7,8,9,10,11]
  | (.vertical₀,.cap,.cup) => ![0,1,0,3,0,0,6,7,8,9,10,10]
  | (.vertical₀,.verticalPair,.vertical₀) => ![0,1,0,3,4,0,4,0,0,9,0,11]
  | (.vertical₀,.verticalPair,.diagonal₀) => ![0,1,0,3,4,0,4,0,0,9,10,0]
  | (.vertical₀,.capCup,.vertical₀) => ![0,1,0,3,0,0,6,6,6,9,6,11]
  | (.vertical₀,.capCup,.diagonal₀) => ![0,1,0,3,0,0,6,6,6,9,10,6]
  | (.vertical₁,.vacant,.vertical₁) => ![0,1,2,1,4,5,6,7,8,1,10,1]
  | (.vertical₁,.vacant,.diagonal₁) => ![0,1,2,1,4,5,6,7,8,1,1,11]
  | (.vertical₁,.vertical₀,.vertical₁) => ![0,1,2,1,4,5,4,7,8,1,10,1]
  | (.vertical₁,.vertical₀,.diagonal₁) => ![0,1,2,1,4,5,4,7,8,1,1,11]
  | (.vertical₁,.diagonal₀,.cap) => ![0,1,2,1,1,5,6,1,1,1,10,11]
  | (.vertical₁,.diagonal₀,.verticalPair) => ![0,1,2,1,4,5,6,4,4,1,4,1]
  | (.vertical₁,.diagonal₀,.capCup) => ![0,1,2,1,1,5,6,1,1,1,10,10]
  | (.vertical₁,.cup,.cap) => ![0,1,2,1,4,5,1,1,1,1,10,11]
  | (.vertical₁,.cup,.verticalPair) => ![0,1,2,1,4,5,6,6,6,1,6,1]
  | (.vertical₁,.cup,.capCup) => ![0,1,2,1,4,5,1,1,1,1,10,10]
  | (.diagonal₀,.vacant,.vertical₁) => ![0,1,2,0,4,5,6,7,8,0,10,0]
  | (.diagonal₀,.vacant,.diagonal₁) => ![0,1,2,0,4,5,6,7,8,0,0,11]
  | (.diagonal₀,.vertical₀,.vertical₁) => ![0,1,2,0,4,5,4,7,8,0,10,0]
  | (.diagonal₀,.vertical₀,.diagonal₁) => ![0,1,2,0,4,5,4,7,8,0,0,11]
  | (.diagonal₀,.diagonal₀,.cap) => ![0,1,2,0,0,5,6,0,0,0,10,11]
  | (.diagonal₀,.diagonal₀,.verticalPair) => ![0,1,2,0,4,5,6,4,4,0,4,0]
  | (.diagonal₀,.diagonal₀,.capCup) => ![0,1,2,0,0,5,6,0,0,0,10,10]
  | (.diagonal₀,.cup,.cap) => ![0,1,2,0,4,5,0,0,0,0,10,11]
  | (.diagonal₀,.cup,.verticalPair) => ![0,1,2,0,4,5,6,6,6,0,6,0]
  | (.diagonal₀,.cup,.capCup) => ![0,1,2,0,4,5,0,0,0,0,10,10]
  | (.diagonal₁,.vertical₁,.vertical₀) => ![0,1,1,3,4,1,6,1,1,9,1,11]
  | (.diagonal₁,.vertical₁,.diagonal₀) => ![0,1,1,3,4,1,6,1,1,9,10,1]
  | (.diagonal₁,.diagonal₁,.vacant) => ![0,1,1,3,4,1,1,7,8,9,10,11]
  | (.diagonal₁,.diagonal₁,.cup) => ![0,1,1,3,4,1,1,7,8,9,10,10]
  | (.diagonal₁,.cap,.vacant) => ![0,1,1,3,1,1,6,7,8,9,10,11]
  | (.diagonal₁,.cap,.cup) => ![0,1,1,3,1,1,6,7,8,9,10,10]
  | (.diagonal₁,.verticalPair,.vertical₀) => ![0,1,1,3,4,1,4,1,1,9,1,11]
  | (.diagonal₁,.verticalPair,.diagonal₀) => ![0,1,1,3,4,1,4,1,1,9,10,1]
  | (.diagonal₁,.capCup,.vertical₀) => ![0,1,1,3,1,1,6,6,6,9,6,11]
  | (.diagonal₁,.capCup,.diagonal₀) => ![0,1,1,3,1,1,6,6,6,9,10,6]
  | (.cap,.vacant,.vacant) => ![0,0,2,3,4,5,6,7,8,9,10,11]
  | (.cap,.vacant,.cup) => ![0,0,2,3,4,5,6,7,8,9,10,10]
  | (.cap,.vertical₀,.vacant) => ![0,0,2,3,4,5,4,7,8,9,10,11]
  | (.cap,.vertical₀,.cup) => ![0,0,2,3,4,5,4,7,8,9,10,10]
  | (.cap,.diagonal₀,.vertical₀) => ![0,0,2,3,4,5,6,4,4,9,4,11]
  | (.cap,.diagonal₀,.diagonal₀) => ![0,0,2,3,4,5,6,4,4,9,10,4]
  | (.cap,.cup,.vertical₀) => ![0,0,2,3,4,5,6,6,6,9,6,11]
  | (.cap,.cup,.diagonal₀) => ![0,0,2,3,4,5,6,6,6,9,10,6]
  | (.cup,.vertical₁,.cap) => ![0,1,2,2,4,2,6,2,2,2,10,11]
  | (.cup,.vertical₁,.verticalPair) => ![0,1,2,2,4,2,6,2,2,2,2,2]
  | (.cup,.vertical₁,.capCup) => ![0,1,2,2,4,2,6,2,2,2,10,10]
  | (.cup,.diagonal₁,.vertical₁) => ![0,1,2,2,4,2,2,7,8,2,10,2]
  | (.cup,.diagonal₁,.diagonal₁) => ![0,1,2,2,4,2,2,7,8,2,2,11]
  | (.cup,.cap,.vertical₁) => ![0,1,2,2,2,2,6,7,8,2,10,2]
  | (.cup,.cap,.diagonal₁) => ![0,1,2,2,2,2,6,7,8,2,2,11]
  | (.cup,.verticalPair,.cap) => ![0,1,2,2,4,2,4,2,2,2,10,11]
  | (.cup,.verticalPair,.verticalPair) => ![0,1,2,2,4,2,4,2,2,2,2,2]
  | (.cup,.verticalPair,.capCup) => ![0,1,2,2,4,2,4,2,2,2,10,10]
  | (.cup,.capCup,.cap) => ![0,1,2,2,2,2,2,2,2,2,10,11]
  | (.cup,.capCup,.verticalPair) => ![0,1,2,2,2,2,6,6,6,2,6,2]
  | (.cup,.capCup,.capCup) => ![0,1,2,2,2,2,2,2,2,2,10,10]
  | (.verticalPair,.vertical₁,.cap) => ![0,0,0,0,4,0,6,0,0,0,10,11]
  | (.verticalPair,.vertical₁,.verticalPair) => ![0,1,0,1,4,0,6,0,0,1,0,1]
  | (.verticalPair,.vertical₁,.capCup) => ![0,0,0,0,4,0,6,0,0,0,10,10]
  | (.verticalPair,.diagonal₁,.vertical₁) => ![0,1,0,1,4,0,0,7,8,1,10,1]
  | (.verticalPair,.diagonal₁,.diagonal₁) => ![0,1,0,1,4,0,0,7,8,1,1,11]
  | (.verticalPair,.cap,.vertical₁) => ![0,1,0,1,0,0,6,7,8,1,10,1]
  | (.verticalPair,.cap,.diagonal₁) => ![0,1,0,1,0,0,6,7,8,1,1,11]
  | (.verticalPair,.verticalPair,.cap) => ![0,0,0,0,4,0,4,0,0,0,10,11]
  | (.verticalPair,.verticalPair,.verticalPair) => ![0,1,0,1,4,0,4,0,0,1,0,1]
  | (.verticalPair,.verticalPair,.capCup) => ![0,0,0,0,4,0,4,0,0,0,10,10]
  | (.verticalPair,.capCup,.cap) => ![0,1,0,1,0,0,1,1,1,1,10,11]
  | (.verticalPair,.capCup,.verticalPair) => ![0,1,0,1,0,0,6,6,6,1,6,1]
  | (.verticalPair,.capCup,.capCup) => ![0,1,0,1,0,0,1,1,1,1,10,10]
  | (.capCup,.vertical₁,.cap) => ![0,0,2,2,4,2,6,2,2,2,10,11]
  | (.capCup,.vertical₁,.verticalPair) => ![0,0,2,2,4,2,6,2,2,2,2,2]
  | (.capCup,.vertical₁,.capCup) => ![0,0,2,2,4,2,6,2,2,2,10,10]
  | (.capCup,.diagonal₁,.vertical₁) => ![0,0,2,2,4,2,2,7,8,2,10,2]
  | (.capCup,.diagonal₁,.diagonal₁) => ![0,0,2,2,4,2,2,7,8,2,2,11]
  | (.capCup,.cap,.vertical₁) => ![0,0,2,2,2,2,6,7,8,2,10,2]
  | (.capCup,.cap,.diagonal₁) => ![0,0,2,2,2,2,6,7,8,2,2,11]
  | (.capCup,.verticalPair,.cap) => ![0,0,2,2,4,2,4,2,2,2,10,11]
  | (.capCup,.verticalPair,.verticalPair) => ![0,0,2,2,4,2,4,2,2,2,2,2]
  | (.capCup,.verticalPair,.capCup) => ![0,0,2,2,4,2,4,2,2,2,10,10]
  | (.capCup,.capCup,.cap) => ![0,0,2,2,2,2,2,2,2,2,10,11]
  | (.capCup,.capCup,.verticalPair) => ![0,0,2,2,2,2,6,6,6,2,6,2]
  | (.capCup,.capCup,.capCup) => ![0,0,2,2,2,2,2,2,2,2,10,10]
  | _ => fun i => i

def parentTable : Config → Fin 12 → Fin 12
  | (.vacant,.vacant,.vacant) => ![0,1,2,3,4,5,6,7,8,9,10,11]
  | (.vacant,.vacant,.cup) => ![0,1,2,3,4,5,6,7,8,9,10,10]
  | (.vacant,.vertical₀,.vacant) => ![0,1,2,3,4,5,4,7,8,9,10,11]
  | (.vacant,.vertical₀,.cup) => ![0,1,2,3,4,5,4,7,8,9,10,10]
  | (.vacant,.diagonal₀,.vertical₀) => ![0,1,2,3,4,5,6,4,7,9,8,11]
  | (.vacant,.diagonal₀,.diagonal₀) => ![0,1,2,3,4,5,6,4,7,9,10,8]
  | (.vacant,.cup,.vertical₀) => ![0,1,2,3,4,5,6,6,7,9,8,11]
  | (.vacant,.cup,.diagonal₀) => ![0,1,2,3,4,5,6,6,7,9,10,8]
  | (.vertical₀,.vertical₁,.vertical₀) => ![0,1,0,3,4,2,6,5,7,9,8,11]
  | (.vertical₀,.vertical₁,.diagonal₀) => ![0,1,0,3,4,2,6,5,7,9,10,8]
  | (.vertical₀,.diagonal₁,.vacant) => ![0,1,0,3,4,2,5,7,8,9,10,11]
  | (.vertical₀,.diagonal₁,.cup) => ![0,1,0,3,4,2,5,7,8,9,10,10]
  | (.vertical₀,.cap,.vacant) => ![0,1,0,3,5,2,6,7,8,9,10,11]
  | (.vertical₀,.cap,.cup) => ![0,1,0,3,5,2,6,7,8,9,10,10]
  | (.vertical₀,.verticalPair,.vertical₀) => ![0,1,0,3,4,2,4,5,7,9,8,11]
  | (.vertical₀,.verticalPair,.diagonal₀) => ![0,1,0,3,4,2,4,5,7,9,10,8]
  | (.vertical₀,.capCup,.vertical₀) => ![0,1,0,3,5,2,6,6,7,9,8,11]
  | (.vertical₀,.capCup,.diagonal₀) => ![0,1,0,3,5,2,6,6,7,9,10,8]
  | (.vertical₁,.vacant,.vertical₁) => ![0,1,2,1,4,5,6,7,8,3,10,9]
  | (.vertical₁,.vacant,.diagonal₁) => ![0,1,2,1,4,5,6,7,8,3,9,11]
  | (.vertical₁,.vertical₀,.vertical₁) => ![0,1,2,1,4,5,4,7,8,3,10,9]
  | (.vertical₁,.vertical₀,.diagonal₁) => ![0,1,2,1,4,5,4,7,8,3,9,11]
  | (.vertical₁,.diagonal₀,.cap) => ![0,1,2,1,7,5,6,8,9,3,10,11]
  | (.vertical₁,.diagonal₀,.verticalPair) => ![0,1,2,1,4,5,6,4,7,3,8,9]
  | (.vertical₁,.diagonal₀,.capCup) => ![0,1,2,1,7,5,6,8,9,3,10,10]
  | (.vertical₁,.cup,.cap) => ![0,1,2,1,4,5,7,8,9,3,10,11]
  | (.vertical₁,.cup,.verticalPair) => ![0,1,2,1,4,5,6,6,7,3,8,9]
  | (.vertical₁,.cup,.capCup) => ![0,1,2,1,4,5,7,8,9,3,10,10]
  | (.diagonal₀,.vacant,.vertical₁) => ![0,1,2,0,4,5,6,7,8,3,10,9]
  | (.diagonal₀,.vacant,.diagonal₁) => ![0,1,2,0,4,5,6,7,8,3,9,11]
  | (.diagonal₀,.vertical₀,.vertical₁) => ![0,1,2,0,4,5,4,7,8,3,10,9]
  | (.diagonal₀,.vertical₀,.diagonal₁) => ![0,1,2,0,4,5,4,7,8,3,9,11]
  | (.diagonal₀,.diagonal₀,.cap) => ![0,1,2,0,7,5,6,8,9,3,10,11]
  | (.diagonal₀,.diagonal₀,.verticalPair) => ![0,1,2,0,4,5,6,4,7,3,8,9]
  | (.diagonal₀,.diagonal₀,.capCup) => ![0,1,2,0,7,5,6,8,9,3,10,10]
  | (.diagonal₀,.cup,.cap) => ![0,1,2,0,4,5,7,8,9,3,10,11]
  | (.diagonal₀,.cup,.verticalPair) => ![0,1,2,0,4,5,6,6,7,3,8,9]
  | (.diagonal₀,.cup,.capCup) => ![0,1,2,0,4,5,7,8,9,3,10,10]
  | (.diagonal₁,.vertical₁,.vertical₀) => ![0,1,1,3,4,2,6,5,7,9,8,11]
  | (.diagonal₁,.vertical₁,.diagonal₀) => ![0,1,1,3,4,2,6,5,7,9,10,8]
  | (.diagonal₁,.diagonal₁,.vacant) => ![0,1,1,3,4,2,5,7,8,9,10,11]
  | (.diagonal₁,.diagonal₁,.cup) => ![0,1,1,3,4,2,5,7,8,9,10,10]
  | (.diagonal₁,.cap,.vacant) => ![0,1,1,3,5,2,6,7,8,9,10,11]
  | (.diagonal₁,.cap,.cup) => ![0,1,1,3,5,2,6,7,8,9,10,10]
  | (.diagonal₁,.verticalPair,.vertical₀) => ![0,1,1,3,4,2,4,5,7,9,8,11]
  | (.diagonal₁,.verticalPair,.diagonal₀) => ![0,1,1,3,4,2,4,5,7,9,10,8]
  | (.diagonal₁,.capCup,.vertical₀) => ![0,1,1,3,5,2,6,6,7,9,8,11]
  | (.diagonal₁,.capCup,.diagonal₀) => ![0,1,1,3,5,2,6,6,7,9,10,8]
  | (.cap,.vacant,.vacant) => ![0,0,2,3,4,5,6,7,8,9,10,11]
  | (.cap,.vacant,.cup) => ![0,0,2,3,4,5,6,7,8,9,10,10]
  | (.cap,.vertical₀,.vacant) => ![0,0,2,3,4,5,4,7,8,9,10,11]
  | (.cap,.vertical₀,.cup) => ![0,0,2,3,4,5,4,7,8,9,10,10]
  | (.cap,.diagonal₀,.vertical₀) => ![0,0,2,3,4,5,6,4,7,9,8,11]
  | (.cap,.diagonal₀,.diagonal₀) => ![0,0,2,3,4,5,6,4,7,9,10,8]
  | (.cap,.cup,.vertical₀) => ![0,0,2,3,4,5,6,6,7,9,8,11]
  | (.cap,.cup,.diagonal₀) => ![0,0,2,3,4,5,6,6,7,9,10,8]
  | (.cup,.vertical₁,.cap) => ![0,1,2,2,4,2,6,5,9,3,10,11]
  | (.cup,.vertical₁,.verticalPair) => ![0,1,2,2,4,2,6,5,7,3,8,9]
  | (.cup,.vertical₁,.capCup) => ![0,1,2,2,4,2,6,5,9,3,10,10]
  | (.cup,.diagonal₁,.vertical₁) => ![0,1,2,2,4,2,5,7,8,3,10,9]
  | (.cup,.diagonal₁,.diagonal₁) => ![0,1,2,2,4,2,5,7,8,3,9,11]
  | (.cup,.cap,.vertical₁) => ![0,1,2,2,5,2,6,7,8,3,10,9]
  | (.cup,.cap,.diagonal₁) => ![0,1,2,2,5,2,6,7,8,3,9,11]
  | (.cup,.verticalPair,.cap) => ![0,1,2,2,4,2,4,5,9,3,10,11]
  | (.cup,.verticalPair,.verticalPair) => ![0,1,2,2,4,2,4,5,7,3,8,9]
  | (.cup,.verticalPair,.capCup) => ![0,1,2,2,4,2,4,5,9,3,10,10]
  | (.cup,.capCup,.cap) => ![0,1,2,2,5,2,7,8,9,3,10,11]
  | (.cup,.capCup,.verticalPair) => ![0,1,2,2,5,2,6,6,7,3,8,9]
  | (.cup,.capCup,.capCup) => ![0,1,2,2,5,2,7,8,9,3,10,10]
  | (.verticalPair,.vertical₁,.cap) => ![0,3,0,9,4,2,6,5,7,8,10,11]
  | (.verticalPair,.vertical₁,.verticalPair) => ![0,1,0,1,4,2,6,5,7,3,8,9]
  | (.verticalPair,.vertical₁,.capCup) => ![0,3,0,9,4,2,6,5,7,8,10,10]
  | (.verticalPair,.diagonal₁,.vertical₁) => ![0,1,0,1,4,2,5,7,8,3,10,9]
  | (.verticalPair,.diagonal₁,.diagonal₁) => ![0,1,0,1,4,2,5,7,8,3,9,11]
  | (.verticalPair,.cap,.vertical₁) => ![0,1,0,1,5,2,6,7,8,3,10,9]
  | (.verticalPair,.cap,.diagonal₁) => ![0,1,0,1,5,2,6,7,8,3,9,11]
  | (.verticalPair,.verticalPair,.cap) => ![0,3,0,9,4,2,4,5,7,8,10,11]
  | (.verticalPair,.verticalPair,.verticalPair) => ![0,1,0,1,4,2,4,5,7,3,8,9]
  | (.verticalPair,.verticalPair,.capCup) => ![0,3,0,9,4,2,4,5,7,8,10,10]
  | (.verticalPair,.capCup,.cap) => ![0,1,0,1,5,2,7,8,9,3,10,11]
  | (.verticalPair,.capCup,.verticalPair) => ![0,1,0,1,5,2,6,6,7,3,8,9]
  | (.verticalPair,.capCup,.capCup) => ![0,1,0,1,5,2,7,8,9,3,10,10]
  | (.capCup,.vertical₁,.cap) => ![0,0,2,2,4,2,6,5,9,3,10,11]
  | (.capCup,.vertical₁,.verticalPair) => ![0,0,2,2,4,2,6,5,7,3,8,9]
  | (.capCup,.vertical₁,.capCup) => ![0,0,2,2,4,2,6,5,9,3,10,10]
  | (.capCup,.diagonal₁,.vertical₁) => ![0,0,2,2,4,2,5,7,8,3,10,9]
  | (.capCup,.diagonal₁,.diagonal₁) => ![0,0,2,2,4,2,5,7,8,3,9,11]
  | (.capCup,.cap,.vertical₁) => ![0,0,2,2,5,2,6,7,8,3,10,9]
  | (.capCup,.cap,.diagonal₁) => ![0,0,2,2,5,2,6,7,8,3,9,11]
  | (.capCup,.verticalPair,.cap) => ![0,0,2,2,4,2,4,5,9,3,10,11]
  | (.capCup,.verticalPair,.verticalPair) => ![0,0,2,2,4,2,4,5,7,3,8,9]
  | (.capCup,.verticalPair,.capCup) => ![0,0,2,2,4,2,4,5,9,3,10,10]
  | (.capCup,.capCup,.cap) => ![0,0,2,2,5,2,7,8,9,3,10,11]
  | (.capCup,.capCup,.verticalPair) => ![0,0,2,2,5,2,6,6,7,3,8,9]
  | (.capCup,.capCup,.capCup) => ![0,0,2,2,5,2,7,8,9,3,10,10]
  | _ => fun i => i

def rankTable : Config → Fin 12 → ℕ
  | (.vacant,.vacant,.vacant) => ![0,0,0,0,0,0,0,0,0,0,0,0]
  | (.vacant,.vacant,.cup) => ![0,0,0,0,0,0,0,0,0,0,0,1]
  | (.vacant,.vertical₀,.vacant) => ![0,0,0,0,0,0,1,0,0,0,0,0]
  | (.vacant,.vertical₀,.cup) => ![0,0,0,0,0,0,1,0,0,0,0,1]
  | (.vacant,.diagonal₀,.vertical₀) => ![0,0,0,0,0,0,0,1,2,0,3,0]
  | (.vacant,.diagonal₀,.diagonal₀) => ![0,0,0,0,0,0,0,1,2,0,0,3]
  | (.vacant,.cup,.vertical₀) => ![0,0,0,0,0,0,0,1,2,0,3,0]
  | (.vacant,.cup,.diagonal₀) => ![0,0,0,0,0,0,0,1,2,0,0,3]
  | (.vertical₀,.vertical₁,.vertical₀) => ![0,0,1,0,0,2,0,3,4,0,5,0]
  | (.vertical₀,.vertical₁,.diagonal₀) => ![0,0,1,0,0,2,0,3,4,0,0,5]
  | (.vertical₀,.diagonal₁,.vacant) => ![0,0,1,0,0,2,3,0,0,0,0,0]
  | (.vertical₀,.diagonal₁,.cup) => ![0,0,1,0,0,2,3,0,0,0,0,1]
  | (.vertical₀,.cap,.vacant) => ![0,0,1,0,3,2,0,0,0,0,0,0]
  | (.vertical₀,.cap,.cup) => ![0,0,1,0,3,2,0,0,0,0,0,1]
  | (.vertical₀,.verticalPair,.vertical₀) => ![0,0,1,0,0,2,1,3,4,0,5,0]
  | (.vertical₀,.verticalPair,.diagonal₀) => ![0,0,1,0,0,2,1,3,4,0,0,5]
  | (.vertical₀,.capCup,.vertical₀) => ![0,0,1,0,3,2,0,1,2,0,3,0]
  | (.vertical₀,.capCup,.diagonal₀) => ![0,0,1,0,3,2,0,1,2,0,0,3]
  | (.vertical₁,.vacant,.vertical₁) => ![0,0,0,1,0,0,0,0,0,2,0,3]
  | (.vertical₁,.vacant,.diagonal₁) => ![0,0,0,1,0,0,0,0,0,2,3,0]
  | (.vertical₁,.vertical₀,.vertical₁) => ![0,0,0,1,0,0,1,0,0,2,0,3]
  | (.vertical₁,.vertical₀,.diagonal₁) => ![0,0,0,1,0,0,1,0,0,2,3,0]
  | (.vertical₁,.diagonal₀,.cap) => ![0,0,0,1,5,0,0,4,3,2,0,0]
  | (.vertical₁,.diagonal₀,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.vertical₁,.diagonal₀,.capCup) => ![0,0,0,1,5,0,0,4,3,2,0,1]
  | (.vertical₁,.cup,.cap) => ![0,0,0,1,0,0,5,4,3,2,0,0]
  | (.vertical₁,.cup,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.vertical₁,.cup,.capCup) => ![0,0,0,1,0,0,5,4,3,2,0,1]
  | (.diagonal₀,.vacant,.vertical₁) => ![0,0,0,1,0,0,0,0,0,2,0,3]
  | (.diagonal₀,.vacant,.diagonal₁) => ![0,0,0,1,0,0,0,0,0,2,3,0]
  | (.diagonal₀,.vertical₀,.vertical₁) => ![0,0,0,1,0,0,1,0,0,2,0,3]
  | (.diagonal₀,.vertical₀,.diagonal₁) => ![0,0,0,1,0,0,1,0,0,2,3,0]
  | (.diagonal₀,.diagonal₀,.cap) => ![0,0,0,1,5,0,0,4,3,2,0,0]
  | (.diagonal₀,.diagonal₀,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.diagonal₀,.diagonal₀,.capCup) => ![0,0,0,1,5,0,0,4,3,2,0,1]
  | (.diagonal₀,.cup,.cap) => ![0,0,0,1,0,0,5,4,3,2,0,0]
  | (.diagonal₀,.cup,.verticalPair) => ![0,0,0,1,0,0,0,1,2,2,3,3]
  | (.diagonal₀,.cup,.capCup) => ![0,0,0,1,0,0,5,4,3,2,0,1]
  | (.diagonal₁,.vertical₁,.vertical₀) => ![0,0,1,0,0,2,0,3,4,0,5,0]
  | (.diagonal₁,.vertical₁,.diagonal₀) => ![0,0,1,0,0,2,0,3,4,0,0,5]
  | (.diagonal₁,.diagonal₁,.vacant) => ![0,0,1,0,0,2,3,0,0,0,0,0]
  | (.diagonal₁,.diagonal₁,.cup) => ![0,0,1,0,0,2,3,0,0,0,0,1]
  | (.diagonal₁,.cap,.vacant) => ![0,0,1,0,3,2,0,0,0,0,0,0]
  | (.diagonal₁,.cap,.cup) => ![0,0,1,0,3,2,0,0,0,0,0,1]
  | (.diagonal₁,.verticalPair,.vertical₀) => ![0,0,1,0,0,2,1,3,4,0,5,0]
  | (.diagonal₁,.verticalPair,.diagonal₀) => ![0,0,1,0,0,2,1,3,4,0,0,5]
  | (.diagonal₁,.capCup,.vertical₀) => ![0,0,1,0,3,2,0,1,2,0,3,0]
  | (.diagonal₁,.capCup,.diagonal₀) => ![0,0,1,0,3,2,0,1,2,0,0,3]
  | (.cap,.vacant,.vacant) => ![0,1,0,0,0,0,0,0,0,0,0,0]
  | (.cap,.vacant,.cup) => ![0,1,0,0,0,0,0,0,0,0,0,1]
  | (.cap,.vertical₀,.vacant) => ![0,1,0,0,0,0,1,0,0,0,0,0]
  | (.cap,.vertical₀,.cup) => ![0,1,0,0,0,0,1,0,0,0,0,1]
  | (.cap,.diagonal₀,.vertical₀) => ![0,1,0,0,0,0,0,1,2,0,3,0]
  | (.cap,.diagonal₀,.diagonal₀) => ![0,1,0,0,0,0,0,1,2,0,0,3]
  | (.cap,.cup,.vertical₀) => ![0,1,0,0,0,0,0,1,2,0,3,0]
  | (.cap,.cup,.diagonal₀) => ![0,1,0,0,0,0,0,1,2,0,0,3]
  | (.cup,.vertical₁,.cap) => ![0,0,0,1,0,1,0,2,3,2,0,0]
  | (.cup,.vertical₁,.verticalPair) => ![0,0,0,1,0,1,0,2,3,2,4,3]
  | (.cup,.vertical₁,.capCup) => ![0,0,0,1,0,1,0,2,3,2,0,1]
  | (.cup,.diagonal₁,.vertical₁) => ![0,0,0,1,0,1,2,0,0,2,0,3]
  | (.cup,.diagonal₁,.diagonal₁) => ![0,0,0,1,0,1,2,0,0,2,3,0]
  | (.cup,.cap,.vertical₁) => ![0,0,0,1,2,1,0,0,0,2,0,3]
  | (.cup,.cap,.diagonal₁) => ![0,0,0,1,2,1,0,0,0,2,3,0]
  | (.cup,.verticalPair,.cap) => ![0,0,0,1,0,1,1,2,3,2,0,0]
  | (.cup,.verticalPair,.verticalPair) => ![0,0,0,1,0,1,1,2,3,2,4,3]
  | (.cup,.verticalPair,.capCup) => ![0,0,0,1,0,1,1,2,3,2,0,1]
  | (.cup,.capCup,.cap) => ![0,0,0,1,2,1,5,4,3,2,0,0]
  | (.cup,.capCup,.verticalPair) => ![0,0,0,1,2,1,0,1,2,2,3,3]
  | (.cup,.capCup,.capCup) => ![0,0,0,1,2,1,5,4,3,2,0,1]
  | (.verticalPair,.vertical₁,.cap) => ![0,7,1,6,0,2,0,3,4,5,0,0]
  | (.verticalPair,.vertical₁,.verticalPair) => ![0,0,1,1,0,2,0,3,4,2,5,3]
  | (.verticalPair,.vertical₁,.capCup) => ![0,7,1,6,0,2,0,3,4,5,0,1]
  | (.verticalPair,.diagonal₁,.vertical₁) => ![0,0,1,1,0,2,3,0,0,2,0,3]
  | (.verticalPair,.diagonal₁,.diagonal₁) => ![0,0,1,1,0,2,3,0,0,2,3,0]
  | (.verticalPair,.cap,.vertical₁) => ![0,0,1,1,3,2,0,0,0,2,0,3]
  | (.verticalPair,.cap,.diagonal₁) => ![0,0,1,1,3,2,0,0,0,2,3,0]
  | (.verticalPair,.verticalPair,.cap) => ![0,7,1,6,0,2,1,3,4,5,0,0]
  | (.verticalPair,.verticalPair,.verticalPair) => ![0,0,1,1,0,2,1,3,4,2,5,3]
  | (.verticalPair,.verticalPair,.capCup) => ![0,7,1,6,0,2,1,3,4,5,0,1]
  | (.verticalPair,.capCup,.cap) => ![0,0,1,1,3,2,5,4,3,2,0,0]
  | (.verticalPair,.capCup,.verticalPair) => ![0,0,1,1,3,2,0,1,2,2,3,3]
  | (.verticalPair,.capCup,.capCup) => ![0,0,1,1,3,2,5,4,3,2,0,1]
  | (.capCup,.vertical₁,.cap) => ![0,1,0,1,0,1,0,2,3,2,0,0]
  | (.capCup,.vertical₁,.verticalPair) => ![0,1,0,1,0,1,0,2,3,2,4,3]
  | (.capCup,.vertical₁,.capCup) => ![0,1,0,1,0,1,0,2,3,2,0,1]
  | (.capCup,.diagonal₁,.vertical₁) => ![0,1,0,1,0,1,2,0,0,2,0,3]
  | (.capCup,.diagonal₁,.diagonal₁) => ![0,1,0,1,0,1,2,0,0,2,3,0]
  | (.capCup,.cap,.vertical₁) => ![0,1,0,1,2,1,0,0,0,2,0,3]
  | (.capCup,.cap,.diagonal₁) => ![0,1,0,1,2,1,0,0,0,2,3,0]
  | (.capCup,.verticalPair,.cap) => ![0,1,0,1,0,1,1,2,3,2,0,0]
  | (.capCup,.verticalPair,.verticalPair) => ![0,1,0,1,0,1,1,2,3,2,4,3]
  | (.capCup,.verticalPair,.capCup) => ![0,1,0,1,0,1,1,2,3,2,0,1]
  | (.capCup,.capCup,.cap) => ![0,1,0,1,2,1,5,4,3,2,0,0]
  | (.capCup,.capCup,.verticalPair) => ![0,1,0,1,2,1,0,1,2,2,3,3]
  | (.capCup,.capCup,.capCup) => ![0,1,0,1,2,1,5,4,3,2,0,1]
  | _ => fun _ => 0

def ForestConditions (t : Config) : Prop :=
  (∀ v w, Adj t v w → rootTable t v = rootTable t w) ∧
  (∀ v, v ≠ rootTable t v → Adj t v (parentTable t v)) ∧
  (∀ v, v ≠ rootTable t v → rankTable t (parentTable t v) < rankTable t v)

instance forestConditionsDecidable (t : Config) : Decidable (ForestConditions t) := by
  unfold ForestConditions; infer_instance

theorem forestConditions_0 (x y : Tile) (h : Compatible (.vacant,x,y)) :
    ForestConditions (.vacant,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_1 (x y : Tile) (h : Compatible (.vertical₀,x,y)) :
    ForestConditions (.vertical₀,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_2 (x y : Tile) (h : Compatible (.vertical₁,x,y)) :
    ForestConditions (.vertical₁,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_3 (x y : Tile) (h : Compatible (.diagonal₀,x,y)) :
    ForestConditions (.diagonal₀,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_4 (x y : Tile) (h : Compatible (.diagonal₁,x,y)) :
    ForestConditions (.diagonal₁,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_5 (x y : Tile) (h : Compatible (.cap,x,y)) :
    ForestConditions (.cap,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_6 (x y : Tile) (h : Compatible (.cup,x,y)) :
    ForestConditions (.cup,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_7 (x y : Tile) (h : Compatible (.verticalPair,x,y)) :
    ForestConditions (.verticalPair,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions_8 (x y : Tile) (h : Compatible (.capCup,x,y)) :
    ForestConditions (.capCup,x,y) := by
  cases x <;> cases y <;>
    first | exact absurd h (by decide) | decide

theorem forestConditions (t : Config) (h : Compatible t) : ForestConditions t := by
  rcases t with ⟨t,x,y⟩
  cases t
  · exact forestConditions_0 x y h
  · exact forestConditions_1 x y h
  · exact forestConditions_2 x y h
  · exact forestConditions_3 x y h
  · exact forestConditions_4 x y h
  · exact forestConditions_5 x y h
  · exact forestConditions_6 x y h
  · exact forestConditions_7 x y h
  · exact forestConditions_8 x y h

def certificate (t : Config) (h : Compatible t) : ConnectivityCertificate (Adj t) where
  root := rootTable t
  parent := parentTable t
  rank := rankTable t
  edge_root := (forestConditions t h).1
  parent_edge := (forestConditions t h).2.1
  parent_rank := (forestConditions t h).2.2

theorem reach_iff_root_eq (t : Config) (h : Compatible t) (v w : Fin 12) :
    Relation.ReflTransGen (Adj t) v w ↔ rootTable t v = rootTable t w :=
  (certificate t h).reach_iff (adj_symm t) v w

end
end CriticalStrip.Diagram.ThreeBox

end OAI
