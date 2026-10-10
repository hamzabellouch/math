import Mathlib
import OAI.Analysis.LaughlinGap.Certificate7
import OAI.Analysis.LaughlinGap.SumTable8

namespace OAI

/-! Certificate8. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate8

def keys : Fin 3 → Finset (Fin 25) := ![{0,1,2,6}, {0,1,3,5}, {0,2,3,4}]
def fibers : Fin 3 → Finset (FourTerm 8) := ![{⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}]
def columns : Matrix (Fin 4) (Fin 3) ℚ := ![![0, 0, 0], ![-360, 360, -360], ![360, -360, 360], ![-630, 630, -630]]
def Y : Matrix (Fin 4) (Fin 4) ℚ := ![![(-1827294336107386054342149/5368709120000000000000), (-789463800364931469995103/13421772800000000000000), (3526618533545862210398961/26843545600000000000000), (492113156078622412304121/13421772800000000000000)], ![(-789463800364931469995103/13421772800000000000000), (-1254450751674697246750761/46976204800000000000000), (3487489846557600630411933/93952409600000000000000), (3450831678396568633599/6710886400000000000000)], ![(3526618533545862210398961/26843545600000000000000), (3487489846557600630411933/93952409600000000000000), (-18773913360925793266587393/187904819200000000000000), (377817184867522132286589/2684354560000000000000)], ![(492113156078622412304121/13421772800000000000000), (3450831678396568633599/6710886400000000000000), (377817184867522132286589/2684354560000000000000), (-7761563551634662760452407/6710886400000000000000)]]
def Z : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, 720, -720, 1260], ![0, -720, 720, -1260], ![0, 1260, -1260, 2205]]
def W : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![(3239659704157609296158071/90194313216000000000000000), (3989767778471444755797239/45097156608000000000000000), (-21574246831047834561617711/90194313216000000000000000), (3842033729311192602927967/45097156608000000000000000)], ![(-3239659704157609296158071/90194313216000000000000000), (-3989767778471444755797239/45097156608000000000000000), (21574246831047834561617711/90194313216000000000000000), (-3842033729311192602927967/45097156608000000000000000)], ![(3239659704157609296158071/51539607552000000000000000), (3989767778471444755797239/25769803776000000000000000), (-21574246831047834561617711/51539607552000000000000000), (3842033729311192602927967/25769803776000000000000000)]]
def M : Matrix (Fin 4) (Fin 4) ℚ := ![![0, 0, 0, 0], ![0, (258005402643479389100760441/751619276800000000000000), (-258005402643479389100760441/751619276800000000000000), (258005402643479389100760441/429496729600000000000000)], ![0, (-258005402643479389100760441/751619276800000000000000), (258005402643479389100760441/751619276800000000000000), (-258005402643479389100760441/429496729600000000000000)], ![0, (258005402643479389100760441/429496729600000000000000), (-258005402643479389100760441/429496729600000000000000), (1806037818504355723705323087/1717986918400000000000000)]]
def L : Matrix (Fin 4) (Fin 4) ℚ := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, -1, 1, 0], ![0, (7/4), 0, 1]]
def diag : Fin 4 → ℚ := ![0, (258005402643479389100760441/751619276800000000000000), 0, 0]

def keyIndexTable : Fin 9 → Fin 13 → Fin 13 → Fin 3 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 9) (j : Fin ((n.val+1)/2)) (x : Fin ((8-n.val+2)/2)) : Fin 3 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 3 → FourTerm 8 := ![⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 5,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 4,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 4,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 3,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 3,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 2,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 2,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 1,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 1,
  (fourTermLabels (by omega : 8 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 8, (fourTermLabels (by omega : 8 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 8 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
  rintro ⟨n,j,x⟩
  fin_cases n
  · exact cover_0 j x
  · exact cover_1 j x
  · exact cover_2 j x
  · exact cover_3 j x
  · exact cover_4 j x
  · exact cover_5 j x
  · exact cover_6 j x
  · exact cover_7 j x
  · exact cover_8 j x
lemma representatives_checked : ∀ a : Fin 3,
  (fourTermLabels (by omega : 8 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 8 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 8 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 8 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 3, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 8,
    (fourTermLabels (by omega : 8 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 3, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 8 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 3, ∀ b : FourTerm 8,
    (fourTermLabels (by omega : 8 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 8 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 3, (∑ b ∈ fibers v, fourTermEval 8 (2*(0 : Fin 4).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 8 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 3, (∑ b ∈ fibers v, fourTermEval 8 (2*(1 : Fin 4).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 8 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 3, (∑ b ∈ fibers v, fourTermEval 8 (2*(2 : Fin 4).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 8 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 3, (∑ b ∈ fibers v, fourTermEval 8 (2*(3 : Fin 4).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 8 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 4, ∀ v : Fin 3, (∑ b ∈ fibers v, fourTermEval 8 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 8 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
lemma gram_checked_0 : ∀ v : Fin 4, (∑ a : Fin 3, columns (0 : Fin 4) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 4, (∑ a : Fin 3, columns (1 : Fin 4) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 4, (∑ a : Fin 3, columns (2 : Fin 4) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 4, (∑ a : Fin 3, columns (3 : Fin 4) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 4, ∀ v : Fin 4, (∑ a : Fin 3, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
lemma rows_table_checked_0 : ∀ v : Fin 4, integerTableEval 8 SumTable8.sums (0 : Fin 4) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 4, integerTableEval 8 SumTable8.sums (1 : Fin 4) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 4, integerTableEval 8 SumTable8.sums (2 : Fin 4) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 4, integerTableEval 8 SumTable8.sums (3 : Fin 4) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 4, ∀ v : Fin 4, integerTableEval 8 SumTable8.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
lemma rows_checked (u v : Fin 4) : exactFourEval 8 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 8 SumTable8.sums SumTable8.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 4, (Z * tableComparison 8 (1/200000) Y) (0 : Fin 4) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 4, (Z * tableComparison 8 (1/200000) Y) (1 : Fin 4) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 4, (Z * tableComparison 8 (1/200000) Y) (2 : Fin 4) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 4, (Z * tableComparison 8 (1/200000) Y) (3 : Fin 4) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 4, ∀ v : Fin 4, (Z * tableComparison 8 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
lemma compression_checked_0 : ∀ v : Fin 4, (W * Z) (0 : Fin 4) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 4, (W * Z) (1 : Fin 4) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 4, (W * Z) (2 : Fin 4) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_3 : ∀ v : Fin 4, (W * Z) (3 : Fin 4) v = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 4, ∀ v : Fin 4, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
  · exact compression_checked_3
lemma ldl_checked_0 : ∀ v : Fin 4, (∑ k : Fin 4, L (0 : Fin 4) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 4, (∑ k : Fin 4, L (1 : Fin 4) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 4, (∑ k : Fin 4, L (2 : Fin 4) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 4, (∑ k : Fin 4, L (3 : Fin 4) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 4, ∀ v : Fin 4, (∑ k : Fin 4, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
lemma diag_checked : ∀ u : Fin 4, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 8 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 8 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 8 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 8 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 8 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate8
end LaughlinGap.RealOccupation

end

end OAI
