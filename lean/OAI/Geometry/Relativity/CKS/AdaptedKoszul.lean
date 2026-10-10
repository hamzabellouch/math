import OAI.Geometry.Relativity.CKS.NonroundFrame

namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open scoped BigOperators
abbrev Coefficients := I → I → I → ℝ

def koszul (b : Coefficients) (i j k : I) : ℝ :=
  (b i j k-b j k i+b k i j)/2

def extractConnection (g : Coefficients) : ConnectionData where
  B := ![g 0 0 1,g 0 0 2]
  rotation := g 0 1 2
  chi11 := g 1 0 1
  chi12 := g 1 0 2
  chi22 := g 2 0 2
  leaf := ![g 1 1 2,g 2 1 2]

lemma koszul_metric {b : Coefficients} (hb : ∀ i j k, b i j k = -b j i k) (i j k : I) :
    koszul b i j k = -koszul b i k j := by
  have h1 := hb i j k
  have h2 := hb j k i
  have h3 := hb k i j
  unfold koszul
  linarith

lemma koszul_torsion {b : Coefficients} (hb : ∀ i j k, b i j k = -b j i k) (i j k : I) :
    koszul b i j k-koszul b j i k = b i j k := by
  have h1 := hb i j k
  have h2 := hb j k i
  have h3 := hb k i j
  unfold koszul
  linarith

lemma koszul_symmetric_chi {b : Coefficients} (hb : ∀ i j k, b i j k = -b j i k)
    (ht : ∀ a d : A, b a.succ d.succ 0 = 0) (a d : A) :
    koszul b a.succ 0 d.succ = koszul b d.succ 0 a.succ := by
  have h1 := koszul_metric hb a.succ 0 d.succ
  have h2 := koszul_metric hb d.succ 0 a.succ
  have h3 := koszul_torsion hb a.succ d.succ 0
  rw [ht] at h3
  linarith

lemma extractConnection_complete {g : Coefficients} (hg : ∀ i j k, g i j k = -g i k j)
    (hχ : g 2 0 1 = g 1 0 2) : connection (extractConnection g) = g := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [connection,extractConnection] <;>
    first | rfl | (have h := hg 0 0 0; linarith) | (have h := hg 0 1 0; linarith) |
      (have h := hg 0 2 0; linarith) | (have h := hg 0 1 1; linarith) |
      (have h := hg 0 2 1; linarith) | (have h := hg 0 2 2; linarith) |
      (have h := hg 1 0 0; linarith) | (have h := hg 1 1 0; linarith) |
      (have h := hg 1 1 1; linarith) | (have h := hg 1 2 0; linarith) |
      (have h := hg 1 2 1; linarith) | (have h := hg 1 2 2; linarith) |
      (have h := hg 2 0 0; linarith) | (have h := hg 2 1 0; linarith) |
      (have h := hg 2 1 1; linarith) | (have h := hg 2 2 0; linarith) |
      (have h := hg 2 2 1; linarith) | (have h := hg 2 2 2; linarith)

theorem adapted_koszul_complete {b : Coefficients} (hb : ∀ i j k, b i j k = -b j i k)
    (ht : ∀ a d : A, b a.succ d.succ 0 = 0) :
    connection (extractConnection (koszul b)) = koszul b := by
  apply extractConnection_complete (koszul_metric hb)
  exact koszul_symmetric_chi hb ht 1 0

end
end CKSFrame

end

end OAI
