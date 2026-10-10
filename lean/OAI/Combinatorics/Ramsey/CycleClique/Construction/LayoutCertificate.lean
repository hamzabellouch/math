import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayoutRefutation
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ClosureSteps

namespace OAI

/-! A complete finite obstruction certificate: verified indexed layout,
initial templates, required paths, closure steps, and final contradiction. -/

namespace CycleClique.Construction
structure LayoutCertificate (n : ℕ) where
  chains : List (List (Fin n))
  clique : Finset (Fin n)
  templates : List (TemplateData (Fin n))
  required : List (RequiredPathData (Fin n))
  closure : List (ClosureStep n)
  bad : BadData n
  deriving DecidableEq

namespace LayoutCertificate

variable {n : ℕ}

def graph (c : LayoutCertificate n) : SimpleGraph (Fin n) := layoutGraph c.clique c.chains

instance (c : LayoutCertificate n) : DecidableRel c.graph.Adj :=
  inferInstanceAs (DecidableRel (layoutGraph c.clique c.chains).Adj)

def initialMatrix (k : ℕ) (c : LayoutCertificate n) : ForbiddenMatrix n :=
  fun i j => templateMatrix c.templates i j ∪ requiredMatrix k c.required i j

def matrix (k : ℕ) (c : LayoutCertificate n) : ForbiddenMatrix n :=
  closureMatrix (c.initialMatrix k) c.closure

def Check (k t : ℕ) (P : List (List ℕ)) (c : LayoutCertificate n) : Prop :=
  c.chains.flatten = List.finRange n ∧
  c.chains.map List.length = P.map (fun w => w.sum + w.length + 1) ∧
  c.chains.map (fun l => l.map (fun i => decide (i ∈ c.clique))) = P.map profileMask ∧
  (∀ T ∈ c.templates, T.Check c.graph c.clique k (patternAmount P) (P.map List.length).sum) ∧
  (∀ p ∈ c.required, p.Check c.graph k) ∧
  ClosureCheck c.graph (c.initialMatrix k) k t c.closure ∧
  c.bad.Check c.graph (c.matrix k) k t

instance (k t : ℕ) (P : List (List ℕ)) (c : LayoutCertificate n) :
    Decidable (c.Check k t P) := inferInstanceAs (Decidable (_ ∧ _))

open scoped Classical

variable {V : Type} [Fintype V] {G : SimpleGraph V} {Q : Finset V}

theorem false_of_check (hCE : CEAlphaTwo) {k t : ℕ}
    (hk : 5 ≤ k) (ht : 1 ≤ t) (hQk : Q.card ≤ k)
    (hQ : G.IsClique (Q : Set V)) (hcycle : ¬ HasCycle G (k + 1))
    (hclique : G.cliqueNum ≤ t) (hbound : IndependenceBound G k)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      k * I.card + 1 ≤ (closedNeighborhood G I).card)
    {S : ExpandedPathSystem G Q} (hopt : S.IsOptimal k)
    (U : RawPathSystem G Q) (hUv : U.vertices = Q ∪ S.vertices)
    (hUa : U.amount = S.amount) (hUe : U.assignedCount = S.assignedCount)
    {P : List (List ℕ)} (hp : List.Forall₂ (AssignedAmounts Q) U.chains P)
    (hne : ∀ l ∈ U.chains, l ≠ [])
    (c : LayoutCertificate n) (hc : c.Check k t P) : False := by
  classical
  obtain ⟨hi, hl, hm, hE, hR, hC, hb⟩ := hc
  have hmasks : c.chains.map (cliqueMask c.clique) = P.map profileMask := by
    calc
      _ = c.chains.map (fun l => l.map (fun i => decide (i ∈ c.clique))) := by
        apply List.map_congr_left
        intro l hl
        exact cliqueMask_eq_map c.clique l
      _ = _ := hm
  obtain ⟨f, hf, hmap, hfQ, hfG⟩ := U.realize_layout hp hne hQ c.chains c.clique hi hl hmasks
  let F : c.graph →g G := ⟨f, fun h => hfG h⟩
  have hfX : ∀ i, f i ∈ Q ∪ S.vertices := by
    intro i
    rw [← hUv]
    apply List.mem_toFinset.mpr
    rw [← hmap, ← List.map_flatten, hi]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  have hX : (Q ∪ S.vertices).card = n := by
    rw [← hUv]
    change U.chains.flatten.toFinset.card = n
    rw [List.toFinset_card_of_nodup U.flatten_nodup, ← hmap,
      ← List.map_flatten, List.length_map, hi, List.length_finRange]
  have ha : S.amount = patternAmount P := by
    rw [← hUa, U.amount_eq_outside_count, ← ChainProfiles.amount hp]
  have he : S.assignedCount = (P.map List.length).sum := by
    rw [← hUe]
    exact (ChainProfiles.assignedCount hp).symm
  have hT := templateMatrix_sound hopt (by omega) hQk hQ hcycle ha he f hf hfQ hfG
    (fun i => Finset.mem_union.mp (hfX i)) c.templates hE
  have hR' := requiredMatrix_sound (by omega) hcycle F hf hfX c.required hR
  have hM := closureMatrix_sound hCE hk ht hcycle hclique hbound F hf hfX hX
    (hT.union hR') hexpand c.closure hC
  exact c.bad.false_of_check hCE hk ht hcycle hclique hbound F hf hfX hX hM hexpand hb

end LayoutCertificate
end CycleClique.Construction

end OAI
