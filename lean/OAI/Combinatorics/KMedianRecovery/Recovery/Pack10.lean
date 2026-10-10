import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.StoredForms
import OAI.Combinatorics.KMedianRecovery.Recovery.Rectangular

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningOracle
open WordOperations BinaryArithmetic RationalLinearFeasibility RationalOpenability
open EffectiveOpenability BinaryExactSolve

def pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : List Bool :=
  BinaryRationalDecision.pack
    ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map
      (fun r=>(forms distance F W v z lam eta i r).enumeratedRow (variableEnum d F)))
    ⌈(1+v^2)*z⌉₊

def resultBits {m d : ℕ} (F : Finset (Fin m)) :
    Option (Variables (Fin d) F → ℚ) → List Bool
  | none=>[]
  | some x=>true::RationalMatrix.rowEncode (fun j=>x (variableEnum d F j))

lemma run_eq {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) :
    BinaryExactSolve.run (pack distance F W v z lam eta i)=
      resultBits F (storedOpening distance F W v z lam eta i) := by
  unfold pack storedOpening storedForms
  rw [BinaryExactSolve.run_pack,Ellipsoid.Stored.exactSolve_eq]
  cases h : Ellipsoid.exactSolve
      ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map
        (fun r=>(forms distance F W v z lam eta i r).enumeratedRow (variableEnum d F)))
      ⌈(1+v^2)*z⌉₊ with
  | none=>rfl
  | some y=>simp only [Option.map_some,resultBits,BinaryExactSolve.resultBits,Equiv.symm_apply_apply]

lemma resultBits_eq_nil_iff {m d : ℕ} (F : Finset (Fin m))
    (o : Option (Variables (Fin d) F → ℚ)) : resultBits F o=[] ↔ o=none := by
  cases o <;> simp [resultBits]

lemma nil_iff {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    BinaryExactSolve.run (pack distance F W v z lam eta i)=[] ↔
      ¬etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  rw [run_eq,resultBits_eq_nil_iff]
  exact storedOpening_none_iff loc distance hd F W v z lam eta i hv hv1 hz

lemma witness {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (h : BinaryExactSolve.run (pack distance F W v z lam eta i)≠[]) :
    ∃ x : Variables (Fin d) F → ℚ,
      BinaryExactSolve.run (pack distance F W v z lam eta i)=resultBits F (some x) ∧
      OpenabilityLinearization.Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
        (fun j=>(x (.inl j):ℝ)) (fun f a j=>(x (.inr (f,a,j)):ℝ)) := by
  cases he : storedOpening distance F W v z lam eta i with
  | none=>exact (h (by rw [run_eq,he]; rfl)).elim
  | some x=>exact ⟨x,by rw [run_eq,he],storedOpening_witness loc distance hd F W v z lam eta i x he⟩

lemma row_count {m d : ℕ} (F W : Finset (Fin m)) :
    (kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).length=
      3*d+d*W.card+1+2*(F.card*d*d)+F.card*d := by
  rw [length_kindRows,List.length_ofFn,subtypeList_length,subtypeList_length]

end MetricKMedianRecovery.BitMachine.BinaryOpeningOracle

end OAI
