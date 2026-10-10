import OAI.Combinatorics.Ramsey.CycleClique.Construction.NormalizedIncident
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawReplacementProfiles

namespace OAI

/-! A replacement between two starting vertices activates exactly the
singleton chains among its targets. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem starting_replacement_incident (U T : RawPathSystem G Q)
    {P M R : List (List V)} {B D J : List V} {x y : V}
    (hsys : U.chains = P ++ (x :: B) :: M ++ (y :: D) :: R)
    (htsys : T.chains = P ++ [] :: M ++ [] :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    T.normalize.incident = U.normalize.incident +
      (if B = [] then 1 else 0) + (if D = [] then 1 else 0) := by
  have hmemB : x :: B ∈ U.chains := by simp [hsys]
  have hmemD : y :: D ∈ U.chains := by simp [hsys]
  have hB : activeCliqueCount Q (x :: B) + (if B = [] then 1 else 0) =
      chainCliqueCount Q (x :: B) := by
    simpa using activeCliqueCount_add_singleton (by simp)
      (U.endpoints _ hmemB) (U.no_clique_steps _ hmemB)
  have hD : activeCliqueCount Q (y :: D) + (if D = [] then 1 else 0) =
      chainCliqueCount Q (y :: D) := by
    simpa using activeCliqueCount_add_singleton (by simp)
      (U.endpoints _ hmemD) (U.no_clique_steps _ hmemD)
  have hmerged : activeCliqueCount Q (B.reverse ++ x :: (J ++ y :: D)) =
      chainCliqueCount Q (x :: B) + chainCliqueCount Q (y :: D) := by
    have heq : B.reverse ++ x :: (J ++ y :: D) = (x :: B).reverse ++ J ++ (y :: D) := by
      simp [List.append_assoc]
    have hlen : 3 ≤ (B.reverse ++ x :: (J ++ y :: D)).length := by
      have hh := List.length_pos_iff.mpr hJne
      simp only [List.length_append, List.length_reverse, List.length_cons]
      omega
    simp only [activeCliqueCount, hlen, ↓reduceIte]
    rw [heq, chainCliqueCount_append,
      chainCliqueCount_append, chainCliqueCount_reverse, chainCliqueCount_eq_zero hJQ]
    omega
  rw [normalize_incident, normalize_incident]
  simp only [htsys, hsys, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons, activeCliqueCount_nil]
  omega

theorem starting_replacement_incident_le (U T : RawPathSystem G Q)
    {P M R : List (List V)} {B D J : List V} {x y : V}
    (hsys : U.chains = P ++ (x :: B) :: M ++ (y :: D) :: R)
    (htsys : T.chains = P ++ [] :: M ++ [] :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hJQ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    T.normalize.incident ≤ U.normalize.incident + 2 := by
  rw [starting_replacement_incident U T hsys htsys hJQ hJne]
  split_ifs <;> omega

end CycleClique.Construction.RawPathSystem

end OAI
