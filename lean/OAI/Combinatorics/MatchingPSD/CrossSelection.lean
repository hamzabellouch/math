import OAI.Combinatorics.MatchingPSD.TableGeometry

namespace OAI

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma simultaneous_cross_approximation (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (V G I T : Type) [Fintype V] [Fintype G] [Group G] [Fintype I] [Fintype T]
      (_e : V ≃ Vertices h) (z : I → V → Fin 3), (∀ i c, 0 < histogram (z i) c) →
      ∀ (M : I → T → Pairing V)
      (lift : I → Equiv.Perm V → G)
      (g : I → G → Pairing V → ℝ),
      (∀ i a p, g i (a * lift i p) = fun N => g i a (Pairing.relabel p N)) →
      ∀ B : ℝ, (∀ i a N, (g i a N)^2 ≤ B^2) →
      ∃ a : G, ∃ P : I → (Fin 3 → ℝ) → ℝ,
        (∀ i, P i ∈ lowDegree (fun c (v : Fin 3 → ℝ) => v c) d) ∧
        (∑ i, ∑ t : T,
          (predicateAverage (fun N => crossVector (z i) N = crossVector (z i) (M i t)) (g i a) -
            P i (crossVector (z i) (M i t)))^2)
          ≤ (Fintype.card I : ℝ) * Fintype.card T * ((2*h : ℝ)^(2*K))⁻¹ * B^2 := by
  classical
  obtain ⟨d,H,hd,hmain⟩ := simultaneous_table_approximation K
  refine ⟨d,H,hd,?_⟩
  intro h hh V G I T _ _ _ _ _ e z hz M lift g hcov B hB
  let ev := Pairing.transportEquiv e.symm
  let z' := fun i => z i ∘ e.symm
  let M' := fun i t => Pairing.transport e (M i t)
  let lift' := fun i (p : Equiv.Perm (Vertices h)) => lift i (e.trans (p.trans e.symm))
  let g' := fun i a N => g i a (ev N)
  have hc (i : I) (a : G) (p : Equiv.Perm (Vertices h)) :
      g' i (a * lift' i p) = fun N => g' i a (Pairing.relabel p N) := by
    funext N
    change g i (a * lift' i p) (ev N) = _
    rw [hcov]
    change g i a (Pairing.relabel (e.trans (p.trans e.symm)) (Pairing.transport e.symm N)) =
      g i a (Pairing.transport e.symm (Pairing.relabel p N))
    rw [Pairing.transport_relabel]
    rfl
  obtain ⟨a,P,hP,hbound⟩ := hmain h hh G I T z'
    (fun i c => by
      have he : histogram (z' i) = histogram (z i) := histogram_comp_equiv (z i) e.symm
      rw [he]
      exact hz i c)
    M' lift' g' hc B (fun i a N => hB i a (ev N))
  refine ⟨a,P,hP,?_⟩
  have hvec (i : I) (t : T) : crossVector (z' i) (M' i t) = crossVector (z i) (M i t) := by
    rw [crossVector_transport]
    have he : z' i ∘ e = z i := by funext v; simp [z']
    rw [he]
  have hav (i : I) (t : T) :
      predicateAverage (fun N => N.table (z' i) = (M' i t).table (z' i)) (g' i a) =
        predicateAverage (fun N => crossVector (z i) N = crossVector (z i) (M i t)) (g i a) := by
    apply predicateAverage_equiv ev
    intro N
    rw [table_eq_iff_cross, hvec]
    change _ ↔ crossVector (z i) (Pairing.transport e.symm N) = _
    rw [crossVector_transport]
  have htvec (i : I) (t : T) :
      (fun c => ((M' i t).table (z' i) (threeEdgeType (crossPair c)) : ℝ)) =
        crossVector (z i) (M i t) := by
    rw [← hvec]
    funext c
    exact (crossCoordinate_eq_table _ _ _).symm
  simpa only [hav, htvec] using hbound

end MatchingSmoothing

end OAI
