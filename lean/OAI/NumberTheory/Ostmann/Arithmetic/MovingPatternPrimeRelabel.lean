import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPatternMean
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalWeightRelabel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkData

namespace OAI

/-! # The original pattern prime integral in the arithmetic coordinates -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingPatternFinData_evaluate {σ B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
    (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → σ) (b : Bool) :
    (movingPatternFinData e n t small bulk pattern b).map x =
      buildMovingSlotData n (t b)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (small b))
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n (bulk b))
        (movingPatternSamples σ n (fun i => x (e.symm (.inr (pattern i)))) b) := by
  rw [movingPatternFinData_build, buildMovingSlotData_map]
  simp only [movingPatternFiniteSmall, treeLeafMap_list_comp, movingPatternFiniteSamples,
    movingPatternSamples_map]
  rfl

/-- The supported prime term of the original pattern, with its values pulled
back along the finite assignment. -/
noncomputable def movingPatternSupportedPrimeTerm {σ I B C : Type}
    {N n : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (pattern : Bool × MovingSampleIndex n → C)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (x : Fin (N + 1) → σ) (b : Bool) (XL XR : ℕ) : ℂ :=
  let T := movingPatternFinData e n t (fun _ => small) (fun _ => bulk) pattern b
  movingSupportedWeight (value ∘ x) outside T XL XR
    (movingOriginalGiantWeight q (value ∘ x) childBound pivotBound
      (fun T => F (T.map x)) (fun _ _ _ _ => 1) g Dq S ψ X lo hi φ G T (t b) XL XR)

theorem movingOriginalPatternPrimeObservable_fin {σ I B C : Type}
    {N n : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (pattern : Bool × MovingSampleIndex n → C)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {d : ℕ} → MovingSlotData σ d → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (t : Bool → FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (u v r w : ℝ) (x : Fin (N + 1) → σ) :
    movingOriginalPatternPrimeObservable e pattern q value outside childBound pivotBound F g Dq S
      ψ X lo hi φ G t small bulk u v r w x =
    complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun z =>
      movingPatternSupportedPrimeTerm e pattern q value outside childBound pivotBound F g Dq S
        ψ X lo hi φ G t small bulk x false ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊ *
      star (movingPatternSupportedPrimeTerm e pattern q value outside childBound pivotBound F g Dq S
        ψ X lo hi φ G t small bulk x true ⌊Real.exp z⌋₊ ⌊Real.exp y⌋₊))) := by
  have hterm (b : Bool) (XL XR : ℕ) :
      let T := buildMovingSlotData n (t b)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n small)
        (treeLeafMap (List.map (fun j => x (e.symm (.inl j)))) n bulk)
        (movingPatternSamples σ n (fun i => x (e.symm (.inr (pattern i)))) b)
      movingSupportedWeight value outside T XL XR
        (movingOriginalGiantWeight q value childBound pivotBound F (fun _ _ _ _ => 1)
          g Dq S ψ X lo hi φ G T (t b) XL XR) =
      movingPatternSupportedPrimeTerm e pattern q value outside childBound pivotBound F g Dq S
        ψ X lo hi φ G t small bulk x b XL XR := by
    dsimp only
    rw [← movingPatternFinData_evaluate e t (fun _ => small) (fun _ => bulk) pattern x b,
      movingOriginalGiantWeight_map, movingSupportedWeight_map]
    rfl
  unfold movingOriginalPatternPrimeObservable movingOriginalPairPrimeKernel
  change complexPrimeInterval 1 0 r w (fun y => complexPrimeInterval 1 0 u v (fun z =>
    _ * star _)) = _
  simp_rw [← hterm]
  rfl

end Ostmann

end OAI
