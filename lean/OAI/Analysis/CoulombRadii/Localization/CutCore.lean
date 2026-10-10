import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PermuteJoinBlock
import OAI.Analysis.CoulombRadii.FieldAnalysis.CorePerm
import OAI.Analysis.CoulombRadii.Localization.CutCombinatorics

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma tensorCut_permute_invariant {n : ℕ} {L : Type*} (χ : L → Space → ℝ)
    (p : Fin n → L) (q : Equiv.Perm (Fin n)) (hp : ∀ i, p (q i)=p i) (x : Configuration n) :
    tensorCut χ p (permute q x) = tensorCut χ p x := by
  unfold tensorCut
  simp only [position_permute]
  calc
    _ = ∏ i, χ (p (q i)) (position x (q i)) := by simp only [hp]
    _ = _ := Equiv.prod_comp q (fun i => χ (p i) (position x i))

lemma labelCut_core_antisymmetric {m k : ℕ} {L : Type*} [Fintype L]
    (ψ : H1Vector (m+k)) (hψ : Antisymmetric ψ)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+k) → L) (l : L) (hc : ∀ i, p (Fin.natAdd m i)=l) (s : Spins m) :
    ∀ᵐ x, Antisymmetric ((ψ.labelCut χ hχ hp D hD hd p).coreSlice s x) := by
  apply H1Vector.coreSlice_antisymmetric
  intro q t
  filter_upwards [hψ (corePerm m q) (Fin.append s t)] with z hz
  have H (i : Fin (m+k)) : p (corePerm m q i)=p i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [corePerm_left]
    · intro j
      rw [corePerm_right,hc,hc]
  change (↑(tensorCut χ p (permute (corePerm m q) z)) : ℂ)*
    ψ.value (Fin.append s t ∘ corePerm m q) (permute (corePerm m q) z)=_
  rw [tensorCut_permute_invariant χ p _ H,hz]
  change (↑(tensorCut χ p z) : ℂ)*((((corePerm m q).sign:ℤ):ℂ)*ψ.value (Fin.append s t) z) =
    (((corePerm m q).sign:ℤ):ℂ)*((↑(tensorCut χ p z):ℂ)*ψ.value (Fin.append s t) z)
  ring

lemma SpatiallySupported.rsmul {n : ℕ} {u : H1Vector n} {A : Set Space}
    (hu : SpatiallySupported u A) (c : ℝ) : SpatiallySupported (u.rsmul c) A := by
  intro s
  filter_upwards [hu s] with x hx hxA
  change (c:ℂ)*u.value s x=0
  rw [hx hxA,mul_zero]
lemma SpatiallySupported.normalized {n : ℕ} {u : H1Vector n} {A : Set Space}
    (hu : SpatiallySupported u A) : SpatiallySupported u.normalized A := hu.rsmul _

lemma labelCut_core_support {m k : ℕ} {L : Type*} [Fintype L]
    (ψ : H1Vector (m+k))
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z ^ 2 = 1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin (m+k) → L) (l : L) (hc : ∀ i, p (Fin.natAdd m i)=l)
    (A : Set Space) (hA : ∀ z ∉ A, χ l z=0) (s : Spins m) :
    ∀ᵐ x, SpatiallySupported ((ψ.labelCut χ hχ hp D hD hd p).coreSlice s x) A := by
  let u := ψ.labelCut χ hχ hp D hD hd p
  filter_upwards [u.coreSliceRegular_ae s] with x hx
  intro t
  filter_upwards [] with z hz
  rw [u.coreSlice_value s hx]
  change (↑(tensorCut χ p (joinConfiguration m k (x,z))):ℂ)*ψ.value (Fin.append s t)
    (joinConfiguration m k (x,z))=0
  have hi : ∃ i : Fin k, position z i ∉ A := by
    simpa only [allPositions,Set.mem_ofPred_eq,not_forall] using hz
  obtain ⟨i,hi⟩ := hi
  have H : tensorCut χ p (joinConfiguration m k (x,z))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (Fin.natAdd m i))
    rw [hc,position_join_right,hA _ hi]
  rw [H,Complex.ofReal_zero,zero_mul]

end Coulomb
end

end
end

end OAI
