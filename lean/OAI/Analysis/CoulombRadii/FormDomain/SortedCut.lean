import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.NuclearPotential
import OAI.Analysis.CoulombRadii.Localization.CutCore
import OAI.Analysis.CoulombRadii.FieldAnalysis.BinaryOrder

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma Antisymmetric.congr_ae {n : ℕ} {u v : H1Vector n} (hu : Antisymmetric u)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) : Antisymmetric v := by
  intro p s
  filter_upwards [(permute_measurePreserving p).quasiMeasurePreserving.ae (he (s ∘ p)),he s,hu p s] with x hx hy hz
  change u.value (s ∘ p) (permute p x)=v.value (s ∘ p) (permute p x) at hx
  rw [← hx,← hy]
  exact hz

lemma Antisymmetric.permutation {n : ℕ} {u : H1Vector n} (hu : Antisymmetric u)
    (p : Equiv.Perm (Fin n)) : Antisymmetric (u.permutation p) := by
  apply (antisymmetric_scale u hu (((p.sign:ℤ):ℂ))).congr_ae
  intro s
  filter_upwards [hu p s] with x hx
  exact hx.symm

lemma mass_congr_ae {n : ℕ} (u v : H1Vector n) (he : ∀ s, u.value s =ᵐ[volume] v.value s) :
    mass u=mass v := by
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [he s] with x hx
  rw [hx]

lemma kinetic_congr_ae {n : ℕ} (u v : H1Vector n) (he : ∀ s, u.value s =ᵐ[volume] v.value s) :
    kinetic u=kinetic v := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro a ha
  apply integral_congr_ae
  filter_upwards [u.gradient_congr_ae v he s a] with x hx
  rw [hx]

lemma potentialEnergy_congr_ae {n : ℕ} (W : Configuration n → ℝ) (u v : H1Vector n)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) : potentialEnergy W u=potentialEnergy W v := by
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [he s] with x hx
  rw [hx]

lemma form_congr_ae {J n : ℕ} (S : Nuclei J) (u v : H1Vector n)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) : form S u=form S v := by
  change kinetic u-potentialEnergy (nuclearPotential S) u+potentialEnergy pairPotential u =
    kinetic v-potentialEnergy (nuclearPotential S) v+potentialEnergy pairPotential v
  rw [kinetic_congr_ae u v he,potentialEnergy_congr_ae _ u v he,potentialEnergy_congr_ae _ u v he]

lemma form_permutation {J n : ℕ} (S : Nuclei J) (u : H1Vector n) (p : Equiv.Perm (Fin n)) :
    form S (u.permutation p)=form S u := by
  change kinetic (u.permutation p)-potentialEnergy (nuclearPotential S) (u.permutation p)+
    potentialEnergy pairPotential (u.permutation p)=_
  rw [kinetic_permutation,potentialEnergy_permutation _ (nuclearPotential_permute S),
    potentialEnergy_permutation _ pairPotential_permute]
  rfl

lemma tensorCut_permute {n : ℕ} {L : Type*} (χ : L → Space → ℝ)
    (p : Fin n → L) (q : Equiv.Perm (Fin n)) (x : Configuration n) :
    tensorCut χ p (permute q x)=tensorCut χ (p ∘ q.symm) x := by
  unfold tensorCut
  simp only [position_permute]
  calc
    _ = ∏ i, χ ((p ∘ q.symm) (q i)) (position x (q i)) := by simp only [Function.comp_apply,Equiv.symm_apply_apply]
    _ = _ := Equiv.prod_comp q (fun i => χ ((p ∘ q.symm) i) (position x i))

lemma labelCut_permute_value {n : ℕ} {L : Type*} [Fintype L] (ψ : H1Vector n)
    (χ : L → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → L) (q : Equiv.Perm (Fin n)) (s : Spins n) (x : Configuration n) :
    ((ψ.labelCut χ hχ hp D hD hd p).permutation q).value s x =
      ((ψ.permutation q).labelCut χ hχ hp D hD hd (p ∘ q.symm)).value s x := by
  change (↑(tensorCut χ p (permute q x)):ℂ)*ψ.value (s ∘ q) (permute q x) = _
  rw [tensorCut_permute]
  rfl

theorem binary_cut_core_outcome {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (χ l))
    (hp : ∀ z, ∑ l, χ l z^2=1) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ l b z, |fderiv ℝ (χ l) z (EuclideanSpace.single b 1)| ≤ D)
    (p : Fin n → Fin 2) (A : Set Space) (hA : ∀ z ∉ A, χ 1 z=0) :
    ∃ m k : ℕ, ∃ u : H1Vector (m+k), m+k=n ∧
      mass u=mass (ψ.labelCut χ hχ hp D hD hd p) ∧
      form S u=form S (ψ.labelCut χ hχ hp D hD hd p) ∧
      (∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x)) ∧
      (∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x) A) := by
  obtain ⟨m,k,e,he0,he1⟩ := exists_binary_order p
  have hn : m+k=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  let v := ψ.labelCut χ hχ hp D hD hd p
  let u := (ψ.permutation e.symm).labelCut χ hχ hp D hD hd (p ∘ e)
  have hval (s : Spins (m+k)) : (v.permutation e.symm).value s =ᵐ[volume] u.value s := by
    exact Eventually.of_forall (fun x => labelCut_permute_value ψ χ hχ hp D hD hd p e.symm s x)
  refine ⟨m,k,u,rfl,?_,?_,?_,?_⟩
  · rw [← mass_congr_ae _ _ hval,mass_permutation]
  · rw [← form_congr_ae S _ _ hval,form_permutation]
  · intro s
    exact labelCut_core_antisymmetric _ (hψ.permutation e.symm) χ hχ hp D hD hd
      (p ∘ e) 1 he1 s
  · intro s
    exact labelCut_core_support _ χ hχ hp D hD hd (p ∘ e) 1 he1 A hA s

end Coulomb
end

end
end

end OAI
