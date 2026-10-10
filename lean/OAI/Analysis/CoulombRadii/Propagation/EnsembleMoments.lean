import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedEnsemble

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb
namespace RecordedEnsemble

def initial {n : ℕ} (ψ : H1Vector n) : RecordedEnsemble n where
  index := Unit
  finite := inferInstance
  out := fun _ => 0
  core := fun _ => n
  vector := fun _ => ψ.reindex (finCongr (Nat.zero_add n))
  labels := fun _ => finCongr (Nat.zero_add n)

lemma initial_conserves {n : ℕ} (ψ : H1Vector n) : (initial ψ).Conserves ψ := by
  intro W hW hB
  change (∑ p : Unit, potentialForm (W ∘ reindexConfiguration (finCongr (Nat.zero_add n)))
    (ψ.reindex (finCongr (Nat.zero_add n))))=potentialForm W ψ
  simp only [potentialForm_reindex]
  simp

lemma initial_fermionic {n : ℕ} (ψ : H1Vector n) (hψ : Antisymmetric ψ) :
    (initial ψ).CoreFermionic := by
  intro p
  exact (hψ.reindex _).partly _

lemma initial_supported {n : ℕ} (ψ : H1Vector n) : (initial ψ).OutSupported ∅ := by
  intro p s
  exact Eventually.of_forall (fun x i hi => by obtain ⟨j,hj⟩ := hi; exact Fin.elim0 j)

lemma initial_mass {n : ℕ} (ψ : H1Vector n) : (initial ψ).totalMass=mass ψ := by
  change (∑ p : Unit, mass (ψ.reindex (finCongr (Nat.zero_add n))))=mass ψ
  simp [mass_reindex]
lemma initial_form {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) : (initial ψ).totalForm S=form S ψ := by
  change (∑ p : Unit, form S (ψ.reindex (finCongr (Nat.zero_add n))))=form S ψ
  simp [form_reindex]

lemma out_square_le {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) (hsupp : T.OutSupported A) :
    (∑ p, (T.out p:ℝ)^2*mass (T.vector p))≤localCountSecondMoment ψ A := by
  calc
    _ = ∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount A x)^2) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [←sliceExpectation_number]
      apply Finset.sum_congr rfl
      intro s hs
      apply integral_congr_ae
      filter_upwards [(hsupp p).recorded_positions s] with x hx
      by_cases hm : mass ((T.vector p).coreSlice s x)=0
      · simp only [hm,zero_mul]
      · have he : localCount A x=(T.out p:ℝ) := by simp only [localCount,indicator_of_mem (hx hm _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
        rw [he]
    _ ≤ _ := hT.recorded_secondMoment hA

lemma count_cover_le {m : ℕ} {C : Type*} [Fintype C] (A : C → Set Space)
    (x : Configuration m) (hcover : ∀ i, ∃ c, position x i∈A c) :
    (m:ℝ)≤∑ c, localCount (A c) x := by
  calc
    _ = ∑ i : Fin m, (1:ℝ) := by simp
    _ ≤ ∑ i : Fin m, ∑ c : C, (A c).indicator (fun _ => (1:ℝ)) (position x i) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨c,hc⟩ := hcover i
      calc
        1=(A c).indicator (fun _ => (1:ℝ)) (position x i) := by rw [indicator_of_mem hc]
        _≤_ := Finset.single_le_sum (fun c _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ c)
    _ = _ := Finset.sum_comm

lemma out_square_cover {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {C : Type*} [Fintype C] (A : C → Set Space)
    (hA : ∀ c, MeasurableSet (A c))
    (hcover : ∀ p s, ∀ᵐ x, mass ((T.vector p).coreSlice s x)≠0 → ∀ i, ∃ c, position x i∈A c) :
    (∑ p, (T.out p:ℝ)^2*mass (T.vector p))≤
      (Fintype.card C:ℝ)*(∑ c, localCountSecondMoment ψ (A c)) := by
  have H (p : T.index) : (T.out p:ℝ)^2*mass (T.vector p)≤
      (Fintype.card C:ℝ)*∑ c, sliceExpectation (T.vector p) (fun _ x => (localCount (A c) x)^2) := by
    rw [←sliceExpectation_number]
    change (∑ s, ∫ x, mass ((T.vector p).coreSlice s x)*(T.out p:ℝ)^2)≤_
    simp only [sliceExpectation]
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_finsetSum _ (fun c _ => sliceCount_weight_integrable (T.vector p) (hA c) s 2),←integral_const_mul]
    apply integral_mono_ae
    · exact (mass_coreSlice_integrable (T.vector p) s).mul_const _
    · exact (integrable_finsetSum _ (fun c _ => sliceCount_weight_integrable (T.vector p) (hA c) s 2)).const_mul _
    · filter_upwards [hcover p s] with x hx
      by_cases hm : mass ((T.vector p).coreSlice s x)=0
      · simp only [hm,zero_mul,Finset.sum_const_zero,mul_zero,le_refl]
      · have H := count_cover_le A x (hx hm)
        have HS := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun c => localCount (A c) x)
        simp only [Finset.card_univ] at HS
        have HG := (pow_le_pow_left₀ (Nat.cast_nonneg _) H 2).trans HS
        have HM := mul_le_mul_of_nonneg_left HG (mass_nonneg ((T.vector p).coreSlice s x))
        simpa only [Finset.mul_sum,mul_left_comm] using HM
  have HH := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => H p)
  rw [←Finset.mul_sum,Finset.sum_comm] at HH
  refine HH.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => ?_)) (Nat.cast_nonneg _))
  exact hT.recorded_secondMoment (hA c)

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
