import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceReindex

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

def positivePivotOfPos (P : ℤ) (hP : 0 < P) : ℕ+ := ⟨P.toNat,by omega⟩

def positivePivotExtension (F : ℕ+ → ℂ) (P : ℤ) : ℂ :=
  if hP : 0 < P then F (positivePivotOfPos P hP) else 0

@[simp] theorem positivePivotExtension_coe (F : ℕ+ → ℂ) (P : ℕ+) :
    positivePivotExtension F (P:ℤ)=F P := by
  have hp : (0:ℤ) < P := by exact_mod_cast P.pos
  rw [positivePivotExtension,dite_eq_left hp]
  congr 1

lemma positivePivotOfPos_mem_image (R : Finset ℕ+) (P : ℤ) (hP : 0 < P) :
    P.toNat ∈ R.image (fun p : ℕ+ => (p:ℕ)) ↔ positivePivotOfPos P hP ∈ R := by
  classical
  constructor
  · intro hp
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hp
    have he' : positivePivotOfPos P hP=p := Subtype.ext he.symm
    simpa only [he'] using hp
  · intro hp
    exact Finset.mem_image.mpr ⟨positivePivotOfPos P hP,hp,rfl⟩

theorem positive_subtype_pivot_frequency_reindex (N : ℤ) (R : Finset ℕ+) (T : Finset ℤ)
    (F : ℕ+ → ℂ)
    (hcut : ∀ P ∈ R, ∀ s : ℤ, N ≠ 0 → N=s*(P:ℤ) → F P ≠ 0 → s ∈ T) :
    (∑ P ∈ R, if (P:ℤ) ∣ N ∧ N ≠ 0 then F P else 0)=
      ∑ s ∈ T, if hp : 0 < N/s then
        if s ≠ 0 ∧ positivePivotOfPos (N/s) hp ∈ R ∧ s*(N/s)=N
          then F (positivePivotOfPos (N/s) hp) else 0
        else 0 := by
  classical
  let Rn := R.image (fun p : ℕ+ => (p:ℕ))
  have hRn : ∀ P ∈ Rn, 0 < P := by
    intro P hP
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
    exact p.pos
  have hcutn : ∀ P ∈ Rn, ∀ s : ℤ, N ≠ 0 → N=s*(P:ℤ) →
      positivePivotExtension F (P:ℤ) ≠ 0 → s ∈ T := by
    intro P hP s hN he hf
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
    exact hcut p hp s hN he (by simpa only [positivePivotExtension_coe] using hf)
  have h := positive_pivot_frequency_reindex N Rn hRn T (positivePivotExtension F) hcutn
  have hl : (∑ P ∈ Rn, if (P:ℤ) ∣ N ∧ N ≠ 0 then positivePivotExtension F (P:ℤ) else 0)=
      ∑ P ∈ R, if (P:ℤ) ∣ N ∧ N ≠ 0 then F P else 0 := by
    dsimp only [Rn]
    rw [Finset.sum_image (g := fun p : ℕ+ => (p:ℕ)) (fun p hp q hq he => Subtype.ext he)]
    simp only [positivePivotExtension_coe]
  rw [hl] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hp : 0 < N/s
  · rw [dite_eq_left hp]
    have hm := positivePivotOfPos_mem_image R (N/s) hp
    dsimp only [Rn]
    have hciff : (s ≠ 0 ∧ 0 < N/s ∧ (N/s).toNat ∈ R.image (fun p : ℕ+ => (p:ℕ)) ∧ s*(N/s)=N) ↔
        (s ≠ 0 ∧ positivePivotOfPos (N/s) hp ∈ R ∧ s*(N/s)=N) := by
      simp only [hp,true_and,hm]
    by_cases hc : s ≠ 0 ∧ positivePivotOfPos (N/s) hp ∈ R ∧ s*(N/s)=N
    · rw [ite_eq_left (hciff.mpr hc),ite_eq_left hc,positivePivotExtension,dite_eq_left hp]
    · rw [ite_eq_right (fun hh => hc (hciff.mp hh)),ite_eq_right hc]
  · rw [dite_eq_right hp]
    exact ite_eq_right (fun hh => hp hh.2.1)

theorem reconstructedPivot_positive_subtype_reindex (k j : ℕ) (x : State k (j+1))
    (v w : ℤ) (R : Finset ℕ+) (T : Finset ℤ) (F : ℕ+ → ℂ)
    (hcut : ∀ P ∈ R, ∀ s : ℤ,
      v*copiedProduct k j false x-w*copiedProduct k j true x ≠ 0 →
      v*copiedProduct k j false x-w*copiedProduct k j true x=s*(P:ℤ) →
      F P ≠ 0 → s ∈ T) :
    (∑ P ∈ R, if (P:ℤ) ∣ v*copiedProduct k j false x-w*copiedProduct k j true x ∧
      v*copiedProduct k j false x-w*copiedProduct k j true x ≠ 0 then F P else 0)=
      ∑ s ∈ T, if hp : 0 < reconstructedPivot k j x s v w then
        if s ≠ 0 ∧ positivePivotOfPos (reconstructedPivot k j x s v w) hp ∈ R ∧
          s*reconstructedPivot k j x s v w=v*copiedProduct k j false x-w*copiedProduct k j true x
          then F (positivePivotOfPos (reconstructedPivot k j x s v w) hp) else 0
        else 0 := by
  classical
  exact positive_subtype_pivot_frequency_reindex
    (v*copiedProduct k j false x-w*copiedProduct k j true x) R T F hcut

end Ostmann.Characters.Template

end

end OAI
