import Mathlib

namespace OAI

section

namespace ExactQuantumFactoring.Exactness
open scoped BigOperators

noncomputable def finiteInner {ι : Type*} [Fintype ι] (v w : ι → ℂ) : ℂ :=
  ∑ x, star (v x)*w x

noncomputable def outcomeMass {ι : Type*} [Fintype ι] (good : ι → Prop) (v : ι → ℂ) : ℝ := by
  classical
  exact ∑ x, if good x then Complex.normSq (v x) else 0

noncomputable def goodPart {ι : Type*} (good : ι → Prop) (v : ι → ℂ) : ι → ℂ := by
  classical
  exact fun x => if good x then v x else 0

noncomputable def stateReflection {ι : Type*} [Fintype ι] (ψ v : ι → ℂ) : ι → ℂ :=
  fun x => 2*finiteInner ψ v*ψ x-v x

lemma finiteInner_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    finiteInner v v = ((∑ x, Complex.normSq (v x):ℝ):ℂ) := by
  simp only [finiteInner, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]

lemma finiteInner_goodPart {ι : Type*} [Fintype ι] (good : ι → Prop) (v : ι → ℂ) :
    finiteInner v (goodPart good v) = (outcomeMass good v:ℂ) := by
  classical
  unfold finiteInner goodPart outcomeMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [Complex.normSq_eq_conj_mul_self]

lemma finiteInner_sub {ι : Type*} [Fintype ι] (u v w : ι → ℂ) :
    finiteInner u (fun x => v x-w x) = finiteInner u v-finiteInner u w := by
  simp only [finiteInner, mul_sub, Finset.sum_sub_distrib]

lemma finiteInner_mul {ι : Type*} [Fintype ι] (u v : ι → ℂ) (c : ℂ) :
    finiteInner u (fun x => c*v x) = c*finiteInner u v := by
  simp only [finiteInner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Literal one-reflection identity (6.9). The amplitude is not renormalized by fiat. -/
lemma one_reflection {ι : Type*} [Fintype ι] (good : ι → Prop) (ψ : ι → ℂ)
    (hψ : (∑ x, Complex.normSq (ψ x))=1) (hg : outcomeMass good ψ=1/4) :
    stateReflection ψ (fun x => ψ x-2*goodPart good ψ x) = fun x => 2*goodPart good ψ x := by
  have h := finiteInner_goodPart good ψ
  rw [hg] at h
  have hn := finiteInner_self ψ
  rw [hψ] at hn
  ext x
  simp only [stateReflection, finiteInner_sub, finiteInner_mul, h, hn]
  norm_num

lemma amplified_mass {ι : Type*} [Fintype ι] (good : ι → Prop) (ψ : ι → ℂ)
    (hg : outcomeMass good ψ=1/4) :
    outcomeMass good (fun x => 2*goodPart good ψ x)=1 := by
  classical
  have he : outcomeMass good (fun x => 2*goodPart good ψ x)=4*outcomeMass good ψ := by
    unfold outcomeMass goodPart
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : good x
    · simp [hx, Complex.normSq_mul]
      norm_num
    · simp [hx]
  rw [he,hg]
  norm_num

/-- Exact success also applies to the externally requested correct-output predicate. -/
lemma one_reflection_correct {ι : Type*} [Fintype ι]
    (good correct : ι → Prop) (ψ : ι → ℂ)
    (hψ : (∑ x, Complex.normSq (ψ x))=1)
    (hg : outcomeMass good ψ=1/4) (hc : ∀ x, good x → correct x) :
    outcomeMass correct (stateReflection ψ (fun x => ψ x-2*goodPart good ψ x))=1 := by
  classical
  rw [one_reflection good ψ hψ hg]
  have he : outcomeMass correct (fun x => 2*goodPart good ψ x)=
      outcomeMass good (fun x => 2*goodPart good ψ x) := by
    unfold outcomeMass goodPart
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : good x
    · simp [hx,hc x hx]
    · simp [hx]
  rw [he]
  exact amplified_mass good ψ hg

end ExactQuantumFactoring.Exactness


end

end OAI
